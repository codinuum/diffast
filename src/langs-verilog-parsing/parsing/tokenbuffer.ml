(*
   Copyright 2012-2025 Codinuum Software Lab <https://codinuum.com>

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(*
 * tokenbuffer.ml
 *
 * Buffer for tokens in preprocessor conditional branches
 *
 *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xqueue = Diffast_misc.Xqueue
module Xstring = Diffast_misc.Xstring

open Common
module Loc = Ast.Loc
module Aux = Parser_aux
module L = Label
module C = Context


let sprintf = Printf.sprintf


let lexposs_to_offsets (st_pos, ed_pos) =
  st_pos.Lexing.pos_cnum, ed_pos.Lexing.pos_cnum

type branch_tag =
  | BTifdef  of string * Loc.t
  | BTifndef of string * Loc.t
  | BTelsif  of string
  | BTelse
  | BTcontext
  | BTselected
  | BTdummy

let branch_tag_to_string = function
  | BTifdef(s, loc)  -> sprintf "BTifdef:%s[%s]" s (Loc.to_string ~short:true loc)
  | BTifndef(s, loc) -> sprintf "BTifndef:%s[%s]" s (Loc.to_string ~short:true loc)
  | BTelsif s        -> "BTelsif:"^s
  | BTelse           -> "BTelse"
  | BTcontext        -> "BTcontext"
  | BTselected       -> "BTselected"
  | BTdummy          -> "BTdummy"

let loc_of_branch_tag = function
  | BTifdef(_, loc)
  | BTifndef(_, loc) -> loc
  | btag -> raise (Invalid_argument (sprintf "Tokenbuffer.loc_of_branch_tag: %s" (branch_tag_to_string btag)))


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  module Tokens = Tokens_
  module Tok = Token.F (Stat)
  module U = Ulexer.F (Stat)
  module A = Aux.F (Stat)

  open Tokens
  open Stat


  let merge_locs = PB.merge_locs ~cache:(Some env#fname_ext_cache)

  let make_branch_tag iftok idtok loc =
    let id =
      match idtok with
      | IDENTIFIER s -> s
      | tok ->
          raise (Invalid_argument
                   ("Tokenbuffer.make_branch_tag: invalid idtoken: "^(Token.rawtoken_to_string tok)))
    in
    match iftok with
    | PP_IFDEF  -> BTifdef(id, loc)
    | PP_IFNDEF -> BTifndef(id, loc)
    | PP_ELSIF  -> BTelsif id
    | PP_ELSE   -> BTelse
    | tok ->
        raise (Invalid_argument
                 ("Tokenbuffer.make_branch_tag: invalid iftoken: "^(Token.rawtoken_to_string tok)))





  type token = Tokens.token * Lexing.position * Lexing.position

  type partial_parser = (token, Ast.partial) MenhirLib.Convert.revised


  exception Not_active

  exception Buffer_empty

  exception Incomplete

  type parse_result =
    | Rcomplete of Ast.partial
    | Rincomplete
    | Runknown


  let peek_nth queue n =
    let q = ref [] in
    Queue.iter (fun x -> q := x :: !q) queue;
    try
      List.nth (List.rev !q) (n - 1)
    with
      _ -> raise Buffer_empty

(*
  let check_error partial =
  let nodes = Ast.nodes_of_partial partial in
  List.iter
  (fun node ->
  Ast.visit
  (fun lab ->
  if L.is_error lab then
  raise Incomplete
  ) node
  ) nodes
 *)

  let check_partial partial =
    let nodes = Ast.nodes_of_partial partial in
    let nnodes = ref 0 in
    let nerrs = ref 0 in
    List.iter
      (fun node ->
        Ast.visit
          (fun nd ->
            incr nnodes;
            if L.is_error nd#label then
              incr nerrs
          ) node
      ) nodes;
    [%debug_log "nnodes=%d, nerrs=%d" !nnodes !nerrs];
    !nnodes, !nerrs


  class buffer_base = object (self : 'self)
    val mutable queue : Token.qtoken_t Xqueue.c = new Xqueue.c
    val mutable ast_cache = Runknown

    method get_list_rev = queue#fold (fun l x -> x :: l) []
    method get_list = List.rev self#get_list_rev

    method _set_queue q = queue <- q
    method _raw = queue
    method clear = queue#clear

    method _add qtoken =
      ast_cache <- Runknown;
       queue#add qtoken

    method add qtoken =
      self#_add qtoken

    method iter f =
       queue#iter f

    method size =  queue#length
    method total_size =
      let sz = ref 0 in
      self#iter
        (fun (tok, _) ->
          sz := !sz + (Tok.size tok)
        );
      !sz

    method is_empty =  queue#is_empty

    method peek =
      try
         queue#peek
      with
        Xqueue.Empty -> raise Buffer_empty

    method peek_nth n =
      try
        queue#peek_nth n
      with
        _ -> raise Buffer_empty

    method take =
      try
        queue#take
      with
        Xqueue.Empty -> raise Buffer_empty

    method receive_all : 'self -> unit =
      fun buf ->
        let q = buf#_raw in
        if q#length > 0 then
          ast_cache <- Runknown;
        q#transfer queue


    method dump =
      [%debug_log "%s" self#to_string]

    method to_string =
      let buf = Buffer.create 0 in
      self#iter
        (fun qtok ->
          Buffer.add_string buf
            (sprintf "%s\n" (Token.qtoken_to_string qtok))
        );
      Buffer.contents buf

    method get_loc =
      try
        let qtoken = queue#peek in
        let _, st = qtoken in

        [%debug_log "start token: %s" (Token.qtoken_to_string qtoken)];

        let ed = ref st in
        self#iter (fun (_, loc) -> ed := loc);
        merge_locs st !ed
      with
        Xqueue.Empty -> raise Buffer_empty

    method get_last =
      if self#size > 0 then
        let last = ref (EOF, Loc.dummy) in
        queue#iter (fun x -> last := x);
        !last
      else
        raise Buffer_empty

    method parse_by : ?cache:bool -> partial_parser -> Ast.partial =
      fun ?(cache=true) _parser ->
        [%debug_log "called"];

        match ast_cache with
        | Rcomplete p ->
            [%debug_log "using cached value (complete)"];
            p

        | Rincomplete ->
            [%debug_log "using cached value (incomplete)"];
            raise Incomplete

        | Runknown ->
            let copied = queue#copy in

            let last_tok = ref EOP in
            let last_loc = ref Loc.dummy in

            let eop_flag = ref false in

            let scanner() =
              try
                let qtoken = copied#take in
                let tok, loc = qtoken in

                [%debug_log "---> %s" (Token.qtoken_to_string qtoken)];

                let st, ed = Loc.to_lexposs loc in
                last_tok := tok;
                last_loc := loc;

                tok, st, ed

              with
              | Xqueue.Empty ->
                  if !eop_flag then
                    raise End_of_file
                  else begin
                    let _, ed = Loc.to_lexposs !last_loc in
                    eop_flag := true;

                    begin %debug_block
                      [%debug_log "last token: %s" (Token.qtoken_to_string (!last_tok, !last_loc))];
                      [%debug_log "EOP[%s]" (Loc.to_string ~short:true (Loc.of_lexposs ed ed))];
                    end;

                    EOP, ed, ed
                  end
            in
            env#set_partial_parsing_flag;
            try
              let p = _parser scanner in
              env#clear_partial_parsing_flag;

              [%debug_log "PARSED"];

              if cache then
                ast_cache <- Rcomplete p;
              p

            with
              _ ->
                [%debug_log "FAILED"];
                env#clear_partial_parsing_flag;
                if cache then
                  ast_cache <- Rincomplete;
                raise Incomplete
    (* end of method parse_by *)

  end (* class Tokenbuffer.buffer_base *)


  class buffer (btag : branch_tag) = object (self : 'self)
    inherit buffer_base

    val mutable context = C.unknown()

    method set_context c =
      [%debug_log "[%s]: %s" (branch_tag_to_string btag) (C.to_string c)];
      context <- c

    method get_context = context

    method get_tag = btag

    method get_copy =
      [%debug_log "called"];
      let copy = new buffer btag in
      copy#_set_queue queue#copy;
      copy#set_context context;
      copy

    method! parse_by : ?cache:bool -> partial_parser -> Ast.partial =
      fun ?(cache=true) _parser ->
        [%debug_log "called"];

        match ast_cache with
        | Rcomplete p ->
            [%debug_log "using cached value (complete)"];
            p

        | Rincomplete ->
            [%debug_log "using cached value (incomplete)"];
            raise Incomplete

        | Runknown ->
            let copied = queue#copy in

            let last_tok = ref EOP in
            let last_loc = ref Loc.dummy in

            let prev_tok = ref EOP in
            let prev_loc = ref Loc.dummy in

            let eop_flag = ref false in

            let scanner() =
              try
                let qtoken = copied#take in
                let tok, loc = qtoken in

                [%debug_log "%s" (Token.qtoken_to_string qtoken)];

                let st, ed = Loc.to_lexposs loc in
                prev_tok := !last_tok;
                prev_loc := !last_loc;
                last_tok := tok;
                last_loc := loc;

                context_stack#deactivate_top;

                if env#context_enter_flag then begin
                  env#clear_context_enter_flag;
                  env#set_last_active_ofss (Loc.to_offsets !last_loc)
                end;
                if env#context_activate_flag then begin
                  env#clear_context_activate_flag;
                  env#set_last_active_ofss (Loc.to_offsets !prev_loc)
                end;

                tok, st, ed

              with
              | Xqueue.Empty ->
                  if !eop_flag then
                    raise End_of_file
                  else begin
                    let _, ed = Loc.to_lexposs !last_loc in
                    eop_flag := true;

                    begin %debug_block
                      [%debug_log "last token: %s" (Token.qtoken_to_string (!last_tok, !last_loc))];
                      [%debug_log "EOP[%s]" (Loc.to_string ~short:true (Loc.of_lexposs ed ed))];
                    end;

                    EOP, ed, ed
                  end
            in
            env#set_partial_parsing_flag;
            try
              let p = _parser scanner in
              env#clear_partial_parsing_flag;
(*
  check_error p;
 *)
              [%debug_log "[%s] parsed!" (branch_tag_to_string btag)];

              if cache then
                ast_cache <- Rcomplete p;
              p

            with
              _ ->
                [%debug_log "[%s] failed to parse!" (branch_tag_to_string btag)];
                env#clear_partial_parsing_flag;
                if cache then
                  ast_cache <- Rincomplete;
                raise Incomplete
    (* end of method parse_by *)


    method to_partial partial =

      match partial with
      | Ast.Pdescription_list ds ->
          self#clear;
          List.iter (fun d -> self#add (Tok.of_description d)) ds

      | Ast.Pmodule_item_list mis ->
          self#clear;
          List.iter (fun mi -> self#add (Tok.of_module_item mi)) mis

      | Ast.Pgenerate_item_list gis ->
          self#clear;
          List.iter (fun gi -> self#add (Tok.of_generate_item gi)) gis

      | Ast.Pblock_decl_stmt_list bdss ->
          self#clear;
          List.iter
            (fun bds ->
              let tok =
                if Ast.is_block_item_declaration bds then
                  Tok.of_block_item_declaration bds

                else
                  if Ast.is_stmt bds then
                    Tok.of_stmt bds
                  else begin
                    Printer.dump bds;
                    assert false
                  end
              in
              self#add tok
            ) bdss

      | Ast.Pcase_item_list cis ->
          self#clear;
          List.iter (fun ci -> self#add (Tok.of_case_item ci)) cis

      | Ast.Pcase_inside_item_list ciis ->
          self#clear;
          List.iter (fun cii -> self#add (Tok.of_case_inside_item cii)) ciis

      | Ast.Pcellpin_list _ -> begin
          let rawtok, loc = self#get_last in
          match rawtok with
          | COMMA -> ()
          | _ ->
              let _, ed = Loc.to_lexposs loc in
              let ed_ = Loc.incr_lexpos ed in
              self#add (PB.make_qtoken COMMA ed_ ed_)
      end

      | Ast.Plist_of_ports _ -> begin
          let rawtok, loc = self#get_last in
          match rawtok with
          | COMMA -> ()
          | _ ->
              let _, ed = Loc.to_lexposs loc in
              let ed_ = Loc.incr_lexpos ed in
              self#add (PB.make_qtoken COMMA ed_ ed_)
      end
      | Ast.Pexpr e -> begin
          self#clear;
          self#add (Tok.of_expr e)
      end

    (* end of method to_partial *)


  end (* of class buffer *)


  class branching_buffer btag = object (self)
    val stack = Stack.create()

    val mutable context = C.unknown()

    method get_tag = btag

    method get_context = context

    method branch_tag = btag

    method set_context c =
      [%debug_log "[%s]: %s" (branch_tag_to_string btag) (C.to_string c)];
      context <- c;
      self#iter_branch (fun buf -> buf#set_context c)


    method top =
(*    [%debug_log "called"]; *)
      Stack.top stack

    method new_branch btag =
      [%debug_log "called"];
      let buf = new buffer btag in
      buf#set_context context;
      Stack.push buf stack

    method add qtoken =
(*    [%debug_log "called"]; *)
      self#top#add qtoken

    method iter_branch f =
      Stack.iter f stack

    method iter f = self#top#iter f

    method select_branches partial_parser_selector =

      begin %debug_block
        [%debug_log "context: %s" (C.to_string context)];
        [%debug_log "branches:"];
        self#iter_branch
        (fun buf ->
          [%debug_log "%s [%s] (ntokens=%d) [%s]"
            (branch_tag_to_string buf#get_tag)
            (try Loc.to_string ~short:true buf#get_loc with _ -> "-")
            buf#size
            (C.to_string buf#get_context)];
          buf#dump
        );
      end;

      let key = loc_of_branch_tag btag in
      context_stack#recover key;
      env#recover key;

      let selected_buf = ref (new buffer BTselected) in
      (!selected_buf)#set_context context;

      let ignored_regions = ref [] in

      context_stack#suspend;
      try
        if not self#top#get_context.C.is_active then
          raise Not_active;
(*
  let partial = self#top#parse_by (partial_parser_selector context) in
  context_stack#resume;
  self#top#to_partial partial;

  [%debug_log "selecting all branches... (current context: %s)"
  (C.to_string (context_stack#top))];

  let blist = ref [] in
  self#iter_branch (fun br -> blist := br::!blist);
  List.iter (fun br -> (!selected_buf)#receive_all br) !blist;

  !selected_buf, !ignored_regions
 *)

(*
  let parser = partial_parser_selector context in

  [%debug_log "current context: %s"
  (C.to_string (context_stack#top))];

  try
  self#iter_branch
  (fun br ->
  try
  let partial = br#parse_by parser in
  br#to_partial partial;
  raise Exit
  with Incomplete -> ()
  );
  [%debug_log "all branches are incomplete"];
  raise Incomplete

  with Exit ->
  [%debug_log "selecting all branches..."];
  context_stack#resume;
  let blist = ref [] in
  self#iter_branch (fun br -> blist := br::!blist);
  List.iter (fun br -> (!selected_buf)#receive_all br) !blist;

  !selected_buf, !ignored_regions
 *)
        [%debug_log "current context: %s" (C.to_string (context_stack#top))];

        let _parser = partial_parser_selector context in

        let blist = ref [] in
        let ignored = ref [] in

        let multi_mode = ref false in

        self#iter_branch
          (fun br ->
            try
              let partial = br#parse_by _parser in
              let nnodes, nerrs = check_partial partial in

              if nnodes > 0 && nerrs = 0 then
                multi_mode := true;

              if nnodes = nerrs then
                ignored := br::!ignored

              else begin
                br#to_partial partial;
                blist := br::!blist
              end
            with Incomplete ->
              ignored := br::!ignored
          );

        context_stack#resume;

        if !blist = [] || not !multi_mode then begin
          [%debug_log "all branches are incomplete"];
          raise Incomplete
        end
        else begin
          [%debug_log "merging selected branches..."];
          List.iter
            (fun br ->

              [%debug_log "selected branch: %s" (branch_tag_to_string br#get_tag)];

              (!selected_buf)#receive_all br
            ) !blist;
          List.iter
            (fun br ->
              try
                let loc = br#get_loc in

                [%debug_log "ignored region: %s" (Loc.to_string ~short:true loc)];

                ignored_regions :=  loc :: !ignored_regions

              with Buffer_empty -> ()
            ) !ignored;

          !selected_buf, !ignored_regions
        end

      with
        Incomplete | Not_active -> begin (* we select a (largest) branch *)
          context_stack#resume;
          [%debug_log "selecting the largest or specified branch..."];
          begin
            self#iter_branch
              (fun buf ->

                [%debug_log "checking %s" (branch_tag_to_string buf#get_tag)];

                match buf#get_tag with
                | BTifdef(id, _) | BTelsif id -> begin
                    try
                      if env#macro_defined id then
                        selected_buf := buf
                    with Not_found ->
                      if (!selected_buf)#total_size < buf#total_size then
                        selected_buf := buf
                end
                | BTifndef(id, _) -> begin
                    try
                      if not (env#macro_defined id) then
                        selected_buf := buf
                    with Not_found ->
                      if (!selected_buf)#total_size < buf#total_size then
                        selected_buf := buf
                end
                | BTelse ->
                    if (!selected_buf)#total_size < buf#total_size then
                      selected_buf := buf

                | _ -> assert false
              )
          end;

          self#iter_branch
            (fun buf ->
              if buf != !selected_buf then
                try
                  ignored_regions := (buf#get_loc) :: !ignored_regions
                with Buffer_empty -> ()
            );

          [%debug_log "largest: %s" (branch_tag_to_string !selected_buf#get_tag)];

          !selected_buf, !ignored_regions

        end
    (* end of method select_branches *)


    method dump =
      let count = ref 0 in
      self#iter_branch
        (fun br ->
          Printf.printf "[%d: BRANCH BEGIN]\n" !count;
          br#dump;
          Printf.printf "[%d: BRANCH END]\n" !count;
          incr count
        )

(*
  method parse_by : partial_parser -> Ast.partial list =
  fun p ->
  [%debug_log "parsing..."];
  let partials = ref [] in
  context_stack#suspend;
  self#iter_branch
  (fun br ->
  begin
  try
  partials := (br#parse_by p)::!partials;

  with Incomplete ->
  [%debug_log "parse failed! (%s)" (branch_tag_to_string br#get_tag)]
  end;
  );
  context_stack#resume;
  !partials
 *)

    initializer
      self#new_branch btag

  end (* of class branching_buffer *)



  class c (partial_parser_selector : C.t -> partial_parser) = object (self)

    val mutable last_token = EOF, Loc.dummy_lexpos, Loc.dummy_lexpos
    val mutable prev_token = EOF, Loc.dummy_lexpos, Loc.dummy_lexpos

    val mutable last_taken = EOL
    val mutable _last_taken = EOL
    val mutable last_taken_loc = Loc.dummy
    val mutable _last_taken_loc = Loc.dummy

    val mutable last_taken_no_pp_branch = EOL
    val mutable _last_taken_no_pp_branch = EOL
    val mutable last_taken_no_pp_branch_loc = Loc.dummy
    val mutable _last_taken_no_pp_branch_loc = Loc.dummy


    val prebuf : (Token.qtoken_t Queue.t) = Queue.create()

    val stack = Stack.create()

    val context_buf = new buffer BTcontext

    val mutable serialized = new buffer BTdummy
    val mutable is_serialized = false

    val mutable in_undef = false

    val mutable ignored_regions : Loc.t list = []


    method partial_parser_selector = partial_parser_selector

    method size_of_serialized = serialized#size

    method get_last_taken =
      [%debug_log "%s" (Token.rawtoken_to_string last_taken)];
      last_taken

    method set_last_taken tok =
      last_taken <- _last_taken;
      _last_taken <- tok

    method get_last_taken_loc =
      [%debug_log "%s" (Loc.to_string last_taken_loc)];
      last_taken_loc

    method set_last_taken_loc loc =
      last_taken_loc <- _last_taken_loc;
      _last_taken_loc <- loc

    method get_last_taken_no_pp_branch =
      [%debug_log "%s" (Token.rawtoken_to_string last_taken_no_pp_branch)];
      last_taken_no_pp_branch

    method _get_last_taken_no_pp_branch =
      [%debug_log "%s" (Token.rawtoken_to_string _last_taken_no_pp_branch)];
      _last_taken_no_pp_branch

    method set_last_taken_no_pp_branch tok =
      last_taken_no_pp_branch <- _last_taken_no_pp_branch;
      [%debug_log "last_taken_no_pp_branch --> %s"
        (Token.rawtoken_to_string last_taken_no_pp_branch)];
      _last_taken_no_pp_branch <- tok

    method get_last_taken_no_pp_branch_loc =
      [%debug_log "%s" (Loc.to_string last_taken_no_pp_branch_loc)];
      last_taken_no_pp_branch_loc

    method set_last_taken_no_pp_branch_loc loc =
      last_taken_no_pp_branch_loc <- _last_taken_no_pp_branch_loc;
      _last_taken_no_pp_branch_loc <- loc

    method get_last_token = last_token
    method get_last_rawtok = Tok.to_rawtoken last_token
    method get_last_offsets = lexposs_to_offsets (Tok.to_lexposs last_token)
    method set_last_token token = last_token <- token

    method get_prev_token = prev_token
    method get_prev_rawtok = Tok.to_rawtoken prev_token
    method get_prev_offsets = lexposs_to_offsets (Tok.to_lexposs prev_token)
    method set_prev_token token = prev_token <- token

    method prebuf_add x =
      [%debug_log "%s" (Token.qtoken_to_string x)];
      Queue.add x prebuf

    method prebuf_take =
      try
        let x = Queue.take prebuf in
        [%debug_log "%s" (Token.qtoken_to_string x)];
        x
      with
        Queue.Empty -> raise Buffer_empty

    method prebuf_peek =
      try
        Queue.peek prebuf
      with
        Queue.Empty -> raise Buffer_empty

    method prebuf_peek_nth n =
      peek_nth prebuf n

    method prebuf_size = Queue.length prebuf

    method add_to_context qtoken =
      [%debug_log "added %s" (Token.qtoken_to_string qtoken)];
      context_buf#_add qtoken


    method set_context c =
      [%debug_log "%s" (C.to_string c)];
      context_buf#set_context (C.copy_context c)

    method get_context = context_buf#get_context
    method clear_context =
      [%debug_log "called"];
      context_buf#clear;
      context_buf#set_context (C.copy_context context_stack#top)


    method get_branch_context =
      let start = ref None in
      let bufs = ref [] in
      begin
        try
          Stack.iter
            (fun bbuf ->
              let cnt = bbuf#top#get_context in

              [%debug_log "bbuf[%s] context=%s"
                (branch_tag_to_string bbuf#branch_tag) (C.to_string cnt)];

              if not (C.is_unknown cnt) && cnt.C.is_active then begin
                start := Some (bbuf#top, loc_of_branch_tag bbuf#get_tag);
                raise Exit
              end
              else
                bufs := bbuf#top :: !bufs;
            ) stack
        with
          Exit -> ()
      end;
      match !start with
      | None -> raise Not_found
      | Some (sbuf, key) ->
          let cpy = sbuf#get_copy in
          List.iter
            (fun buf ->
              cpy#receive_all buf#get_copy
            ) !bufs;

          [%debug_log "loc: %s"
            (try Loc.to_string ~short:true cpy#get_loc with Buffer_empty -> "-")];

          (cpy : buffer), key



    method is_serialized = is_serialized

    method in_undef = in_undef
    method begin_undef = in_undef <- true
    method end_undef = in_undef <- false


    method size = Stack.length stack

    method in_branch = not (Stack.is_empty stack)

    method current_bbuf = Stack.top stack

    method is_context_empty = context_buf#is_empty

    method begin_branch ~open_if btag =

      [%debug_log "open_if=%B, branch depth: %d" open_if self#size];

      let bbuf = new branching_buffer btag in

      if not self#in_branch then begin

        let c = context_buf#get_context in

        if not context_buf#is_empty then begin

          begin %debug_block
            [%debug_log "location of context buffer: %s"
            (Loc.to_string ~short:true context_buf#get_loc)];
          [%debug_log "context of context buffer: %s"
            (C.to_string c)];
          [%debug_log "parsing context buffer..."];
          end;

          context_stack#checkpoint Aux.top_key;
          env#checkpoint Aux.top_key;
          begin
            try
              if open_if then
                raise Incomplete;
              ignore (context_buf#parse_by (partial_parser_selector c));
            with
              Incomplete | Not_found -> [%debug_log "failed to parse context_buf"];
          end;
          if open_if then
            context_stack#deactivate_top_no_delay;
          bbuf#set_context (C.copy_context context_stack#top);
          self#clear_context;

        end
        else begin (* context buffer is empty *)
          [%debug_log "context buffer is empty"];

          bbuf#set_context (C.copy_context c)
        end
      end
      else begin (* in branch *)
        [%debug_log "in branch"];
        try
          let branch_context, key = self#get_branch_context in
          let c = branch_context#get_context in

          if not branch_context#is_empty then begin

            begin %debug_block
              [%debug_log "branch context buffer: %s (context: %s)"
              (Loc.to_string ~short:true branch_context#get_loc) (C.to_string c)];
            [%debug_log "parsing branch context buffer..."];
            end;

            context_stack#recover key;
            env#recover key;
            begin
              try
                if open_if then
                  raise Incomplete;
                ignore (branch_context#parse_by (partial_parser_selector c))
              with
                Incomplete | Not_found ->
                  [%debug_log "failed to parse branch context"]
            end;
            if open_if then
              context_stack#deactivate_top_no_delay;
            bbuf#set_context (C.copy_context context_stack#top);
          end
          else begin (* branch context is empty *)
            [%debug_log "branch context is empty"];
            bbuf#set_context (C.copy_context c)
          end
        with
          Not_found -> bbuf#set_context (C.copy_context context_stack#top)
      end;

      [%debug_log "[%s][%s]: current depth=%d (current context: %s)"
        (branch_tag_to_string btag) (C.to_string bbuf#get_context) (self#size)
        (C.to_string context_stack#top)];

      let bcont = bbuf#get_context in
      if (* bcont.C.is_active && *) not (C.is_unknown bcont) then begin
        let key = loc_of_branch_tag btag in
        context_stack#checkpoint key;
        env#checkpoint key
      end;
      Stack.push bbuf stack
    (* end of method begin_branch *)


    method end_branch ~open_if =
      [%debug_log "open_if=%B, branch depth=%d" open_if (self#size)];

      let check_buf (buf : buffer) =

        [%debug_log "checking %s..." (branch_tag_to_string buf#get_tag)];

        try
          let _parser = partial_parser_selector buf#get_context in

          context_stack#suspend;
          try
            if not buf#get_context.C.is_active then
              raise Not_active;

            let partial = buf#parse_by _parser in
            context_stack#resume;
            if not open_if then
              buf#to_partial partial;
            context_stack#activate_top_no_delay;
          with
            Incomplete | Not_active ->
              context_stack#resume;
              context_stack#deactivate_top_no_delay
        with
          Not_found -> ()
      in (* end of check_buf *)

      let bbuf = Stack.pop stack in
      let selected, ignored =
        bbuf#select_branches partial_parser_selector
      in
      ignored_regions <- ignored_regions @ ignored;
      try
        let buf = self#current_bbuf#top in

        [%debug_log "transferring selected branch to %s..." (branch_tag_to_string buf#get_tag)];

        buf#receive_all selected;
        check_buf buf

      with
        Stack.Empty ->
          is_serialized <- true;
          serialized <- selected;
          check_buf serialized;
          context_stack#recover Aux.top_key;
          env#recover Aux.top_key;

    (* end of method end_branch *)


    method peek =
(*    [%debug_log "called"]; *)
      let tok, loc = serialized#peek in
      tok, loc

    method peek_nth n =
(*    [%debug_log "called"]; *)
      serialized#peek_nth n

    method take =
(*    [%debug_log "called"]; *)
      let tok, loc = serialized#take in
      if serialized#is_empty then
        is_serialized <- false;
      tok, loc

    method add qtoken =
(*    [%debug_log "called"]; *)
      (self#current_bbuf)#add qtoken

    method new_branch btag =
      [%debug_log "btag=%s" (branch_tag_to_string btag)];
      (self#current_bbuf)#new_branch btag

    method dump_top =
      (self#current_bbuf)#dump

    method dump_ignored_regions =
      if ignored_regions <> [] then
        Printf.printf "ignored regions:\n";
      Loc.dump_locs ignored_regions

    method ignored_LOC =
      Loc.lines_of_locs ignored_regions

    method ignored_regions = ignored_regions

    method ignored_offsets = List.map Loc.to_offsets ignored_regions

    initializer
      context_buf#set_context (C.toplevel());
      context_stack#register_push_callback
        (fun c ->
          [%debug_log "push_callback: called"];
          if not self#in_branch then begin
            context_stack#checkpoint Aux.top_key;
            env#checkpoint Aux.top_key;
            self#clear_context;
            self#set_context c
          end
        );
      context_stack#register_pop_callback
        (fun terminate_surrounding_construct c ->
          [%debug_log "pop_callback: called"];
          if not self#in_branch then begin

            if terminate_surrounding_construct then begin
              context_stack#activate_top;
              context_stack#checkpoint Aux.top_key;
              env#checkpoint Aux.top_key;
              self#clear_context;
              self#set_context c
            end

          end
        );
      context_stack#register_activate_callback
        (fun c ->
          [%debug_log "activate_callback: called"];
          if not self#in_branch then begin
            context_stack#checkpoint Aux.top_key;
            env#checkpoint Aux.top_key;
            self#clear_context;
            self#set_context c
          end

        );
      context_stack#register_deactivate_callback
        (fun c ->
          [%debug_log "deactivate_callback: called"];
          if not self#in_branch then begin
            context_stack#checkpoint Aux.top_key;
            env#checkpoint Aux.top_key;
            self#clear_context;
            self#set_context c
          end
        )

  end (* of class Tokenbuffer.c *)

  let find_macro id =
    try
      env#find_macro id
    with
      Not_found ->
        env#lex_find_macro id

  let hide_macro id =
    env#macrotbl#hide id;
    env#lex_macrotbl#hide id;
    fun () ->
      env#macrotbl#expose id;
      env#lex_macrotbl#expose id

  let rec expand_line (*base_loc*)_ st ed line =
    [%debug_log "line=^%s$" line];
    let ulexbuf = U.from_string line in
    let scanner () = U.token ulexbuf in
    let buf = new buffer_base in
    begin
      try
        while true do
          try
            let tok, _ = scanner() in
            [%debug_log "tok=%s" (Token.rawtoken_to_string tok)];
            match tok with
            | EOF -> raise Sedlexing.MalFormed

            | PP_MACRO_ID id -> begin
                try
                  match find_macro id with
                  | Macro.Object line0 ->
                      let buf0 = expand_line line0.Macro.ln_loc st ed line0.Macro.ln_raw in
                      buf#receive_all buf0
                  | _ -> assert false
                with
                  Not_found -> assert false
            end
            | PP_MACRO_APPL(id, args) -> begin
                let line0, base_loc0 =
                  try
                    match find_macro id with
                    | Macro.Function(params, l) -> begin
                        try
                          List.fold_left2
                            (fun s param arg ->
                              let pat = Str.regexp (String.concat "" ["{";param;"}"]) in
                              Str.global_replace pat arg s
                            ) l.Macro.ln_raw params args,
                          l.Macro.ln_loc
                        with
                          Invalid_argument _ ->
                            Common.fail_to_parse
                              ~head:(Printf.sprintf "[%s:%d:%d]"
                                       env#current_filename
                                       st.Lexing.pos_lnum
                                       (st.Lexing.pos_cnum - st.Lexing.pos_bol))
                              "invalid number of macro arguments"

                    end
                    | _ -> assert false
                  with
                    Not_found -> assert false
                in
                let buf0 = expand_line base_loc0 st ed line0 in
                buf#receive_all buf0
            end
            | _ -> buf#add (PB.make_qtoken tok st ed)
          with
            Sedlexing.MalFormed -> raise Exit
        done
      with
        Exit -> ()
    end;
    buf
 (* end of func expand_line *)

  exception Token_found of Token.qtoken_t


  class tokensource (tbuf : c) ulexbuf = object (self)

    val ulexbuf_stack : Sedlexing.lexbuf Stack.t = Stack.create()

    initializer
      Stack.push ulexbuf ulexbuf_stack

    method tokenbuf = tbuf

    method in_included = (Stack.length ulexbuf_stack) > 1

    method current_ulexbuf = Stack.top ulexbuf_stack

    method enter_source (src : Source.c) =
      [%debug_log "%s" src#filename];
      let ulbuf = src#get_ulexbuf in
      Stack.push ulbuf ulexbuf_stack;
      ulbuf

    method exit_source =
      [%debug_log "called"];
      let _ = Stack.pop ulexbuf_stack in
      env#pop_loc;
      env#exit_source

    method get_token() =
      [%debug_log "prebuf_size=%d" tbuf#prebuf_size];

      let ulexbuf = self#current_ulexbuf in

      if tbuf#prebuf_size < 1 then begin
        let qtoken = U.token ulexbuf in
        self#record_qtoken qtoken;
        self#conv_token qtoken;
      end;

      let qtoken =
        try
          tbuf#prebuf_take
        with
          Buffer_empty -> self#get_token()
      in
      match qtoken with
      | EOF, _ -> begin
          if self#in_included then begin
            self#exit_source;
            self#get_token()
          end
          else
            qtoken
      end
      | _ -> qtoken

    method peek_nth_token n =
      let ulexbuf = self#current_ulexbuf in

      let rec prebuf_peek m =
        try
          tbuf#prebuf_peek_nth m
        with
          Buffer_empty ->
            for _ = 1 to (m - tbuf#prebuf_size) do
              let qtoken = U.token ulexbuf in
              self#conv_token qtoken
            done;
            prebuf_peek m
      in
      if tbuf#is_serialized then
        try
          tbuf#peek_nth n
        with
          Buffer_empty ->
            prebuf_peek (n - tbuf#size_of_serialized)
      else
        prebuf_peek n

    method peek_token() = (* skip compiler directives *)
      let skip_until_endif_flag = ref false in
      let n = ref 1 in
      let branch_depth = ref 0 in
      try
        while true do
          let qtoken = self#peek_nth_token !n in
          let rawtok, _ = qtoken in

          [%debug_log "peeking %dth token: %s" !n (Token.qtoken_to_string qtoken)];

          if Tok.is_compiler_directive rawtok then begin
            begin
              match rawtok with
              | PP_IFDEF
              | PP_IFNDEF
                -> incr branch_depth; incr n

              | PP_UNDEF
              | PP_DEFAULT_DECAY_TIME
              | PP_DEFAULT_TRIREG_STRENGTH
              | PP_ERROR
              | PP_DEFAULT_NETTYPE
                -> incr n

              | PP_TIMESCALE
              | PP_LINE
              | PP_PRAGMA
                -> n := !n + 3

              | PP_ELSE   ->
                  if !branch_depth = 0 then
                    skip_until_endif_flag := true

              | PP_ELSIF  ->
                  if !branch_depth = 0 then
                    skip_until_endif_flag := true;
                  incr n

              | PP_ENDIF  ->
                  if !branch_depth > 0 then
                    decr branch_depth;
                  skip_until_endif_flag := false

              | _ -> ()
            end;
            incr n
          end
          else
            if !skip_until_endif_flag then
              incr n
            else
              raise (Token_found qtoken)
        done;
        EOF, Loc.dummy
      with
        Token_found qtoken -> qtoken
    (* end of method peek_token *)

    method conv_token qtoken =
      [%debug_log "%s" (Token.qtoken_to_string qtoken)];
      let tok, loc = qtoken in
      let st, ed = Loc.to_lexposs loc in
      let ln = st.Lexing.pos_lnum in

      let divide qtkn =
        let _, loc = qtkn in
        let st, ed = Loc.to_lexposs loc in
        let _st = Loc.incr_lexpos st in
        let _ed = Loc.decr_lexpos ed in
        st, _st, _ed, ed
      in
      begin
        match tok with
        | GENERATE ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken GENERATE st _st);
            tbuf#prebuf_add (PB.make_qtoken GENERATE_ _ed ed)

        | BEGIN ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken BEGIN st _st);
            tbuf#prebuf_add (PB.make_qtoken BEGIN_ _ed ed)

        | END ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken END st _st);
            tbuf#prebuf_add (PB.make_qtoken END_ _ed ed)

        | FORK ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken FORK st _st);
            tbuf#prebuf_add (PB.make_qtoken FORK_ _ed ed)

        | JOIN js ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken (JOIN js) st _st);
            tbuf#prebuf_add (PB.make_qtoken JOIN_ _ed ed)

        | ENDMODULE ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken ENDMODULE st _st);
            tbuf#prebuf_add (PB.make_qtoken ENDMODULE_ _ed ed)

        | MATCHES ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken MATCHES st _st);
            tbuf#prebuf_add (PB.make_qtoken MATCHES_ _ed ed)

        | INSIDE ->
            let st, _st, _ed, ed = divide qtoken in
            tbuf#prebuf_add (PB.make_qtoken INSIDE st _st);
            tbuf#prebuf_add (PB.make_qtoken INSIDE_ _ed ed)

        | PP_MACRO_ID id -> begin
            try
              match find_macro id with
              | Macro.Object l -> begin
                  let recover = hide_macro id in
                  self#handle_macro_line st ed id [] l l.Macro.ln_raw;
                  recover()
              end
              | _ -> assert false
            with
              Not_found -> assert false
        end
        | PP_MACRO_APPL(id, args) -> begin
            let line, raw =
              try
                match find_macro id with
                | Macro.Function(params, l) -> begin
                    try
                      l,
                      List.fold_left2
                        (fun s param arg ->
                          let pat = Str.regexp (String.concat "" ["{";param;"}"]) in
                          Str.global_replace pat arg s
                        ) l.Macro.ln_raw params args
                    with
                      Invalid_argument _ ->
                        Common.fail_to_parse
                          ~head:(sprintf "[%s:%d:%d]"
                                   env#current_filename
                                   ln
                                   (st.Lexing.pos_cnum - st.Lexing.pos_bol))
                          (sprintf "invalid number of macro arguments: %s" id)

                end
                | _ -> assert false
              with
                Not_found -> assert false
            in
            let recover = hide_macro id in
            self#handle_macro_line st ed id args line raw;
            recover()
        end
        | _ -> tbuf#prebuf_add qtoken
      end
    (* end of method conv_token *)

    method record_qtoken qtoken =
      [%debug_log "%s" (Token.qtoken_to_string qtoken)];
      let tok, loc = qtoken in
      tbuf#set_last_taken tok;
      tbuf#set_last_taken_loc loc;
      begin
        match tok with
        | PP_IFDEF | PP_IFNDEF | PP_ELSE | PP_ELSIF | PP_ENDIF
          -> ()
        | _ ->
            tbuf#set_last_taken_no_pp_branch tok;
            tbuf#set_last_taken_no_pp_branch_loc loc
      end


    method handle_macro_line st ed id args line raw =
      let args_str =
        let s = Xlist.to_string (fun x -> x) "," args in
        if s = "" then "" else String.concat "" ["("; s; ")"]
      in

      [%debug_log "id:%s args:%s line:%s [%s]"
        id args_str raw (Macro.stat_to_string line.Macro.ln_stat)];

      let ida = id^args_str in

      match line.Macro.ln_stat with
      | Macro.Resolved obj -> begin
          [%debug_log "macro stat: RESOLVED"];
          let tok = Obj.obj obj in
          let t = PB.make_qtoken tok st ed in
          tbuf#prebuf_add t
      end
      | Macro.Unresolved ->
          [%debug_log "macro stat: UNRESOLVED"];
          let buf = expand_line line.Macro.ln_loc st ed raw in
          let buf_as_list = buf#get_list in
          begin
            [%debug_log "buf#get_list (%d):" (List.length buf_as_list)];
            begin %debug_block
              List.iter
              (fun (tok, _) ->
                [%debug_log "  %s" (Token.rawtoken_to_string tok)])
              buf_as_list
              end;
            match buf_as_list with
            | [] -> begin
            end
            | [(IDENTIFIER _, _)]      -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_NAME ida) st ed)
            | [(STRING_LITERAL _, _)]  -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_CONST_STR ida) st ed)
            | [(INTEGRAL_NUMBER _, _)] -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_CONST_INT ida) st ed)

            | [(REAL_NUMBER _, _)]
            | [(TIME_NUMBER _, _)]
              ->
                tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_CONST ida) st ed)

            | [(INTEGRAL_NUMBER _, _);(INTEGRAL_NUMBER _, _)]
              ->
                tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_CONST_INT ida) st ed)

            | (IDENTIFIER id', _)::_ when id' = id -> (* e.g. macro for swapping arguments *)
                buf#iter
                  (fun (tok, _) ->
                    tbuf#prebuf_add (PB.make_qtoken tok st ed)
                  )

            | xs ->
                buf#add (PB.make_qtoken EOP Loc.dummy_lexpos Loc.dummy_lexpos);

                let rec is_concat = function
                  | _ :: (PP_CONCAT,_) :: rest -> is_concat rest
                  | [_] -> true
                  | _ -> false
                in

                let contexts =
                  if is_concat xs then
                    [ C.expr(),  PP_MACRO_NAME ida, (fun t -> tbuf#prebuf_add t) ]
                  else
                    [
                     C.pev_expr(), PP_MACRO_EXPR ida, (fun t -> tbuf#prebuf_add t);
                     C.ev_expr(),  PP_MACRO_EXPR ida, (fun t -> tbuf#prebuf_add t);
                     C.expr(),     PP_MACRO_EXPR ida, (fun t -> tbuf#prebuf_add t);
                   ]
                in
                env#checkpoint Loc.dummy;

                let last_tok = tbuf#get_last_taken_no_pp_branch in
                let _ = last_tok in
                [%debug_log "last_tok=%s" (Token.rawtoken_to_string last_tok)];

                try
                  List.iter
                    (fun (context, tok, handler) ->
                      [%debug_log "trying to parse with context:%s..." (C.to_string context)];

                      let _parser = tbuf#partial_parser_selector context in
                      try
                        env#recover Loc.dummy;

                        let _ = buf#parse_by ~cache:false _parser in
                        handler (PB.make_qtoken tok st ed);
                        Macro.resolve_line line tok;

                        env#recover ~remove:true Loc.dummy;

                        raise Exit
                      with
                      | Incomplete -> ()
                    ) contexts;

                  env#recover ~remove:true Loc.dummy;

                  [%debug_log "all attempts failed, expanding..."];

                  let add_to_tbuf() =
                    buf#iter
                      (fun (tok, _) ->
                        if tok = EOP then
                          raise Exit
                        else
                          tbuf#prebuf_add (PB.make_qtoken tok st ed)
                      )
                  in

                  add_to_tbuf()

                with
                  Exit -> ()

          end
    (* end of method handle_macro_line *)



  end (* class Tokenbuffer.tokensource *)


  let hack_token tokensrc qtoken =
    let tokenbuf = tokensrc#tokenbuf in
    let _tok, _loc = qtoken in
    let st, ed = _loc.Loc.start_offset, _loc.Loc.end_offset + 1 in

    let tok = ref _tok in
    let loc = ref _loc in

    [%debug_log "%s" (Token.qtoken_to_string qtoken)];

    let peek_next() =
      let tok, _ = tokensrc#peek_token() in
      tok
    in

(*
    begin
      match env#lang_spec with
      | Common.V1995 | Common.V2001 | Common.V2005 ->
          if Tok.is_sv_keyword !tok then
            tok := IDENTIFIER (Token.rawtoken_to_rep !tok)

      | Common.SV2005 ->
          if Tok.is_sv2009_keyword !tok then
            tok := IDENTIFIER (Token.rawtoken_to_rep !tok)

      | _ -> ()
    end;
*)
    begin
      match !tok with
      | PP_IDENTIFIER s ->
          begin
            match tokenbuf#get_last_rawtok with
            | LT_EQ -> begin
                let next_tok = peek_next() in
                [%debug_log "next tok: %s" (Token.rawtoken_to_string next_tok)];
                match next_tok with
                | SEMICOLON | RPAREN | DOT -> ()
                | _ -> tok := NB_ASSIGN_POSTFIX s
            end

            | _ -> ()
          end

      | IDENTIFIER _ -> () (* handle later *)

      | BYTE | INT | REF | TYPE -> begin
          let next_tok = peek_next() in
          begin
            match next_tok with
            | COMMA | SEMICOLON | EQ | RBRACE | RPAREN
            | OR | AND | AMP_AMP | EQ_EQ ->
                let s = Token.rawtoken_to_rep !tok in
                env#current_source#set_lang_spec_v2005;

                let st_pos, ed_pos = Loc.to_lexposs !loc in
                parse_warning st_pos ed_pos
                  "System Verilog keyword \"%s\" used as an identifier: maybe \"%s\""
                  s (Source.lang_spec_to_string env#current_source#lang_spec);

                tok := IDENTIFIER s
            | _ -> ()
          end;

          match tokenbuf#get_last_rawtok with
          | DOT ->
              let s = Token.rawtoken_to_rep !tok in
              env#current_source#set_lang_spec_v2005;

              let st_pos, ed_pos = Loc.to_lexposs !loc in
              parse_warning st_pos ed_pos
                "System Verilog keyword \"%s\" used as an identifier: maybe \"%s\""
                s (Source.lang_spec_to_string env#current_source#lang_spec);

              tok := IDENTIFIER s
          | _ -> ()
      end

      | COLON_COLON ->
          if env#scoped_flag then
            let next_tok = peek_next() in
            begin
              match next_tok with
              | IDENTIFIER _ -> ()
              | _ -> env#clear_scoped_flag; A.end_scope()
            end

      | COMMA ->
          if env#in_table then
            let next_tok = peek_next() in
            begin
              match next_tok with
              | IDENTIFIER _ -> tok := COMMA__I
              | _ -> ()
            end

      | CONST ->
          let next_tok = peek_next() in
          begin
            match next_tok with
            | REF -> tok := CONST__R
            | _ -> ()
          end

      | CONTEXT -> begin
          match tokenbuf#get_last_rawtok with
          | STRING_LITERAL _ -> ()
          | _ ->
              env#current_source#set_lang_spec_v2005;

              let st_pos, ed_pos = Loc.to_lexposs !loc in
              parse_warning st_pos ed_pos
                "System Verilog keyword \"context\" used as an identifier: maybe \"%s\""
                (Source.lang_spec_to_string env#current_source#lang_spec);

              tok := IDENTIFIER "context"
      end

      | ENDTABLE -> env#end_table

      | FUNCTION ->
          if env#pvstate = 2 then begin
            tok := FUNCTION__PV;
            env#set_pvstate 0
          end

      | GLOBAL ->
          let next_tok = peek_next() in
          begin
            match next_tok with
            | CLOCKING -> ()
            | _ ->
                env#current_source#set_lang_spec_sv2005;

                let st_pos, ed_pos = Loc.to_lexposs !loc in
                parse_warning st_pos ed_pos
                  "System Verilog (2009) keyword \"global\" used as an identifier: maybe \"%s\""
                  (Source.lang_spec_to_string env#current_source#lang_spec);

                tok := IDENTIFIER "global" (* to avoid conflict between SV09 and the others *)
          end

      | LOCAL ->
          let next_tok = peek_next() in
          begin
            match next_tok with
            | COLON_COLON -> tok := LOCAL__CC
            | COMMA | SEMICOLON | EQ | RBRACE | RPAREN | LBRACKET
            | OR | AND | AMP_AMP ->
                env#current_source#set_lang_spec_v2005;

                let st_pos, ed_pos = Loc.to_lexposs !loc in
                parse_warning st_pos ed_pos
                  "System Verilog keyword \"local\" used as an identifier: maybe \"%s\""
                  (Source.lang_spec_to_string env#current_source#lang_spec);

                tok := IDENTIFIER "local"
            | _ -> ()
          end

      | LPAREN ->
          let next_tok = peek_next() in
          begin
            match next_tok with
            | STRENGTH _ -> tok := LPAREN__S
            | SUPPLY0    -> tok := LPAREN__S
            | SUPPLY1    -> tok := LPAREN__S
            | _ -> ()
          end

      | NEW ->
          let next_tok = peek_next() in
          begin
            match next_tok with
            | LPAREN -> tok := NEW__P
            | _ -> ()
          end

      | PURE -> env#set_pvstate 1

      | SEMICOLON -> env#set_pvstate 0

      | STATIC ->
          let next_tok = peek_next() in
          begin
            match next_tok with
            | CONSTRAINT -> tok := STATIC__C
            | _ -> ()
          end

      | TABLE -> env#begin_table

      | TASK ->
          if env#pvstate = 2 then begin
            tok := TASK__PV;
            env#set_pvstate 0
          end

      | VIRTUAL ->
          if env#pvstate = 1 then
            env#set_pvstate 2
          else
            env#set_pvstate 0;

          let next_tok = peek_next() in
          begin
            match next_tok with
            | CLASS        -> tok := VIRTUAL__C
            | INTERFACE    -> tok := VIRTUAL__I
            | IDENTIFIER _ -> tok := VIRTUAL__ID
            | _ -> ()
          end

      | WITHx ->
          let next_tok = peek_next() in
          begin
            match next_tok with
            | LPAREN   -> tok := WITH__P
            | LBRACKET -> tok := WITH__B
            | LBRACE   -> tok := WITH__C
            | _ -> ()
          end

      | _ ->
          if env#pvstate = 1 then
            env#set_pvstate 0
    end;

    begin
      match !tok with
      | IDENTIFIER s ->
          let attr_opt = ref None in
          begin

            if Xstring.startswith s "PATHPULSE$" then
              tok := PATHPULSE_IDENTIFIER s

            else if env#in_table then
              let symbol =
                match s with
                | "x" | "X" -> SYMBOL_xX s
                | "b" | "B" -> SYMBOL_bB s
                | "r" | "R" | "f" | "F" | "p" | "P" | "n" | "N" -> SYMBOL_rRfFpPnN s
                | _ -> IDENTIFIER s
              in
              tok := symbol

            else
              try
                match env#lookup_identifier s with
                | ((Aux.IApackage) as a)::_ -> tok := PACKAGE_IDENTIFIER s; attr_opt := Some a
                | ((Aux.IAclass _) as a)::_ -> tok := CLASS_IDENTIFIER s;   attr_opt := Some a
                (*| (Aux.IAinterface)::_      -> tok := INTERFACE_IDENTIFIER s*)
                | (Aux.IAtype)::_           -> tok := TYPE_IDENTIFIER s
                | (Aux.IAcovergroup)::_     -> tok := COVERGROUP_IDENTIFIER s
                | (Aux.IAclocking)::_       -> (* tok := CLOCKING_IDENTIFIER s *) ()
                | (Aux.IAproperty)::_       -> (* tok := PROPERTY_IDENTIFIER s *) ()

                | ((Aux.IAextern_method) (* as a *))::_ -> ()

                | _ -> ()

              with Not_found -> ()
          end;

          begin
            match !attr_opt with
            | Some Aux.IApackage | Some (Aux.IAclass _) ->
                let next_tok = peek_next() in
                begin
                  match next_tok with
                  | COLON_COLON ->
                      env#set_scoped_flag;
                      A.begin_scope();
                      begin
                        match !attr_opt with
                        | Some Aux.IApackage      -> env#import_any s
                        | Some (Aux.IAclass tblr) -> env#_import_any !tblr
                        | _ -> assert false
                      end

                  | _ -> ()
                end

            | _ ->
                if env#scoped_flag then begin
                  A.end_scope();
                  env#clear_scoped_flag
                end
          end

      | _ -> ()
    end;

    begin
      match !tok with
      | IDENTIFIER s -> begin
          match tokenbuf#get_last_rawtok with
          | IMPORT -> begin
              match peek_next() with
              | COLON_COLON -> tok := PACKAGE_IDENTIFIER s
              | _ -> ()
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    if _tok <> !tok then
      [%debug_log " --> %s" (Token.rawtoken_to_string !tok)];

    tokenbuf#set_prev_token tokenbuf#get_last_token;
    tokenbuf#set_last_token (!tok, Loc.mklexpos st, Loc.mklexpos ed);

    !tok, !loc
  (* end of func hack_token *)


  let rec pp tokensrc =
    let tokenbuf = tokensrc#tokenbuf in
    [%debug_log "called"];
    let next() =
      let qtoken = tokensrc#get_token() in
      let tok, _ = qtoken in
      [%debug_log "%s" (Token.qtoken_to_string qtoken)];
      tok
    in
    let mkbtag = make_branch_tag in

    let consume() =
      let qtoken = tokensrc#get_token() in
      let tok, loc = qtoken in

      let buffer_add() =
        tokenbuf#add (hack_token tokensrc qtoken)
      in

      [%debug_log "%s" (Token.qtoken_to_string qtoken)];

      match tok with
      | PP_IFDEF | PP_IFNDEF ->
          let btag = mkbtag tok (next()) loc in

          let qtok = tokensrc#peek_token() in
          let ntok, _ = qtok in

          [%debug_log "case %s: next token: %s (compiler directives skipped)"
            (Token.rawtoken_to_string tok) (Token.qtoken_to_string qtok)];

          let open_if =
            match ntok with
            | ELSE -> true
            | _ -> false
          in
          tokenbuf#begin_branch ~open_if btag;
          [%debug_log "calling pp"];
          pp tokensrc

      | PP_ELSIF ->
          tokenbuf#new_branch (mkbtag tok (next()) loc);
          [%debug_log "calling pp"];
          pp tokensrc

      | PP_ELSE ->
          tokenbuf#new_branch (mkbtag tok (IDENTIFIER "dummy") loc);
          [%debug_log "calling pp"];
          pp tokensrc

      | PP_ENDIF -> begin
          let qtok = tokensrc#peek_token() in
          let ntok, _ = qtok in

          [%debug_log "case PP_ENDIF: next token: %s (compiler directives skipped)"
            (Token.qtoken_to_string qtok)];

          let open_if =
            match ntok with
            | ELSE -> true
            | _ -> false
          in
          tokenbuf#end_branch ~open_if;
          [%debug_log "calling pp"];
          pp tokensrc
      end

      | PP_LINE | PP_INCLUDE _ | PP_SYS_INCLUDE _ | PP_ERROR
      | PP_TIMESCALE | PP_RESETALL | PP_DEFAULT_NETTYPE | PP_PRAGMA
      | PP_BEGIN_KEYWORDS | PP_END_KEYWORDS | PP_DEFAULT_DECAY_TIME
      | PP_DEFAULT_TRIREG_STRENGTH | PP_DELAY_MODE_DISTRIBUTED
      | PP_DELAY_MODE_PATH | PP_DELAY_MODE_UNIT | PP_DELAY_MODE_ZERO
      | PP_CELLDEFINE | PP_ENDCELLDEFINE | PP_UNCONNECTED_DRIVE
      | PP_NOUNCONNECTED_DRIVE
        ->
          if tokenbuf#in_branch then begin
            buffer_add();
            [%debug_log "calling pp"];
            pp tokensrc
          end
          else begin
            tokenbuf#add_to_context (tok, loc);
            tok, loc
          end

      | PP_UNDEFINEALL ->
          if tokenbuf#in_branch then begin
            buffer_add();
            [%debug_log "calling pp"];
            pp tokensrc
          end
          else begin
            tokenbuf#add_to_context (tok, loc);
            env#macrotbl#clear;
            tok, loc
          end

      | _ ->
          if tokenbuf#in_branch then begin
            [%debug_log "in_branch"];
            begin
              match tok with
              | EOF -> raise End_of_file;
              | _ -> ()
            end;

            buffer_add();
(*
  if not (Tok.is_compiler_directive tok) then
  context_stack#deactivate_top;
 *)
            [%debug_log "calling pp"];
            pp tokensrc
          end
          else begin
            begin
              match tok with
              | PP_DEFINE__IDENT__BODY(id, body) -> begin
                  env#define_macro id body
              end
              | PP_UNDEF__IDENT id -> begin
                  env#undefine_macro id
              end
              | _ -> ()
            end;

            if tokenbuf#is_context_empty then
              if context_stack#top_is_active && not context_stack#top_is_unknown then
                tokenbuf#set_context context_stack#top;

            begin
              match tok with
              | BEGIN_ | END_ | FORK_ | JOIN_ | ENDMODULE_ | MATCHES_ | INSIDE_
                -> ()
              | _ -> context_stack#deactivate_top
            end;

            tokenbuf#add_to_context (tok, loc);

            tok, loc

          end
    in (* end of func consume *)

    if tokenbuf#is_serialized then begin
      try
        tokenbuf#take
      with
        Buffer_empty -> [%debug_log "calling consume (serialized)"]; consume()
    end
    else begin
      [%debug_log "calling consume"];
      consume()
    end


end (* of functor Tokenbuffer.F *)
]
