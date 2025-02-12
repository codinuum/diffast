(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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

(* Author: Masatomo Hashimoto <m.hashimoto@stair.center> *)

(* tokenpp.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xqueue = Diffast_misc.Xqueue
module Xset = Diffast_misc.Xset
module Astloc = Langs_common.Astloc
module Layeredloc = Langs_common.Layeredloc
module Parserlib_base = Langs_common.Parserlib_base

module Loc = Astloc
module LLoc = Layeredloc
module Aux = Parser_aux
module PB  = Parserlib_base
module C   = Context
module TB  = Tokenbuffer
module B   = Branch
module Partial = Ast.Partial


open Labels

module PPD = PpDirective

module DL = Common.DirectiveLine


[%%capture_path
let check_partial partial =
  let nodes = Partial.get_nodes partial in
  let nnodes = ref 0 in
  let nerrs = ref 0 in
  List.iter
    (fun node ->
      Ast.visit
	(fun nd ->
	  incr nnodes;
	  if Label.is_error nd#label then
	    incr nerrs
	) node
    ) nodes;
  [%debug_log "nnodes=%d, nerrs=%d" !nnodes !nerrs];
  !nnodes, !nerrs
]


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  module TrunkF = Trunk.F (Stat)
  module TokenF = Token.F (Stat)
  module TBF = TB.F (Stat)
  module BF = B.F (Stat)
  module U = Ulexer.F (Stat)
  module P = Parser.Make (Stat)
  module A = Aux.F (Stat)

  open Tokens_
  open Stat

  let lexbuf_from_line loc ofs line =
    [%debug_log "loc=%s ofs=%d line=%s" (Loc.to_string ~short:true loc) ofs (String.escaped line)];
    let lexbuf = U.from_string line in
    let st_pos = Loc.to_start_lexpos loc in
    let base_pos = Loc.incr_n_lexpos ofs st_pos in
    Sedlexing.set_position lexbuf base_pos;
    lexbuf

  let lloc_to_loc (lloc : LLoc.c) =
    lloc#to_loc ~cache:(Some env#fname_ext_cache) ()

  let merge_locs = PB.merge_locs ~cache:(Some env#fname_ext_cache)

  let mkbtag = BF.make_tag


  class branching_buffer btag = object (self)

    val stack = Stack.create()

    val mutable context = C.unknown()

    method get_tag = btag

    method get_context =
(*      [%debug_log "%s" (C.to_string context)]; *)
      context

    method set_context c =
      [%debug_log "[%s]: %s" (B.tag_to_string btag) (C.to_string c)];
      context <- c;
      self#iter_branch (fun buf -> buf#set_context c)

    method top =
      Stack.top stack

    method new_branch btag =
      [%debug_log "creating new branch (nbranches=%d)" self#nbranches];
      let buf = new TBF.c btag in
      buf#set_context context;
      Stack.push buf stack


    method add token =
      self#top#add token

    method iter_branch f =
      Stack.iter f stack

    method iter f = self#top#iter f

    method nbranches = Stack.length stack

    method dump =
      let count = ref 0 in
      self#iter_branch
	(fun br ->
	  Printf.printf "[%d: BRANCH BEGIN]\n" !count;
	  br#dump;
	  Printf.printf "[%d: BRANCH END]\n" !count;
	  incr count
	)

    initializer
      self#new_branch btag

  end (* of class branching_buffer *)


  class bogus_buf = object
    val mutable context = C.unknown()
    val mutable is_empty = true
    val mutable last_added = (* non-pp *)
      PB.make_qtoken NOTHING Loc.dummy_lexpos Loc.dummy_lexpos

    method is_empty = is_empty
    method set_context c = context <- c
    method get_context = context
    method clear = is_empty <- true

    method _add (qtoken : Token.qtoken_t) =
      let tok, _ = qtoken in
      if not (TokenF.is_pp_directive tok) then begin
        [%debug_log "adding %s" (Token.qtoken_to_string qtoken)];
        last_added <- qtoken
      end;
      is_empty <- false

    method get_last = last_added
    method get_copy = {<context=(C.copy_context context);is_empty=is_empty;last_added=last_added>}
  end

  class context_buffer = object (self)

    val mutable stack = Stack.create()

    val checkpoint_tbl = Hashtbl.create 0


    method current_is_empty = self#current#is_empty

    method set_context c =
      [%debug_log "%s" (Context.to_string c)];
      self#current#set_context (Context.copy_context c)

    method get_context = self#current#get_context

    method clear_context =
      [%debug_log "called"];
      self#current#clear;
      self#current#set_context (Context.copy_context context_stack#top)

    method current =
      try
        Stack.top stack
      with
        Stack.Empty ->
          (*failwith "Tokenpp.context_buffer#current"*)
          [%warn_log "context buffer is empty"];
          let cbuf = new bogus_buf in
          Stack.push cbuf stack;
          cbuf

    method stack_size = Stack.length stack

    method enter_context =
      [%debug_log "stack size: %d" self#stack_size];
(*      let cbuf = new TBF.c B.Tcontext in*)
      let cbuf = new bogus_buf in
      Stack.push cbuf stack

    method exit_context =
      [%debug_log "stack size: %d" self#stack_size];
      try
        let buf = Stack.pop stack in
        self#current#_add buf#get_last
      with
        Stack.Empty -> failwith "Tokenpp.context_buffer#exit_context"

    method copy_stack s =
      let copy = Stack.create() in
      let bs = ref [] in
      Stack.iter
        (fun buf ->
	  bs := buf#get_copy :: !bs
        ) s;
      List.iter
        (fun buf ->
	  Stack.push buf copy
        ) !bs;
      copy

    method checkpoint (key : C.key_t) =
      [%debug_log "key=%s size=%d\n%s" (C.key_to_string key) self#stack_size self#to_string];
      let copy = self#copy_stack stack in
      Hashtbl.replace checkpoint_tbl key copy

    method recover key =
      [%debug_log "key=%s size=%d\n%s" (C.key_to_string key) self#stack_size self#to_string];
      try
        stack <- self#copy_stack (Hashtbl.find checkpoint_tbl key)
      with
        Not_found ->
          [%fatal_log "stack not found: key=%s" (C.key_to_string key)];
          raise (Common.Internal_error "Tokenpp.context_buffer#recover")

    method to_string =
      let buf = Buffer.create 0 in
      Stack.iter
        (fun b ->
          Buffer.add_string buf (Printf.sprintf "%s\n" (Context.to_string b#get_context))
        ) stack;
      Buffer.contents buf

  end (* of class context_buffer *)



  type open_section_tag =
    | OSTnone

    | OSTif
    | OSTdo
    | OSTselect
    | OSTforall
    | OSTwhere
    | OSTtype

    | OSTfunction
    | OSTsubroutine
    | OSTpu

  let open_section_tag_to_string = function
    | OSTnone       -> "OSTnone"

    | OSTif         -> "OSTif"
    | OSTdo         -> "OSTdo"
    | OSTselect     -> "OSTselect"
    | OSTforall     -> "OSTforall"
    | OSTwhere      -> "OSTwhere"
    | OSTtype       -> "OSTtype"

    | OSTfunction   -> "OSTfunction"
    | OSTsubroutine -> "OSTsubroutine"
    | OSTpu         -> "OSTpu"

  exception Branch_canceled


  let mutually_exclusive cond0 cond1 =
    let b = ("!"^cond0) = cond1 || cond0 = ("!"^cond1) in
    [%debug_log "%s vs %s -> %B" cond0 cond1 b];
    b

  class buffer ?(context=None) lv partial_parser_selector (tokensrc : Tokensource.c) =
    let new_context =
      match context with
      | None -> true
      | _ -> false
    in
    object (self)

    val top_key = C.mktopkey lv

    val stack = Stack.create()

    val mutable ignored_regions : Loc.t list = []

    val context_buf =
      match context with
      | None -> new context_buffer
      | Some cb -> cb

    val branch_tag_stack = Stack.create()

    val branches_with_else = Xset.create 0
(* *)

    method has_else btag =
      Xset.mem branches_with_else btag

    method reg_branch_with_else btag =
      Xset.add branches_with_else btag

(*
    method current_context_buf = context_buf#current

    method set_context c =
      [%debug_log "[%d] %s" lv (Context.to_string c)];
      context_buf#set_context c
*)
    method clear_context =
      [%debug_log "[%d] called" lv];
      context_buf#clear_context

    method enter_context =
      [%debug_log "[%d] context buffer stack size: %d" lv context_buf#stack_size];
      context_buf#enter_context

    method exit_context =
      [%debug_log "[%d] context buffer stack size: %d" lv context_buf#stack_size];
      context_buf#exit_context


    method checkpoint (key : C.key_t) =
      context_stack#checkpoint key;
      env#checkpoint key;
      context_buf#checkpoint key

    method recover (key : C.key_t) =
      context_stack#recover key;
      env#recover key;
      context_buf#recover key


    method branch_depth =
      Stack.length branch_tag_stack

    method enter_branch btag =
      [%debug_log "[%d] pushing %s" lv (B.tag_to_string btag)];
      Stack.push btag branch_tag_stack

    method exit_branch =
      let btag = Stack.pop branch_tag_stack in
      let _ = btag in
      [%debug_log "[%d] poped %s" lv (B.tag_to_string btag)]

    method nbbuf = Stack.length stack

    method in_branch = not (Stack.is_empty stack)

    method current_bbuf = Stack.top stack

    method add ?(raise_if_failed=false) qtoken =
      [%debug_log "[%d] adding %s (raise_if_failed=%B)"
        lv (Token.qtoken_to_string qtoken) raise_if_failed];
      try
        (self#current_bbuf)#add qtoken
      with
        Stack.Empty ->
          if env#discarded_branch_entry_count > 0 then begin
            if raise_if_failed then
              raise Branch_canceled
          end
          else
            Common.fail_to_parse
              ~head:(Printf.sprintf "[%s]" (Loc.to_string (Token.qtoken_to_loc qtoken)))
              "failed to parse pp-branch"


    method dump_top =
      (self#current_bbuf)#dump



    method get_branch_context =
      let start = ref None in
      let bufs = ref [] in
      begin
	try
	  Stack.iter
	    (fun bbuf ->
	      let cnt = bbuf#top#get_context in

	      [%debug_log "[%d] bbuf[%s] context=%s" lv
		(B.tag_to_string bbuf#get_tag) (C.to_string cnt)];

	      if not (C.is_unknown cnt) && C.is_active cnt then begin
		start := Some (bbuf#top, B.key_loc_of_tag bbuf#get_tag);
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

	  [%debug_log "[%d] loc: %s" lv (try Loc.to_string cpy#get_loc with TB.Empty -> "-")];

	  cpy, key


    method dump_ignored_regions =
      if ignored_regions <> [] then
	Printf.printf "ignored regions:\n";
      Loc.dump_locs ignored_regions

    method ignored_LOC =
      Loc.lines_of_locs ignored_regions

    method ignored_regions = ignored_regions

    method add_ignored_region r =
      [%debug_log "%s" (Loc.to_string ~show_ext:true r)];
      ignored_regions <- r :: ignored_regions

    method add_ignored_regions rs =
      begin %debug_block
        List.iter (fun r -> [%debug_log "%s" (Loc.to_string ~show_ext:true r)]) rs
      end;
      ignored_regions <- rs @ ignored_regions

(*
    method ignored_offsets = List.map Loc.to_offsets ignored_regions
*)

    method begin_branch ~open_if btag =

      [%debug_log "[%d] open_if=%B, nbbuf=%d context=%s btag=%s"
        lv open_if self#nbbuf (C.to_string context_stack#top) (B.tag_to_string btag)];

      let bbuf = new branching_buffer btag in


      if self#in_branch then begin
        [%debug_log "in branch"];
      end
      else begin (* not in branch *)
        [%debug_log "not in branch"];

        let cbuf = context_buf#current in

	let c = cbuf#get_context in

	[%debug_log "[%d] context of context buffer: %s" lv (C.to_string c)];


	if cbuf#is_empty then begin

	  [%debug_log "[%d] context buffer is empty" lv];
	  bbuf#set_context (C.copy_context c)

	end
	else begin (* context buffer is not empty *)

	  [%debug_log "[%d] last non-pp qtoken in context buffer: %s" lv
            (Token.qtoken_to_string cbuf#get_last)];


	  self#checkpoint top_key;

          let bbuf_context = ref (Context.copy_context context_stack#top) in

	  if open_if then
	    context_stack#deactivate_top_no_delay;

          begin
            let last_tok, _ = cbuf#get_last in
            match last_tok with
            | EOL | SEMICOLON
            | SPEC_PART_CONSTRUCT _ | EXEC_PART_CONSTRUCT _
            | DERIVED_TYPE_DEF_PART _ | END_FRAGMENT
            | FUNCTION_HEAD _ | SUBROUTINE_HEAD _ | PU_TAIL _ | STMT _
            | SUBPROGRAM _ | PROGRAM_UNIT _
            | NOTHING
            | INCLUDE__FILE _
                -> ()

            | _ ->
                [%debug_log "changing context: %s -> %s (last_tok=%s)"
                  (C.tag_to_string (C.get_tag !bbuf_context))
                  (C.tag_to_string C.Tin_stmt) (Token.rawtoken_to_string last_tok)];

                C.set_tag (!bbuf_context) C.Tin_stmt
          end;

	  bbuf#set_context !bbuf_context

	end
      end;

      [%debug_log "[%d][%s][%s]: nbbuf=%d (current context: %s)" lv
	(B.tag_to_string btag) (C.to_string bbuf#get_context) self#nbbuf
	(C.to_string context_stack#top)];

      let bcont = bbuf#get_context in
      if not (C.is_unknown bcont) then begin
	let key = C.mkkey lv (B.key_loc_of_tag btag) in
	self#checkpoint key
      end;
      [%debug_log "stack size: %d" self#nbbuf];
      Stack.push bbuf stack;
      [%debug_log "bbuf pushed: %s" (B.tag_to_string bbuf#get_tag)]
    (* end of method begin_branch *)


    method end_branch ~open_if endif_loc =
      ignore open_if;
      [%debug_log "[%d] open_if=%B, nbbuf=%d" lv open_if self#nbbuf];
      let bbuf = Stack.pop stack in
      [%debug_log "bbuf poped: %s" (B.tag_to_string bbuf#get_tag)];
      let selected, ignored = self#select_branches endif_loc bbuf in
      self#add_ignored_regions ignored;

      [%debug_log "[%d] sending to tokensrc" lv];
      selected#dump;
      let key = C.mkkey lv (B.key_loc_of_tag bbuf#get_tag) in
      tokensrc#prepend_queue ~copy:false selected#_raw;
      self#recover key
    (* end of method end_branch *)




    method add_to_context qtoken =
      [%debug_log "[%d] adding %s" lv (Token.qtoken_to_string qtoken)];
      context_buf#current#_add qtoken

    method set_context c =
      [%debug_log "[%d] context=%s" lv (Context.to_string c)];
      context_buf#current#set_context (Context.copy_context c)


    method discard_line =
      begin
        try
          while true do
            let qtoken = tokensrc#get() in
            let tok, _ = qtoken in
            [%debug_log "[%d] discarding %s" lv (Token.rawtoken_to_string tok)];
            match tok with
            | EOL -> raise Exit
            | _ -> ()
          done
        with
          Exit -> ()
      end;
      [%debug_log "finished"]


    method discard_branch ?(start_opt=None) () =
      let branch_depth = ref 0 in
      let loc_opt = ref start_opt in
      let last_eol = ref None in
      begin
        try
          while true do
            let qtoken = tokensrc#get() in
            let tok, loc = qtoken in
            begin
              match !loc_opt with
              | None -> loc_opt := Some loc
              | _ -> ()
            end;
            [%debug_log "[%d] discarding %s" lv (Token.rawtoken_to_string tok)];
            match tok with
            | PP_BRANCH (PPD.Ifdef _ | PPD.Ifndef _ | PPD.If _) -> incr branch_depth

	    | PP_BRANCH (PPD.Endif _) -> begin
		if !branch_depth = 0 then begin
                  let ignored =
                    match !loc_opt with
                    | Some loc' -> merge_locs loc' loc
                    | None -> loc
                  in
                  self#add_ignored_region ignored;
                  raise Exit
                end;

		if !branch_depth > 0 then
		    decr branch_depth
            end
            | EOL ->
                last_eol := Some qtoken

            | OCL _ | OMP _ | XLF _ | ACC _ | DEC _ -> ()

            | _ ->
                if TokenF.is_pp_directive tok then
                  ()
                else
                  last_eol := None
          done
        with
          Exit -> ()
      end;
      begin
        match !last_eol with
        | Some t -> tokensrc#prepend t
        | _ -> ()
      end;
      [%debug_log "finished"]


    method private consume () =
      let qtoken = tokensrc#get() in
      let tok, loc = qtoken in

      let buffer_add ?(raise_if_failed=false) () =
        [%debug_log "[%d] in_branch=%B" lv self#in_branch];
        let t =
          if self#in_branch then
            qtoken
          else
            TBF.hack_token tokensrc qtoken
        in
	self#add ~raise_if_failed t
      in

      [%debug_log "[%d] %s[%s]" lv
        (Token.rawtoken_to_string tok) (Loc.to_string ~show_ext:true loc)];

      match tok with
      | RAW {DL.tag=DL.OCL;DL.line=line;_} -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
          env#current_source#add_ext_Fujitsu;
          let ofs = 4 in (* length of '!ocl' *)
          let ulb = lexbuf_from_line loc ofs (line^"\n") in
          let scanner () = PB.qtoken_to_token (U.scan_ocl ulb) in
          try
            let nd = (PB.mkparser P.ocl) scanner in
            nd#set_lloc (LLoc.merge (env#mklloc loc) nd#lloc);
            let tok' = OCL nd in
            if self#in_branch then begin
              let t = (tok', loc) in
              self#add t;
              self#pp ()
            end
            else
              tok', loc
          with
            _ ->
              Common.parse_warning_loc loc "failed to parse ocl:%s" line;
              self#pp ()
      end
      | RAW {DL.tag=DL.DEC;DL.head=prefix;DL.line=line;_} -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
          env#current_source#add_ext_Intel;
          let ofs = (String.length prefix) + 1 in (* length of '!' + prefix *)
          let ulb = lexbuf_from_line loc ofs (line^"\n") in
          let scanner () = PB.qtoken_to_token (U.scan_dec ulb) in
          try
            let nd = (PB.mkparser P.dec) scanner in
            nd#set_lloc (LLoc.merge (env#mklloc loc) nd#lloc);
            let tok' = DEC nd in
            if self#in_branch then begin
              let t = (tok', loc) in
              self#add t;
              self#pp ()
            end
            else
              tok', loc
          with
            _ ->
              Common.parse_warning_loc loc "failed to parse dec:%s" line;
              self#pp ()
      end
      | RAW {DL.tag=DL.XLF;
             DL.head=trigger;
             DL.line=line;
             DL.queue=q;
             DL.fixed_cont=_;
             DL.free_cont=free_cont;
             _
           } -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
          env#current_source#add_ext_IBM;
          let queue = q in
          begin
            let cur_free_cont = ref free_cont in
            try
              while true do
                let ntok = tokensrc#peek_nth_rawtok 1 in
                [%debug_log "next token: %s" (Token.rawtoken_to_string ntok)];
                match ntok with
                | RAW {DL.tag=DL.XLF;
                       DL.line=nline;
                       DL.queue=nq;
                       DL.fixed_cont=nfix_cont;
                       DL.free_cont=nfree_cont;
                       _
                     } ->
                    if !cur_free_cont || nfix_cont then begin
                      [%debug_log "continued: %s" nline];
                      let _ = tokensrc#get() in
                      nq#transfer queue;
                      cur_free_cont := nfree_cont
                    end
                    else
                      raise Exit
                | _ -> raise Exit
              done
            with
              Exit -> ()
          end;

          let last_t = ref (Obj.repr qtoken) in
          queue#iter (fun t -> last_t := t);
          queue#add (Obj.repr (EOL, Token.qtoken_to_loc (Obj.obj !last_t)));

          begin %debug_block
            [%debug_log "queue:"];
            queue#iter (fun r -> [%debug_log " %s" (Token.qtoken_to_string (Obj.obj r))])
          end;

          let scanner () =
            let t =
              try
                Obj.obj queue#take
              with
                Xqueue.Empty -> raise Sedlexing.MalFormed
            in
            let rt, _ = t in
            let _ = rt in
            [%debug_log "--> %s" (Token.rawtoken_to_string rt)];
            PB.qtoken_to_token t
          in
          try
            let nd = (PB.mkparser P.xlf) scanner in
            nd#set_lloc (LLoc.merge (env#mklloc loc) nd#lloc);
            let tok' = XLF nd in
            if self#in_branch then begin
              let t = (tok', loc) in
              self#add t;
              self#pp ()
            end
            else
              tok', loc
          with
            exn ->
              Common.parse_warning_loc loc "failed to parse xlf: [%s]:%s" line (Printexc.to_string exn);
              self#pp ()
      end
      | RAW {DL.tag=DL.OMP;
             DL.line=line;
             DL.queue=q;
             DL.fixed_cont=_;
             DL.free_cont=free_cont;
             _
           } -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
          let queue = q(*#copy*) in
          begin
            let cur_free_cont = ref free_cont in
            try
              while true do
                let ntok = tokensrc#peek_nth_rawtok 1 in
                [%debug_log "next token: %s" (Token.rawtoken_to_string ntok)];
                match ntok with
                | RAW {DL.tag=DL.OMP;
                       DL.line=nline;
                       DL.queue=nq;
                       DL.fixed_cont=nfix_cont;
                       DL.free_cont=nfree_cont;
                       _
                     } ->
                    let _ = nline in
                    if !cur_free_cont || nfix_cont then begin
                      [%debug_log "continued: %s" nline];
                      let _ = tokensrc#get() in
                      nq#transfer queue;
                      cur_free_cont := nfree_cont
                    end
                    else begin
                      raise Exit
                    end
                | _ -> raise Exit
              done
            with
              Exit -> ()
          end;
          let last_t = ref (Obj.repr qtoken) in
          queue#iter (fun t -> last_t := t);
          queue#add (Obj.repr (EOL, Token.qtoken_to_loc (Obj.obj !last_t)));

          begin %debug_block
            [%debug_log "queue:"];
            queue#iter (fun r -> [%debug_log " %s" (Token.qtoken_to_string (Obj.obj r))])
          end;

          (* check for separated keywords *)
          let queue2 = new Xqueue.c in
          let _ =
            queue#fold
              (fun tmp_opt r ->
                let t = Obj.obj r in
                match Token.qtoken_to_rawtoken t with
                | IDENTIFIER i -> begin
                    match tmp_opt with
                    | Some (tmp, _) -> begin
                        let tmp_tok, tmp_loc = tmp in
                        match tmp_tok with
                        | IDENTIFIER tmp_i ->
                            let st, _ = Loc.to_lexposs tmp_loc in
                            let _, ed = Loc.to_lexposs (Token.qtoken_to_loc t) in
                            let t' = PB.make_qtoken (IDENTIFIER (tmp_i^i)) st ed in
                            Some (t', true)

                        | _ -> assert false
                    end
                    | None -> Some (t, false)
                end
                | _ -> begin
                    begin
                      match tmp_opt with
                      | Some (tmp, merged) ->
                          if merged then begin
                            match Token.qtoken_to_rawtoken tmp with
                            | IDENTIFIER i ->
                                let tok = U.find_omp_keyword i in
                                let loc = Token.qtoken_to_loc tmp in
                                let t = (tok, loc) in
                                queue2#add t
                            | _ -> assert false
                          end
                          else begin
                            queue2#add tmp
                          end
                      | None -> ()
                    end;
                    queue2#add (Obj.obj r);
                    None
                end
              ) None
          in
          begin %debug_block
            [%debug_log "queue2:"];
            queue2#iter (fun t -> [%debug_log " %s" (Token.qtoken_to_string t)])
          end;

          (* further *)
          let queue3 = new Xqueue.c in
          let qadd x = queue3#add x in
          let _ =
            queue2#fold (U.check_omp_separated_keyword qadd) None
          in

          begin %debug_block
            [%debug_log "queue3:"];
            queue3#iter (fun t -> [%debug_log " %s" (Token.qtoken_to_string t)])
          end;

          (* end: separated keyword check *)

          let tok_hist = ref [] in (* recent ... first *)
          let paren_level = ref 0 in

          let is_type_kw = function
(*
            | COMPLEX _
            | INTEGER _
            | LOGICAL _
            | REAL _
*)
            | KINDED_TYPE_SPEC _
            | DOUBLE_PRECISION _
            | DOUBLE_COMPLEX _
            | CHARACTER _
            | KIND _
            | LEN _ -> true
            | _ -> false
          in
          let in_omp_kind_context() =
            match !tok_hist with
            | LPAREN::(OMP_SCHEDULE|OMP_DIST_SCHEDULE)::_ -> true
            | _ -> false
          in
          let in_omp_default_context() =
            match !tok_hist with
            | LPAREN::OMP_DEFAULT::_ -> true
            | _ -> false
          in
          let in_omp_depend_context() =
            match !tok_hist with
            | LPAREN::OMP_DEPEND::_ -> true
            | _ -> false
          in
          let in_omp_proc_bind_context() =
            match !tok_hist with
            | LPAREN::OMP_PROC_BIND::_ -> true
            | _ -> false
          in
          let in_omp_map_type_context = function
            | Some COLON -> begin
                match !tok_hist with
                | LPAREN::OMP_MAP::_ -> true
                | _ -> false
            end
            | Some _
            | None -> false
          in
          let in_type_context() =
            let rec scan = function
              | COLON::rest -> rest
              | _::rest -> scan rest
              | [] -> []
            in
            match scan !tok_hist with
            | _::LPAREN::OMP_DECLARE_REDUCTION::_ -> true
            | _ -> false
          in

          let scanner () =
            let final_t =
              try
                let t = queue3#take in
                let tok, loc = t in
                begin
                  match tok with
                  | LPAREN -> incr paren_level
                  | RPAREN -> decr paren_level
                  | _ -> ()
                end;
                begin (* convert token to ident according to the context *)
                  match tok with
                  | IDENTIFIER _ -> t
                  | _ -> begin
                      try
                        let kw = U.get_omp_keyword_string tok in

                        let mk_ident_token() =
                          (IDENTIFIER kw, loc)
                        in

                        let next_tok_opt =
                          try
                            let next_t = queue3#peek in
                            Some (Token.qtoken_to_rawtoken next_t)
                          with
                            Xqueue.Empty -> None
                        in

                        if in_omp_kind_context() then begin
                          [%debug_log "in omp_kind context"];
                          t
                        end
                        else if in_omp_default_context() then begin
                          [%debug_log "in omp_default context"];
                          t
                        end
                        else if in_omp_depend_context() then begin
                          [%debug_log "in omp_depend context"];
                          t
                        end
                        else if in_omp_proc_bind_context() then begin
                          [%debug_log "in omp_proc_bind context"];
                          t
                        end
                        else if in_omp_map_type_context next_tok_opt then begin
                          [%debug_log "in omp_map_type context"];
                          t
                        end
                        else if in_type_context() then begin
                          [%debug_log "in type context"];
                          if is_type_kw tok then
                            t
                          else begin
                            [%debug_log "<non type keyword> --> <identifier> (in type context)"];
                            mk_ident_token()
                          end
                        end
                        else if !paren_level > 0 then begin
                          [%debug_log "in paren"];
(*
                          let next_cond =
                            try
                              let next_t = queue3#peek in
                              match Token.to_rawtoken next_t with
                              | COMMA -> begin
                                  [%debug_log "<keyword> --> <identifier> (<keyword> ',')"];
                                  true
                              end
                              | _ -> false
                            with
                              Xqueue.Empty -> false
                          in
                          let prev_cond =
                            match !tok_hist with
                              | COMMA::_ -> begin
                                  [%debug_log "<keyword> --> <identifier> (',' <keyword>)"];
                                  true
                              end
                              | _ -> false
                          in
                          if next_cond || prev_cond then
*)
                            mk_ident_token()
(*
                          else
                            t
*)
                        end
                        else
                          t
                      with
                        Not_found -> t
                  end
                end
              with
                Xqueue.Empty -> raise Sedlexing.MalFormed
            in
            let final_tok, _ = final_t in
            tok_hist := final_tok :: !tok_hist;
            [%debug_log "--> %s" (Token.rawtoken_to_string final_tok)];
            PB.qtoken_to_token final_t

          in (* scanner *)

          try
            let nd = (PB.mkparser P.omp) scanner in
            nd#set_lloc (LLoc.merge (env#mklloc loc) nd#lloc);
            let tok' = OMP nd in
            if self#in_branch then begin
              let t = (tok', loc) in
              self#add t;
              self#pp ()
            end
            else
              tok', loc
          with
            exn ->
              Common.parse_warning_loc loc
                "failed to parse omp: [%s]:%s" line (Printexc.to_string exn);
              self#pp ()
      end
      | RAW {DL.tag=DL.ACC;
             DL.line=line;
             DL.queue=q;
             DL.fixed_cont=_;
             DL.free_cont=free_cont;
             _
           } -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
          let queue = q in
          begin
            let cur_free_cont = ref free_cont in
            try
              while true do
                let ntok = tokensrc#peek_nth_rawtok 1 in
                [%debug_log "next token: %s" (Token.rawtoken_to_string ntok)];
                match ntok with
                | RAW {DL.tag=DL.ACC;
                       DL.line=nline;
                       DL.queue=nq;
                       DL.fixed_cont=nfix_cont;
                       DL.free_cont=nfree_cont;
                       _
                     } ->
                    let _ = nline in
                    if !cur_free_cont || nfix_cont then begin
                      [%debug_log "continued: %s" nline];
                      let _ = tokensrc#get() in
                      nq#transfer queue;
                      cur_free_cont := nfree_cont
                    end
                    else
                      raise Exit
                | _ -> raise Exit
              done
            with
              Exit -> ()
          end;

          let last_t = ref (Obj.repr qtoken) in
          queue#iter (fun t -> last_t := t);
          queue#add (Obj.repr (EOL, Token.qtoken_to_loc (Obj.obj !last_t)));

          begin %debug_block
            [%debug_log "queue:"];
            queue#iter (fun r -> [%debug_log " %s" (Token.qtoken_to_string (Obj.obj r))])
          end;

          let scanner () =
            let t =
              try
                Obj.obj queue#take
              with
                Xqueue.Empty -> raise Sedlexing.MalFormed
            in
            let rt, _ = t in
            let _ = rt in
            [%debug_log "--> %s" (Token.rawtoken_to_string rt)];
            PB.qtoken_to_token t
          in
          try
            let nd = (PB.mkparser P.acc) scanner in
            nd#set_lloc (LLoc.merge (env#mklloc loc) nd#lloc);
            let tok' = ACC nd in
            if self#in_branch then begin
              let t = (tok', loc) in
              self#add t;
              self#pp ()
            end
            else
              tok', loc
          with
            exn ->
              Common.parse_warning_loc loc
                "failed to parse acc: [%s]:%s" line (Printexc.to_string exn);
              self#pp ()
      end
      | PP_BRANCH (PPD.Ifdef id | PPD.Ifndef id) -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
	  let btag = mkbtag tok id loc loc in

          self#enter_branch btag;
          if self#branch_depth = 1 then begin
            self#begin_branch ~open_if:false btag
          end
          else begin
            buffer_add()
          end;

	  [%debug_log "[%d] calling pp" lv];
	  self#pp ()
      end
      | PP_BRANCH (PPD.If _) -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
	  let btag = mkbtag tok "" loc loc in

          self#enter_branch btag;
          if self#branch_depth = 1 then begin
            self#begin_branch ~open_if:false btag
          end
          else begin
            buffer_add()
          end;

	  [%debug_log "[%d] calling pp" lv];
	  self#pp ()
      end
      | PP_BRANCH (PPD.Elif _) -> begin
          let branch_depth = self#branch_depth in

          [%debug_log "processing %s (branch depth: %d)"
            (Token.rawtoken_to_string tok) branch_depth];

          if branch_depth = 1 then begin
            let kloc =
              try
                let tag = Stack.top branch_tag_stack in
                [%debug_log "top branch tag: %s" (B.tag_to_string tag)];
                B.key_loc_of_tag tag
              with
                _ -> loc
            in
	    self#current_bbuf#new_branch (mkbtag tok "" loc kloc)
          end
          else if branch_depth = 0 then begin
            Common.parse_warning_loc loc "ignoring dangling #elif"
          end
          else begin
            try
              buffer_add ~raise_if_failed:true ()
            with
              Branch_canceled -> self#discard_branch ~start_opt:(Some loc) ()
          end;

	  [%debug_log "[%d] calling pp" lv];
	  self#pp ()
      end
      | PP_BRANCH PPD.Else -> begin
          let branch_depth = self#branch_depth in

          [%debug_log "processing %s (branch depth: %d)"
            (Token.rawtoken_to_string tok) branch_depth];

          if branch_depth = 1 then begin
            let top_btag = Stack.top branch_tag_stack in
            self#reg_branch_with_else top_btag;
            let kloc =
              try
                B.key_loc_of_tag top_btag
              with
                _ -> loc
            in
	    self#current_bbuf#new_branch (mkbtag tok "" loc kloc)
          end
          else if branch_depth = 0 then begin
            Common.parse_warning_loc loc "ignoring dangling #else"
          end
          else begin
            try
              buffer_add ~raise_if_failed:true ()
            with
              Branch_canceled -> self#discard_branch ~start_opt:(Some loc) ()
          end;

	  [%debug_log "[%d] calling pp" lv];
	  self#pp ()
      end
      | PP_BRANCH (PPD.Endif(br, plv)) -> begin
          let branch_depth = self#branch_depth in

          [%debug_log "processing %s (branch depth: %d)"
            (Token.rawtoken_to_string tok) self#branch_depth];

          begin
            try
              if branch_depth = 0 then begin
                Common.parse_warning_loc loc "ignoring dangling #endif"
              end
              else begin
                if branch_depth = 1 then begin

                  let to_be_discarded = ref 0 in

                  let top_btag = Stack.top branch_tag_stack in

                  [%debug_log "has_else=%B" (self#has_else top_btag)];

                  let is_virtual_else = (* should be false when the branch has else *)
                    not (self#has_else top_btag) &&
                    match br with
                    | PPD.If cond -> begin
                        (*Printf.printf "! %s ->\n  %s\n  %s\n%!"
                          (Token.qtoken_to_string (tok, loc))
                          (Token.rawtoken_to_string (tokensrc#peek_nth_rawtok 1))
                          (Token.rawtoken_to_string (tokensrc#peek_nth_rawtok 2));*)
                        match tokensrc#peek_nth_rawtok 1 with
                        | END_FRAGMENT -> begin
                            match tokensrc#peek_nth_rawtok 2 with
                            | PP_BRANCH (PPD.If cond') -> begin
                                [%debug_log "paren level: %d -> %d" plv env#lex_paren_level];
                                let b =
                                  mutually_exclusive cond cond' || plv <> env#lex_paren_level
                                in
                                if b then
                                  to_be_discarded := 2;
                                b
                            end
                            | _ -> false
                        end
                        | PP_BRANCH (PPD.If cond') -> begin
                            [%debug_log "paren level: %d -> %d" plv env#lex_paren_level];
                            let b =
                              mutually_exclusive cond cond' || plv <> env#lex_paren_level
                            in
                            if b then
                              to_be_discarded := 1;
                            b
                        end
                        | _ -> false
                    end
                    | _ -> false
                  in
                  [%debug_log "is_virtual_else=%B to_be_discarded=%d" is_virtual_else !to_be_discarded];

                  if is_virtual_else then begin
                    for _ = 1 to !to_be_discarded do
                      let t, _ = tokensrc#discard ~skip_pp_branch:false () in
                      let _ = t in
                      [%debug_log "discarded: %s" (Token.rawtoken_to_string t)]
                    done;
                    let kloc =
                      try
                        B.key_loc_of_tag top_btag
                      with
                        _ -> loc
                    in
	            self#current_bbuf#new_branch (mkbtag tok "" loc kloc)
                  end
                  else begin
                    self#end_branch ~open_if:false loc;
                    self#exit_branch
                  end
                end
                else begin
                  buffer_add ~raise_if_failed:true ();
                  self#exit_branch
                end
              end
            with
              Branch_canceled -> env#decr_discarded_branch_entry_count
          end;

	  [%debug_log "[%d] calling pp" lv];
	  self#pp ()

      end

      | PP_INCLUDE__FILE _ | INCLUDE__FILE _ | OPTIONS__OPTS _ -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];

	  if self#in_branch then begin
	    buffer_add();
	    [%debug_log "[%d] calling pp" lv];
	    self#pp ()
	  end
	  else begin
	    self#add_to_context (tok, loc);
	    tok, loc
	  end
      end
      | PP_UNDEF__IDENT id -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
	  if self#in_branch then begin
	    buffer_add();
	    [%debug_log "[%d] calling pp" lv];
	    self#pp ()
	  end
	  else begin
            env#undefine_macro id;
	    self#add_to_context (tok, loc);
	    tok, loc
	  end
      end

      | PP_DEFINE__IDENT__BODY(id, body) -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
	  if self#in_branch then begin

            [%debug_log "branch: %s" (B.tag_to_string self#current_bbuf#top#get_tag)];

            let unconditional =
              lv = 0 &&
              match self#current_bbuf#top#get_tag with
              | B.Tifndef(id', _) -> id' = id
              | _ -> false
            in
            [%debug_log "unconditional=%B" unconditional];
            if unconditional then
              env#define_macro ~conditional:false id body;

	    buffer_add();
	    [%debug_log "[%d] calling pp" lv];
	    self#pp ()
	  end
	  else begin
            env#define_macro ~conditional:(lv > 0) id body;
	    self#add_to_context (tok, loc);
	    tok, loc
	  end
      end

      | _ -> begin
          [%debug_log "processing %s" (Token.rawtoken_to_string tok)];
	  [%debug_log "[%d] in_branch=%B" lv self#in_branch];

	  if self#in_branch then begin
	    begin
	      match tok with
	      | EOF _ -> begin
                  Common.parse_warning_loc loc "non-terminated pp-branch";
                  try
                    self#end_branch ~open_if:false loc;
                    self#exit_branch
                  with
                    Branch_canceled -> env#decr_discarded_branch_entry_count
              end
	      | _ -> buffer_add()
	    end;
	    [%debug_log "[%d] calling pp" lv];
	    self#pp ()
	  end
	  else begin (* not in branch *)
	    if context_buf#current_is_empty then
	      if context_stack#top_is_active && not context_stack#top_is_unknown then
		self#set_context context_stack#top;

            self#add_to_context (tok, loc);

	    tok, loc

	  end (* not in branch *)
      end (* | _ -> *)

    (* end of method consume *)


    method pp () =
      [%debug_log "[%d] tokenbuf#in_branch=%B" lv self#in_branch];
      [%debug_log "[%d] calling consume" lv];
      self#consume ()
   (* end of method pp *)


    method select_branches endif_loc bbuf =

      let context = bbuf#get_context in

      begin %debug_block
	[%debug_log "[%d] context: %s" lv (C.to_string context)];
        [%debug_log "[%d] branches:" lv];
        bbuf#iter_branch
	  (fun buf ->
	    [%debug_log "%s [%s] (ntokens=%d) [%s]"
	      (B.tag_to_string buf#get_tag)
	      (try Loc.to_string buf#get_loc with _ -> "-")
	      buf#size
	      (C.to_string buf#get_context)];
	    buf#dump
	  );
      end;

      let selected_buf = ref (new TBF.c B.Tselected) in
      (!selected_buf)#set_context context;

      let ignored_regions = ref [] in

(*      context_stack#suspend; *)

      let tag_loc = B.loc_of_tag bbuf#get_tag in

      [%debug_log "tag_loc: %s" (Loc.to_string ~show_ext:true tag_loc)];

      let key = C.mkkey lv tag_loc in


      let bbuf_top_last_EOL_opt = bbuf#top#get_last_EOL in
      let bbuf_top_length = bbuf#top#total_length_no_pp in

      [%debug_log "bbuf_top_last_EOL_opt: %s (buf length: %d)"
        (Common.opt_to_string Token.qtoken_to_string bbuf_top_last_EOL_opt)
        bbuf_top_length];

      let bbuf_top_last_EOL_exists =
        match bbuf_top_last_EOL_opt with
        | Some _ -> true
        | None -> false
      in


      let adjust_last ?(context=C.dummy) buf =
        begin %debug_block
          [%debug_log "context: %s" (C.to_string context)];
          [%debug_log "buf length: %d" buf#total_length];
          buf#dump;
        end;

        if buf#total_length > 0 && bbuf_top_length > 0 then

          let pp_only =
            try
              buf#iter
                (fun (t, _) ->
                  if not (TokenF.is_pp_directive t || TokenF.is_include t) then
                    raise Exit
                );
              true
            with
              Exit -> false
          in
          [%debug_log "pp_only=%B" pp_only];
          (*Printf.printf "! pp_only=%B\n%!" pp_only;*)

          let directive_only =
            try
              buf#iter
                (fun (t, _) ->
                  if not (TokenF.is_directive t) then
                    raise Exit
                );
              true
            with
              Exit -> false
          in
          [%debug_log "directive_only=%B" directive_only];

          if pp_only || directive_only then
            buf#set_irregular;

          if buf#ends_with_EOL then begin
            [%debug_log "buffer ends with EOL"];
            (*Printf.printf "! buffer ends with EOL\n%!";*)
            match bbuf_top_last_EOL_opt with
            | Some _ -> begin
                match context.C.tag with
                | C.Texpr | C.Tin_stmt -> begin
                    [%debug_log "removing EOL..."];
                    (*Printf.printf "! removing EOL...\n%!";*)
                    buf#remove_last_EOL
                end
                | _ -> ()
            end
            | None -> begin
                if bbuf#top#is_regular then begin
                  [%debug_log "removing EOL..."];
                  (*Printf.printf "! removing EOL...\n%!";*)
                  buf#remove_last_EOL
                end
            end
          end
          else begin
            [%debug_log "buffer does not end with EOL"];
            (*Printf.printf "! buffer does not end with EOL\n%!";*)
            match bbuf_top_last_EOL_opt with
            | Some t -> begin
                match context.C.tag with
                | C.Texpr | C.Tin_stmt -> ()
                | _ ->
                    if not pp_only && not directive_only then begin
                      [%debug_log "adding EOL..."];
                      (*Printf.printf "! adding EOL...\n%!";*)
                      buf#_add t
                    end
            end
            | None -> ()
          end
      in (* func adjust_last *)

      let top_context = bbuf#top#get_context in
      [%debug_log "[%d] top context: %s" lv (C.to_string top_context)];

      let blist = ref [] in

      try
	if not (C.is_active top_context) then
	  raise C.Not_active;

	[%debug_log "[%d] current context: %s" lv (C.to_string (context_stack#top))];

        [%debug_log "context: %s" (C.to_string context)];

	let parsers = partial_parser_selector context in

        [%debug_log "%d parsers selected" (List.length parsers)];


	let ignored = ref [] in

	let multi_mode = ref false in

        [%debug_log "nbranches=%d" bbuf#nbranches];

        let incomplete_flag = ref true in

	bbuf#iter_branch
	  (fun br ->

            adjust_last ~context:top_context br;
            br#remove_first_END_FRAGMENT;

            let pcount = ref 1 in

            try
              List.iter
                (fun _parser ->
	          try
                    self#recover key;

                    [%debug_log "trying to parse with the %s parser (context=%s)"
                      (Common.num_to_ordinal !pcount) (C.to_string context)];

                    (*Printf.printf "! trying to parse with the %s parser (context=%s)\n%!"
                      (Common.num_to_ordinal !pcount) (C.to_string context);*)

                    let use_cache_incomplete = !pcount = 1 in

	            let partial = self#parse ~use_cache_incomplete _parser br in
	            let nnodes, nerrs = check_partial partial in
                    (*Printf.printf "! nnodes=%d nerrs=%d\n%!" nnodes nerrs;*)

	            if nnodes > 0 && nerrs = 0 then
		      multi_mode := true;

                    if nnodes = 0 then begin
                      [%debug_log "empty branch"]
                    end
	            else if nnodes = nerrs then begin
                      [%debug_log "ignoring branch:"];
                      br#dump;
		      ignored := br::!ignored
                    end
	            else begin
		      br#to_partial ~context_opt:(Some context) partial;
		      blist := br::!blist
	            end;
                    [%debug_log "successfully parsed"];
                    (*Printf.printf "! PARSED (nnodes=%d nerrs=%d)\n%!" nnodes nerrs;*)
                    incomplete_flag := false;
                    raise Exit

	          with
                    TB.Incomplete ->
                      [%debug_log "INCOMPLETE"];
                      (*Printf.printf "! INCOMPLETE\n%!";*)
                      incr pcount

                ) parsers;

              [%debug_log "ignoring branch:"];
              (*Printf.printf "ignoring branch:\n%s\n%!" br#to_string;*)
              br#dump;
              ignored := br::!ignored

            with
              Exit -> ()
	  );

(*	context_stack#resume; *)

        [%debug_log "incomplete_flag=%B multi_mode=%B" !incomplete_flag !multi_mode];

	if !incomplete_flag || !blist = [] || not !multi_mode then begin
	  [%debug_log "[%d] incomplete branch" lv];
	  raise TB.Incomplete
	end
	else begin

          let get_open_section_list br =
            let reverse_mode = ref false in
            let cstack = Stack.create() in
            begin
              try
                List.iter
                  (fun nd ->
                    match nd#label with
                    | Label.Stmt stmt -> begin
                        match Stmt.get_raw_stmt stmt with
                        | Stmt.DoStmt _              -> Stack.push (nd, OSTdo) cstack
                        | Stmt.ForallConstructStmt _ -> Stack.push (nd, OSTforall) cstack
                        | Stmt.IfThenStmt _          -> Stack.push (nd, OSTif) cstack
                        | Stmt.SelectCaseStmt _      -> Stack.push (nd, OSTselect) cstack
                        | Stmt.WhereConstructStmt _  -> Stack.push (nd, OSTwhere) cstack
                        | Stmt.DerivedTypeStmt _     -> Stack.push (nd, OSTtype) cstack
                        | Stmt.FunctionStmt _        -> Stack.push (nd, OSTfunction) cstack
                        | Stmt.SubroutineStmt _      -> Stack.push (nd, OSTsubroutine) cstack
                        | Stmt.ModuleStmt _          -> Stack.push (nd, OSTpu) cstack
                        | Stmt.SubmoduleStmt _       -> Stack.push (nd, OSTpu) cstack
                        | Stmt.BlockDataStmt _       -> Stack.push (nd, OSTpu) cstack

                        | Stmt.EndDoStmt _     -> begin
                            match Stack.top cstack with
                            | (_, OSTdo) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndForallStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTforall) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndIfStmt _     -> begin
                            match Stack.top cstack with
                            | (_, OSTif) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndSelectStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTselect) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndWhereStmt _  -> begin
                            match Stack.top cstack with
                            | (_, OSTwhere) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndTypeStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTtype) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndFunctionStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTfunction) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndSubroutineStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTsubroutine) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndModuleStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTpu) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndSubmoduleStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTpu) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndBlockDataStmt _ -> begin
                            match Stack.top cstack with
                            | (_, OSTpu) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Stmt.EndStmt -> begin
                            match Stack.top cstack with
                            | (_, OSTpu)
                            | (_, OSTfunction)
                            | (_, OSTsubroutine) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end

                        | _ -> ()
                    end

                    | Label.PpBranchDo          -> Stack.push (nd, OSTdo) cstack
                    | Label.PpBranchForall      -> Stack.push (nd, OSTforall) cstack
                    | Label.PpBranchIf          -> Stack.push (nd, OSTif) cstack
                    | Label.PpBranchSelect      -> Stack.push (nd, OSTselect) cstack
                    | Label.PpBranchWhere       -> Stack.push (nd, OSTwhere) cstack
                    | Label.PpBranchDerivedType -> Stack.push (nd, OSTtype) cstack
                    | Label.PpBranchFunction    -> Stack.push (nd, OSTfunction) cstack
                    | Label.PpBranchSubroutine  -> Stack.push (nd, OSTsubroutine) cstack
                    | Label.PpBranchPu          -> Stack.push (nd, OSTpu) cstack

                    | Label.PpBranchEndDo     -> begin
                        match Stack.top cstack with
                        | (_, OSTdo) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndForall -> begin
                        match Stack.top cstack with
                        | (_, OSTforall) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndIf     -> begin
                        match Stack.top cstack with
                        | (_, OSTif) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndSelect -> begin
                        match Stack.top cstack with
                        | (_, OSTselect) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndWhere  -> begin
                        match Stack.top cstack with
                        | (_, OSTwhere) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndType  -> begin
                        match Stack.top cstack with
                        | (_, OSTtype) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndFunction  -> begin
                        match Stack.top cstack with
                        | (_, OSTfunction) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndSubroutine  -> begin
                        match Stack.top cstack with
                        | (_, OSTsubroutine) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end
                    | Label.PpBranchEndPu  -> begin
                        match Stack.top cstack with
                        | (_, OSTpu) -> ignore (Stack.pop cstack)
                        | _ -> raise TB.Incomplete
                    end

                    | _ -> ()
                  ) br#children
              with
                Stack.Empty ->
                  [%debug_log "reverse mode"];
                  reverse_mode := true;
                  Stack.clear cstack;
                  try
                    List.iter
                      (fun nd ->
                        match nd#label with
                        | Label.Stmt stmt -> begin
                            match Stmt.get_raw_stmt stmt with
                            | Stmt.EndDoStmt _         -> Stack.push (nd, OSTdo) cstack
                            | Stmt.EndForallStmt _     -> Stack.push (nd, OSTforall) cstack
                            | Stmt.EndIfStmt _         -> Stack.push (nd, OSTif) cstack
                            | Stmt.EndSelectStmt _     -> Stack.push (nd, OSTselect) cstack
                            | Stmt.EndWhereStmt _      -> Stack.push (nd, OSTwhere) cstack
                            | Stmt.EndTypeStmt _       -> Stack.push (nd, OSTtype) cstack
                            | Stmt.EndFunctionStmt _   -> Stack.push (nd, OSTfunction) cstack
                            | Stmt.EndSubroutineStmt _ -> Stack.push (nd, OSTsubroutine) cstack
                            | Stmt.EndStmt             -> Stack.push (nd, OSTpu) cstack

                            | Stmt.DoStmt _              -> begin
                                match Stack.top cstack with
                                | (_, OSTdo) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.ForallConstructStmt _ -> begin
                                match Stack.top cstack with
                                | (_, OSTforall) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.IfThenStmt _          -> begin
                                match Stack.top cstack with
                                | (_, OSTif) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.SelectCaseStmt _      -> begin
                                match Stack.top cstack with
                                | (_, OSTselect) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.WhereConstructStmt _  -> begin
                                match Stack.top cstack with
                                | (_, OSTwhere) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.DerivedTypeStmt _     -> begin
                                match Stack.top cstack with
                                | (_, OSTtype) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.FunctionStmt _     -> begin
                                match Stack.top cstack with
                                | (_, OSTpu)
                                | (_, OSTfunction) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.SubroutineStmt _     -> begin
                                match Stack.top cstack with
                                | (_, OSTpu)
                                | (_, OSTsubroutine) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.ModuleStmt _     -> begin
                                match Stack.top cstack with
                                | (_, OSTpu) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.SubmoduleStmt _     -> begin
                                match Stack.top cstack with
                                | (_, OSTpu) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end
                            | Stmt.BlockDataStmt _     -> begin
                                match Stack.top cstack with
                                | (_, OSTpu) -> ignore (Stack.pop cstack)
                                | _ -> raise TB.Incomplete
                            end

                            | _ -> ()
                        end

                        | Label.PpBranchEndDo         -> Stack.push (nd, OSTdo) cstack
                        | Label.PpBranchEndForall     -> Stack.push (nd, OSTforall) cstack
                        | Label.PpBranchEndIf         -> Stack.push (nd, OSTif) cstack
                        | Label.PpBranchEndSelect     -> Stack.push (nd, OSTselect) cstack
                        | Label.PpBranchEndWhere      -> Stack.push (nd, OSTwhere) cstack
                        | Label.PpBranchEndType       -> Stack.push (nd, OSTtype) cstack
                        | Label.PpBranchEndFunction   -> Stack.push (nd, OSTfunction) cstack
                        | Label.PpBranchEndSubroutine -> Stack.push (nd, OSTsubroutine) cstack
                        | Label.PpBranchEndPu         -> Stack.push (nd, OSTpu) cstack

                        | Label.PpBranchDo     -> begin
                            match Stack.top cstack with
                            | (_, OSTdo) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchForall -> begin
                            match Stack.top cstack with
                            | (_, OSTforall) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchIf     -> begin
                            match Stack.top cstack with
                            | (_, OSTif) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchSelect -> begin
                            match Stack.top cstack with
                            | (_, OSTselect) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchWhere  -> begin
                            match Stack.top cstack with
                            | (_, OSTwhere) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchDerivedType -> begin
                            match Stack.top cstack with
                            | (_, OSTtype) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchFunction -> begin
                            match Stack.top cstack with
                            | (_, OSTpu)
                            | (_, OSTfunction) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchSubroutine -> begin
                            match Stack.top cstack with
                            | (_, OSTpu)
                            | (_, OSTsubroutine) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end
                        | Label.PpBranchPu -> begin
                            match Stack.top cstack with
                            | (_, OSTpu) -> ignore (Stack.pop cstack)
                            | _ -> raise TB.Incomplete
                        end

                        | _ -> ()
                      ) (List.rev br#children)
                  with
                    Stack.Empty -> raise TB.Incomplete
            end;

            let open_section_list = ref [] in
            Stack.iter (fun (n, t) -> open_section_list := (n, t)::!open_section_list) cstack;
            !open_section_list, !reverse_mode

          in (* get_open_section_list *)

          let mknd part br =
            if part = [] then
              []
            else
              match br#label with
              | Label.PpSectionIf _
              | Label.PpSectionElif _
              | Label.PpSectionIfdef _
              | Label.PpSectionIfndef _
              | Label.PpSectionElse
                -> [new Ast.node ~lloc:(Ast.lloc_of_nodes part) ~children:part br#label]
              | _ -> assert false
          in
          let mkspec = Partial.mkspec in

          begin
            match !blist with
            | [br] -> begin
	        [%debug_log "[%d] selected branch: %s" lv (B.tag_to_string br#get_tag)];

                let selected_lloc = Ast.lloc_of_locs tag_loc endif_loc in

                let selected_loc = lloc_to_loc selected_lloc in

                [%debug_log "selected_loc: %s" (Loc.to_string ~show_ext:true selected_loc)];

	        (!selected_buf)#receive_all br;

                let need_eol =
                  match context.C.tag with
                  | C.Taction_stmt -> true
                  | C.Texpr        -> bbuf_top_last_EOL_exists
                  | _ -> false
                in
                [%debug_log "need_eol=%B" need_eol];
                if need_eol then
                  let _, ed = Loc.to_lexposs selected_loc in
                  (!selected_buf)#add (PB.make_qtoken EOL ed ed);
            end

            | _ -> begin
	        [%debug_log "[%d] merging selected branches..." lv];

                let open_section_flag = ref false in

                let open_construct_flag = ref false in

                let get_tag spec = Partial.tag_of_spec spec in

                let _children, length, tags =
                  List.fold_left
                    (fun (lst, len, tags) br ->
                      let br_as_list = br#get_list in
                      match br_as_list with
                      | [(tok, _)] -> begin
                          match tok with
                          | PROGRAM_UNIT(spec, nd) | SUBPROGRAM(spec, nd)
                          | INTERFACE_SPEC(spec, nd)
                          | CASE_BLOCK(spec, nd)
                          | SPEC_PART_CONSTRUCT(spec, nd)
                          | DATA_STMT_SET(spec, nd) | TYPE_SPEC(spec, nd)
                          | VARIABLE(spec, nd) | EXPR(spec, nd)
                          | DERIVED_TYPE_DEF_PART(spec, nd) ->
                              nd :: lst, (Partial.length_of_spec spec) + len, (get_tag spec) :: tags

                          | EXEC_PART_CONSTRUCT(spec, nd) ->
                              open_section_flag := true;
                              open_construct_flag := true;
                              nd :: lst, (Partial.length_of_spec spec) + len, (get_tag spec) :: tags

                          | STMT(spec, nd) ->
                              open_section_flag := true;
                              open_construct_flag := true;
                              nd :: lst, (Partial.length_of_spec spec) + len, C.Tstmts :: tags

                          | FUNCTION_HEAD(spec, nd) | SUBROUTINE_HEAD(spec, nd)
                          | PU_TAIL(spec, nd) ->
                              open_section_flag := true;
                              nd :: lst, (Partial.length_of_spec spec) + len, (get_tag spec) :: tags

                          | FUNCTION_STMT_HEAD(spec, nd) | SUBROUTINE_STMT_HEAD(spec, nd) ->
                              nd :: lst, (Partial.length_of_spec spec) + len, (get_tag spec) :: tags

                          | _ ->
                              begin %debug_block
                                [%debug_log "br#get_list:"];
                                List.iter
                                  (fun (t, _) ->
                                    [%debug_log "  %s" (Token.rawtoken_to_string t)]
                                  ) br_as_list
                              end;
                              assert false
                      end
                      | [(tok, _);(EOL, _)] -> begin
                          match tok with
                          | ACTION_STMT(spec, nd) ->
                              nd :: lst, (Partial.length_of_spec spec) + len, C.Taction_stmt :: tags
                          | _ -> assert false
                      end
                      | _ -> begin
                          begin %debug_block
                            [%debug_log "br#get_list:"];
                            List.iter
                              (fun (t, _) ->
                                [%debug_log "  %s" (Token.rawtoken_to_string t)]
                              ) br_as_list
                          end;
                          assert false
                      end
                    ) ([], 0, []) !blist

                in (* _children, length, tags *)

                let children = List.rev _children in

                [%debug_log "tag_loc: %s" (Loc.to_string ~show_ext:true tag_loc)];
                [%debug_log "endif_loc: %s" (Loc.to_string ~show_ext:true endif_loc)];

                let selected_lloc = Ast.lloc_of_locs tag_loc endif_loc in

                let selected_loc = lloc_to_loc selected_lloc in

                [%debug_log "selected_loc: %s" (Loc.to_string ~show_ext:true selected_loc)];

                let tag =
                  match tags with
                  | [] -> context.C.tag
                  | [t] -> t
                  | t :: rest ->
                      if List.for_all (fun x -> x = t) rest then
                        t
                      else
                        context.C.tag
                in

                [%debug_log "tag of branch: %s" (C.tag_to_string tag)];

                let basic_case() =
                  let tok, need_eol =
                    let node = new Ast.node ~lloc:selected_lloc ~children Label.PpBranch in
                    match tag with
                    | C.Tunknown               -> assert false
                    | C.Ttoplevel              -> PROGRAM_UNIT(mkspec ~length (), node), false
                    | C.Tprogram_unit          -> PROGRAM_UNIT(mkspec ~length (), node), false
                    | C.Tspec__exec            -> STMT(mkspec ~length (), node), false
                    | C.Tspecification_part    -> SPEC_PART_CONSTRUCT(mkspec ~length (), node), false
                    | C.Texecution_part        -> EXEC_PART_CONSTRUCT(mkspec ~length (), node), false
                    | C.Tsubprograms           -> SUBPROGRAM(mkspec ~length (), node), false
                    | C.Tinterface_spec        -> INTERFACE_SPEC(mkspec ~length (), node), false
                    | C.Tcase_block            -> CASE_BLOCK(mkspec ~length (), node), false
                    | C.Tvariable              -> VARIABLE(mkspec ~length (), node), bbuf_top_last_EOL_exists
                    | C.Texpr                  -> EXPR(mkspec ~length (), node), bbuf_top_last_EOL_exists
                    | C.Tstmts                 -> STMT(mkspec ~length (), node), false
                    | C.Tdata_stmt_sets        -> DATA_STMT_SET(mkspec ~length (), node), false
                    | C.Ttype_spec             -> TYPE_SPEC(mkspec ~length (), node), false
                    | C.Taction_stmt           -> ACTION_STMT(mkspec ~length (), node), true
                    | C.Tderived_type_def_part -> DERIVED_TYPE_DEF_PART(mkspec ~length (), node), false
                    | C.Tonlys                 -> ONLY_(mkspec ~length (), node), false
                    | C.Tfunction_stmt_head    -> FUNCTION_STMT_HEAD(mkspec ~length (), node), false
                    | C.Tsubroutine_stmt_head  -> SUBROUTINE_STMT_HEAD(mkspec ~length (), node), false

                    | C.Tassignment_stmt       -> assert false
                    | C.Ttype_declaration_stmt -> assert false
                    | C.Tfunction_stmt         -> assert false
                    | C.Ttype_bound_proc_part  -> assert false
                    | C.Tfunction_head         -> assert false
                    | C.Tsubroutine_head       -> assert false
                    | C.Tpu_tail               -> assert false
                    | C.Tin_stmt               -> assert false
                  in

                  [%debug_log "tok=%s need_eol=%B" (Token.rawtoken_to_string tok) need_eol];

                  (!selected_buf)#add (tok, selected_loc);

                  if need_eol then
                    let _, ed = Loc.to_lexposs selected_loc in
                    (!selected_buf)#add (PB.make_qtoken EOL ed ed);

                in (* basic_case() *)


                if !open_section_flag then begin

                  let open_section_list_list = ref [] in

                  let br_count = ref (-1) in

                  let reverse_mode = ref false in

                  List.iter
                    (fun br ->
                      incr br_count;
                      [%debug_log "branch [%d]\n%s" !br_count (Printer.to_string br)];

                      let open_section_list, rev_mode = get_open_section_list br in
                      reverse_mode := rev_mode;
                      open_section_list_list := open_section_list :: !open_section_list_list;

                    ) _children;


                  let crosscutting_open_sections_list =
                    let rec doit res list_list =
                      try
                        let cand, rest =
                          List.split
                            (List.map
                               (function
                                 | [] -> raise Exit
                                 | open_section::rest -> open_section, rest
                               ) list_list)
                        in
                        match cand with
                        | [] -> res
                        | (_, tag)::_ ->
                            if List.for_all (fun (_, t) -> t = tag) cand then
                              doit (cand::res) rest
                            else
                              res
                      with
                        Exit -> res
                    in
                    List.rev (doit [] !open_section_list_list)
                  in

                  begin %debug_block
                    let c = ref 0 in
                    List.iter
                      (fun crosscutting_open_sections ->
                        [%debug_log "open sections[%d]: [%s]" !c
                          (Xlist.to_string (fun (_, t) -> open_section_tag_to_string t) ";" crosscutting_open_sections)];
                        incr c
                      ) crosscutting_open_sections_list
                  end;

                  let open_section_tag_a =
                    Array.of_list
                      (List.map
                         (function
                           | [] -> assert false
                           | (_, t)::_ -> t
                         ) crosscutting_open_sections_list)
                  in

                  let ncrosscutting = List.length crosscutting_open_sections_list in

                  [%debug_log "ncrosscutting=%d" ncrosscutting];

                  let crosscutting = ncrosscutting > 0 in

                  [%debug_log "crosscutting=%B" crosscutting];

                  if crosscutting then begin

                    let nbranches = List.length children in

                    [%debug_log "nbranches=%d" nbranches];

                    let part_matrix = Array.make_matrix (ncrosscutting + 1) nbranches [] in

                    let part_count = ref 0 in

                    let br_a =
                      let f =
                        if !reverse_mode then
                          fun br -> List.rev br#children
                        else
                          fun br -> br#children
                      in
                      Array.of_list (List.map f children)
                    in

                    List.iter
                      (fun crosscutting_open_sections ->

                        let open_sections = List.map (fun (n, _) -> n) crosscutting_open_sections in

                        let br_count = ref 0 in

                        List.iter2
                          (fun br open_section ->
                            [%debug_log "branch [%d]" !br_count];
                            [%debug_log "open_section: %s" (Label.to_string open_section#label)];

                            let _former, latter =
                              let stmts = br_a.(!br_count) in

                              [%debug_log "stmts: %s"
                                (Xlist.to_string (fun x -> Label.to_string x#label) "; " stmts)];

                              let dtv_and_open_sec =
                                match stmts with
                                | [stmt0; _] -> Label.is_pp_directive stmt0#label
                                | _ -> false
                              in
                              if dtv_and_open_sec then (* branching directive and open section *)
                                [], stmts
                              else
                                let rec scan f = function
                                  | [] -> f, []
                                  | stmt::rest as l -> begin
                                      [%debug_log "%s" (Label.to_string stmt#label)];
                                      if stmt == open_section then
                                        f, l
                                      else
                                        scan (stmt::f) rest
                                  end
                                in
                                scan [] stmts

                            in (* _former, latter *)
                            let former =
                              if !reverse_mode then
                                _former
                              else
                                List.rev _former
                            in
                            [%debug_log "part=%d br=%d" !part_count !br_count];
                            [%debug_log "former(part):\n%s" (Xlist.to_string (fun n -> n#to_string) "\n" former)];
                            [%debug_log "latter:\n%s\n" (Xlist.to_string (fun n -> n#to_string) "\n" latter)];

                            part_matrix.(!part_count).(!br_count) <- mknd former br;

                            br_a.(!br_count) <- latter;

                            incr br_count;

                          ) children open_sections;

                        incr part_count;

                      ) crosscutting_open_sections_list;

                    let _ =
                      let i = ref 0 in
                      List.iter
                        (fun br ->
                          [%debug_log "branch [%d]" !i];
                          let last =
                            if !reverse_mode then
                              List.rev br_a.(!i)
                            else
                              br_a.(!i)
                          in
                          [%debug_log "last part:\n%s\n" (Xlist.to_string (fun n -> n#to_string) "\n" last)];
                          part_matrix.(ncrosscutting).(!i) <- mknd last br;
                          incr i
                        ) children
                    in

                    let former_children = List.flatten (Array.to_list part_matrix.(0)) in

                    let token_list_for_reverse_mode = ref [] in

                    [%debug_log "former children:\n%s\n"
                      (Xlist.to_string (fun n -> n#to_string) "\n" former_children)];

                    if former_children <> [] then begin
                      let fc =
                        (*if !reverse_mode then
                          List.rev former_children
                        else*)
                          former_children
                      in
                      let lloc = Ast.lloc_of_nodes fc in
                      let nd = new Ast.node ~lloc ~children:fc Label.PpBranch in
                      let tok =
                        if !open_construct_flag then
                          STMT(mkspec(), nd)
                        else
                          PROGRAM_UNIT(mkspec(), nd)
                      in
                      let qtoken = (tok, lloc#to_loc ~cache:(Some env#fname_ext_cache) ()) in
                      if !reverse_mode then
                        token_list_for_reverse_mode := qtoken :: !token_list_for_reverse_mode
                      else
                        (!selected_buf)#add qtoken
                    end;

                    for i = 1 to ncrosscutting do
                      let latter_children = List.flatten (Array.to_list part_matrix.(i)) in
                      let open_section_tag = open_section_tag_a.(i - 1) in

                      [%debug_log "[%d] latter children:\n%s\n"
                        i (Xlist.to_string (fun n -> n#to_string) "\n" latter_children)];

                      if latter_children <> [] then begin
                        let lc =
                          (*if !reverse_mode then
                            List.rev latter_children
                          else*)
                            latter_children
                        in
                        let lab =
                          match open_section_tag with
                          | OSTnone       -> assert false
                          | OSTif         -> Label.PpBranchIf
                          | OSTdo         -> Label.PpBranchDo
                          | OSTselect     -> Label.PpBranchSelect
                          | OSTforall     -> Label.PpBranchForall
                          | OSTwhere      -> Label.PpBranchWhere
                          | OSTtype       -> Label.PpBranchDerivedType
                          | OSTfunction   -> Label.PpBranchFunction
                          | OSTsubroutine -> Label.PpBranchSubroutine
                          | OSTpu         -> Label.PpBranchPu
                        in
                        let lloc = Ast.lloc_of_nodes lc in
                        let nd = new Ast.node ~lloc ~children:lc lab in
                        let tok =
                          if !reverse_mode then
                            match open_section_tag with
                            | OSTnone       -> assert false
                            | OSTif         -> END_IF_STMT(mkspec(), nd)
                            | OSTdo         -> END_DO_STMT(mkspec(), nd)
                            | OSTselect     -> END_SELECT_STMT(mkspec(), nd)
                            | OSTforall     -> END_FORALL_STMT(mkspec(), nd)
                            | OSTwhere      -> END_WHERE_STMT(mkspec(), nd)
                            | OSTtype       -> END_TYPE_STMT(mkspec(), nd)
                            | OSTfunction   -> assert false
                            | OSTsubroutine -> assert false
                            | OSTpu         -> PU_TAIL(mkspec(), nd)
                          else
                            match open_section_tag with
                            | OSTnone       -> assert false
                            | OSTif         -> IF_THEN_STMT(mkspec(), nd)
                            | OSTdo         -> DO_STMT(mkspec(), nd)
                            | OSTselect     -> SELECT_CASE_STMT(mkspec(), nd)
                            | OSTforall     -> FORALL_CONSTRUCT_STMT(mkspec(), nd)
                            | OSTwhere      -> WHERE_CONSTRUCT_STMT(mkspec(), nd)
                            | OSTtype       -> DERIVED_TYPE_STMT(mkspec(), nd)
                            | OSTfunction   -> FUNCTION_HEAD(mkspec(), nd)
                            | OSTsubroutine -> SUBROUTINE_HEAD(mkspec(), nd)
                            | OSTpu         -> assert false
                        in
                        let qtoken =
                          tok, lloc#to_loc ~cache:(Some env#fname_ext_cache) ()
                        in
                        if !reverse_mode then
                          token_list_for_reverse_mode := qtoken :: !token_list_for_reverse_mode
                        else
                          (!selected_buf)#add qtoken
                      end

                    done;
                    if !reverse_mode then
                      List.iter
                        (fun qtoken ->
                          (!selected_buf)#add qtoken
                        ) !token_list_for_reverse_mode
                  end
                  else begin (* not crosscutting *)
                    basic_case()
                  end
                end
                else begin (* not !open_section_flag *)
                  basic_case()
                end

            end
          end;

          begin %debug_block
            [%debug_log "selected buffer:"];
            !selected_buf#dump;
          end;

	  List.iter
	    (fun br ->
	      try
                br#dump;
		let loc = br#get_loc in

		[%debug_log "[%d] ignored region: %s" lv (Loc.to_string loc)];

                if lv = 0 then
		  ignored_regions :=  loc :: !ignored_regions

	      with
                TB.Empty -> ()
	    ) !ignored;

      	  !selected_buf, !ignored_regions
	end

      with
        TB.Incomplete | C.Not_active -> begin
	  context_stack#resume;

	  [%debug_log "[%d] selecting (the largest) branch..." lv];

          begin
            try
	      bbuf#iter_branch
	        (fun buf ->

	          [%debug_log "[%d] checking %s" lv (B.tag_to_string buf#get_tag)];

                  adjust_last buf;

	          match buf#get_tag with

	          | B.Tifdef(id, _) -> begin
                      [%debug_log "size=%d" buf#total_length];
                      [%debug_log "id=%s" id];
                      if id <> "_OPENMP" then
		        if (!selected_buf)#total_length < buf#total_length then begin
		          selected_buf := buf;
                        end
	          end
	          | B.Tifndef(id, _) -> begin
                      [%debug_log "size=%d" buf#total_length];
                      [%debug_log "id=%s" id];
                      if env#macrotbl#is_unconditionally_defined id then begin
                        (* ignore: like #if 0 *)
                        [%debug_log "%s is unconditionally defined" id]
                      end
                      else
		        if (!selected_buf)#total_length < buf#total_length then begin
		          selected_buf := buf
                        end
	          end
                  | B.Tif(cond, _) | B.Telif(cond, _, _) -> begin
                      let _ = cond in
                      [%debug_log "size=%d" buf#total_length];
                      [%debug_log "cond=%s" cond];
		      if (!selected_buf)#total_length < buf#total_length then begin
		        selected_buf := buf;
                      end
                  end
                  | B.Telse(_, _) -> begin
                      [%debug_log "size=%d" buf#total_length];
		      if (!selected_buf)#total_length < buf#total_length then begin
		        selected_buf := buf
                      end
                  end
	          | t ->
                      let _ = t in
                      [%debug_log "invalid branch tag: %s" (B.tag_to_string t)];
                      assert false
	        )
            with
              Exit -> ()
          end;

	  bbuf#iter_branch
	    (fun buf ->
	      if lv = 0 && buf != !selected_buf then begin
                [%debug_log "ignored buf:"];
                buf#dump;
                if buf#total_length > 0 then
	          try
		    ignored_regions := buf#get_loc :: !ignored_regions
	          with
                    TB.Empty -> ()
              end
	    );

	  [%debug_log "[%d] selected: %s" lv (B.tag_to_string !selected_buf#get_tag)];

          self#recover key;

          [%debug_log "finished"];

	  !selected_buf, !ignored_regions

        end
    (* end of method select_branches *)



  method parse ?(use_cache_incomplete=true) (_parser : TB.partial_parser) (tokenbuf : TBF.c) =
    let cache =
      if use_cache_incomplete then
        tokenbuf#ast_cache
      else
        match tokenbuf#ast_cache with
        | TB.Rincomplete -> TB.Runknown
        | r -> r
    in

    [%debug_log "LEVEL=%d" lv];
    [%debug_log "branch tag: %s" (B.tag_to_string tokenbuf#get_tag)];


    match cache with
    | TB.Rcomplete p ->
	[%debug_log "[%d] using cached value (complete)" lv];
	p

    | TB.Rincomplete ->
	[%debug_log "[%d] using cached value (incomplete)" lv];
	raise TB.Incomplete

    | TB.Runknown ->
	[%debug_log "[%d] parsing..." lv];
        (*Printf.printf "! [%d] parsing...\n%!" lv;*)

        tokenbuf#dump;

        let tokensrc = tokenbuf#get_tokensrc in

        let ppbuf =
          new buffer
            (*~context:(Some context_buf)*)
            (lv+1) partial_parser_selector (tokensrc :> Tokensource.c)
        in

        if C.is_program_unit tokenbuf#get_context then
          ppbuf#exit_context;

	let scanner() =
	  try
            let _qtoken = ppbuf#pp () in
            let qtoken =
              match Token.qtoken_to_rawtoken _qtoken with
              | PP_DEFINE__IDENT__BODY(_, body) -> begin
                  begin
                    match tokenbuf#get_tag with
                    | B.Tifndef(_, _) -> Macro.body_clear_conditional body
                    | _ -> ()
                  end;
                  _qtoken
              end

              | PP_UNDEF__IDENT _ -> _qtoken

              | _ -> begin
                  [%debug_log "[%d] calling TBF.hack_token" lv];
                  TBF.hack_token (tokensrc :> Tokensource.c) _qtoken;
              end
            in
            [%debug_log "[%d] ---------> %s" lv (Token.qtoken_to_string qtoken)];
            (*Printf.printf "! [%d] %s\n%!" lv (Token.qtoken_to_string qtoken);*)
            PB.qtoken_to_token qtoken
	  with
	  | Tokensource.Empty ->
	      if tokensrc#eop_flag then begin
                [%debug_log "raising End_of_file"];
                raise End_of_file
              end
	      else begin
		let _, ed = Loc.to_lexposs tokensrc#get_last_loc in

		begin %debug_block
		  [%debug_log "[%d] last token: %s[%s]" lv
		    (Token.rawtoken_to_string tokensrc#get_last_rawtok)
                    (Loc.to_string tokensrc#get_last_loc)];
		  [%debug_log "[%d] EOP[%s]" lv
		    (Loc.to_string (Astloc.of_lexposs ed ed))];
		end;

		let eop = PB.make_token EOP ed ed in
                (*Printf.printf "! [%d] %s\n%!" lv (Token.to_string eop);*)
		tokensrc#set_eop_flag;
                eop
	      end

	in (* scanner() *)

	env#set_partial_parsing_flag;
	try
	  let p = _parser scanner in
          ppbuf#finish;
          self#add_ignored_regions ppbuf#ignored_regions;
	  env#clear_partial_parsing_flag;
(*
  check_error p;
 *)
	  [%debug_log "[%d] result: PARSED" lv];
          (*Printf.printf "! [%d] result: PARSED\n%!" lv;*)

          Partial.set_length p tokenbuf#total_length;
	  tokenbuf#set_ast_cache (TB.Rcomplete p);
	  p

	with
	  exn ->
            let _ = exn in
            ppbuf#finish;

	    [%debug_log "[%d] result: FAILED (raised exception: %s)" lv
              (Printexc.to_string exn)];

	    (*Printf.printf "! [%d] result: FAILED (raised exception: %s)\n%!" lv
              (Printexc.to_string exn);*)

	    env#clear_partial_parsing_flag;
	    tokenbuf#set_ast_cache TB.Rincomplete;
	    raise TB.Incomplete


    method finish =
      context_stack#unregister_push_callback;
      context_stack#unregister_pop_callback;
      context_stack#unregister_activate_callback;
      context_stack#unregister_deactivate_callback


    initializer
      [%debug_log "init: LEVEL=%d" lv];

      if new_context then begin
        self#enter_context;
        context_buf#current#set_context (Context.toplevel());
        self#enter_context;
        context_buf#current#set_context (Context.program_unit());
        self#enter_context;
        context_buf#current#set_context (Context.spec__exec());
      end;

      context_stack#register_push_callback
	(fun c ->
	  [%debug_log "[%d] push_callback: %s" lv (C.to_string c)];

	  if self#in_branch then begin
            ()
          end
	  else begin
	    self#checkpoint top_key;
            self#enter_context;
	    self#set_context c
	  end
	);
      context_stack#register_pop_callback
	(fun c ->
	  [%debug_log "[%d] pop_callback: %s" lv (C.to_string c)];

          (*env#pop_latest_stmt_node_set;*)

	  if self#in_branch then begin
            ()
          end
          else begin
	    context_stack#activate_top;
	    self#checkpoint top_key;
	    self#exit_context;
	    self#set_context c
	  end
	);
      context_stack#register_activate_callback
	(fun c ->
	  [%debug_log "[%d] activate_callback: %s" lv (C.to_string c)];
	  if not self#in_branch then begin
	    self#checkpoint top_key;
	    self#clear_context;
	    self#set_context c
	  end

	);
      context_stack#register_deactivate_callback
	(fun c ->
	  [%debug_log "[%d] deactivate_callback: %s" lv (C.to_string c)];
	  if not self#in_branch then begin
	    self#checkpoint top_key;
	    self#clear_context;
	    self#set_context c
	  end
	)


  end (* of class Tokenpp.buffer *)


end (* of Tokenpp.F *)
]
