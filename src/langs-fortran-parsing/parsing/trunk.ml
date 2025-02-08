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

(* trunk.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xqueue = Diffast_misc.Xqueue
module Xprint = Diffast_misc.Xprint
module Fname = Langs_common.Fname
module Astloc = Langs_common.Astloc
module Parserlib_base = Langs_common.Parserlib_base

module Loc = Astloc
module Aux = Parser_aux
module PB  = Parserlib_base
module C   = Context
module TB  = Tokenbuffer
module PPD = Labels.PpDirective
module N   = Pinfo.Name


let sprintf = Printf.sprintf


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  module Tokens = Tokens_
  module TokenF = Token.F (Stat)
  module TBF = TB.F (Stat)
  module U = Ulexer.F (Stat)
  module A = Aux.F (Stat)

  open Tokens
  open Stat

  let lexing_pos_end = Langs_common.Position.lexing_pos_end


  let make_eof_token ulexbuf =
    let pos = lexing_pos_end ulexbuf in
    let loc = Astloc.of_lexposs pos pos in
    EOF None, loc

  let make_eol_token ulexbuf =
    let pos = lexing_pos_end ulexbuf in
    let loc = Astloc.of_lexposs pos pos in
    EOL, loc

  let make_end_fragment_token ulexbuf =
    let pos = lexing_pos_end ulexbuf in
    let loc = Astloc.of_lexposs pos pos in
    let ext = env#current_loc_layers_encoded in
    Loc.extend loc ext;
    let qt = END_FRAGMENT, loc in
    [%debug_log "%s" (Token.qtoken_to_string qt)];
    qt

  let make_end_module_token ulexbuf =
    let pos = lexing_pos_end ulexbuf in
    let loc = Astloc.of_lexposs pos pos in
    let ext = env#current_loc_layers_encoded in
    Loc.extend loc ext;
    let qt = END_MODULE "END MODULE", loc in
    [%debug_log "%s" (Token.qtoken_to_string qt)];
    qt

  let marker_qtoken = MARKER,  Loc.dummy

  let pp_marker_qtoken = PP_MARKER,  Loc.dummy

  let in_name_context_for_composite last_tok tok =
    [%debug_log "last_tok=%s tok=%s"
      (Token.rawtoken_to_string last_tok) (Token.rawtoken_to_string tok)];
    let in_name_context =
      let last_cond = TBF.get_last_cond last_tok tok in
      let paren_cond =
        env#in_paren_context &&
        (match tok with
        | KIND _ | LEN _ (*| STAT _*)
        | INTENT_SPEC _ -> false
        | DOUBLE_PRECISION _ | DOUBLE _ | DOUBLE_COMPLEX _ | CHARACTER _
        | TYPE _ | BYTE _
        (*| INTEGER _ | REAL _ | COMPLEX _ | LOGICAL _*) | KINDED_TYPE_SPEC _
        | PP_MACRO_TYPE_SPEC _ (*| ERRMSG _*) (*| SOURCE _ | MOLD _*)| ALLOC_OPT_EXPR _
          -> not env#in_allocate_context
        | _ -> true
        )
      in
      let kind_len_stat_cond =
        match tok with
        | KIND _ | LEN _ (*| STAT _*) -> not env#in_paren_context
        | _ -> false
      in
      let intent_cond =
        match tok with
        | INTENT_SPEC _ -> not env#in_intent_context
        | _ -> false
      in
      let result_cond =
        match tok with
        | RESULT _ -> not env#in_result_context
        | _ -> false
      in
      let character_cond =
        match tok with
        | KIND _ | LEN _
        | PUBLIC _ | PRIVATE _
        | PARAMETER _ | ALLOCATABLE _ | DIMENSION _ | CODIMENSION _ | INTENT _
        (*| EXTERNAL _ | PROTECTED _ | VALUE _ | VOLATILE _*) | SIMPLE_ATTR _
        | INTRINSIC _ | OPTIONAL _ | POINTER _ | SAVE _ | TARGET _
        | ASYNCHRONOUS _
          -> false
        | _ -> env#in_character_context
      in
      let edit_desc_cond =
        match tok with
        | DATA_EDIT_DESC _ | POSITION_EDIT_DESC _ -> TBF.is_head_of_stmt last_tok
        | _ -> false
      in

      let do_cond =
(*        TBF.get_do_cond tok*)
        match last_tok with
        | DO _ -> begin
            match tok with
            | WHILE _ -> false
            | _ -> true
        end
        | _ -> false
      in

      let type_spec_cond = TBF.get_type_spec_cond tok in

      let misc_cond =
        match tok with
        | OPEN _ | CLOSE _ (* requires LPAREN *)
          -> true
        | _ -> false
      in

      [%debug_log ("\n"^^
                 "env#in_name_context      :%B\n"^^
                 "env#in_io_control_context:%B\n"^^
                 "env#in_array_ctor_context:%B\n"^^
                 "last_cond                :%B\n"^^
                 "intent_cond              :%B\n"^^
                 "kind_len_stat_cond       :%B\n"^^
                 "result_cond              :%B\n"^^
                 "paren_cond               :%B\n"^^
                 "character_cond           :%B\n"^^
                 "edit_desc_cond           :%B\n"^^
                 "do_cond                  :%B\n"^^
                 "type_spec_cond           :%B\n"^^
                 "misc_cond                :%B\n"
                )

        env#in_name_context env#in_io_control_context env#in_array_ctor_context
        last_cond intent_cond kind_len_stat_cond result_cond paren_cond
        character_cond edit_desc_cond do_cond type_spec_cond misc_cond];

      let if_action_cond = TBF.get_if_action_cond last_tok tok in

      last_cond ||
      ((env#in_name_context || paren_cond) && (not if_action_cond)) ||
      env#in_io_control_context ||
      env#in_array_ctor_context ||
      kind_len_stat_cond ||
      intent_cond ||
      result_cond ||
      character_cond ||
      edit_desc_cond ||
      do_cond ||
      type_spec_cond ||
      misc_cond
    in

    let b = in_name_context in
    [%debug_log "%B" b];
    b


  exception Token_found of Token.qtoken_t


  class buffer (partial_parser_selector : C.t -> TB.partial_parser list) = object (self)

    val mutable last_rawtok = EOL
    val mutable last_loc = Loc.dummy

    val mutable prev_rawtok = EOL
    val mutable prev_loc = Loc.dummy

    val mutable last_taken = EOL
    val mutable _last_taken = EOL

    val mutable last_taken_loc = Loc.dummy
    val mutable _last_taken_loc = Loc.dummy

    val mutable last_taken_no_pp_branch = EOL
    val mutable _last_taken_no_pp_branch = EOL

    val mutable last_taken_no_pp_branch_loc = Loc.dummy
    val mutable _last_taken_no_pp_branch_loc = Loc.dummy

    val mutable prebuf : Token.qtoken_t Xqueue.c = new Xqueue.c

    val stack = Stack.create()

    initializer
      ignore self

    method prepend_queue ?(copy=true) (q : Token.qtoken_t Xqueue.c) = (* !!! *)
      prebuf#prepend_from (if copy then q#copy else q)

    method prepend tok_loc =
      [%debug_log "prepending %s" (Token.qtoken_to_string tok_loc)];
      prebuf#prepend tok_loc

    method partial_parser_selector = partial_parser_selector

    method get_last_rawtok = last_rawtok
    method set_last_rawtok tok = last_rawtok <- tok

    method get_last_loc = last_loc
    method set_last_loc loc = last_loc <- loc

    method get_prev_rawtok = prev_rawtok
    method set_prev_rawtok tok = prev_rawtok <- tok

    method get_prev_loc = prev_loc
    method set_prev_loc loc = prev_loc <- loc

    method get_last_offsets = Loc.to_offsets last_loc
    method get_prev_offsets = Loc.to_offsets prev_loc

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

    method prebuf_count_markers =
      let c = ref 0 in
      prebuf#iter
        (fun (tok, _) ->
          match tok with
          | MARKER -> incr c
          | _ -> ()
        );
      !c

    method prebuf_count_pp_markers =
      let c = ref 0 in
      prebuf#iter
        (fun (tok, _) ->
          match tok with
          | PP_MARKER -> incr c
          | _ -> ()
        );
      !c

    method prebuf_add qtoken =
      [%debug_log "adding %s" (Token.qtoken_to_string qtoken)];
      [%debug_log "prebuf (size=%d):\n%s" self#prebuf_size self#prebuf_to_string];
      prebuf#add qtoken

    method prebuf_add_queue (q : Token.qtoken_t Xqueue.c) =
      begin %debug_block
        q#iter
        (fun (tok, _) ->
          [%debug_log "adding %s" (Token.rawtoken_to_string tok)]
        );
        [%debug_log "prebuf (size=%d):\n%s" self#prebuf_size self#prebuf_to_string]
      end;
      q#transfer prebuf

    method prebuf_take =
      [%debug_log "prebuf (size=%d):\n%s" self#prebuf_size self#prebuf_to_string];
      try
        prebuf#take
      with
        Xqueue.Empty -> raise TB.Empty

    method prebuf_peek =
      try
        prebuf#peek
      with
        Xqueue.Empty -> raise TB.Empty

    method prebuf_peek_nth n =
      prebuf#peek_nth n

    method prebuf_peek_last =
      prebuf#peek_last

    method prebuf_size = prebuf#length

    method prebuf_get_last =
      try
        let tok, _ = prebuf#peek_last in
        tok
      with
        Xqueue.Empty -> raise TB.Empty


    method prebuf_to_string =
      let buf = Buffer.create 0 in
      prebuf#iter
        (fun t ->
          Buffer.add_string buf (sprintf "%s\n" (Token.qtoken_to_string t))
        );
      Buffer.contents buf

    method prebuf_filter f =
      prebuf#filter f

    method prebuf_remove_marker =
      prebuf#filter
        (fun (tok, _) ->
          match tok with
          | MARKER -> false
          | _ -> true
        )

    method prebuf_replace1 ?(pp=false) ?(nth=1) qtoken =
      [%debug_log "nth=%d pp=%B qtoken=%s" nth pp (Token.qtoken_to_string qtoken)];
      [%debug_log "before:\n%s" self#prebuf_to_string];

      let marker_count = ref 0 in
      prebuf#replace
        (fun tok_loc ->
          let tok, _ = tok_loc in
          match tok with
          | MARKER when not pp -> begin
              incr marker_count;
              if !marker_count = nth then
                qtoken
              else
                tok_loc
          end
          | PP_MARKER when pp -> begin
              incr marker_count;
              if !marker_count = nth then
                qtoken
              else
                tok_loc
          end
          | MARKER when pp -> tok_loc
          | PP_MARKER when not pp -> tok_loc

          | _ -> tok_loc
        )

    method prebuf_replace ?(pp=false) ?(nth=1) (q : Token.qtoken_t Xqueue.c) =
      [%debug_log "nth=%d pp=%B" nth pp];
      [%debug_log "before:\n%s" self#prebuf_to_string];
      let new_prebuf = new Xqueue.c in
      let marker_count = ref 0 in
       prebuf#iter
        (fun qtoken ->
          let tok, _ = qtoken in
          match tok with
          | MARKER when not pp -> begin
              incr marker_count;
              if !marker_count = nth then
                q#transfer new_prebuf
              else
                new_prebuf#add qtoken
          end
          | PP_MARKER when pp -> begin
              incr marker_count;
              if !marker_count = nth then
                q#transfer new_prebuf
              else
                new_prebuf#add qtoken
          end

          | MARKER when pp -> new_prebuf#add qtoken
          | PP_MARKER when not pp -> new_prebuf#add qtoken

          | _ -> new_prebuf#add qtoken
        );
      prebuf <- new_prebuf


  end (* of class Trunk.buffer *)



  let find_macro id =
    [%debug_log "id=%s" id];
    try
      env#find_macro id
    with
      Not_found ->
        env#lex_find_macro id

  let find_all_macros id =
    [%debug_log "id=%s" id];
    let ms =
      env#find_all_macros id
    in
    if ms = [] then
      env#lex_find_all_macros id
    else
      ms

  let hide_macro id =
    env#macrotbl#hide id;
    env#lex_macrotbl#hide id;
    fun () ->
      env#macrotbl#expose id;
      env#lex_macrotbl#expose id


  let ifdef_openmp = PPD.Ifdef "_OPENMP"


  class tokensource (tbuf : buffer) ulexbuf = object (self)
    inherit Tokensource.c

    val ulexbuf_stack : Sedlexing.lexbuf Stack.t = Stack.create()

    val mutable current_ulexbuf = ulexbuf

    val mutable finished = false


    initializer
      Stack.push ulexbuf ulexbuf_stack

    method in_included = (Stack.length ulexbuf_stack) > 1

    method enter_source (src : Source.c) =
      let ulbuf =
        let file = src#file in
        let form = U.guess_source_form file in

        env#verbose_msg
          "setting source form of \"%s\" to %s"
          file#path (Common.SourceForm.to_string form);

        src#set_source_form form;
        src#get_ulexbuf
      in
      current_ulexbuf <- ulbuf;
      Stack.push ulbuf ulexbuf_stack;
      ulbuf

    method exit_source =
      [%debug_log "called"];
      let _ = Stack.pop ulexbuf_stack in
      current_ulexbuf <- Stack.top ulexbuf_stack;
      env#pop_loc;
      env#exit_source


    method private conv_token qtoken =
      [%debug_log "converting %s..." (Token.qtoken_to_string qtoken)];
      let tok, loc = qtoken in
      let st, ed = Loc.to_lexposs loc in
      let ln = st.Lexing.pos_lnum in

      let last_loc = tbuf#get_last_taken_loc in

      let adjust =
        if st.Lexing.pos_fname = last_loc.Loc.filename then
          ln - last_loc.Loc.end_line - 1
        else
          0
      in
      [%debug_log "adjust=%d" adjust];

      let incomplete =
        match tbuf#get_last_taken with
        | LPAREN
          -> true
        | _ -> false
      in

      if
        env#current_source#omp_cc_lines#is_head ~mask:true ~adjust incomplete ln
      then begin
        [%debug_log "OMP Conditional Compilation BEGIN"];
        let bol = st.Lexing.pos_bol in
        let fn = st.Lexing.pos_fname in
        let pos0 = Loc.mklexpos ~fname:fn ~lnum:ln ~bol bol in
        let pos1 = Loc.mklexpos ~fname:fn ~lnum:ln ~bol (bol+1) in
        tbuf#prebuf_add (PB.make_qtoken (PP_BRANCH ifdef_openmp) pos0 pos1)
      end;

      [%debug_log "last_loc: %s" (Loc.to_string last_loc)];
      [%debug_log "loc: %s" (Loc.to_string loc)];

      let last_fname = Fname.strip last_loc.Loc.filename in
      let cur_fname = Fname.strip loc.Loc.filename in

      if last_fname <> cur_fname && last_fname <> "" && cur_fname <> "" then begin
        ()
      end
      else if env#current_source#omp_cc_lines#is_normal_head ~mask:true ~adjust ln then begin
        [%debug_log "OMP Conditional Compilation END"];
        let _, ed0 = Loc.to_lexposs last_loc in
        let qtoken =
          PB.make_qtoken (PP_BRANCH (PPD.Endif(ifdef_openmp, env#lex_paren_level))) ed0 ed0
        in
        tbuf#prebuf_add qtoken
      end;

      begin
        match tok with
        | SLASH_SLASH -> begin
            if env#in_format_context then begin
              tbuf#prebuf_add (PB.make_qtoken SLASH st st);
              tbuf#prebuf_add (PB.make_qtoken SLASH ed ed)
            end
            else
              tbuf#prebuf_add qtoken
        end
        | SLASH_RPAREN -> begin
            [%debug_log "in_format_context:%B\nin_array_ctor_context:%B"
              env#in_format_context env#in_array_ctor_context];

            if env#in_format_context || not env#in_array_ctor_context then begin
              tbuf#prebuf_add (PB.make_qtoken SLASH st st);
              tbuf#prebuf_add (PB.make_qtoken RPAREN ed ed)
            end
            else
              tbuf#prebuf_add qtoken
        end
        | DEFINED_OP s -> begin
            [%debug_log "decomposing \"%s\"" s];
            let len = (String.length s) - 2 in
            let s' = String.sub s 1 len in
            let bol = st.Lexing.pos_bol in
            let fn = st.Lexing.pos_fname in
            let pos0 = Loc.mklexpos ~fname:fn ~lnum:ln ~bol (st.Lexing.pos_cnum+1) in
            let pos1 = Loc.mklexpos ~fname:fn ~lnum:ln ~bol (st.Lexing.pos_cnum+len) in
            tbuf#prebuf_add (PB.make_qtoken DOT st st);
            tbuf#prebuf_add (PB.make_qtoken (IDENTIFIER s') pos0 pos1);
            tbuf#prebuf_add (PB.make_qtoken DOT ed ed);
        end
        | REAL_LITERAL s -> begin
            if try s.[0] = '.' with Invalid_argument _ -> false then begin
              let sl = String.lowercase_ascii s in
              if (String.contains sl 'e') || (String.contains sl 'd') then
                tbuf#prebuf_add qtoken
              else begin
                [%debug_log "decomposing \"%s\"" s];
                let len = (String.length s) - 1 in
                let s' = String.sub s 1 len in
                let bol = st.Lexing.pos_bol in
                let fn = st.Lexing.pos_fname in
                let pos0 = Loc.mklexpos ~fname:fn ~lnum:ln ~bol (st.Lexing.pos_cnum+1) in
                let pos1 = Loc.mklexpos ~fname:fn ~lnum:ln ~bol (st.Lexing.pos_cnum+len) in
                tbuf#prebuf_add (PB.make_qtoken DOT st st);
                tbuf#prebuf_add (PB.make_qtoken (INT_LITERAL s') pos0 pos1);
              end
            end
            else
              tbuf#prebuf_add qtoken
        end
        | COMPOSITE_IDENTIFIER(force_decomp, str, ol) -> begin
            if force_decomp then begin
              List.iter (fun o -> tbuf#prebuf_add (Obj.obj o)) ol
            end
            else begin
              let last_tok_ = tbuf#get_last_taken_no_pp_branch in
              let last_tok = ref last_tok_ in

              [%debug_log "last_tok_=%s" (Token.rawtoken_to_string last_tok_)];

              let get_qtoken_queue() =
                let q = new Xqueue.c in
                let cur_pos = ref st in
                let add t =
                  let e = Loc.incr_n_lexpos (Token.rawtoken_size t) !cur_pos in
                  let next = Loc.incr_lexpos e in
                  q#add (PB.make_qtoken t !cur_pos e);
                  cur_pos := next;
                  last_tok := t
                in
                begin
                  List.iter
                    (fun o ->
                      let t = Obj.obj o in
                      [%debug_log "t=%s" (Token.rawtoken_to_string t)];
                      add t
                    ) ol
                end;
                q
              in
              [%debug_log "!last_tok (no pp_branch): %s" (Token.rawtoken_to_string !last_tok)];

              let is_head_of_stmt = TBF.is_head_of_stmt !last_tok in
              let orig_qtoken = PB.make_qtoken (IDENTIFIER str) st ed in

              if is_head_of_stmt then begin
                let buf = new TBF.base in
                tbuf#prebuf_add marker_qtoken;
                let nmarkers = tbuf#prebuf_count_markers in
                self#peek_stmt nmarkers buf orig_qtoken;
                buf#add (EOP, Loc.dummy);

                [%debug_log "peeked stmt:"];
                buf#dump;

                [%debug_log "checkpointing..."];
                env#checkpoint C.tempkey;

                let need_recovery = ref true in

                begin
                  match tbuf#partial_parser_selector (C.assignment_stmt()) with
                  | [_parser] -> begin
                      [%debug_log "parsing with assignment_stmt parser"];
                      try
                        env#reset_stat;
                        let _ = buf#parse_by ~cache:false _parser in (* successfully parsed *)
                        tbuf#prebuf_replace1 ~nth:nmarkers orig_qtoken;
                      with
                      | TB.Incomplete -> begin (* failed to parse *)

                          match tbuf#partial_parser_selector (C.type_declaration_stmt()) with
                          | [_parser] -> begin
                              [%debug_log "parsing with type_declaration_stmt parser"];
                              let macro_qtoken =
                                PB.make_qtoken (PP_MACRO_ID(Macro.K_TYPE_SPEC, str)) st ed
                              in
                              buf#replace_first macro_qtoken;
                              try
                                env#reset_stat;
                                let _ =
                                  buf#parse_by ~cache:false _parser
                                in (* successfully parsed *)
                                tbuf#prebuf_replace1 ~nth:nmarkers macro_qtoken;
                              with
                              | TB.Incomplete -> begin
                                  [%debug_log "parsing with function_stmt parser"];
                                  match tbuf#partial_parser_selector (C.function_stmt()) with
                                  | [_parser] -> begin
                                      try
                                        env#reset_stat;
                                        let _ =
                                          buf#parse_by _parser
                                        in (* successfully parsed *)

                                        env#recover ~remove:true C.tempkey;

                                        let need_end_fragment = not env#fragment_impossible in

                                        if need_end_fragment then begin
                                          (* END_FRAGMENT should be added *)
                                          let q0 = new Xqueue.c in
                                          [%debug_log "adding end_fragment token..."];
                                          let end_fragment_token = make_end_fragment_token current_ulexbuf in
                                          (*Printf.printf "! 668 %s\n%!" (Token.qtoken_to_string end_fragment_token);*)
                                          q0#add end_fragment_token;
                                          q0#add macro_qtoken;
                                          tbuf#prebuf_replace ~nth:nmarkers q0
                                        end
                                        else
                                          tbuf#prebuf_replace1 ~nth:nmarkers macro_qtoken;

                                        need_recovery := false

                                      with
                                      | TB.Incomplete -> begin
                                          let q = get_qtoken_queue() in
                                          tbuf#prebuf_replace ~nth:nmarkers q
                                      end
                                      | e ->
                                          let _ = e in
                                          [%fatal_log "exception raised: %s"
                                            (Printexc.to_string e)]
                                  end
                                  | _ -> assert false
                              end
                              | e ->
                                  let _ = e in
                                  [%fatal_log "exception raised: %s" (Printexc.to_string e)]
                          end
                          | _ -> assert false

                      end
                      | e ->
                          let _ = e in
                          [%fatal_log "exception raised: %s" (Printexc.to_string e)]
                  end
                  | _ -> assert false
                end;
                if !need_recovery then
                  env#recover ~remove:true C.tempkey
              end
              else begin (* not is_head_of_stmt *)
(*
  let q = get_token_queue() in
  tbuf#prebuf_add_queue q
 *)
                tbuf#prebuf_add orig_qtoken
              end

            end
        end (* COMPOSITE_IDENTIFIER *)

        | PP_MACRO_ID(_, id) -> begin
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

        (*| RECURSIVE _ | PURE _ | ELEMENTAL _ | IMPURE _*)
        | PREFIX_SPEC _
        | PROGRAM _ | FUNCTION _ | SUBROUTINE _ | BLOCK _ | BLOCK_DATA _
        | MODULE _ | SUBMODULE _
        | FUNCTION_HEAD _ | SUBROUTINE_HEAD _
          -> begin
            self#check_BOPU;
            tbuf#prebuf_add qtoken
          end

        | PP_BRANCH (PPD.If _|PPD.Ifdef _|PPD.Ifndef _) -> begin
            self#check_BOPU_pp_branch qtoken
        end

        (*| INTEGER _ | REAL _ | COMPLEX _ | LOGICAL _*) | KINDED_TYPE_SPEC _
        | CHARACTER _ | DOUBLE _ | DOUBLE_PRECISION _ | DOUBLE_COMPLEX _ | TYPE _
        | PP_IDENTIFIER _
          -> begin
            [%debug_log "checking BOPU line: %s" (Token.rawtoken_to_string tok)];
            self#check_BOPU_line qtoken
          end

        | PP_INCLUDE__FILE _ -> begin
            [%debug_log "in_paren_context=%B" env#in_paren_context];
            if env#in_paren_context then begin
              [%debug_log "ignoring #include in parentheses context"];
              Common.parse_warning_loc loc "ignoring #include in parentheses"
            end
            else
              tbuf#prebuf_add qtoken
        end

        | _ -> tbuf#prebuf_add qtoken
      end
    (* end of method conv_token *)


    method private check_BOPU =
      let last_tok = tbuf#get_last_taken_no_pp_branch in
      let is_head_of_stmt = TBF.is_head_of_stmt last_tok in
      [%debug_log "is_head_of_stmt: %B" is_head_of_stmt];
      if is_head_of_stmt then begin
        if env#fragment_impossible then begin
          ()
        end
        else begin
          [%debug_log "adding end_fragment token..."];
          let end_fragment_token = make_end_fragment_token current_ulexbuf in
          (*Printf.printf "! 804 %s\n%!" (Token.qtoken_to_string end_fragment_token);*)
          tbuf#prebuf_add end_fragment_token
        end
      end



    method private check_BOPU_line token =
      [%debug_log "%s" (Token.qtoken_to_string token)];

      let last_tok = tbuf#get_last_taken_no_pp_branch in

      let is_head_of_stmt = TBF.is_head_of_stmt last_tok in
      [%debug_log "is_head_of_stmt: %B" is_head_of_stmt];
      if is_head_of_stmt then begin

        if env#fragment_impossible then
          tbuf#prebuf_add token

        else begin
          let buf = new TBF.base in

          let end_fragment_token = make_end_fragment_token current_ulexbuf in

          tbuf#prebuf_add marker_qtoken;

          let nmarkers = tbuf#prebuf_count_markers in

          [%debug_log "%d markers found" nmarkers];

          self#peek_stmt nmarkers buf token;

          [%debug_log "peeked:"];
          buf#dump;

          let contains_subprogram_keyword =
            try
              buf#iter
                (fun (tok, _) ->
                  match tok with
                  | FUNCTION _ | SUBROUTINE _ | PREFIX_SPEC _
                  | FUNCTION_HEAD _ | SUBROUTINE_HEAD _
                  (*| RECURSIVE _ | PURE _ | ELEMENTAL _ | IMPURE _*) ->
                      raise Exit
                  | _ -> ()
                );
              false
            with
              Exit -> true
          in
          [%debug_log "contains_subprogram_keyword: %B" contains_subprogram_keyword];

          if contains_subprogram_keyword then begin

            let q = new Xqueue.c in
            [%debug_log "adding end_fragment token..."];
            (*Printf.printf "! 860 %s\n%!" (Token.qtoken_to_string end_fragment_token);*)
            q#add end_fragment_token;
            q#add token;

            tbuf#prebuf_replace ~nth:nmarkers q;
          end
          else
            tbuf#prebuf_replace1 ~nth:nmarkers token
        end

      end
      else
        tbuf#prebuf_add token


    method private check_BOPU_pp_branch token =
      [%debug_log "%s" (Token.qtoken_to_string token)];

      let last_tok =
        match Token.qtoken_to_rawtoken token with
        | PP_BRANCH _ -> tbuf#_get_last_taken_no_pp_branch
        | _ -> assert false
      in
      let is_head_of_stmt = TBF.is_head_of_stmt last_tok in
      [%debug_log "is_head_of_stmt: %B" is_head_of_stmt];
      if is_head_of_stmt then begin

        if env#fragment_impossible then
          tbuf#prebuf_add token

        else begin

          let buf = new TBF.base in

          let end_fragment_token = make_end_fragment_token current_ulexbuf in

          tbuf#prebuf_add pp_marker_qtoken;

          let nmarkers = tbuf#prebuf_count_pp_markers in

          [%debug_log "%d pp-markers found" nmarkers];

          let blv = self#peek_up_to_non_pp nmarkers buf token in
          let _ = blv in
          [%debug_log "branch level: %d" blv];
          (*Printf.printf "[%d] %s\n%!" blv (Token.qtoken_to_string token);*)

          let contains_subprogram_keyword =
            try
              buf#iter
                (fun (tok, _) ->
                  match tok with
                  | FUNCTION _ | SUBROUTINE _ | MODULE _ | SUBMODULE _ | BLOCK_DATA _ | PROGRAM _
                  | PREFIX_SPEC _
                  | FUNCTION_HEAD _ | SUBROUTINE_HEAD _
                      (*| RECURSIVE _ | PURE _ | ELEMENTAL _ | IMPURE _*)
                    -> raise Exit

                  | _ -> ()
                );
              false
            with
              Exit -> true
          in
          [%debug_log "contains_subprogram_keyword: %B" contains_subprogram_keyword];

          if contains_subprogram_keyword (*&& blv = 0*) then begin
            let q = new Xqueue.c in
            [%debug_log "adding end_fragment token..."];
            (*Printf.printf "! 929 %s \n%!" (Token.qtoken_to_string end_fragment_token);*)
            q#add end_fragment_token;
            q#add token;
            tbuf#prebuf_replace ~pp:true ~nth:nmarkers q;
          end
          else
            tbuf#prebuf_replace1 ~pp:true ~nth:nmarkers token
        end

      end
      else
        tbuf#prebuf_add token


    method private expand_line ?(gen_regexp=false) (*base_loc*)_ st ed line =
      [%debug_log "gen_regexp=%B, line=^%s$" gen_regexp line];
      let ulexbuf = U.from_string line in
      Sedlexing.set_filename ulexbuf U.special_fname;
      let scanner () = U._token ulexbuf in
      let buf = new TBF.base in

      let middle_of_free_form_src =
        let last_loc = tbuf#get_last_taken_loc in
        let last_path = Fname.strip last_loc.Loc.filename in
        let last_form = env#get_source_form last_path in
        last_form = Common.SourceForm.Free && env#current_source#is_free_source_form
      in
      [%debug_log "middle_of_free_form_src=%B" middle_of_free_form_src];
      if not middle_of_free_form_src then begin
        try
          buf#add (Obj.obj env#take_pending_EOL_obj)
        with
          Not_found -> ()
      end;
      begin
        try
          while true do
            try
              let tok, _ = scanner() in
              [%debug_log "tok=%s" (Token.rawtoken_to_string tok)];
              match tok with
              | EOF _ -> raise End_of_file

              | PP_MACRO_ID(_, id) when not gen_regexp -> begin
                  try
                    match find_macro id with
                    | Macro.Object line0 ->
                        [%debug_log "line0: %s" (Macro.line_to_string line0)];
                        let buf0 =
                          self#expand_line ~gen_regexp line0.Macro.ln_loc st ed line0.Macro.ln_raw
                        in
                        buf#receive_all buf0
                    | _ -> assert false
                  with
                    Not_found -> assert false
              end
              | PP_MACRO_ID(_, id) when gen_regexp -> begin
                  let ss =
                    List.map
                      (function
                        | Macro.Object ln0 ->
                            [%debug_log "ln0: %s" (Macro.line_to_string ln0)];
                            let b0 =
                              self#expand_line ~gen_regexp ln0.Macro.ln_loc st ed ln0.Macro.ln_raw
                            in
                            let s =
                              String.concat ""
                                (List.map
                                   (fun x ->
                                     Token.rawtoken_to_rep
                                       (Token.qtoken_to_rawtoken x)
                                   ) b0#get_list)
                            in
                            [%debug_log "s=^%s$" s];
                            s
                        | _ -> ""
                      ) (find_all_macros id)
                  in
                  let ss = List.sort_uniq Stdlib.compare ss in
                  let pat = "\\("^(String.concat "\\|" ss)^"\\)" in
                  [%debug_log "pat=%s" pat];
                  buf#add (PB.make_qtoken (IDENTIFIER pat) Loc.dummy_lexpos Loc.dummy_lexpos)
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
                      | x ->
                          Xprint.warning
                            "not a function-like macro %s --> %s" id (Macro.body_to_string x);
                          assert false
                    with
                      Not_found -> assert false
                  in
                  let buf0 = self#expand_line ~gen_regexp base_loc0 st ed line0 in
                  buf#receive_all buf0
              end
              | _ -> buf#add (PB.make_qtoken tok st ed)
            with
            | End_of_file -> raise Exit
          done
        with
          Exit -> ()
      end;
      buf


    method private handle_macro_line st ed id args line raw =
      let args_str =
        let s = Xlist.to_string (fun x -> x) "," args in
        if s = "" then "" else String.concat "" ["("; s; ")"]
      in

      [%debug_log "id:%s args:%s line:%s [%s]" id args_str raw (Macro.stat_to_string line.Macro.ln_stat)];

      let ida = id^args_str in

      match line.Macro.ln_stat with
      | Macro.Resolved obj -> begin
          [%debug_log "macro stat: RESOLVED"];
          let tok = Obj.obj obj in
          let t = PB.make_qtoken tok st ed in
          match tok with
          | PP_MACRO_NAME _ -> tbuf#prebuf_add t
          | PP_MACRO_EXPR _ -> tbuf#prebuf_add t
          | PP_MACRO_TYPE_SPEC _ -> self#check_BOPU_line t
          | _ -> tbuf#prebuf_add t
      end
      | Macro.Unresolved -> begin
          [%debug_log "macro stat: UNRESOLVED"];
          let buf = self#expand_line line.Macro.ln_loc st ed raw in
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
                let last_tok = tbuf#get_last_taken_no_pp_branch in
                [%debug_log "empty definition: last_tok=%s" (Token.rawtoken_to_string last_tok)];
                let is_head_of_stmt = TBF.is_head_of_stmt last_tok in
                [%debug_log "is_head_of_stmt: %B" is_head_of_stmt];
                if is_head_of_stmt then begin

                  tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_STMT ida) st ed) (* may be discarded later if the next token is not EOL *)

                end
            end
            | [(IDENTIFIER s, _)]   -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_NAME(ida, s)) st ed)
            | [(CHAR_LITERAL _, _)] -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_CONST(*_CHAR*) ida) st ed)
            | [(INT_LITERAL _, _)]  -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_CONST(*_INT*) ida) st ed)

            | [(REAL_LITERAL _, _)]
            | [(BOZ_LITERAL _, _)]
            | [(LOGICAL_LITERAL _, _)]
            | [(HOLLERITH _, _)]
            | [(INT_LITERAL _, _);(DOT, _)]
            | [(DOT, _);(INT_LITERAL _, _)]
              -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_CONST ida) st ed)

            | (DATA_EDIT_DESC _, _)::_
            | (POSITION_EDIT_DESC _, _)::_
                -> tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_ID(Macro.K_GENERAL, ida)) st ed)

            | (IDENTIFIER id', _)::_ when id' = id -> (* e.g. macro for swapping arguments *)
                buf#iter
                  (fun (tok, _) ->
                    tbuf#prebuf_add (PB.make_qtoken tok st ed)
                  )

            | xs ->
                buf#add (PB.make_qtoken EOP Loc.dummy_lexpos Loc.dummy_lexpos);

                (*let rec is_concat = function
                  | x :: (PP_CONCAT,_) :: rest -> is_concat rest
                  | [x] -> true
                  | _ -> false
                in*)
                let is_concat =
                  List.for_all
                    (function
                      | (IDENTIFIER _, _)
                      | (PP_UNDERSCORE _, _)
                      | (PP_IDENTIFIER _, _)
                      | (INT_LITERAL _, _)
                      | (PP_CONCAT, _) -> true
                      | _ -> false
                    )
                in
                let consists_only_of_id =
                  let id_flag = ref false in
                  let underscore_flag = ref false in
                  let rec doit = function
                    | [] -> true
                    | x::rest -> begin
                        match x with
                        | (IDENTIFIER _, _) -> id_flag := true; doit rest
                        | (PP_UNDERSCORE _, _) -> underscore_flag := true; doit rest
                        | (PP_IDENTIFIER _, _) | (INT_LITERAL _, _) -> doit rest
                        | _ -> false
                    end
                  in
                  (doit xs) && (!id_flag || !underscore_flag)
                in
                [%debug_log "consists_only_of_id --> %B" consists_only_of_id];

                if consists_only_of_id then begin
                  let b = self#expand_line ~gen_regexp:true line.Macro.ln_loc st ed raw in
                  let xs = b#get_list in
                  let expanded =
                    String.concat ""
                      (List.map
                         (fun x -> Token.rawtoken_to_rep (Token.qtoken_to_rawtoken x)) xs)
                  in
                  [%debug_log "expanded=%s" expanded];
                  tbuf#prebuf_add (PB.make_qtoken (PP_MACRO_NAME(ida, expanded)) st ed)
                end
                else begin
                  let contexts =
                    if is_concat xs then
                      [ C.variable(),  PP_MACRO_NAME(ida, ""), (fun t -> tbuf#prebuf_add t) ]
                    else
                      [ C.variable(),  PP_MACRO_VARIABLE ida,  (fun t -> tbuf#prebuf_add t);
                        C.expr(),      PP_MACRO_EXPR ida,      (fun t -> tbuf#prebuf_add t);
                        C.type_spec(), PP_MACRO_TYPE_SPEC ida, (fun t -> self#check_BOPU_line t);
                      ]
                  in
                  env#checkpoint C.tempkey;

                  let last_tok = tbuf#get_last_taken_no_pp_branch in
                  [%debug_log "last_tok=%s" (Token.rawtoken_to_string last_tok)];

                  let is_head_of_stmt = TBF.is_head_of_stmt last_tok in
                  [%debug_log "is_head_of_stmt: %B" is_head_of_stmt];

                  try
                    List.iter
                      (fun (context, tok, handler) ->
                        [%debug_log "trying to parse with context:%s..." (C.to_string context)];

                        match tbuf#partial_parser_selector context with
                        | _parser::_ -> begin
                            try
                              if is_head_of_stmt then
                                env#reset_stat
                              else
                                env#recover C.tempkey;

                              let head, _ = buf#peek in
                              if head = LPAREN then begin
                                [%debug_log "starts with LPAREN"];
                                raise TB.Incomplete
                              end;

                              let _ = buf#parse_by ~cache:false _parser in
                              handler (PB.make_qtoken tok st ed);
                              Macro.resolve_line line tok;

                              env#recover ~remove:true C.tempkey;

                              raise Exit
                            with
                            | TB.Incomplete -> ()
                        end
                        | _ -> assert false
                      ) contexts;

                    env#recover ~remove:true C.tempkey;

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

                    let last_tok = tbuf#get_last_taken_no_pp_branch in

                    let is_head_of_stmt = TBF.is_head_of_stmt last_tok in

                    if not is_head_of_stmt || env#fragment_impossible then begin
                      add_to_tbuf()
                    end
                    else begin
                      let count = ref 0 in
                      try
                        buf#iter
                          (fun (tok, _) ->
                            if !count = 0 then begin
                              match tok with
                                (*| INTEGER _ | REAL _ | COMPLEX _ | LOGICAL _*) | KINDED_TYPE_SPEC _
                              | CHARACTER _ | DOUBLE_PRECISION _ | DOUBLE_COMPLEX _ | TYPE _ -> ()

                              | _ -> raise Not_found
                            end;

                            begin
                              match tok with
                              | FUNCTION _ | SUBROUTINE _ | PREFIX_SPEC _
                              | FUNCTION_HEAD _ | SUBROUTINE_HEAD _
                                  (*| RECURSIVE _ | PURE _ | ELEMENTAL _ | IMPURE _*) ->
                                    raise Exit

                              | EOL | SEMICOLON -> raise Not_found

                              | _ -> ()
                            end;
                            incr count
                          );
                        tbuf#prebuf_add marker_qtoken;
                        add_to_tbuf();
                        self#handle_macro_line_sub tbuf#prebuf_count_markers

                      with
                      | Exit ->
                          [%debug_log "adding end_fragment token..."];
                          let end_fragment_token = make_end_fragment_token current_ulexbuf in
                          (*Printf.printf "! 1216 %s\n%!" (Token.qtoken_to_string end_fragment_token);*)
                          tbuf#prebuf_add end_fragment_token;
                          add_to_tbuf()
                      | Not_found -> add_to_tbuf()
                    end

                  with
                    Exit -> ()
                end
          end
      end


    method private handle_macro_line_sub nmarkers =
      let n = ref 1 in
      let eos_found = ref false in
      try
        while true do
          let t = self#peek_nth !n in
          let tok, _ = t in
          [%debug_log "peeking %s token: %s" (Common.num_to_ordinal !n) (Token.qtoken_to_string t)];
          begin
            match tok with
            | EOL | SEMICOLON ->
                if !eos_found then
                  raise Not_found
                else
                  eos_found := true;
                incr n

            | FUNCTION _ | SUBROUTINE _ | PREFIX_SPEC _
            | FUNCTION_HEAD _ | SUBROUTINE_HEAD _
            (*| RECURSIVE _ | PURE _ | ELEMENTAL _ | IMPURE _*) ->
                raise Exit

            | _ -> incr n
          end
        done
      with
      | End_of_file -> begin
          [%debug_log "exception raised at %d" (Sedlexing.lexeme_start current_ulexbuf)];
          if self#in_included then begin
            self#exit_source;
            self#handle_macro_line_sub nmarkers
          end
      end
      | Exit -> begin
          [%debug_log "adding end_fragment token..."];
          let end_fragment_token = make_end_fragment_token current_ulexbuf in
          (*Printf.printf "! 1264 %s\n%!" (Token.qtoken_to_string end_fragment_token);*)
          tbuf#prebuf_replace1 ~nth:nmarkers end_fragment_token
      end
      | Not_found -> tbuf#prebuf_remove_marker
    (* end of method handle_macro_line_sub *)


    method private peek_stmt ?(nth=1) ?(count=0) nmarkers buf orig_token =
      let n = ref nth in
      let marker_count = ref count in
      let marker_found = ref false in
      try
        while true do
          let qtoken = self#peek_nth !n in
          let tok, _ = qtoken in
          [%debug_log "peeking %s token: %s"
            (Common.num_to_ordinal !n) (Token.qtoken_to_string qtoken)];
          begin
            match tok with
            | EOF _ | EOL | SEMICOLON ->
                if !marker_found then begin
                  buf#add (EOL, Loc.dummy);
                  raise Exit
                end
                else begin
                  incr n
                end

            | MARKER -> begin
                incr marker_count;
                if not !marker_found then begin
                  if !marker_count = nmarkers then begin
                    [%debug_log "marker found"];
                    buf#add orig_token;
                    marker_found := true
                  end
                end;
                incr n
            end

            (*| PP_IF__COND _ | PP_ELIF__COND _ | PP_IFDEF__IDENT _ | PP_IFNDEF__IDENT _*)
            (*| PP_ELSE | PP_ENDIF*)
            | PP_BRANCH _
            | PP_DEFINE__IDENT__BODY _ | PP_UNDEF__IDENT _
            | PP_INCLUDE__FILE _
            | PP_ISSUE__MESG _ (*| PP_ERROR__MESG _ | PP_WARNING__MESG _*)
            | PP_UNKNOWN__REST _
            | INCLUDE__FILE _ | OPTIONS__OPTS _
            | SPEC_PART_CONSTRUCT _ | EXEC_PART_CONSTRUCT _ | STMT _
                -> incr n

            | _ ->
                if !marker_found then
                  buf#add qtoken;
                incr n
          end
        done
      with
      | End_of_file -> begin
          [%debug_log "exception raised at %d" (Sedlexing.lexeme_start current_ulexbuf)];
          if self#in_included then begin
            self#exit_source;
            self#peek_stmt ~nth:(!n) ~count:(!marker_count) nmarkers buf orig_token
          end
      end
      | Exit -> ()
    (* end of method peek_stmt *)


    method private peek_up_to_non_pp ?(nth=1) ?(lv=0) ?(count=0) nmarkers buf orig_token =
      let n = ref nth in
      let marker_count = ref count in
      let marker_found = ref false in
      let branch_level = ref lv in
      [%debug_log "branch level: %d" !branch_level];
      try
        while true do
          let qtoken = self#peek_nth !n in
          let tok, _ = qtoken in
          [%debug_log "peeking %s token: %s"
            (Common.num_to_ordinal !n) (Token.qtoken_to_string qtoken)];
          begin
            match tok with
            | EOF _ | EOL | SEMICOLON -> begin
                if !marker_found then begin
                  raise Exit
                end
                else begin
                  incr n
                end
            end

            | PP_MARKER -> begin
                incr marker_count;
                [%debug_log "branch level: %d -> %d" !branch_level (!branch_level+1)];
                incr branch_level;
                if not !marker_found then begin
                  if !marker_count = nmarkers then begin
                    buf#add orig_token;
                    marker_found := true
                  end
                end;
                incr n
            end

            | PP_BRANCH b -> begin
                if !marker_found then begin
                  match b with
                  | PPD.If _ | PPD.Ifdef _ | PPD.Ifndef _ -> begin
                      [%debug_log "branch level: %d -> %d" !branch_level (!branch_level+1)];
                      incr branch_level;
                  end
                  | PPD.Endif _ -> begin
                      [%debug_log "branch level: %d -> %d" !branch_level (!branch_level-1)];
                      decr branch_level;
                      if !branch_level = 0 then
                        raise Exit
                  end
                  | _ -> ()
                end;
                incr n
            end

            | PP_DEFINE__IDENT__BODY _ | PP_UNDEF__IDENT _
            | PP_INCLUDE__FILE _
            | PP_ISSUE__MESG _ (*| PP_ERROR__MESG _ | PP_WARNING__MESG _*)
            | PP_UNKNOWN__REST _
            | INCLUDE__FILE _ | OPTIONS__OPTS _ -> incr n

            | _ -> begin
                buf#add qtoken;
                incr n
            end
          end
        done;
        0
      with
      | End_of_file -> begin
          [%debug_log "Sedlexing exception raised at %d" (Sedlexing.lexeme_start current_ulexbuf)];
          if self#in_included then begin
            self#exit_source;
            self#peek_up_to_non_pp
              ~nth:(!n) ~lv:(!branch_level) ~count:(!marker_count)
              nmarkers buf orig_token
          end
          else
            !branch_level
      end
      | Exit -> !branch_level
    (* end of method peek_up_to_non_pp *)

    method private record_qtoken qtoken =
      [%debug_log "%s" (Token.qtoken_to_string qtoken)];
      let tok, loc = qtoken in
      tbuf#set_last_taken tok;
      tbuf#set_last_taken_loc loc;
      begin
        match tok with
(*
        | PP_IF__COND _ | PP_ELIF__COND _ | PP_IFDEF__IDENT _ | PP_IFNDEF__IDENT _
        | PP_ELSE | PP_ENDIF
*)
        | PP_BRANCH _ -> ()
(*
        | PP_INCLUDE__FILE _ | PP_DEFINE__IDENT__BODY _ | PP_UNDEF__IDENT _
        | PP_ERROR__MESG _ | PP_WARNING__MESG _ | PP_UNKNOWN__REST _ -> ()
*)
        | _ ->
            tbuf#set_last_taken_no_pp_branch tok;
            tbuf#set_last_taken_no_pp_branch_loc loc
      end

    method private take_from_lexer ?(pending_EOL=None) ?(tempq=None) () =
      ignore tempq;
      let pending_EOL_ref = ref pending_EOL in
      let cur_src = env#current_source in
      try
        [%debug_log "taking from lexer..."];
        let qtoken = U.token ~pending_EOL:(!pending_EOL_ref) current_ulexbuf in
        let tok, loc = qtoken in
        let _ = loc in
        [%debug_log "lexer --> %s[%s]"
          (Token.rawtoken_to_string tok) (Loc.to_string ~show_ext:true loc)];

        match tok with
        | EOF o_opt -> begin
            begin
              match o_opt with
              | None -> pending_EOL_ref := None
              | Some o ->
                  let eol = Obj.obj o in
                  [%debug_log "pending_EOL: %s" (Token.qtoken_to_string eol)];
                  pending_EOL_ref := Some eol
            end;
            raise End_of_file
        end
        | _ -> begin
          self#record_qtoken qtoken;
          self#conv_token qtoken
        end
      with
      | End_of_file -> begin
          begin %debug_block
            let pos = lexing_pos_end ulexbuf in
            let loc = Loc.of_lexposs pos pos in
            [%debug_log "exception raised at %s" (Loc.to_string loc)]
          end;

          let last_loc = tbuf#get_last_taken_loc in

          let omp_endif_opt = ref None in

          if cur_src#omp_cc_lines#is_tail last_loc.Loc.end_line then begin
            [%debug_log "OMP Conditional Compilation END"];
            let _, ed0 = Loc.to_lexposs last_loc in
            let qtoken =
              PB.make_qtoken (PP_BRANCH (PPD.Endif(ifdef_openmp, env#lex_paren_level))) ed0 ed0
            in
            omp_endif_opt := Some qtoken;
            tbuf#prebuf_add qtoken
          end;

          if self#in_included then begin
            self#exit_source;
            env#clear_token_feeded;
            match !pending_EOL_ref with
            | Some eol -> begin

                if env#current_source#is_free_source_form then begin
                  tbuf#prebuf_add eol;
                  env#set_lex_mode_queue;
                  self#take_from_lexer ()
                end
                else begin
                  self#take_from_lexer ~pending_EOL:(!pending_EOL_ref) ()
                end;

                match !omp_endif_opt with
                | Some omp_endif -> begin
                    if tbuf#prebuf_peek_last == eol then begin
                      tbuf#prebuf_filter (fun x -> x != omp_endif);
                      tbuf#prebuf_add omp_endif
                    end
                end
                | None -> ()
            end
            | None -> self#take_from_lexer ()
          end
          else if not finished then begin
            begin
              match !pending_EOL_ref with
              | Some eol -> tbuf#prebuf_add eol
              | None -> ()
            end;
            begin
              [%debug_log "current scope: %s" (N.ScopingUnit.to_string env#current_frame#scope)];
              match env#current_frame#scope with
              | N.ScopingUnit.Module _ when begin
                  match tbuf#get_last_rawtok with
                  | END_MODULE _ | END _ -> false
                  | _ -> true
              end -> begin
                  [%debug_log "adding end_module token..."];
                  let end_module_token = make_end_module_token current_ulexbuf in
                  tbuf#prebuf_add end_module_token;
                  tbuf#prebuf_add (make_eol_token current_ulexbuf)
              end
              | _ -> begin
                  [%debug_log "adding end_fragment token..."];
                  let end_fragment_token = make_end_fragment_token current_ulexbuf in
                  tbuf#prebuf_add end_fragment_token
              end
            end;
            tbuf#prebuf_add (make_eof_token current_ulexbuf);
            finished <- true
          end
          else
            tbuf#prebuf_add (make_eof_token current_ulexbuf)
        end
    (* end of method take_from_lexer *)

    method get ?(prefetch=true) () =
      [%debug_log "prebuf_size=%d" tbuf#prebuf_size];
      let thresh =
        if prefetch then
          2
        else
          1
      in
      if tbuf#prebuf_size < thresh then begin
        self#take_from_lexer ()
      end;
      let qtoken =
        try
          tbuf#prebuf_take
        with
          TB.Empty -> self#get ~prefetch ()
      in
      let tok, _ = qtoken in
      [%debug_log "tok: %s" (Token.rawtoken_to_string tok)];
      begin
        match tok with
        | LPAREN -> env#enter_paren_context
        | RPAREN | SLASH_RPAREN -> env#exit_paren_context
        | _ -> ()
      end;
      qtoken

    method peek_nth n =
      [%debug_log "n=%d" n];
      let rec prebuf_peek m =
        try
          tbuf#prebuf_peek_nth m
        with
          Failure _ ->
            for _ = 1 to (m - tbuf#prebuf_size) do
              self#take_from_lexer ()
            done;
            prebuf_peek m
      in
      prebuf_peek n


    method private peek_token ?(skip_eol=false) () = (* skip compiler directives *)

      [%debug_log "skip_eol=%B" skip_eol];

      let ulexbuf = current_ulexbuf in

      let skip_until_endif_flag = ref false in
      let n = ref 1 in
      let branch_depth = ref 0 in
      try
        while true do
          let qtoken = self#peek_nth !n in
          let tok, _ = qtoken in

          [%debug_log "peeking %s token: %s"
            (Common.num_to_ordinal !n) (Token.qtoken_to_string qtoken)];

          if TokenF.is_pp_directive tok then begin
            begin
              match tok with
              | PP_BRANCH br -> begin
                  match br with
                  | PPD.Ifdef _
                  | PPD.Ifndef _
                  | PPD.If _
                    ->
                      incr branch_depth

                  | PPD.Else ->
                      if !branch_depth = 0 then
                        skip_until_endif_flag := true

                  | PPD.Elif _  ->
                      if !branch_depth = 0 then
                        skip_until_endif_flag := true

                  | PPD.Endif _ ->
                      if !branch_depth > 0 then
                        decr branch_depth;
                      skip_until_endif_flag := false
              end
              | _ -> ()
            end;
            incr n
          end
          else if tok = EOL && skip_eol then
            incr n
          else begin
            match tok with
            | EOF _ -> raise (Token_found qtoken)
            | _ ->
                if !skip_until_endif_flag then
                  incr n
                else
                  raise (Token_found qtoken)
          end
        done;
        make_eof_token ulexbuf
      with
      | End_of_file -> begin
          [%debug_log "exception raised at %d" (Sedlexing.lexeme_start current_ulexbuf)];
          if self#in_included then begin
            self#exit_source;
            self#peek_token ~skip_eol ()
          end
          else
            make_eof_token ulexbuf
      end
      | Token_found qtoken ->
          [%debug_log "result=%s" (Token.qtoken_to_string qtoken)];
          qtoken
    (* end of method peek_token *)


    method prepend_queue = tbuf#prepend_queue

    method prepend qtoken = tbuf#prepend qtoken

    method peek_nth_rawtok n = Token.qtoken_to_rawtoken (self#peek_nth n)

    method peek_next_rawtok ?(skip_eol=false) () =
      Token.qtoken_to_rawtoken (self#peek_token ~skip_eol ())

    method discard ?(skip_pp_branch=true) () =
      if skip_pp_branch then begin
        let skip_eol = false in
        let skip_until_endif_flag = ref false in
        let n = ref 1 in
        let branch_depth = ref 0 in
        try
          while true do
            [%debug_log "discarding..."];
            let qtoken = self#get() in
            [%debug_log "discarded: %s" (Token.qtoken_to_string qtoken)];

            let tok, _ = qtoken in

            if TokenF.is_pp_directive tok then begin
              begin
                match tok with
                | PP_BRANCH br -> begin
                    match br with
                    | PPD.Ifdef _
                    | PPD.Ifndef _
                    | PPD.If _
                      ->
                        incr branch_depth;
                        env#incr_discarded_branch_entry_count

                    | PPD.Else ->
                        if !branch_depth = 0 then
                          skip_until_endif_flag := true

                    | PPD.Elif _  ->
                        if !branch_depth = 0 then
                          skip_until_endif_flag := true

                    | PPD.Endif _ ->
                        if !branch_depth > 0 then
                          decr branch_depth;
                        skip_until_endif_flag := false
                end
                | _ -> ()
              end;
              incr n
            end
            else if tok = EOL && skip_eol then
              incr n
            else
              if !skip_until_endif_flag then
                incr n
              else
                raise (Token_found qtoken)
          done;
          assert false
        with
          Token_found qtoken -> qtoken

      end
      else begin
        [%debug_log "discarding..."];
        let qtoken = self#get() in
        [%debug_log "discarded: %s" (Token.qtoken_to_string qtoken)];
        qtoken
      end


    method get_last_rawtok = tbuf#get_last_rawtok
    method set_last_rawtok t = tbuf#set_last_rawtok t

    method get_last_loc = tbuf#get_last_loc
    method set_last_loc l = tbuf#set_last_loc l

    method get_prev_rawtok = tbuf#get_prev_rawtok
    method set_prev_rawtok t = tbuf#set_prev_rawtok t

    method get_prev_loc = tbuf#get_prev_loc
    method set_prev_loc l = tbuf#set_prev_loc l

  end (* of class Trunk.tokensource *)


end (* of functor Trunk.F *)
]
