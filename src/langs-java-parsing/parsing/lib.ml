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
(* lib.ml *)

[%%prepare_logger]

module Xprint = Diffast_misc.Xprint
module Storage = Diffast_misc.Storage
module PB = Langs_common.Parserlib_base
module Aux = Parser_aux


let get_lc = Langs_common.Position.get_lc


[%%capture_path
class parser_c = object (self)
  inherit [Tokens_.token, Ast.c] PB.sb_c (new Aux.env)

  val mutable java_lang_spec = 11
  val mutable keep_going_flag = true
  val mutable rely_on_naming_convention_flag = false
  val mutable partial_name_resolution_flag = false
  val mutable no_implicit_name_resolution_flag = false

  val mutable parser_main = fun _ -> Obj.magic ()
  val mutable scanner     = Obj.magic ()
  val mutable _parse      = fun () -> Obj.magic ()

  val mutable rollback_record = [] (* (error_state_num * rawtoken) list *)

  method set_java_lang_spec lv =
    [%debug_log "lv=%d" lv];
    if lv = 2 || lv = 3 || lv > 6 then begin
      java_lang_spec <- lv;
      env#set_java_lang_spec lv;
      if lv < 3 then begin
        Ulexer.delete_keyword "enum";
      end;
      if lv < 9 then begin
        Ulexer.delete_keyword "exports";
        Ulexer.delete_keyword "module";
        Ulexer.delete_keyword "open";
        Ulexer.delete_keyword "opens";
        Ulexer.delete_keyword "provides";
        Ulexer.delete_keyword "requires";
        Ulexer.delete_keyword "to";
        Ulexer.delete_keyword "transitive";
        Ulexer.delete_keyword "uses";
        Ulexer.delete_keyword "with";
      end;
      if lv < 14 then begin
        Ulexer.delete_keyword "yield";
      end;
      if lv < 16 then begin
        Ulexer.delete_keyword "record";
      end;
      if lv < 17 then begin
        Ulexer.delete_keyword "non-sealed";
        Ulexer.delete_keyword "permits";
        Ulexer.delete_keyword "sealed";
      end
    end
    else
      invalid_arg "Java.Lib.parser_c#set_java_lang_spec"

  method! _set_keep_going_flag b =
    [%debug_log "%B" b];
    keep_going_flag <- b;
    env#_set_keep_going_flag b

  method _set_rely_on_naming_convention_flag b =
    [%debug_log "%B" b];
    rely_on_naming_convention_flag <- b;
    env#_set_rely_on_naming_convention_flag b

  method _set_partial_name_resolution_flag b =
    [%debug_log "%B" b];
    partial_name_resolution_flag <- b;
    env#_set_partial_name_resolution_flag b

  method _set_no_implicit_name_resolution_flag b =
    [%debug_log "%B" b];
    no_implicit_name_resolution_flag <- b;
    env#_set_no_implicit_name_resolution_flag b

  method! parser_init =
    env#begin_scope();
    env#set_last_rawtoken (Obj.repr Tokens_.T.EOF)


  method _parse = _parse()


  method __parse =
    Ulexer.restore_keywords();
(*    self#parser_init; *)
    try
      let srcdir =
        let current_file = env#current_source#file in
        let tree = current_file#tree in
	try
	  match Common.guess_src_dir current_file with
	  | Common.SD_unnamed s ->
              let dir = tree#get_entry s in
	      env#classtbl#add_package ~dir "";
	      dir

	  | Common.SD_named s -> tree#get_entry s
	with
	  Failure mes ->
	    (*WARN_MSG mes;*)
            Xprint.verbose env#verbose_flag "%s" mes;
	    Storage.dummy_entry
      in
      if srcdir != Storage.dummy_entry then begin
	[%debug_log "guessed source directory: \"%s\"" srcdir#path];
	Xprint.verbose env#verbose_flag "guessed source directory: \"%s\"" srcdir#path;
	env#classtbl#set_source_dir srcdir;
      end;

      let cu = parser_main ()(*scanner#get_token*) in
      let ast = new Ast.c cu in
      ast#set_lines_read env#current_pos_mgr#lines_read;
      ast#set_comment_regions env#comment_regions#get_offsets;
      ast#set_comment_LOC env#comment_regions#get_LOC;
      ast#set_missed_regions env#missed_regions#get_offsets;
      ast#set_missed_LOC env#missed_regions#get_LOC;

      ast#set_nintegers env#nintegers;
      ast#set_nfloats env#nfloats;
      ast#set_nstrings env#nstrings;

      let resolve_qname nattr_ref qname =
        [%debug_log "resolving \"%s\"..." qname];
        let attrs = env#lookup_global_qname qname in
        match attrs with
        | [iattr] -> begin
            try
              nattr_ref := Ast.iattr_to_nattr iattr
            with
              _ -> ()
        end
        | _ -> ()
      in

      let rec resolve_name name =
        let qname = Printer.name_to_simple_string name in
	[%debug_log "resolving \"%s\"..." qname];
	match name.Ast.n_desc with
	| Ast.Nsimple(nattr_r, id) -> begin
            let _ = id in
            [%debug_log "nattr=%s id=%s" (Printer.name_attribute_to_string !nattr_r) id];
            match !nattr_r with
	    | Ast.NAtype _      -> [%debug_log "NAtype"]; env#finalize_name_attribute nattr_r
            | Ast.NAambiguous _ -> [%debug_log "NAambiguous"]; env#finalize_name_attribute nattr_r
            | Ast.NAunknown     -> [%debug_log "NAunknown"]; resolve_qname nattr_r qname
            | a -> let _ = a in [%debug_log "%s" (Printer.name_attribute_to_string a)]
        end
	| Ast.Nqualified(nattr_r, q, _, id) -> begin
            [%debug_log "nattr=%s id=%s" (Printer.name_attribute_to_string !nattr_r) id];
	    resolve_name q;
            match Ast.get_name_attribute q with
            | Ast.NAexpression _ as a -> nattr_r := a
            | _ -> begin
              [%debug_log "nattr=%s id=%s" (Printer.name_attribute_to_string !nattr_r) id];
              match !nattr_r with
              | Ast.NAtype _ -> env#finalize_name_attribute nattr_r
              | Ast.NAambiguous _ -> begin
                  env#finalize_name_attribute nattr_r;
                  match !nattr_r with
                  | NAtype (R_resolved x) when x = qname -> begin
                      match Ast.get_name_attribute q with
                      | NAtype (R_resolved fqn) ->
                          let fqn_ = fqn^"$"^id in
                          [%debug_log "fqn_=%s" fqn_];
                          nattr_r := NAtype (R_resolved fqn_)
                      | _ -> ()
                  end
                  | _ -> ()
              end
              | Ast.NAunknown -> resolve_qname nattr_r qname
              | _ -> ()
            end
        end
        | _ -> ()
      in
      [%debug_log "resolving names..."];
      ast#iter_name resolve_name;
      ast
    with
    | Parsing.Parse_error ->
	let l, c = env#current_pos_mgr#get_current_position in
        Common.fail_to_parse
          ~head:(Printf.sprintf "[%s:%d:%d]" env#current_filename l c)
          "syntax error"

    | Ulexer.EOF_reached ->
        Common.fail_to_parse
          ~head:(Printf.sprintf "[%s]" env#current_filename)
          "EOF reached unexpectedly"


  initializer
    let module S = struct
      let env      = env
    end
    in
    let module U = Ulexer.F (S) in
    let module P = Parser.Make (S) in
    let module I = P.MenhirInterpreter in
    let module Scan = Scanner.F (S) in
    (*parser_main <- PB.mkparser P.main;*)
    scanner <- new Scan.c;

    let backup_size = 3 in
    let menv_backup_objs = ref [] in
    let error_state = ref (-1) in

    let save_state _menv =
      let sn = I.current_state_number _menv in
      [%debug_log "current state: %d" sn];
      if List.length !menv_backup_objs >= backup_size then begin
        match List.rev !menv_backup_objs with
        | _ :: tl -> menv_backup_objs := List.rev tl
        | _ -> ()
      end;
      menv_backup_objs := (sn, scanner#copy_shadow_queue, scanner#copy_shadow_q, _menv) :: !menv_backup_objs;
      [%debug_log "\n%s"
        (String.concat "\n"
           (List.map
              (fun (sn, scq, soq, _) ->
                Printf.sprintf "%d: ^%s$ ^%s$"
                  sn (Scanner.token_queue_to_string scq) (Scanner.outline_queue_to_string soq)
              ) !menv_backup_objs)
        )];
      scanner#reset_shadow_queue;
      scanner#reset_shadow_q
    in
    let poss_of_menv _menv =
      match I.get 0 _menv with
      | Some (I.Element (_, _, stp, edp)) -> stp, edp
      | _ -> Lexing.dummy_pos, Lexing.dummy_pos
    in
    let syntax_error menv =
      let stp, edp = poss_of_menv menv in
      let sl, sc = get_lc stp in
      let el, ec = get_lc edp in
      Common.fail_to_parse
        ~head:(Printf.sprintf "[%s:%dL,%dC-%dL,%dC]" env#current_filename sl sc el ec)
        "syntax error"
    in
    let iter_items ?(ith=0) _menv f =
      match I.get ith _menv with
      | Some (I.Element (stat, _, _, _)) -> begin
          let sn = I.number stat in
          let proc o (prod, i) =
            let lhs = I.lhs prod in
            let rhs = I.rhs prod in
            let rhs0 = List.hd rhs in
            let rhsi = List.nth rhs (i-1) in
            match o with
            | Some (s, lh, rh0, rhx, i0) when
                s == sn && lh == lhs && rhx == rhsi && rh0 == rhs0 && i0 = i -> o
            | _ ->
                let x = (sn, lhs, rhs0, rhsi, i) in
                f x;
                Some x
          in
          ignore (List.fold_left proc None (I.items stat))
      end
      | None -> ()
    in
    let iter_items_w ?(from_ith=0) ?(to_ith=0) menv_ f =
      try
        for ith = from_ith to to_ith do
          iter_items ~ith menv_ f
        done
      with
        Exit -> ()
    in
    let rec rollback _menv sn =
      match I.top _menv with
      | Some _ -> begin
          if I.current_state_number _menv = sn then
            _menv
          else
            match I.pop _menv with
            | Some me -> rollback me sn
            | None -> _menv
      end
      | None -> _menv
    in
    let rec loop ckpt =
      match ckpt with
      | I.InputNeeded _menv -> begin
          [%debug_log "[InputNeeded] %d" (I.current_state_number _menv)];
          let tok = scanner#get_token() in
          let ckpt = I.offer ckpt tok in
          loop ckpt
      end
      | I.Shifting (_menv, menv_, _) -> begin
          [%debug_log "[Shifting] %d" (I.current_state_number _menv)];
          env#set_shift_flag;
          let proc_shift (_, l, r0, r, _) =
            match l, r0, r with
            | I.X (I.N N_declare_declaration), _, I.X (I.T T_DECLARE) -> begin
                env#set_in_declare_flag;
                raise Exit
            end
            | I.X (I.N N_declare_declaration), _, I.X (I.T T_SEMICOLON) -> begin
                env#clear_in_declare_flag;
                raise Exit
            end
            | I.X (I.N N_pointcut_declaration), _, I.X (I.T T_POINTCUT) -> begin
                env#set_in_pointcut_flag;
                raise Exit
            end
            | I.X (I.N N_pointcut_declaration), _, I.X (I.T T_SEMICOLON) -> begin
                env#clear_in_pointcut_flag;
                raise Exit
            end

            | I.X (I.N N_block), _, I.X (I.T T_LBRACE) -> begin
                [%debug_log "@"];
                env#open_block;
                env#set_stmt_head_flag;
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_block), _, I.X (I.T T_RBRACE) -> begin
                env#close_block;
                save_state menv_;
                if env#keep_going_flag && env#in_method && env#block_level = 1 then begin
                  try
                    iter_items_w ~from_ith:4 ~to_ith:4 _menv
                      (function
                        | sn, I.X (I.N N_variable_declarator), _, _, i -> begin
                            let _ = sn in
                            let _ = i in
                            [%debug_log "sn=%d i=%d" sn i];
                            let t1, rt1 = scanner#peek_nth 1 in
                            begin
                              match rt1 with
                              | RBRACE -> begin
                                  let _, stp, edp = Token.decompose t1 in
                                  let loc = Scan.loc_of_poss stp edp in
                                  Common.warning_loc loc "adding SEMICOLON";
                                  scanner#prepend_rawtoken Tokens_.SEMICOLON Lexing.dummy_pos Lexing.dummy_pos
                              end
                              | _ -> ()
                            end;
                            raise Exit
                          end
                        | sn, I.X (I.N N_if_then_else_statement), _, _, i -> begin
                            let _ = sn in
                            let _ = i in
                            [%debug_log "sn=%d i=%d" sn i];
                            raise Exit
                        end
                        | sn, _, _, _, _ -> let _ = sn in [%debug_log "sn=%d" sn]
                        (*| _ -> ()*)
                      )
                  with
                    Exit -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_switch_block), _, I.X (I.T T_LBRACE) -> begin
                [%debug_log "@"];
                env#open_block;
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_switch_block), _, I.X (I.T T_RBRACE) -> begin
                env#close_block;
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_array_initializer), _, I.X (I.T T_LBRACE) -> begin
                env#enter_array;
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_array_initializer), _, I.X (I.T T_RBRACE) -> begin
                env#exit_array;
                raise Exit
            end
            | I.X (I.N N_lambda_expression), _, I.X (I.T T_MINUS_GT) -> begin
                env#enter_lambda;
                raise Exit
            end
            | I.X (I.N N_lambda_e), _, I.X (I.T T_MINUS_GT) -> begin
                env#enter_lambda;
                raise Exit
            end
            | I.X (I.N N_class_body), _, I.X (I.T T_RBRACE) -> begin
                save_state menv_;
                env#exit_context;
                raise Exit
            end
            | I.X (I.N N_enum_body), _, I.X (I.T T_RBRACE) -> begin
                save_state menv_;
                env#exit_context;
                raise Exit
            end
            | I.X (I.N N_constructor_body), _, I.X (I.T T_LBRACE) -> begin
                [%debug_log "@"];
                env#enter_method;
                env#open_block;
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_aspect_body), _, I.X (I.T T_RBRACE) -> begin
                save_state menv_;
                env#exit_context;
                env#clear_in_aspect_flag;
                raise Exit
            end
            | I.X (I.N N_labeled_statement_head), _, I.X (I.T T_COLON) -> begin
                save_state menv_;
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_local_variable_declaration_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_expression_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                if env#keep_going_flag && env#in_method && env#block_level > 2 then begin
                  try
                    iter_items_w ~from_ith:2 ~to_ith:2 _menv
                      (function
                        | sn, I.X (I.N N_if_then_else_statement), _, _, i when i = 6 -> begin
                            let _ = sn in
                            [%debug_log "sn=%d i=%d" sn i];
                            let t1, rt1 = scanner#peek_nth 1 in
                            begin
                              match rt1 with
                              | RBRACE -> begin
                                  let _, rt2 = scanner#peek_nth 2 in
                                  begin
                                    match rt2 with
                                    | ELSE _ -> begin
                                        let _, stp, edp = Token.decompose t1 in
                                        let loc = Scan.loc_of_poss stp edp in
                                        Common.warning_loc loc "adding a closing brace";
                                        scanner#prepend_rawtoken Tokens_.RBRACE Lexing.dummy_pos Lexing.dummy_pos
                                    end
                                    | _ -> ()
                                  end
                              end
                              | _ -> ()
                            end;
                            raise Exit
                        end
                        | sn, _, _, _, _ -> let _ = sn in [%debug_log "sn=%d" sn]
                        (*| _ -> ()*)
                      )
                  with
                    Exit -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_return_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_break_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_continue_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_throw_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_do_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_empty_statement), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_array_initializer), _, I.X (I.T T_COMMA) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_if_then_statement), _, I.X (I.T T_RPAREN) -> begin
                (*save_state menv_;*)
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_if_then_else_statement), _, I.X (I.T T_RPAREN) -> begin
                (*save_state menv_;*)
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_if_then_else_statement), _, I.X (I.T T_ELSE) -> begin
                (*save_state menv_;*)
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_if_then_else_statement_no_short_if), _, I.X (I.T T_RPAREN) -> begin
                (*save_state menv_;*)
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_if_then_else_statement_no_short_if), _, I.X (I.T T_ELSE) -> begin
                (*save_state menv_;*)
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_while_statement), _, I.X (I.T T_RPAREN) -> begin
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_do_statement), _, I.X (I.T T_DO) -> begin
                env#set_stmt_head_flag;
                raise Exit
            end
            (* *)
            | I.X (I.N N_method_invocation), _, I.X (I.T T_LPAREN) -> begin
                env#enter_ivk;
                raise Exit
            end
            | I.X (I.N N_method_invocation), _, I.X (I.T T_RPAREN) -> begin
                env#exit_ivk;
                raise Exit
            end
            | I.X (I.N N_explicit_constructor_invocation), _, I.X (I.T T_LPAREN) -> begin
                env#enter_ivk;
                raise Exit
            end
            | I.X (I.N N_explicit_constructor_invocation), _, I.X (I.T T_RPAREN) -> begin
                env#exit_ivk;
                raise Exit
            end
            | I.X (I.N N_resource_spec), _, I.X (I.T T_LPAREN) -> begin
                env#open_res;
                raise Exit
            end
            | I.X (I.N N_resource_spec), _, I.X (I.T T_RPAREN) -> begin
                env#close_res;
                raise Exit
            end
            | I.X (I.N N_type_arguments), _, I.X (I.T T_LT) -> begin
                env#open_tap;
                raise Exit
            end
            | I.X (I.N N_type_arguments), _, I.X (I.T T_GT) -> begin
                env#close_tap;
                raise Exit
            end
            | I.X (I.N N_reference_type_1), _, I.X (I.T T_GT) -> begin
                env#close_tap;
                raise Exit
            end
            | I.X (I.N N_reference_type_1), _, I.X (I.T T_LT) -> begin
                env#open_tap;
                raise Exit
            end
            | I.X (I.N N_reference_type_2), _, I.X (I.T T_LT) -> begin
                env#open_tap;
                raise Exit
            end
            | I.X (I.N N_wildcard_1), _, I.X (I.T T_GT) -> begin
                env#close_tap;
                raise Exit
            end
            | I.X (I.N N_reference_type_2), _, I.X (I.T T_GT_GT) -> begin
                env#close_tap;
                env#close_tap;
                raise Exit
            end
            | I.X (I.N N_wildcard_2), _, I.X (I.T T_GT_GT) -> begin
                env#close_tap;
                env#close_tap;
                raise Exit
            end
            | I.X (I.N N_reference_type_3), _, I.X (I.T T_GT_GT_GT) -> begin
                env#close_tap;
                env#close_tap;
                env#close_tap;
                raise Exit
            end
            | I.X (I.N N_wildcard_3), _, I.X (I.T T_GT_GT_GT) -> begin
                env#close_tap;
                env#close_tap;
                env#close_tap;
                raise Exit
            end
            | I.X (I.N N_type_parameters), _, I.X (I.T T_LT) -> begin
                env#open_tap;
                raise Exit
            end
            | I.X (I.N N_type_parameter_1), _, I.X (I.T T_GT) -> begin
                env#close_tap;
                raise Exit
            end

            | I.X (I.N N_module_body), _, I.X (I.T T_LBRACE) -> begin
                (*save_state menv_;*)
                env#enter_module;
                raise Exit
            end
            | I.X (I.N N_module_body), _, I.X (I.T T_RBRACE) -> begin
                save_state menv_;
                env#exit_context;
                raise Exit
            end
            | I.X (I.N N_class_body), _, I.X (I.T T_LBRACE) -> begin
                (*save_state menv_;*)
                env#enter_class;
                raise Exit
            end
            | I.X (I.N N_interface_body), _, I.X (I.T T_LBRACE) -> begin
                env#enter_class;
                raise Exit
            end
            | I.X (I.N N_enum_body), _, I.X (I.T T_LBRACE) -> begin
                env#enter_class;
                raise Exit
            end
            | I.X (I.N N_aspect_body), _, I.X (I.T T_LBRACE) -> begin
                (*save_state menv_;*)
                env#enter_class;
                env#set_in_aspect_flag;
                raise Exit
            end
            | I.X (I.N N_field_declaration), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_interface_body), _, I.X (I.T T_RBRACE) -> begin
                save_state menv_;
                env#exit_context;
                raise Exit
            end
            | I.X (I.N N_annotation_type_body), _, I.X (I.T T_LBRACE) -> begin
                env#enter_class;
                raise Exit
            end
            | I.X (I.N N_annotation_type_body), _, I.X (I.T T_RBRACE) -> begin
                save_state menv_;
                env#exit_context;
                raise Exit
            end
            | I.X (I.N N_class_member_declaration), _, I.X (I.T T_SEMICOLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_constructor_body), _, I.X (I.T T_RBRACE) -> begin
                save_state menv_;
                env#close_block;
                env#exit_context;
                raise Exit
            end
            (* *)
            | I.X (I.N N_if_then_statement), _, I.X (I.T T_LPAREN) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_if_then_else_statement), _, I.X (I.T T_LPAREN) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_if_then_else_statement_no_short_if), _, I.X (I.T T_LPAREN) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_assignment), _, x -> begin
                match x with
                | I.X (I.T T_EQ)
                | I.X (I.T T_STAR_EQ)
                | I.X (I.T T_SLASH_EQ)
                | I.X (I.T T_PERCENT_EQ)
                | I.X (I.T T_PLUS_EQ)
                | I.X (I.T T_MINUS_EQ)
                | I.X (I.T T_LT_LT_EQ)
                | I.X (I.T T_GT_GT_EQ)
                | I.X (I.T T_GT_GT_GT_EQ)
                | I.X (I.T T_AND_EQ)
                | I.X (I.T T_HAT_EQ)
                | I.X (I.T T_OR_EQ)
                  ->
                    save_state menv_;
                    raise Exit
                | _ -> ()
            end
            | I.X (I.N N_separated_nonempty_list_COMMA_expr_or_err_), _, I.X (I.T T_COMMA) -> begin
                save_state menv_;
                raise Exit
            end

            | I.X (I.N N_class_instance_creation_expression), _, I.X (I.T T_RPAREN) -> begin
                env#enter_new;
                raise Exit
            end
            | I.X (I.N N_for_statement_head), _, I.X (I.T T_LPAREN) -> begin
                env#enter_for;
                raise Exit
            end
            | I.X (I.N N_for_statement), _, I.X (I.T T_RPAREN) -> begin
                env#exit_for;
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_for_statement_no_short_if), _, I.X (I.T T_RPAREN) -> begin
                env#exit_for;
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_enhanced_for_statement), _, I.X (I.T T_RPAREN) -> begin
                env#exit_for;
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_enhanced_for_statement_no_short_if), _, I.X (I.T T_RPAREN) -> begin
                env#exit_for;
                env#set_stmt_head_flag;
                raise Exit
            end

            | I.X (I.N N_class_declaration_head0), _, I.X (I.T T_CLASS) -> begin
                env#set_class_flag;
                raise Exit
            end

            | I.X (I.N N_switch_label), _, I.X (I.T T_CASE) -> begin
                env#set_case_flag;
                raise Exit
            end
            | I.X (I.N N_switch_rule_label), _, I.X (I.T T_CASE) -> begin
                env#set_case_flag;
                raise Exit
            end
            | I.X (I.N N_switch_label), _, I.X (I.T T_COLON) -> begin
                env#clear_case_flag;
                env#set_stmt_head_flag;
                raise Exit
            end
            | I.X (I.N N_switch_rule_label), _, I.X (I.T T_MINUS_GT__CASE) -> begin
                env#clear_case_flag;
                raise Exit
            end

            | _ -> ()
          in
          begin
            try
              iter_items menv_ proc_shift
            with
              Exit -> ()
          end;
          let ckpt = I.resume ckpt in
          loop ckpt
      end
      | I.AboutToReduce (_menv, prod) -> begin
          let last_rawtok = (Obj.obj env#last_rawtoken) in
          [%debug_log "last_rawtoken=%s" (Token.rawtoken_to_string last_rawtok)];
          if !error_state > -1 then begin
            match last_rawtok with
            | Tokens_.ERROR _ -> ()
            | _ ->
                error_state := -1;
                rollback_record <- []
          end;

          [%debug_log "[AboutToReduce] %d" (I.current_state_number _menv)];
          begin
            let lhs = I.lhs prod in
            match lhs with
            | I.X (I.N N_lambda_expression) -> begin
                env#exit_lambda;
            end
            | I.X (I.N N_lambda_e) -> begin
                env#exit_lambda;
            end
            | I.X (I.N N_class_instance_creation_expression) -> begin
                env#exit_new;
            end
            | I.X (I.N N_method_header) -> begin
                env#enter_method;
            end
            | I.X (I.N N_method_body) -> begin
                env#exit_context;
            end
            | _ -> ()
          end;
          let ckpt = I.resume ckpt in
          loop ckpt
      end
      | I.HandlingError _menv -> begin
          let sn = I.current_state_number _menv in
          [%debug_log "[HandlingError] %d" sn];
          if keep_going_flag then begin

            [%debug_log "error_state=%d" !error_state];
            let to_be_popped =
              !error_state > -1 &&
              match !menv_backup_objs with
              | (_, _, _, menv0)::_ -> begin
                  try
                    iter_items menv0
                      (function
                        | sn, I.X (I.N N_separated_nonempty_list_COMMA_expr_or_err_), _, _, _ -> begin
                            let _ = sn in
                            [%debug_log "sn=%d" sn];
                            raise Exit
                        end
                        | sn, _, _, _, _ -> let _ = sn in [%debug_log "sn=%d" sn]
                      );
                    false
                  with
                    Exit -> true
              end
              | _ -> false
            in
            [%debug_log "to_be_popped=%B" to_be_popped];
            if to_be_popped then begin
              match !menv_backup_objs with
              | (_, scq, soq, _)::tl -> begin
                  menv_backup_objs := tl;
                  scanner#prepend_shadow_queue scq;
                  scanner#prepend_shadow_q soq;
              end
              | _ -> ()
            end;

            let stp, edp = poss_of_menv _menv in
            let loc = Scan.loc_of_poss stp edp in
            let e = scanner#shadow_outline in
            let err = scanner#shadow_contents in
            scanner#reset_shadow_q;
            scanner#reset_shadow_queue;
            [%debug_log "shadow_q: %s" e];
            [%debug_log "shadow_queue: %s" err];
            (*let last_char_opt =
              let len = String.length err in
              if len > 0 then begin
                let c = err.[len - 1] in
                [%debug_log "last=%c" c];
                Some c
              end
              else begin
                [%debug_log "last="];
                None
              end
            in
            let li = (String.length e) - 1 in*)
            [%debug_log "shift_flag=%B" env#shift_flag];
            begin
              let len = String.length e in
              for i = len - 1 downto 0 do
                match e.[i] with
                (*| '}' when i = li && last_char = '}' && not env#shift_flag -> ()*)
                | '{' when env#in_method && env#block_level = 1 -> ()
                | '{' when env#in_class -> env#exit_context
                | '(' -> env#close_paren
                | ')' -> env#open_paren
                | '{' -> env#close_block
                (*| '}' -> env#open_block*)
                | _ -> ()
              done
            end;
            Common.warning_loc loc "syntax error: %s" err;
            let rawtok = Tokens_.ERROR err in
            let tok = Token.create rawtok stp edp in
            scanner#prepend_token tok;
            error_state := sn;
            let menv =
              match !menv_backup_objs with
              | (sn0, scq0, _, menv0)::_ -> begin
                  let _ = scq0 in
                  [%debug_log "saved state: %d: %s" sn0 (Scanner.token_queue_to_string scq0)];
                  let rrec =  (sn, rawtok) in
                  [%debug_log "rrec=(%d,%s)" sn (Token.rawtoken_to_string rawtok)];
                  if not (List.mem rrec rollback_record) then begin
                    rollback_record <- rrec :: rollback_record;
                    rollback menv0 sn0
                  end
                  else
                    syntax_error _menv
              end
              | _ -> syntax_error _menv
            in
            let ckpt = I.input_needed menv in
            loop ckpt
          end
          else
            syntax_error _menv
      end
      | I.Accepted v -> begin
          v
      end
      | I.Rejected -> raise P.Error
    in
    let do_parse () =
      let ini_pos =
        { Lexing.pos_fname = env#current_filename;
          Lexing.pos_lnum  = 1;
          Lexing.pos_bol   = 0;
          Lexing.pos_cnum  = 0
        }
      in
      let ini_ckpt = P.Incremental.main ini_pos in
      loop ini_ckpt
    in
    parser_main <- do_parse;

    _parse <-
      (fun () ->
	try
	  self#__parse
	with
	| P.Error ->
	    let l, c = env#current_pos_mgr#get_current_position in
            Common.fail_to_parse
              ~head:(Printf.sprintf "[%s:%d:%d]" env#current_filename l c)
              "syntax error"
        | Stack.Empty ->
	    let l, c = env#current_pos_mgr#get_current_position in
            Common.fail_to_parse
              ~head:(Printf.sprintf "[%s:%d:%d]" env#current_filename l c)
              "failed to parse"
      )

end (* of class Lib.parser_c *)
]
