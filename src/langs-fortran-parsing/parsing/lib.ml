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

(* lib.ml *)

[%%prepare_logger]

module Storage = Diffast_misc.Storage
module Astloc = Langs_common.Astloc
module Parserlib_base = Langs_common.Parserlib_base

module Loc = Astloc
module Aux = Parser_aux
module PB = Parserlib_base
module SF = Common.SourceForm
module C = Context

let mkparser = PB.mkparser


let predefined_macrotbl =
  let open Tokens_ in

  let mkconst id    = PP_MACRO_CONST id in
  let mkname id     = PP_MACRO_NAME(id, "") in
  let mkexpr id     = PP_MACRO_EXPR id in
  let mkstmt id     = PP_MACRO_STMT id in
  let mktypespec id = PP_MACRO_TYPE_SPEC id in

  let tbl = new Macro.table "predefined" in
  let list =
    [ "__FXXP_CONST__",     [], Macro.mk_line mkconst;
      "__FXXP_NAME__",      [], Macro.mk_line mkname;
      "__FXXP_EXPR__",      [], Macro.mk_line mkexpr;
      "__FXXP_STMT__",      [], Macro.mk_line mkstmt;
      "__FXXP_TYPE_SPEC__", [], Macro.mk_line mktypespec;

      "__FILE__", [], Macro.mk_line mkconst;
      "__LINE__", [], Macro.mk_line mkconst;
      "__DATE__", [], Macro.mk_line mkconst;
      "__TIME__", [], Macro.mk_line mkconst;
    ]
  in
  List.iter
    (fun (id, args, mk_line) ->
      let body =
        match args with
        | [] -> Macro.Object (mk_line id)
        | _ -> Macro.Function(args, mk_line id)
      in
      tbl#define id body
    ) list;
  tbl

[%%capture_path
class parser_c = object (self)
  inherit [Source.c, Tokens_.token, Ast.c] PB.c (new Aux.env)


  val mutable parse_d_lines_flag = false
  val mutable max_line_length = None


  val mutable context_stack = Obj.magic ()

  val mutable begin_program_scope      = fun () -> ()
  val mutable begin_main_program_scope = fun _ -> ()
  val mutable end_scope                = fun () -> ()

  val mutable parser_partial_program               = fun _ -> Obj.magic ()
  val mutable parser_partial_program_unit          = fun _ -> Obj.magic ()
  val mutable parser_partial_spec__exec            = fun _ -> Obj.magic ()
  val mutable parser_partial_specification_part    = fun _ -> Obj.magic ()
  val mutable parser_partial_execution_part        = fun _ -> Obj.magic ()
  val mutable parser_partial_subprograms           = fun _ -> Obj.magic ()
  val mutable parser_partial_interface_spec        = fun _ -> Obj.magic ()
  val mutable parser_partial_case_block            = fun _ -> Obj.magic ()
  val mutable parser_partial_assignment_stmt       = fun _ -> Obj.magic ()
  val mutable parser_partial_type_declaration_stmt = fun _ -> Obj.magic ()
  val mutable parser_partial_function_stmt         = fun _ -> Obj.magic ()
  val mutable parser_partial_variable              = fun _ -> Obj.magic ()
  val mutable parser_partial_expr                  = fun _ -> Obj.magic ()
  val mutable parser_partial_stmts                 = fun _ -> Obj.magic ()
  val mutable parser_partial_data_stmt_sets        = fun _ -> Obj.magic ()
  val mutable parser_partial_type_spec             = fun _ -> Obj.magic ()
  val mutable parser_partial_action_stmt           = fun _ -> Obj.magic ()
  val mutable parser_partial_derived_type_def_part = fun _ -> Obj.magic ()
  val mutable parser_partial_onlys                 = fun _ -> Obj.magic ()
  val mutable parser_partial_type_bound_proc_part  = fun _ -> Obj.magic ()
  val mutable parser_partial_function_head         = fun _ -> Obj.magic ()
  val mutable parser_partial_function_stmt_head    = fun _ -> Obj.magic ()
  val mutable parser_partial_subroutine_head       = fun _ -> Obj.magic ()
  val mutable parser_partial_subroutine_stmt_head  = fun _ -> Obj.magic ()
  val mutable parser_partial_pu_tail               = fun _ -> Obj.magic ()

  val mutable parser_main         = fun _ -> Ast.dummy_node

  val mutable parse_error = fun _ _ _ -> Common.fail_to_parse ""

  val mutable scanner = Obj.magic ()

  val mutable _parse = fun () -> Obj.magic ()

  method _parse = _parse()

  method! parse_file file =
    self#parser_init;
    let src = self#make_source file in
    let _ = env#enter_source src in
    env#set_base_file src#path;
    let ast = _parse() in
    env#exit_source;
    ast


  method set_ignore_case_flag = env#set_ignore_case_flag
  method clear_ignore_case_flag = env#clear_ignore_case_flag

  method set_ignore_include_flag = env#set_ignore_include_flag
  method clear_ignore_include_flag = env#clear_ignore_include_flag

  method macrotbl = env#macrotbl
  method set_predefined_macrotbl tbl = env#set_predefined_macrotbl tbl


  method _set_parse_d_lines_flag b = parse_d_lines_flag <- b
  method set_parse_d_lines_flag = parse_d_lines_flag <- true
  method clear_parse_d_lines_flag = parse_d_lines_flag <- false

  method set_max_line_length n =
    max_line_length <- Some n

  method clear_max_line_length =
    max_line_length <- None


  method _make_source src =
    let config = src#lang_config in
    config#_set_parse_d_lines_flag parse_d_lines_flag;
    begin
      match max_line_length with
      | Some n -> config#set_max_line_length n
      | _ -> ()
    end;
    src

  method make_source file =
    self#_make_source (new Source.c file)

  method make_source_stdin =
    self#_make_source (new Source.c Storage.stdin)





  method dump_ignored_regions =
    env#ignored_regions#dump

  method ignored_LOC =
    env#ignored_regions#get_LOC

  method dump_missed_regions =
    env#missed_regions#dump

  method missed_LOC =
    env#missed_regions#get_LOC



  method partial_parser_selector c =
    match C.get_tag c with
    | C.Tunknown            ->
        [%debug_log "unknown context"];
        raise Not_found

    | C.Ttoplevel              -> [parser_partial_program]

    | C.Tprogram_unit          -> [parser_partial_program_unit;
                                   parser_partial_spec__exec]

    | C.Tspec__exec            -> [parser_partial_spec__exec;
                                   parser_partial_type_spec;
                                   parser_partial_stmts;
                                   parser_partial_pu_tail;
                                   parser_partial_function_stmt_head;
                                   parser_partial_subroutine_stmt_head;
                                   parser_partial_function_head;
                                   parser_partial_subroutine_head;
                                   parser_partial_program]

    | C.Tspecification_part    -> [parser_partial_specification_part;
                                   parser_partial_stmts]

    | C.Texecution_part        -> [parser_partial_execution_part;
                                   parser_partial_stmts]

    | C.Tsubprograms           -> [parser_partial_subprograms;
                                   parser_partial_function_stmt_head;
                                   parser_partial_subroutine_stmt_head;
                                   parser_partial_function_head;
                                   parser_partial_subroutine_head]

    | C.Tinterface_spec        -> [parser_partial_interface_spec]
    | C.Tcase_block            -> [parser_partial_case_block]
    | C.Tassignment_stmt       -> [parser_partial_assignment_stmt]
    | C.Ttype_declaration_stmt -> [parser_partial_type_declaration_stmt]
    | C.Tfunction_stmt         -> [parser_partial_function_stmt]
    | C.Tvariable              -> [parser_partial_variable]
    | C.Texpr                  -> [parser_partial_expr]
    | C.Tstmts                 -> [parser_partial_stmts]
    | C.Tdata_stmt_sets        -> [parser_partial_data_stmt_sets]
    | C.Ttype_spec             -> [parser_partial_type_spec]
    | C.Taction_stmt           -> [parser_partial_action_stmt]
    | C.Tderived_type_def_part -> [parser_partial_derived_type_def_part]
    | C.Tonlys                 -> [parser_partial_onlys]
    | C.Ttype_bound_proc_part  -> [parser_partial_type_bound_proc_part]
    | C.Tfunction_head         -> [parser_partial_function_head]
    | C.Tfunction_stmt_head    -> [parser_partial_function_stmt_head]
    | C.Tsubroutine_head       -> [parser_partial_subroutine_head]
    | C.Tsubroutine_stmt_head  -> [parser_partial_subroutine_stmt_head]
    | C.Tpu_tail               -> [parser_partial_pu_tail]

    | C.Tin_stmt               -> [](*[parser_partial_variable;parser_partial_expr]*)
(*
    | t                     ->
        [%debug_log "parser for %s not found" (C.tag_to_string t)];
        raise Not_found
*)

  method! parser_init =
    [%debug_log "called"];
    begin_program_scope();
    context_stack#reset;

(* for head-less main_program *)
    begin_main_program_scope();
    context_stack#push (C.spec__exec());

    let topkey = C.mktopkey 0 in
    context_stack#checkpoint topkey;
    env#checkpoint topkey


  method private __parse() =
    try
      let root = parser_main scanner#get_token in
      let ast = new Ast.c root in

      let elab = new Elaborate.c in
      elab#elaborate_ast ast;

      scanner#set_ignored_regions;

      ast#set_lines_read (env#lines_read + env#current_pos_mgr#lines_read);
      ast#set_comment_regions env#comment_regions#get_offsets;
      ast#set_comment_LOC env#comment_regions#get_LOC;
      ast#set_missed_regions (env#missed_regions#get_offsets);
      ast#set_missed_LOC (env#missed_regions#get_LOC);
      ast#set_ignored_regions (env#ignored_regions#get_offsets);
      ast#set_ignored_LOC (env#ignored_regions#get_LOC);
      ast
    with
    | Common.Parse_error(_head, msg) ->
        let head =
          if _head = "" then
            let loc = scanner#last_loc in
            Loc.end_to_string ~prefix:"[" ~suffix:"]" loc
          else
            _head
        in
	Common.fail_to_parse ~head msg

    | Parsing.Parse_error ->
        let loc = scanner#last_loc in
	Common.fail_to_parse ~head:(Loc.end_to_string ~prefix:"[" ~suffix:"]" loc) "syntax error"



  initializer
    context_stack <- new C.stack env;
    env#set_last_lex_qtoken_obj (Obj.repr (Tokens_.EOF None, Loc.dummy));
    let module S = struct
      let env           = env
      let context_stack = context_stack
    end
    in
    let module A = Aux.F (S) in
    let module P = Parser.Make (S) in
    let module Scan = Scanner.F (S) in

    begin_program_scope      <- A.begin_program_scope;
    begin_main_program_scope <- A.begin_headless_main_program_scope;
    end_scope                <- A.end_scope;

    scanner <- new Scan.c env self#partial_parser_selector;

    parser_partial_program               <- mkparser P.partial_program;
    parser_partial_program_unit          <- mkparser P.partial_program_unit;
    parser_partial_spec__exec            <- mkparser P.partial_spec__exec;
    parser_partial_specification_part    <- mkparser P.partial_specification_part;
    parser_partial_execution_part        <- mkparser P.partial_execution_part;
    parser_partial_subprograms           <- mkparser P.partial_subprograms;
    parser_partial_interface_spec        <- mkparser P.partial_interface_spec;
    parser_partial_case_block            <- mkparser P.partial_case_block;
    parser_partial_assignment_stmt       <- mkparser P.partial_assignment_stmt;
    parser_partial_type_declaration_stmt <- mkparser P.partial_type_declaration_stmt;
    parser_partial_function_stmt         <- mkparser P.partial_function_stmt;
    parser_partial_variable              <- mkparser P.partial_variable;
    parser_partial_expr                  <- mkparser P.partial_expr;
    parser_partial_stmts                 <- mkparser P.partial_stmts;
    parser_partial_data_stmt_sets        <- mkparser P.partial_data_stmt_sets;
    parser_partial_type_spec             <- mkparser P.partial_type_spec;
    parser_partial_action_stmt           <- mkparser P.partial_action_stmt;
    parser_partial_derived_type_def_part <- mkparser P.partial_derived_type_def_part;
    parser_partial_onlys                 <- mkparser P.partial_onlys;
    parser_partial_type_bound_proc_part  <- mkparser P.partial_type_bound_proc_part;
    parser_partial_function_head         <- mkparser P.partial_function_head;
    parser_partial_function_stmt_head    <- mkparser P.partial_function_stmt_head;
    parser_partial_subroutine_head       <- mkparser P.partial_subroutine_head;
    parser_partial_subroutine_stmt_head  <- mkparser P.partial_subroutine_stmt_head;
    parser_partial_pu_tail               <- mkparser P.partial_pu_tail;

    parser_main                          <- mkparser P.main;

    parse_error <- A.parse_error;

    _parse <-
      (fun () ->
	try
	  self#__parse()
	with
	| P.Error ->
	    let l, c = env#current_pos_mgr#get_current_position in
	    Common.fail_to_parse ~head:(Printf.sprintf "[%s:%d:%d]" env#current_filename l c) "syntax error"
      );

    self#set_predefined_macrotbl (Some predefined_macrotbl)


end (* of Lib.parser_c *)
]
