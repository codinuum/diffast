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

module Storage = Diffast_misc.Storage
module Parserlib_base = Langs_common.Parserlib_base
module Astloc = Langs_common.Astloc

module Loc = Astloc
module Aux = Parser_aux
module PB = Parserlib_base
module C = Context

let mkparser = PB.mkparser


let predefined_macrotbl =
  let open Tokens_ in

  let mkstring id  = PP_MACRO_CONST_STR id in
  let mkinteger id = PP_MACRO_CONST_INT id in

  let tbl = new Macro.table "predefined" in
  let list =
    [
      "`__FILE__", [], Macro.mk_line mkstring;
      "`__LINE__", [], Macro.mk_line mkinteger;
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

  val mutable context_stack = Obj.magic ()

  val mutable begin_scope = fun () -> ()
  val mutable end_scope   = fun () -> ()

  val mutable parser_partial_description_list      = fun _ -> Obj.magic ()
  val mutable parser_partial_module_item_list      = fun _ -> Obj.magic ()
  val mutable parser_partial_generate_item_list    = fun _ -> Obj.magic ()
  val mutable parser_partial_block_decl_stmt_list  = fun _ -> Obj.magic ()
  val mutable parser_partial_case_item_list        = fun _ -> Obj.magic ()
  val mutable parser_partial_case_inside_item_list = fun _ -> Obj.magic ()
  val mutable parser_partial_cellpin_list          = fun _ -> Obj.magic ()
  val mutable parser_partial_list_of_ports         = fun _ -> Obj.magic ()
  val mutable parser_partial_pev_expr              = fun _ -> Obj.magic ()
  val mutable parser_partial_ev_expr               = fun _ -> Obj.magic ()
  val mutable parser_partial_expr                  = fun _ -> Obj.magic ()

  val mutable parser_main                          = fun _ -> Ast.dummy_node


  val mutable parse_error = fun _ _ _ -> Common.fail_to_parse ""

  val mutable scanner = Obj.magic ()

  val mutable _parse = fun () -> Obj.magic ()

  method set_ignore_include_flag = env#set_ignore_include_flag
  method clear_ignore_include_flag = env#clear_ignore_include_flag

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
    | C.Cunknown               -> [%debug_log "not found"]; raise Not_found
    | C.Ctoplevel              -> parser_partial_description_list
    | C.Cmodule_item_list      -> parser_partial_module_item_list
    | C.Cgenerate_item_list    -> parser_partial_generate_item_list
    | C.Cblock_decl_stmt_list  -> parser_partial_block_decl_stmt_list
    | C.Ccase_item_list        -> parser_partial_case_item_list
    | C.Ccase_inside_item_list -> parser_partial_case_inside_item_list
    | C.Ccellpin_list          -> parser_partial_cellpin_list
    | C.Clist_of_ports         -> parser_partial_list_of_ports
    | C.Cpev_expr              -> parser_partial_pev_expr
    | C.Cev_expr               -> parser_partial_ev_expr
    | C.Cexpr                  -> parser_partial_expr

  method! parser_init =
    [%debug_log "initializing..."];
    begin_scope();
    List.iter
      (fun (pkg, _) ->
	env#import_any pkg;
	env#register_identifier pkg Aux.IApackage
      ) Aux.builtin_packages;
    context_stack#reset;
    [%debug_log "finished"]


  method _parse = _parse()

  method macrotbl = env#macrotbl
  method set_predefined_macrotbl tbl = env#set_predefined_macrotbl tbl


  method make_source file =
    new Source.c file

  method make_source_stdin =
    new Source.c Storage.stdin


  method __parse =
(*    self#parser_init; *)
    try
      let root = parser_main scanner#get_token in
      let ast = new Ast.c root in

      ast#set_lines_read (env#lines_read + env#current_pos_mgr#lines_read);
      ast#set_comment_regions env#comment_regions#get_offsets;
      ast#set_comment_LOC env#comment_regions#get_LOC;
      ast#set_missed_regions (env#missed_regions#get_offsets);
      ast#set_missed_LOC (env#missed_regions#get_LOC);
      ast#set_ignored_regions (env#ignored_regions#get_offsets);
      ast#set_ignored_LOC (env#ignored_regions#get_LOC);
      ast
    with
    | Parsing.Parse_error ->
	let l, c = env#current_pos_mgr#get_current_position in
        Common.fail_to_parse
          ~head:(Printf.sprintf "[%s:%d:%d]" env#current_filename l c)
          "syntax error"



  initializer
    context_stack <- new C.stack env;
    let module S = struct
      let env           = env
      let context_stack = context_stack
    end
    in
    let module A = Aux.F (S) in
    let module P = Parser.Make (S) in
    let module TB = Tokenbuffer.F (S) in
    let module Scan = Scanner.F (S) in

    begin_scope <- A.begin_scope;
    end_scope   <- A.end_scope;

    scanner <- new Scan.c env self#partial_parser_selector;

    parser_partial_description_list      <- mkparser P.partial_description_list;
    parser_partial_module_item_list      <- mkparser P.partial_module_item_list;
    parser_partial_generate_item_list    <- mkparser P.partial_gen_item_list;
    parser_partial_block_decl_stmt_list  <- mkparser P.partial_block_decl_stmt_list;
    parser_partial_case_item_list        <- mkparser P.partial_case_item_list;
    parser_partial_case_inside_item_list <- mkparser P.partial_case_inside_item_list;
    parser_partial_cellpin_list          <- mkparser P.partial_cellpin_list;
    parser_partial_list_of_ports         <- mkparser P.partial_list_of_ports;
    parser_partial_pev_expr              <- mkparser P.partial_pev_expr;
    parser_partial_ev_expr               <- mkparser P.partial_ev_expr;
    parser_partial_expr                  <- mkparser P.partial_expr;

    parser_main                          <- mkparser P.main;

    parse_error <- A.parse_error;

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
      )


end (* of Lib.parser_c *)
]
