(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>
   Copyright 2020-2025 Chiba Institute of Technology

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

[%%prepare_logger]

module Xset = Diffast_misc.Xset
module Xhash = Diffast_misc.Xhash
module Binding = Diffast_misc.Binding
module Loc = Diffast_misc.Loc
module Env_base = Langs_common.Env_base
module Astloc = Langs_common.Astloc

module UID = Diffast_misc.UID
module L = Label
module B = Binding
module BID = Binding.ID
module I = Pinfo
module N = Pinfo.Name
module Type = Pinfo.Type
module C = Context
module Loc_ = Loc

open Common

let is_asm_kw =
  let l = [
    "pop";
    "push";
    "add";
    "sub";

    "subs"; (* ARM *)

    "movn"; (* MIPS *)
    "movz";
    "sll";
    "srl";
  ] in
  let names = Xset.create 0 in
  List.iter (Xset.add names) l;
  fun s -> Xset.mem names s

let conv_loc
    { Ast.Loc.filename     = fn;
      Ast.Loc.start_offset = so;
      Ast.Loc.end_offset   = eo;
      Ast.Loc.start_line   = sl;
      Ast.Loc.start_char   = sc;
      Ast.Loc.end_line     = el;
      Ast.Loc.end_char     = ec;
    } =
  Loc_.make ~fname:fn so eo sl sc el ec

let mes fmt = _mes "Parser_aux" fmt

type paren_kind_sub =
  | PKS_NONE
  | PKS_SIZEOF
  | PKS_IF
  | PKS_NUMERIC

type paren_kind =
  | PK_NORMAL of paren_kind_sub
  | PK_ARG
  | PK_TYPE of paren_kind_sub
  | PK_MACRO
  | PK_PP (* preprocessor *)
  | PK_SS (* statements *)
  | PK_PS (* old-style function parameters *)
  | PK_FOLD
  | PK_BRACKET (* objective-C *)

let paren_kind_sub_to_string = function
  | PKS_NONE   -> "PKS_NONE"
  | PKS_SIZEOF -> "PKS_SIZEOF"
  | PKS_IF     -> "PKS_IF"
  | PKS_NUMERIC -> "PKS_NUMERIC"

let paren_kind_to_string = function
  | PK_NORMAL s -> "PK_NORMAL:"^(paren_kind_sub_to_string s)
  | PK_ARG    -> "PK_ARG"
  | PK_TYPE s -> "PK_TYPE:"^(paren_kind_sub_to_string s)
  | PK_MACRO  -> "PK_MACRO"
  | PK_PP     -> "PK_PP"
  | PK_SS     -> "PK_SS"
  | PK_PS     -> "PK_PS"
  | PK_FOLD   -> "PK_FOLD"
  | PK_BRACKET -> "PK_BRACKET"

type templ_param_arg_context = {
    mutable tpac_expr_flag : bool;
  }

let make_templ_param_arg_context () = { tpac_expr_flag=false }

let templ_param_arg_context_to_string {
  tpac_expr_flag=e;
} =
  let sl = ref [] in
  if e then
    sl := "expr" :: !sl;
  if !sl = [] then
    ""
  else
    ":" ^ String.concat ";" !sl

type bracket_kind =
  | BK_PAREN of paren_kind
  | BK_TEMPL_PARAM of templ_param_arg_context
  | BK_TEMPL_ARG of templ_param_arg_context
  | BK_SUBSCR
  | BK_LAM_INTR
  | BK_ATTR
  | BK_OBJC_MSG
  | BK_BRACE of int (* indent *) option
  | BK_CLASS_BRACE
  | BK_INI_BRACE
  | BK_REQ_BRACE

let make_templ_param () = BK_TEMPL_PARAM (make_templ_param_arg_context())
let make_templ_arg () = BK_TEMPL_ARG (make_templ_param_arg_context())

let bracket_kind_to_string = function
  | BK_PAREN pk    -> "BK_PAREN:"^(paren_kind_to_string pk)
  | BK_TEMPL_PARAM c -> "BK_TEMPL_PARAM"^(templ_param_arg_context_to_string c)
  | BK_TEMPL_ARG c   -> "BK_TEMPL_ARG"^(templ_param_arg_context_to_string c)
  | BK_SUBSCR      -> "BK_SUBSCR"
  | BK_LAM_INTR    -> "BK_LAM_INTR"
  | BK_ATTR        -> "BK_ATTR"
  | BK_OBJC_MSG    -> "BK_OBJC_MSG"
  | BK_BRACE i_opt -> "BK_BRACE:"^(match i_opt with Some i -> string_of_int i | _ -> "")
  | BK_CLASS_BRACE -> "BK_CLASS_BRACE"
  | BK_INI_BRACE   -> "BK_INI_BRACE"
  | BK_REQ_BRACE   -> "BK_REQ_BRACE"

type parsing_mode =
  | M_NORMAL
  | M_STMTS
  | M_DECLS_SUB of string
  | M_MEM_DECLS_SUB of string
  | M_STMTS_SUB of string
  | M_EXPR_SUB of string
  | M_INIT_SUB of string
  | M_TYPE_SUB of string
  | M_SPECS_SUB of string
  | M_DTORS_SUB of string
  | M_ETORS_SUB of string
  | M_OBJC_DECLS_SUB of string

let parsing_mode_to_string = function
  | M_NORMAL -> "M_NORMAL"
  | M_STMTS -> "M_STMTS"
  | M_DECLS_SUB s -> "M_DECLS_SUB:"^s
  | M_MEM_DECLS_SUB s -> "M_MEM_DECLS_SUB:"^s
  | M_STMTS_SUB s -> "M_STMTS_SUB:"^s
  | M_EXPR_SUB s -> "M_EXPR_SUB:"^s
  | M_INIT_SUB s -> "M_INIT_SUB:"^s
  | M_TYPE_SUB s -> "M_TYPE_SUB:"^s
  | M_SPECS_SUB s -> "M_SPECS_SUB:"^s
  | M_DTORS_SUB s -> "M_DTORS_SUB:"^s
  | M_ETORS_SUB s -> "M_ETORS_SUB:"^s
  | M_OBJC_DECLS_SUB s -> "M_OBJC_DECLS_SUB:"^s

type odd_brace_lv_t = { o_lv : int; mutable o_ini_lv : int }
let odd_brace_lv_to_string { o_lv=lv; o_ini_lv=ilv } = sprintf "%d(%d)" lv ilv

let stack_2nd stack =
  let count = ref 0 in
  let y = ref (Stack.top stack) in
  begin
    try
      Stack.iter
        (fun x ->
          incr count;
          if !count = 2 then begin
            y := x;
            raise Exit
          end
        ) stack;
      raise Not_found
    with
      Exit -> ()
  end;
  !y

[%%capture_path
class pstat = object (self)
  val mutable for_flag = false
  val mutable templ_flag = false
  val mutable sizeof_ty_flag = false
  val mutable str_flag = false
  val mutable macro_arg_level = 0
  val mutable end_of_if_head_flag = false
  val mutable pp_line_flag = false
  val mutable pp_if_flag = false
  val mutable pp_ifdef_flag = false
  val mutable pp_ifx_d_level = 0
  val mutable asm_flag = false
  val mutable asm_block_flag = false
  val mutable asm_paren_level = 0
  val mutable braced_asm_flag = false
  val mutable enum_head_flag = false
  val mutable ty_param_flag = false
  val mutable ty_param_rhs_flag = false
  val mutable exec_config_flag = false
  val mutable decltype_flag = false
  val mutable alignas_flag = false
  val mutable alignof_flag = false
  val mutable noexcept_flag = false
  val mutable end_of_id_macro_call_flag = false
  val mutable end_of_literal_macro_call_flag = false
  val mutable end_of_decltype_flag = false
  val mutable trailing_retty_flag = false
  val mutable base_clause_flag = false
  val mutable start_of_func_body_flag = false
  val mutable end_of_old_param_decl_flag = false
  val mutable end_of_class_spec_flag = false
  val mutable end_of_enum_spec_flag = false
  val mutable end_of_cast_type_flag = false
  val mutable stmts_flag = false
  val mutable end_of_templ_head_flag = false
  val mutable end_of_params_flag = false
  val mutable end_of_req_params_flag = false
  val mutable decl_stmt_block_flag = false
  val mutable lambda_dtor_flag = false
  val mutable lambda_intro_flag = false
  val mutable end_of_lambda_templ_flag = false
  val mutable ctor_init_flag = false
  val mutable asm_shader_flag = false
  val mutable dsl_flag = false
  val mutable objc_class_interface_flag = false
  val mutable objc_protocol_decl_flag = false
  val mutable objc_class_flag = false
  val mutable objc_block_flag = false
  val mutable objc_sel_flag = false
  val mutable objc_meth_sel_flag = false
  val mutable objc_meth_decl_flag = false
  val mutable objc_superclass_flag = false
  val mutable objc_cat_flag = false
  val mutable objc_protocol_ref_flag = false
  val mutable end_of_objc_meth_sel_flag = false
  val mutable end_of_objc_meth_type_flag = false
  val mutable end_of_objc_property_attrs_decl_flag = false
  val mutable end_of_objc_protocol_ref_list_flag = false
  val mutable end_of_decl_spec_macro_call_flag = false
  val mutable end_of_attr_macro_call_flag = false
  val mutable end_of_type_macro_call_flag = false
  val mutable dtor_flag = false
  val mutable pp_func_body_odd_flag = false
  val mutable class_name_flag = false
  val mutable broken_flag = false
  val mutable end_of_noptr_dtor_paren_flag = false
  val mutable ns_alias_flag = false
  val mutable old_param_decl_flag = false
  val mutable end_of_sizeof_flag = false
  val mutable end_of_handler_head_flag = false
  val mutable cast_head_flag = false
  val mutable end_of_broken_decl_section_flag = false
  val mutable end_of_label_flag = false
  val mutable end_of_mem_initializer_flag = false
  val mutable attr_flag = false
  val mutable linkage_spec_flag = false
  val mutable condition_flag = false
  val mutable mem_acc_flag = false
  val mutable alias_flag = false
  val mutable using_flag = false
  val mutable mock_qualifier_flag = false
  val mutable end_of_str_section_flag = false
  val mutable new_flag = false
  val mutable concept_flag = false
  val mutable requires_clause_flag = false
  val mutable rhs_flag = false
  val mutable eq_init_flag = false

  val bracket_stack_stack = Stack.create()

  val paren_stack = Stack.create()
  val brace_stack = Stack.create()

  val templ_param_arg_stack = (Stack.create() : int Stack.t)
  val pp_if_section_stack = (Stack.create() : I.pp_if_section_info Stack.t)
  val pp_group_rel_brace_level_stack = (Stack.create() : int ref Stack.t)
  val top_stmts_stack = (Stack.create() : int Stack.t)
  val templ_arg_stack = (Stack.create() : bool Stack.t)
  val odd_brace_lv_stack = (Stack.create() : odd_brace_lv_t Stack.t)

  val mutable last_templ_arg_stack_top = false

  val mutable typename_level = 0
  val mutable braced_init_level = 0
  val mutable bracket_level = 0
  val mutable _pp_if_section_level = 0
  val mutable pp_paren_level = 0
  val mutable objc_message_expr_level = 0

  val mutable brace_level_marker = 0
  val mutable brace_level_marker_flag = false
  val mutable brace_level_marker_unbalanced_flag = false
  val mutable canceled_brace_level_marker = 0
  val mutable pp_line_rel_brace_level = 0

  val mutable last_pp_if_section_info = I.dummy_info

  initializer
    Stack.push (Stack.create() : bracket_kind Stack.t) bracket_stack_stack;
    Stack.push (ref 0) pp_group_rel_brace_level_stack

  method reset () =
    for_flag <- false;
    templ_flag <- false;
    sizeof_ty_flag <- false;
    str_flag <- false;
    macro_arg_level <- 0;
    end_of_if_head_flag <- false;
    pp_line_flag <- false;
    pp_if_flag <- false;
    pp_ifdef_flag <- false;
    pp_ifx_d_level <- 0;
    asm_flag <- false;
    asm_block_flag <- false;
    asm_paren_level <- 0;
    braced_asm_flag <- false;
    enum_head_flag <- false;
    ty_param_flag <- false;
    ty_param_rhs_flag <- false;
    exec_config_flag <- false;
    decltype_flag <- false;
    alignas_flag <- false;
    alignof_flag <- false;
    noexcept_flag <- false;
    start_of_func_body_flag <- false;
    end_of_id_macro_call_flag <- false;
    end_of_literal_macro_call_flag <- false;
    end_of_decltype_flag <- false;
    trailing_retty_flag <- false;
    base_clause_flag <- false;
    end_of_old_param_decl_flag <- false;
    end_of_class_spec_flag <- false;
    end_of_enum_spec_flag <- false;
    end_of_cast_type_flag <- false;
    stmts_flag <- false;
    end_of_templ_head_flag <- false;
    end_of_params_flag <- false;
    end_of_req_params_flag <- false;
    decl_stmt_block_flag <- false;
    lambda_dtor_flag <- false;
    lambda_intro_flag <- false;
    end_of_lambda_templ_flag <- false;
    ctor_init_flag <- false;
    asm_shader_flag <- false;
    dsl_flag <- false;
    objc_class_interface_flag <- false;
    objc_protocol_decl_flag <- false;
    objc_class_flag <- false;
    objc_block_flag <- false;
    objc_sel_flag <- false;
    objc_meth_sel_flag <- false;
    objc_meth_decl_flag <- false;
    objc_superclass_flag <- false;
    objc_cat_flag <- false;
    objc_protocol_ref_flag <- false;
    end_of_objc_meth_sel_flag <- false;
    end_of_objc_meth_type_flag <- false;
    end_of_objc_property_attrs_decl_flag <- false;
    end_of_objc_protocol_ref_list_flag <- false;
    end_of_decl_spec_macro_call_flag <- false;
    end_of_attr_macro_call_flag <- false;
    end_of_type_macro_call_flag <- false;
    dtor_flag <- false;
    pp_func_body_odd_flag <- false;
    class_name_flag <- false;
    broken_flag <- false;
    end_of_noptr_dtor_paren_flag <- false;
    ns_alias_flag <- false;
    old_param_decl_flag <- false;
    end_of_sizeof_flag <- false;
    end_of_handler_head_flag <- false;
    cast_head_flag <- false;
    end_of_broken_decl_section_flag <- false;
    end_of_label_flag <- false;
    end_of_mem_initializer_flag <- false;
    attr_flag <- false;
    linkage_spec_flag <- false;
    condition_flag <- false;
    mem_acc_flag <- false;
    alias_flag <- false;
    using_flag <- false;
    mock_qualifier_flag <- false;
    end_of_str_section_flag <- false;
    new_flag <- false;
    concept_flag <- false;
    requires_clause_flag <- false;
    rhs_flag <- false;
    eq_init_flag <- false;
    Stack.clear bracket_stack_stack;
    Stack.push (Stack.create() : bracket_kind Stack.t) bracket_stack_stack;
    Stack.clear paren_stack;
    Stack.clear brace_stack;
    Stack.clear templ_param_arg_stack;
    Stack.clear pp_if_section_stack;
    Stack.clear pp_group_rel_brace_level_stack;
    Stack.push (ref 0) pp_group_rel_brace_level_stack;
    Stack.clear top_stmts_stack;
    Stack.clear templ_arg_stack;
    Stack.clear odd_brace_lv_stack;
    last_templ_arg_stack_top <- false;
    typename_level <- 0;
    braced_init_level <- 0;
    bracket_level <- 0;
    pp_paren_level <- 0;
    _pp_if_section_level <- 0;
    objc_message_expr_level <- 0;
    brace_level_marker <- 0;
    brace_level_marker_flag <- false;
    brace_level_marker_unbalanced_flag <- false;
    canceled_brace_level_marker <- 0;
    pp_line_rel_brace_level <- 0

  method to_string =
    let l = [
      "paren_lv", self#paren_level;
      "brace_lv", self#brace_level;
      "templ_param_arg_lv", self#templ_param_arg_level;
      "typename_lv", typename_level;
      "braced_init_lv", braced_init_level;
      "bracket_lv", bracket_level;
      "macro_arg_lv", macro_arg_level;
      "odd_brace_lv", self#odd_brace_level;
      "pp_paren_lv", self#pp_paren_level;
      "_pp_if_section_lv", self#_pp_if_section_level;
      "objc_message_expr_lv", objc_message_expr_level;
      "pp_group_rel_brace_lv", self#pp_group_rel_brace_level;
    ]
    in
    sprintf "{%s}"
      (String.concat ";"
         (List.map
            (fun (k, v) ->
              sprintf "%s:%d" k v
            ) (List.filter (fun (_, v) -> v <> 0) l)))

  method copy =
    let bracket_stack_stack_copy =
      let stack_list = ref [] in
      Stack.iter
        (fun bracket_stack ->
          let bracket_stack_copy = Stack.copy bracket_stack in
          stack_list := bracket_stack_copy :: !stack_list
        ) bracket_stack_stack;
      let stack_copy = Stack.create() in
      List.iter (fun x -> Stack.push x stack_copy) !stack_list;
      stack_copy
    in
    {<bracket_stack_stack = bracket_stack_stack_copy;
      paren_stack = Stack.copy paren_stack;
      brace_stack = Stack.copy brace_stack;
      templ_param_arg_stack = Stack.copy templ_param_arg_stack;
      pp_if_section_stack = Stack.copy pp_if_section_stack;
      pp_group_rel_brace_level_stack = Stack.copy pp_group_rel_brace_level_stack;
      top_stmts_stack = Stack.copy top_stmts_stack;
      templ_arg_stack = Stack.copy templ_arg_stack;
      odd_brace_lv_stack = Stack.copy odd_brace_lv_stack;
      >}

  method set_brace_level_marker_flag () =
    [%debug_log "set"];
    brace_level_marker_flag <- true

  method clear_brace_level_marker_flag () =
    [%debug_log "cleared"];
    brace_level_marker_flag <- false;
    brace_level_marker_unbalanced_flag <- false

  method brace_level_marker_flag = brace_level_marker_flag

  method set_brace_level_marker_unbalanced_flag () =
    [%debug_log "set"];
    brace_level_marker_unbalanced_flag <- true

  method clear_brace_level_marker_unbalanced_flag () =
    [%debug_log "cleared"];
    brace_level_marker_unbalanced_flag <- false

  method brace_level_marker_unbalanced_flag = brace_level_marker_unbalanced_flag

  method brace_level_marker = brace_level_marker

  method incr_brace_level_marker () =
    let lv = brace_level_marker in
    let lv1 = lv + 1 in
    [%debug_log "lv=%d -> %d" lv lv1];
    brace_level_marker <- lv1

  method decr_brace_level_marker () =
    let lv = brace_level_marker in
    let lv1 = lv - 1 in
    [%debug_log "lv=%d -> %d" lv lv1];
    brace_level_marker <- lv1

  method canceled_brace_level_marker = canceled_brace_level_marker

  method set_canceled_brace_level_marker lv =
    [%debug_log "lv=%d" lv];
    canceled_brace_level_marker <- lv

  method reset_canceled_brace_level_marker () =
    [%debug_log "@"];
    canceled_brace_level_marker <- 0

  method pp_line_rel_brace_level = pp_line_rel_brace_level

  method incr_pp_line_rel_brace_level () =
    let lv = pp_line_rel_brace_level in
    let lv1 = lv + 1 in
    [%debug_log "lv=%d -> %d" lv lv1];
    pp_line_rel_brace_level <- lv1

  method decr_pp_line_rel_brace_level () =
    let lv = pp_line_rel_brace_level in
    let lv1 = lv - 1 in
    [%debug_log "lv=%d -> %d" lv lv1];
    pp_line_rel_brace_level <- lv1

  method pp_group_rel_brace_level_stack = pp_group_rel_brace_level_stack

  method pp_group_rel_brace_level =
    try
      !(Stack.top pp_group_rel_brace_level_stack)
    with _ -> 0

  method reset_pp_group_rel_brace_level () =
    (Stack.top pp_group_rel_brace_level_stack) := 0

  method incr_pp_group_rel_brace_level () =
    let lv = self#pp_group_rel_brace_level in
    let lv1 = lv + 1 in
    [%debug_log "lv=%d -> %d" lv lv1];
    (Stack.top pp_group_rel_brace_level_stack) := lv1

  method decr_pp_group_rel_brace_level () =
    let lv = self#pp_group_rel_brace_level in
    let lv1 = lv - 1 in
    [%debug_log "lv=%d -> %d" lv lv1];
    (Stack.top pp_group_rel_brace_level_stack) := lv1

  method enter_templ_arg is_type =
    [%debug_log "entering templ_arg (is_type=%B)" is_type];
    Stack.push is_type templ_arg_stack

  method exit_templ_arg () =
    [%debug_log "exiting templ_arg"];
    let is_ty = Stack.pop templ_arg_stack in
    last_templ_arg_stack_top <- is_ty;
    [%debug_log "templ_arg exited (is_type=%B)" is_ty]

  method templ_arg_flag = (Stack.length templ_arg_stack) > 0
  method ty_templ_id_flag =
    try
      Stack.top templ_arg_stack
    with
      _ -> false
  method last_ty_templ_id_flag = last_templ_arg_stack_top

  method set_for_flag () =
    [%debug_log "for_flag set"];
    for_flag <- true

  method clear_for_flag () =
    if for_flag then begin
      [%debug_log "for_flag cleared"];
      for_flag <- false
    end

  method for_flag = for_flag

  method set_templ_flag () =
    [%debug_log "templ_flag set"];
    templ_flag <- true

  method clear_templ_flag () =
    if templ_flag then begin
      [%debug_log "templ_flag cleared"];
      templ_flag <- false
    end

  method templ_flag = templ_flag

  method set_start_of_func_body_flag () =
    [%debug_log "start_of_func_body_flag set"];
    start_of_func_body_flag <- true

  method clear_start_of_func_body_flag () =
    if start_of_func_body_flag then begin
      [%debug_log "start_of_func_body_flag cleared"];
      start_of_func_body_flag <- false
    end

  method start_of_func_body_flag = start_of_func_body_flag

  method set_end_of_old_param_decl_flag () =
    [%debug_log "end_of_old_param_decl_flag set"];
    end_of_old_param_decl_flag <- true

  method clear_end_of_old_param_decl_flag () =
    if end_of_old_param_decl_flag then begin
      [%debug_log "end_of_old_param_decl_flag cleared"];
      end_of_old_param_decl_flag <- false
    end

  method end_of_old_param_decl_flag = end_of_old_param_decl_flag

  method set_end_of_lambda_templ_flag () =
    [%debug_log "end_of_lambda_templ_flag set"];
    end_of_lambda_templ_flag <- true

  method clear_end_of_lambda_templ_flag () =
    if end_of_lambda_templ_flag then begin
      [%debug_log "end_of_lambda_templ_flag cleared"];
      end_of_lambda_templ_flag <- false
    end

  method end_of_lambda_templ_flag = end_of_lambda_templ_flag

  method set_old_param_decl_flag () =
    [%debug_log "old_param_decl_flag set"];
    old_param_decl_flag <- true

  method clear_old_param_decl_flag () =
    if old_param_decl_flag then begin
      [%debug_log "old_param_decl_flag cleared"];
      old_param_decl_flag <- false
    end

  method old_param_decl_flag = old_param_decl_flag

  method set_end_of_class_spec_flag () =
    [%debug_log "end_of_class_spec_flag set"];
    end_of_class_spec_flag <- true

  method clear_end_of_class_spec_flag () =
    if end_of_class_spec_flag then begin
      [%debug_log "end_of_class_spec_flag cleared"];
      end_of_class_spec_flag <- false
    end

  method end_of_class_spec_flag = end_of_class_spec_flag

  method set_end_of_enum_spec_flag () =
    [%debug_log "end_of_enum_spec_flag set"];
    end_of_enum_spec_flag <- true

  method clear_end_of_enum_spec_flag () =
    if end_of_enum_spec_flag then begin
      [%debug_log "end_of_enum_spec_flag cleared"];
      end_of_enum_spec_flag <- false
    end

  method end_of_enum_spec_flag = end_of_enum_spec_flag

  method set_end_of_cast_type_flag () =
    [%debug_log "end_of_cast_type_flag set"];
    end_of_cast_type_flag <- true

  method clear_end_of_cast_type_flag () =
    if end_of_cast_type_flag then begin
      [%debug_log "end_of_cast_type_flag cleared"];
      end_of_cast_type_flag <- false
    end

  method end_of_cast_type_flag = end_of_cast_type_flag

  method set_end_of_templ_head_flag () =
    [%debug_log "end_of_templ_head_flag set"];
    end_of_templ_head_flag <- true

  method clear_end_of_templ_head_flag () =
    if end_of_templ_head_flag then begin
      [%debug_log "end_of_templ_head_flag cleared"];
      end_of_templ_head_flag <- false
    end

  method end_of_templ_head_flag = end_of_templ_head_flag

  method set_end_of_params_flag () =
    [%debug_log "end_of_params_flag set"];
    end_of_params_flag <- true

  method clear_end_of_params_flag () =
    if end_of_params_flag then begin
      [%debug_log "end_of_params_flag cleared"];
      end_of_params_flag <- false
    end

  method end_of_params_flag = end_of_params_flag

  method set_end_of_req_params_flag () =
    [%debug_log "end_of_req_params_flag set"];
    end_of_req_params_flag <- true

  method clear_end_of_req_params_flag () =
    if end_of_req_params_flag then begin
      [%debug_log "end_of_req_params_flag cleared"];
      end_of_req_params_flag <- false
    end

  method end_of_req_params_flag = end_of_req_params_flag

  method set_decl_stmt_block_flag () =
    [%debug_log "decl_stmt_block_flag set"];
    decl_stmt_block_flag <- true

  method clear_decl_stmt_block_flag () =
    if decl_stmt_block_flag then begin
      [%debug_log "decl_stmt_block_flag cleared"];
      decl_stmt_block_flag <- false
    end

  method decl_stmt_block_flag = decl_stmt_block_flag

  method set_lambda_dtor_flag () =
    [%debug_log "lambda_dtor_flag set"];
    lambda_dtor_flag <- true

  method clear_lambda_dtor_flag () =
    if lambda_dtor_flag then begin
      [%debug_log "lambda_dtor_flag cleared"];
      lambda_dtor_flag <- false
    end

  method lambda_dtor_flag = lambda_dtor_flag

  method set_asm_shader_flag () =
    [%debug_log "asm_shader_flag set"];
    asm_shader_flag <- true

  method clear_asm_shader_flag () =
    if asm_shader_flag then begin
      [%debug_log "asm_shader_flag cleared"];
      asm_shader_flag <- false
    end

  method asm_shader_flag = asm_shader_flag

  method set_dsl_flag () =
    [%debug_log "dsl_flag set"];
    dsl_flag <- true

  method clear_dsl_flag () =
    if dsl_flag then begin
      [%debug_log "dsl_flag cleared"];
      dsl_flag <- false
    end

  method dsl_flag = dsl_flag

  method enter_pp_ifx_d () =
    [%debug_log "entering pp_ifx_d"];
    pp_ifx_d_level <- pp_ifx_d_level + 1

  method exit_pp_ifx_d () =
    if pp_ifx_d_level > 0 then begin
      [%debug_log "exiting pp_ifx_d"];
      pp_ifx_d_level <- pp_ifx_d_level - 1
    end

  method pp_ifx_d_level = pp_ifx_d_level
  method pp_ifx_d_flag = pp_ifx_d_level > 0

  method set_objc_class_interface_flag () =
    [%debug_log "objc_class_interface_flag set"];
    objc_class_interface_flag <- true

  method clear_objc_class_interface_flag () =
    if objc_class_interface_flag then begin
      [%debug_log "objc_class_interface_flag cleared"];
      objc_class_interface_flag <- false
    end

  method objc_class_interface_flag = objc_class_interface_flag

  method set_objc_protocol_decl_flag () =
    [%debug_log "objc_protocol_decl_flag set"];
    objc_protocol_decl_flag <- true

  method clear_objc_protocol_decl_flag () =
    if objc_protocol_decl_flag then begin
      [%debug_log "objc_protocol_decl_flag cleared"];
      objc_protocol_decl_flag <- false
    end

  method objc_protocol_decl_flag = objc_protocol_decl_flag

  method set_objc_class_flag () =
    [%debug_log "objc_class_flag set"];
    objc_class_flag <- true

  method clear_objc_class_flag () =
    if objc_class_flag then begin
      [%debug_log "objc_class_flag cleared"];
      objc_class_flag <- false
    end

  method objc_class_flag = objc_class_flag

  method enter_objc_message_expr () =
    [%debug_log "entering objc_message_expr"];
    objc_message_expr_level <- objc_message_expr_level + 1

  method exit_objc_message_expr () =
    if objc_message_expr_level > 0 then begin
      [%debug_log "exiting objc_message_expr"];
      objc_message_expr_level <- objc_message_expr_level - 1
    end

  method objc_message_expr_level = objc_message_expr_level
  method in_objc_message_expr = objc_message_expr_level > 0

  method set_objc_block_flag () =
    [%debug_log "objc_block_flag set"];
    objc_block_flag <- true

  method clear_objc_block_flag () =
    if objc_block_flag then begin
      [%debug_log "objc_block_flag cleared"];
      objc_block_flag <- false
    end

  method objc_block_flag = objc_block_flag

  method set_objc_sel_flag () =
    [%debug_log "objc_sel_flag set"];
    objc_sel_flag <- true

  method clear_objc_sel_flag () =
    if objc_sel_flag then begin
      [%debug_log "objc_sel_flag cleared"];
      objc_sel_flag <- false
    end

  method objc_sel_flag = objc_sel_flag

  method set_objc_meth_sel_flag () =
    [%debug_log "objc_meth_sel_flag set"];
    objc_meth_sel_flag <- true

  method clear_objc_meth_sel_flag () =
    if objc_meth_sel_flag then begin
      [%debug_log "objc_meth_sel_flag cleared"];
      objc_meth_sel_flag <- false
    end

  method objc_meth_sel_flag = objc_meth_sel_flag

  method set_objc_meth_decl_flag () =
    [%debug_log "objc_meth_decl_flag set"];
    objc_meth_decl_flag <- true

  method clear_objc_meth_decl_flag () =
    if objc_meth_decl_flag then begin
      [%debug_log "objc_meth_decl_flag cleared"];
      objc_meth_decl_flag <- false
    end

  method objc_meth_decl_flag = objc_meth_decl_flag

  method set_objc_superclass_flag () =
    [%debug_log "objc_superclass_flag set"];
    objc_superclass_flag <- true

  method clear_objc_superclass_flag () =
    if objc_superclass_flag then begin
      [%debug_log "objc_superclass_flag cleared"];
      objc_superclass_flag <- false
    end

  method objc_superclass_flag = objc_superclass_flag

  method set_objc_cat_flag () =
    [%debug_log "objc_cat_flag set"];
    objc_cat_flag <- true

  method clear_objc_cat_flag () =
    if objc_cat_flag then begin
      [%debug_log "objc_cat_flag cleared"];
      objc_cat_flag <- false
    end

  method objc_cat_flag = objc_cat_flag

  method set_objc_protocol_ref_flag () =
    [%debug_log "objc_protocol_ref_flag set"];
    objc_protocol_ref_flag <- true

  method clear_objc_protocol_ref_flag () =
    if objc_protocol_ref_flag then begin
      [%debug_log "objc_protocol_ref_flag cleared"];
      objc_protocol_ref_flag <- false
    end

  method objc_protocol_ref_flag = objc_protocol_ref_flag

  method set_dtor_flag () =
    [%debug_log "dtor_flag set"];
    dtor_flag <- true

  method clear_dtor_flag () =
    if dtor_flag then begin
      [%debug_log "dtor_flag cleared"];
      dtor_flag <- false
    end

  method dtor_flag = dtor_flag

  method set_pp_func_body_odd_flag () =
    [%debug_log "pp_func_body_odd_flag set"];
    pp_func_body_odd_flag <- true

  method clear_pp_func_body_odd_flag () =
    if pp_func_body_odd_flag then begin
      [%debug_log "pp_func_body_odd_flag cleared"];
      pp_func_body_odd_flag <- false
    end

  method pp_func_body_odd_flag = pp_func_body_odd_flag

  method set_class_name_flag () =
    [%debug_log "class_name_flag set"];
    class_name_flag <- true

  method clear_class_name_flag () =
    if class_name_flag then begin
      [%debug_log "class_name_flag cleared"];
      class_name_flag <- false
    end

  method class_name_flag = class_name_flag

  method set_cast_head_flag () =
    [%debug_log "cast_head_flag set"];
    cast_head_flag <- true

  method clear_cast_head_flag () =
    if cast_head_flag then begin
      [%debug_log "cast_head_flag cleared"];
      cast_head_flag <- false
    end

  method cast_head_flag = cast_head_flag

  method set_broken_flag () =
    [%debug_log "broken_flag set"];
    broken_flag <- true

  method clear_broken_flag () =
    if broken_flag then begin
      [%debug_log "broken_flag cleared"];
      broken_flag <- false
    end

  method broken_flag = broken_flag

  method set_ns_alias_flag () =
    [%debug_log "ns_alias_flag set"];
    ns_alias_flag <- true

  method clear_ns_alias_flag () =
    if ns_alias_flag then begin
      [%debug_log "ns_alias_flag cleared"];
      ns_alias_flag <- false
    end

  method ns_alias_flag = ns_alias_flag

  method set_end_of_objc_meth_sel_flag () =
    [%debug_log "end_of_objc_meth_sel_flag set"];
    end_of_objc_meth_sel_flag <- true

  method clear_end_of_objc_meth_sel_flag () =
    if end_of_objc_meth_sel_flag then begin
      [%debug_log "end_of_objc_meth_sel_flag cleared"];
      end_of_objc_meth_sel_flag <- false
    end

  method end_of_objc_meth_sel_flag = end_of_objc_meth_sel_flag

  method set_end_of_objc_meth_type_flag () =
    [%debug_log "end_of_objc_meth_type_flag set"];
    end_of_objc_meth_type_flag <- true

  method clear_end_of_objc_meth_type_flag () =
    if end_of_objc_meth_type_flag then begin
      [%debug_log "end_of_objc_meth_type_flag cleared"];
      end_of_objc_meth_type_flag <- false
    end

  method end_of_objc_meth_type_flag = end_of_objc_meth_type_flag

  method set_end_of_objc_property_attrs_decl_flag () =
    [%debug_log "end_of_objc_property_attrs_decl_flag set"];
    end_of_objc_property_attrs_decl_flag <- true

  method clear_end_of_objc_property_attrs_decl_flag () =
    if end_of_objc_property_attrs_decl_flag then begin
      [%debug_log "end_of_objc_property_attrs_decl_flag cleared"];
      end_of_objc_property_attrs_decl_flag <- false
    end

  method end_of_objc_property_attrs_decl_flag = end_of_objc_property_attrs_decl_flag

  method set_end_of_objc_protocol_ref_list_flag () =
    [%debug_log "end_of_objc_protocol_ref_list_flag set"];
    end_of_objc_protocol_ref_list_flag <- true

  method clear_end_of_objc_protocol_ref_list_flag () =
    if end_of_objc_protocol_ref_list_flag then begin
      [%debug_log "end_of_objc_protocol_ref_list_flag cleared"];
      end_of_objc_protocol_ref_list_flag <- false
    end

  method end_of_objc_protocol_ref_list_flag = end_of_objc_protocol_ref_list_flag

  method set_end_of_decl_spec_macro_call_flag () =
    [%debug_log "end_of_decl_spec_macro_call_flag set"];
    end_of_decl_spec_macro_call_flag <- true

  method clear_end_of_decl_spec_macro_call_flag () =
    if end_of_decl_spec_macro_call_flag then begin
      [%debug_log "end_of_decl_spec_macro_call_flag cleared"];
      end_of_decl_spec_macro_call_flag <- false
    end

  method end_of_decl_spec_macro_call_flag = end_of_decl_spec_macro_call_flag

  method set_end_of_attr_macro_call_flag () =
    [%debug_log "end_of_attr_macro_call_flag set"];
    end_of_attr_macro_call_flag <- true

  method clear_end_of_attr_macro_call_flag () =
    if end_of_attr_macro_call_flag then begin
      [%debug_log "end_of_attr_macro_call_flag cleared"];
      end_of_attr_macro_call_flag <- false
    end

  method end_of_attr_macro_call_flag = end_of_attr_macro_call_flag

  method set_end_of_type_macro_call_flag () =
    [%debug_log "end_of_type_macro_call_flag set"];
    end_of_type_macro_call_flag <- true

  method clear_end_of_type_macro_call_flag () =
    if end_of_type_macro_call_flag then begin
      [%debug_log "end_of_type_macro_call_flag cleared"];
      end_of_type_macro_call_flag <- false
    end

  method end_of_type_macro_call_flag = end_of_type_macro_call_flag

  method set_str_flag () =
    [%debug_log "str_flag set"];
    str_flag <- true

  method clear_str_flag () =
    if str_flag then begin
      [%debug_log "str_flag cleared"];
      str_flag <- false
    end

  method str_flag = str_flag

  method set_ty_param_rhs_flag () =
    [%debug_log "ty_param_rhs_flag set"];
    ty_param_rhs_flag <- true

  method clear_ty_param_rhs_flag () =
    if ty_param_rhs_flag then begin
      [%debug_log "ty_param_rhs_flag cleared"];
      ty_param_rhs_flag <- false
    end

  method ty_param_rhs_flag = ty_param_rhs_flag

  method set_end_of_if_head_flag () =
    [%debug_log "end_of_if_head_flag set"];
    end_of_if_head_flag <- true

  method clear_end_of_if_head_flag () =
    if end_of_if_head_flag then begin
      [%debug_log "end_of_if_head_flag cleared"];
      end_of_if_head_flag <- false
    end

  method end_of_if_head_flag = end_of_if_head_flag

  method set_trailing_retty_flag () =
    [%debug_log "trailing_retty_flag set"];
    trailing_retty_flag <- true

  method clear_trailing_retty_flag () =
    if trailing_retty_flag then begin
      [%debug_log "trailing_retty_flag cleared"];
      trailing_retty_flag <- false
    end

  method trailing_retty_flag = trailing_retty_flag

  method set_end_of_id_macro_call_flag () =
    [%debug_log "end_of_id_macro_call_flag set"];
    end_of_id_macro_call_flag <- true

  method clear_end_of_id_macro_call_flag () =
    if end_of_id_macro_call_flag then begin
      [%debug_log "end_of_id_macro_call_flag cleared"];
      end_of_id_macro_call_flag <- false
    end

  method end_of_id_macro_call_flag = end_of_id_macro_call_flag

  method set_end_of_literal_macro_call_flag () =
    [%debug_log "end_of_literal_macro_call_flag set"];
    end_of_literal_macro_call_flag <- true

  method clear_end_of_literal_macro_call_flag () =
    if end_of_literal_macro_call_flag then begin
      [%debug_log "end_of_literal_macro_call_flag cleared"];
      end_of_literal_macro_call_flag <- false
    end

  method end_of_literal_macro_call_flag = end_of_literal_macro_call_flag

  method set_end_of_decltype_flag () =
    [%debug_log "end_of_decltype_flag set"];
    end_of_decltype_flag <- true

  method clear_end_of_decltype_flag () =
    if end_of_decltype_flag then begin
      [%debug_log "end_of_decltype_flag cleared"];
      end_of_decltype_flag <- false
    end

  method end_of_decltype_flag = end_of_decltype_flag

  method set_end_of_noptr_dtor_paren_flag () =
    [%debug_log "end_of_noptr_dtor_paren_flag set"];
    end_of_noptr_dtor_paren_flag <- true

  method clear_end_of_noptr_dtor_paren_flag () =
    if end_of_noptr_dtor_paren_flag then begin
      [%debug_log "end_of_noptr_dtor_paren_flag cleared"];
      end_of_noptr_dtor_paren_flag <- false
    end

  method end_of_noptr_dtor_paren_flag = end_of_noptr_dtor_paren_flag

  method set_end_of_sizeof_flag () =
    [%debug_log "end_of_sizeof_flag set"];
    end_of_sizeof_flag <- true

  method clear_end_of_sizeof_flag () =
    if end_of_sizeof_flag then begin
      [%debug_log "end_of_sizeof_flag cleared"];
      end_of_sizeof_flag <- false
    end

  method end_of_sizeof_flag = end_of_sizeof_flag

  method set_end_of_handler_head_flag () =
    [%debug_log "end_of_handler_head_flag set"];
    end_of_handler_head_flag <- true

  method clear_end_of_handler_head_flag () =
    if end_of_handler_head_flag then begin
      [%debug_log "end_of_handler_head_flag cleared"];
      end_of_handler_head_flag <- false
    end

  method end_of_handler_head_flag = end_of_handler_head_flag

  method set_end_of_broken_decl_section_flag () =
    [%debug_log "end_of_broken_decl_section_flag set"];
    end_of_broken_decl_section_flag <- true

  method clear_end_of_broken_decl_section_flag () =
    if end_of_broken_decl_section_flag then begin
      [%debug_log "end_of_broken_decl_section_flag cleared"];
      end_of_broken_decl_section_flag <- false
    end

  method end_of_broken_decl_section_flag = end_of_broken_decl_section_flag

  method set_end_of_label_flag () =
    [%debug_log "end_of_label_flag set"];
    end_of_label_flag <- true

  method clear_end_of_label_flag () =
    if end_of_label_flag then begin
      [%debug_log "end_of_label_flag cleared"];
      end_of_label_flag <- false
    end

  method end_of_label_flag = end_of_label_flag

  method set_end_of_mem_initializer_flag () =
    [%debug_log "end_of_mem_initializer_flag set"];
    end_of_mem_initializer_flag <- true

  method clear_end_of_mem_initializer_flag () =
    if end_of_mem_initializer_flag then begin
      [%debug_log "end_of_mem_initializer_flag cleared"];
      end_of_mem_initializer_flag <- false
    end

  method end_of_mem_initializer_flag = end_of_mem_initializer_flag

  method set_attr_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "attr_flag set"];
      attr_flag <- true
    end

  method clear_attr_flag () =
    if attr_flag then begin
      [%debug_log "attr_flag cleared"];
      attr_flag <- false
    end

  method attr_flag = attr_flag

  method set_linkage_spec_flag () =
    [%debug_log "linkage_spec_flag set"];
    linkage_spec_flag <- true

  method clear_linkage_spec_flag () =
    if linkage_spec_flag then begin
      [%debug_log "linkage_spec_flag cleared"];
      linkage_spec_flag <- false
    end

  method linkage_spec_flag = linkage_spec_flag

  method set_condition_flag () =
    [%debug_log "condition_flag set"];
    condition_flag <- true

  method clear_condition_flag () =
    if condition_flag then begin
      [%debug_log "condition_flag cleared"];
      condition_flag <- false
    end

  method condition_flag = condition_flag

  method set_mem_acc_flag () =
    [%debug_log "mem_acc_flag set"];
    mem_acc_flag <- true

  method clear_mem_acc_flag () =
    if mem_acc_flag then begin
      [%debug_log "mem_acc_flag cleared"];
      mem_acc_flag <- false
    end

  method mem_acc_flag = mem_acc_flag

  method set_alias_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "alias_flag set"];
      alias_flag <- true
    end

  method clear_alias_flag () =
    if alias_flag then begin
      [%debug_log "alias_flag cleared"];
      alias_flag <- false
    end

  method alias_flag = alias_flag

  method set_using_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "using_flag set"];
      using_flag <- true
    end

  method clear_using_flag () =
    if using_flag then begin
      [%debug_log "using_flag cleared"];
      using_flag <- false
    end

  method using_flag = using_flag

  method set_mock_qualifier_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "mock_qualifier_flag set"];
      mock_qualifier_flag <- true
    end

  method clear_mock_qualifier_flag () =
    if mock_qualifier_flag then begin
      [%debug_log "mock_qualifier_flag cleared"];
      mock_qualifier_flag <- false
    end

  method mock_qualifier_flag = mock_qualifier_flag

  method set_end_of_str_section_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "end_of_str_section_flag set"];
      end_of_str_section_flag <- true
    end

  method clear_end_of_str_section_flag () =
    if end_of_str_section_flag then begin
      [%debug_log "end_of_str_section_flag cleared"];
      end_of_str_section_flag <- false
    end

  method end_of_str_section_flag = end_of_str_section_flag

  method set_new_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "new_flag set"];
      new_flag <- true
    end

  method clear_new_flag () =
    if new_flag then begin
      [%debug_log "new_flag cleared"];
      new_flag <- false
    end

  method new_flag = new_flag

  method set_concept_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "concept_flag set"];
      concept_flag <- true
    end

  method clear_concept_flag () =
    if concept_flag then begin
      [%debug_log "concept_flag cleared"];
      concept_flag <- false
    end

  method concept_flag = concept_flag

  method set_requires_clause_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "requires_clause_flag set"];
      requires_clause_flag <- true
    end

  method clear_requires_clause_flag () =
    if requires_clause_flag then begin
      [%debug_log "requires_clause_flag cleared"];
      requires_clause_flag <- false
    end

  method requires_clause_flag = requires_clause_flag

  method set_rhs_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "rhs_flag set"];
      rhs_flag <- true
    end

  method clear_rhs_flag () =
    if rhs_flag then begin
      [%debug_log "rhs_flag cleared"];
      rhs_flag <- false
    end

  method rhs_flag = rhs_flag

  method set_eq_init_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "eq_init_flag set"];
      eq_init_flag <- true
    end

  method clear_eq_init_flag () =
    if eq_init_flag then begin
      [%debug_log "eq_init_flag cleared"];
      eq_init_flag <- false
    end

  method eq_init_flag = eq_init_flag

  method enter_sizeof_ty () =
    [%debug_log "entering sizeof_ty"];
    sizeof_ty_flag <- true

  method exit_sizeof_ty () =
    if sizeof_ty_flag then begin
      [%debug_log "exiting sizeof_ty"];
      sizeof_ty_flag <- false
    end

  method sizeof_ty_flag = sizeof_ty_flag

  method enter_lambda_intro () =
    [%debug_log "entering lambda_intro"];
    lambda_intro_flag <- true

  method exit_lambda_intro () =
    if lambda_intro_flag then begin
      [%debug_log "exiting lambda_intro"];
      lambda_intro_flag <- false
    end

  method lambda_intro_flag = lambda_intro_flag

  method enter_ctor_init () =
    [%debug_log "entering ctor_init"];
    ctor_init_flag <- true

  method exit_ctor_init () =
    if ctor_init_flag then begin
      [%debug_log "exiting ctor_init"];
      ctor_init_flag <- false
    end

  method ctor_init_flag = ctor_init_flag

  method enter_stmts () =
    [%debug_log "entering stmts"];
    stmts_flag <- true

  method exit_stmts () =
    if stmts_flag then begin
      [%debug_log "exiting stmts"];
      stmts_flag <- false
    end

  method stmts_flag = stmts_flag

  method enter_base_clause () =
    [%debug_log "entering base_clause"];
    base_clause_flag <- true

  method exit_base_clause () =
    if base_clause_flag then begin
      [%debug_log "exiting base_clause"];
      base_clause_flag <- false
    end

  method base_clause_flag = base_clause_flag

  method enter_asm plv =
    [%debug_log "entering asm"];
    asm_paren_level <- plv;
    asm_flag <- true

  method exit_asm () =
    if asm_flag then begin
      [%debug_log "exiting asm"];
      asm_paren_level <- 0;
      asm_flag <- false
    end

  method asm_flag = asm_flag
  method asm_paren_level = asm_paren_level

  method enter_braced_asm () =
    [%debug_log "entering braced_asm"];
    braced_asm_flag <- true

  method exit_braced_asm () =
    if braced_asm_flag then begin
      [%debug_log "exiting braced_asm"];
      braced_asm_flag <- false
    end

  method braced_asm_flag = braced_asm_flag

  method enter_asm_block () =
    [%debug_log "entering asm_block"];
    asm_block_flag <- true

  method exit_asm_block () =
    if asm_block_flag then begin
      [%debug_log "exiting asm_block"];
      asm_block_flag <- false
    end

  method asm_block_flag = asm_block_flag

  method enter_enum_head () =
    [%debug_log "entering enum_head"];
    enum_head_flag <- true

  method exit_enum_head () =
    if enum_head_flag then begin
      [%debug_log "exiting enum_head"];
      enum_head_flag <- false
    end

  method enum_head_flag = enum_head_flag

  method enter_ty_param () =
    [%debug_log "entering ty_param"];
    ty_param_flag <- true

  method exit_ty_param () =
    if ty_param_flag then begin
      [%debug_log "exiting ty_param"];
      ty_param_flag <- false
    end

  method ty_param_flag = ty_param_flag

  method enter_exec_config () =
    [%debug_log "entering exec_config"];
    exec_config_flag <- true

  method exit_exec_config () =
    if exec_config_flag then begin
      [%debug_log "exiting exec_config"];
      exec_config_flag <- false
    end

  method exec_config_flag = exec_config_flag

  method enter_decltype () =
    [%debug_log "entering decltype"];
    decltype_flag <- true

  method exit_decltype () =
    if decltype_flag then begin
      [%debug_log "exiting decltype"];
      decltype_flag <- false
    end

  method decltype_flag = decltype_flag

  method enter_alignas () =
    [%debug_log "entering alignas"];
    alignas_flag <- true

  method exit_alignas () =
    if alignas_flag then begin
      [%debug_log "exiting alignas"];
      alignas_flag <- false
    end

  method alignas_flag = alignas_flag

  method enter_alignof () =
    [%debug_log "entering alignof"];
    alignof_flag <- true

  method exit_alignof () =
    if alignof_flag then begin
      [%debug_log "exiting alignof"];
      alignof_flag <- false
    end

  method alignof_flag = alignof_flag

  method enter_noexcept () =
    [%debug_log "entering noexcept"];
    noexcept_flag <- true

  method exit_noexcept () =
    if noexcept_flag then begin
      [%debug_log "exiting noexcept"];
      noexcept_flag <- false
    end

  method noexcept_flag = noexcept_flag

  method enter_macro_arg () =
    [%debug_log "entering macro_arg"];
    macro_arg_level <- macro_arg_level + 1

  method exit_macro_arg () =
    [%debug_log "exiting macro_arg"];
    macro_arg_level <- macro_arg_level - 1

  method macro_arg_level = macro_arg_level
  method macro_arg_flag = macro_arg_level > 0

  method enter_pp_line () =
    [%debug_log "entering pp_line"];
    pp_line_flag <- true;
    pp_line_rel_brace_level <- 0

  method exit_pp_line () =
    if pp_line_flag then begin
      [%debug_log "exiting pp_line"];
      pp_line_flag <- false;
      pp_line_rel_brace_level <- 0
    end

  method pp_line_flag = pp_line_flag

  method enter_pp_if () =
    [%debug_log "entering pp_if"];
    pp_if_flag <- true

  method exit_pp_if () =
    [%debug_log "exiting pp_if"];
    pp_if_flag <- false

  method pp_if_flag = pp_if_flag

  method enter_pp_ifdef () =
    [%debug_log "entering pp_ifdef"];
    pp_ifdef_flag <- true

  method exit_pp_ifdef () =
    [%debug_log "exiting pp_ifdef"];
    pp_ifdef_flag <- false

  method pp_ifdef_flag = pp_ifdef_flag

  method enter_pp_group () =
    [%debug_log "entering:\n%s" self#bracket_stack_to_string];
    Stack.push (Stack.copy self#bracket_stack) bracket_stack_stack

  method exit_pp_group ?(last=false) () =
    [%debug_log "exiting (last=%B):\n%s" last self#bracket_stack_to_string];
    let len = Stack.length bracket_stack_stack in
    if last && len = 1 then
      ()
    else if len > 1 then begin
      let s = Stack.pop bracket_stack_stack in
      if last then begin
        let _ = Stack.pop bracket_stack_stack in
        Stack.push s bracket_stack_stack
      end
    end;
    [%debug_log "after:\n%s" self#bracket_stack_to_string];
    ()

  method enter_pp_if_section ln c sc cond =
    let brace_lv = self#brace_level in
    let paren_lv = self#paren_level in
    let templ_param_arg_lv = self#templ_param_arg_level in
    let info = I.make_pp_if_section_info ln c sc brace_lv paren_lv templ_param_arg_lv cond in
    [%debug_log "entering pp_if_section %s" (I.pp_if_section_info_to_string info)];
    Stack.push info pp_if_section_stack;
    Stack.push (ref 0) pp_group_rel_brace_level_stack;
    self#enter_pp_group()

  method exit_pp_if_section ?(odd=false) () =
    [%debug_log "exiting pp_if_section (odd=%B)..." odd];
    let info = Stack.pop pp_if_section_stack in
    last_pp_if_section_info <- info;
    let _ =
      try
        Stack.pop pp_group_rel_brace_level_stack
      with _ -> ref 0
    in
    if odd && self#pp_odd_if_section_level > 0 then
      (Stack.top odd_brace_lv_stack).o_ini_lv <- info.i_brace_level;
    [%debug_log "pp_if_section exited %s" (I.pp_if_section_info_to_string info)];
    self#exit_pp_group ~last:true ()

  method pp_if_section_stack = pp_if_section_stack

  method pp_if_section_level = Stack.length pp_if_section_stack
  method pp_if_section_top_info = Stack.top pp_if_section_stack

  method last_pp_if_section_info = last_pp_if_section_info

  method pp_if_section_nth_info nth =
    match nth with
    | 1 -> self#pp_if_section_top_info
    | n when n < 0 -> invalid_arg "Cpp.Parser_aux.pstat#pp_if_section_nth_info"
    | _ ->
        let count = ref 0 in
        let res = ref None in
        begin
          try
            Stack.iter
              (fun x ->
                if !count = nth - 1 then begin
                  res := Some x;
                  raise Exit
                end;
                incr count
              ) pp_if_section_stack
          with
            Exit -> ()
        end;
        match !res with
        | Some x -> x
        | _ -> raise Stack.Empty

  method pp_if_section_rel_brace_level =
    let lv =
      try
        self#brace_level - (Stack.top pp_if_section_stack).i_brace_level
      with
        _ -> 0
    in
    [%debug_log "%d" lv];
    lv

  method pp_odd_if_section_rel_brace_level =
    let lv =
      try
        self#brace_level - (Stack.top odd_brace_lv_stack).o_ini_lv
      with
        _ -> 0
    in
    [%debug_log "%d" lv];
    lv

  method pp_if_section_rel_paren_level =
    let lv = self#paren_level - (Stack.top pp_if_section_stack).i_paren_level in
    [%debug_log "%d" lv];
    lv

  method pp_top_label = (Stack.top pp_if_section_stack).i_label

  method set_pp_top_label lab =
    try
      (Stack.top pp_if_section_stack).i_label <- lab
    with
      Stack.Empty -> ()

  method pp_if_section_flag = not (Stack.is_empty pp_if_section_stack)

  method add_pp_elif () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let top = Stack.top pp_if_section_stack in
      top.i_pp_elif <- self#brace_level::top.i_pp_elif
    end

  method pp_elif_flag =
    try
      (Stack.top pp_if_section_stack).i_pp_elif != []
    with
      Stack.Empty -> false

  method add_pp_else () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      (Stack.top pp_if_section_stack).i_pp_else <- Some self#brace_level
    end

  method clear_lbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_lbraces <- 0
    end

  method set_lbrace_info x =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_lbraces <- x
    end

  method get_lbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_lbraces
    end
    else
      0

  method incr_lbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_lbraces <- info.i_lbraces + 1
    end

  method decr_lbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_lbraces <- info.i_lbraces - 1
    end

  method clear_rbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_rbraces <- 0
    end

  method set_rbrace_info x =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_rbraces <- x
    end

  method get_rbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_rbraces
    end
    else
      0

  method incr_rbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_rbraces <- info.i_rbraces + 1
    end

  method decr_rbrace_info () =
    let lv = self#pp_if_section_level in
    [%debug_log "pp_if_section_level=%d" lv];
    if lv > 0 then begin
      let info = Stack.top pp_if_section_stack in
      info.i_rbraces <- info.i_rbraces - 1
    end

  method set_odd_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_odd <- true

  method set_odd_canceled_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_odd_canceled <- true

  method get_odd_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_odd
    with
      _ -> false

  method set_broken_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_broken <- true

  method get_broken_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_broken
    with
      _ -> false

  method set_paren_closing_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_paren_closing <- true

  method get_paren_closing_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_paren_closing
    with
      _ -> false

  method set_brace_paren_closing_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_brace_paren_closing <- true

  method get_brace_paren_closing_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_brace_paren_closing
    with
      _ -> false

  method set_brace_closing_info n =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_brace_closing <- n

  method incr_brace_closing_info() =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_brace_closing <- info.i_brace_closing + 1

  method get_brace_closing_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_brace_closing
    with
      _ -> 0

  method set_brace_opening_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_brace_opening <- true

  method clear_brace_opening_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_brace_opening <- false

  method get_brace_opening_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_brace_opening
    with
      _ -> false

  method set_func_head_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_func_head <- true

  method get_func_head_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_func_head
    with
      _ -> false

  method set_broken_func_head_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_broken_func_head <- true

  method get_broken_func_head_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_broken_func_head
    with
      _ -> false

  method set_templ_closing_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_templ_closing <- true

  method get_templ_closing_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_templ_closing
    with
      _ -> false

  method set_func_body_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_func_body <- true

  method get_func_body_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_func_body
    with
      _ -> false

  method set_semicolon_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_semicolon <- true

  method clear_semicolon_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_semicolon <- false

  method get_semicolon_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_semicolon
    with
      _ -> false

  method set_comma_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_comma <- true

  method get_comma_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_comma
    with
      _ -> false

  method set_cond_expr_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_cond_expr <- true

  method get_cond_expr_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_cond_expr
    with
      _ -> false

  method set_cond_expr__info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_cond_expr_ <- true

  method get_cond_expr__info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_cond_expr_
    with
      _ -> false

  method set_asm_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_asm <- true

  method get_asm_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_asm
    with
      _ -> false

  method set_begin_asm_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_begin_asm <- true

  method get_begin_asm_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_begin_asm
    with
      _ -> false

  method set_lack_of_dtor_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_lack_of_dtor <- true

  method get_lack_of_dtor_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_lack_of_dtor
    with
      _ -> false

  method set_class_brace_opening_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_class_brace_opening <- true

  method get_class_brace_opening_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_class_brace_opening
    with
      _ -> false

  method set_follows_comma_info () =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_follows_comma <- true

  method get_follows_comma_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_follows_comma
    with
      _ -> false

  method get_pp_if_compl_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_pp_if_compl
    with
      _ -> {c_brace=0;c_paren=0}

  method get_pp_if_compl_brace_info () =
    (self#get_pp_if_compl_info()).c_brace

  method get_pp_if_compl_paren_info () =
    (self#get_pp_if_compl_info()).c_paren

  method reset_pp_if_compl_info () =
    try
      let info = Stack.top pp_if_section_stack in
      let c = info.i_pp_if_compl in
      c.c_brace <- 0;
      c.c_paren <- 0
    with
      _ -> ()

  method set_cond_sub_info x =
    let info = Stack.top pp_if_section_stack in
    [%debug_log "%s" (I.pp_if_section_info_to_string info)];
    info.i_cond_sub <- x

  method get_cond_sub_info () =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_cond_sub
    with
      _ -> PP_NONE

  method pp_else_flag =
    try
      (Stack.top pp_if_section_stack).i_pp_else != None
    with
      Stack.Empty -> false

  method alt_pp_branch_flag =
    try
      let info = Stack.top pp_if_section_stack in
      info.i_pp_elif != [] || info.i_pp_else != None
    with
      Stack.Empty -> false

  method check_pp_branch_cond f =
    try
      let info = Stack.top pp_if_section_stack in
      f info.i_cond
    with
      Stack.Empty -> false

  method bracket_stack = Stack.top bracket_stack_stack

  method bracket_stack_top = Stack.top self#bracket_stack

  method bracket_stack_2nd = stack_2nd self#bracket_stack

  method bracket_stack_to_string =
    let buf = Buffer.create 0 in
    Stack.iter
      (fun bk ->
        Buffer.add_string buf (bracket_kind_to_string bk);
        Buffer.add_string buf "\n"
      ) self#bracket_stack;
    Buffer.contents buf

  method _open_bracket bk =
    [%debug_log "opening %s" (bracket_kind_to_string bk)];
    Stack.push bk self#bracket_stack

  method __close_bracket () =
    try
      let bk = Stack.pop self#bracket_stack in
      [%debug_log "closed %s" (bracket_kind_to_string bk)];
      begin
        try
          [%debug_log "top changed to %s" (bracket_kind_to_string (self#bracket_stack_top))]
        with _ -> ()
      end;
      match bk with
      | BK_BRACE i_opt -> i_opt
      | _ -> None
    with
      Stack.Empty -> begin
        [%debug_log "stack empty"];
        None
      end

  method _close_bracket () =
    let _ = self#__close_bracket() in
    ()

  method open_paren k =
    [%debug_log "opening paren (%s)" (paren_kind_to_string k)];
    Stack.push k paren_stack;
    self#_open_bracket (BK_PAREN k)

  method open_paren_normal ?(kind=PKS_NONE) () =
    self#open_paren (PK_NORMAL kind);

  method open_paren_arg () =
    self#open_paren PK_ARG

  method close_paren ?(pseudo=false) () =
    [%debug_log "closing paren (pseudo=%B)..." pseudo];
    let k = Stack.pop paren_stack in
    let _ = k in
    [%debug_log "paren closed (%s)" (paren_kind_to_string k)];
    begin
      try
        [%debug_log "top became %s" (paren_kind_to_string (self#paren_stack_top))]
      with _ -> ()
    end;
    if not pseudo then
      self#_close_bracket()

  method paren_stack_to_string =
    let buf = Buffer.create 0 in
    Stack.iter
      (fun pk ->
        Buffer.add_string buf (paren_kind_to_string pk);
        Buffer.add_string buf "\n"
      ) paren_stack;
    Buffer.contents buf

  method paren_level = Stack.length paren_stack
  method paren_stack_top = Stack.top paren_stack

  method at_ini_brace =
    try
      match self#bracket_stack_top with
      | BK_INI_BRACE -> true
      | _ -> false
    with
      _ -> false

  method at_ini_brace_2 =
    try
      match self#bracket_stack_2nd with
      | BK_INI_BRACE -> true
      | _ -> false
    with
      _ -> false

  method at_class_brace =
    try
      match self#bracket_stack_top with
      | BK_CLASS_BRACE -> true
      | _ -> false
    with
      _ -> false

  method at_brace =
    try
      match self#bracket_stack_top with
      | BK_BRACE _ -> true
      | _ -> false
    with
      _ -> false

  method at_brace_2 =
    try
      match self#bracket_stack_2nd with
      | BK_BRACE _ -> true
      | _ -> false
    with
      _ -> false

  method at_req_brace =
    try
      match self#bracket_stack_top with
      | BK_REQ_BRACE -> true
      | _ -> false
    with
      _ -> false

  method at_objc_msg =
    try
      match self#bracket_stack_top with
      | BK_OBJC_MSG -> true
      | _ -> false
    with
      _ -> false

  method at_attr =
    try
      match self#bracket_stack_top with
      | BK_ATTR -> true
      | _ -> false
    with
      _ -> false

  method at_lam_intr =
    try
      match self#bracket_stack_top with
      | BK_LAM_INTR -> true
      | _ -> false
    with
      _ -> false

  method at_subscr =
    try
      match self#bracket_stack_top with
      | BK_SUBSCR -> true
      | _ -> false
    with
      _ -> false

  method at_templ_arg =
    try
      match self#bracket_stack_top with
      | BK_TEMPL_ARG _ -> true
      | _ -> false
    with
      _ -> false

  method at_templ_arg_2 =
    try
      match self#bracket_stack_2nd with
      | BK_TEMPL_ARG _ -> true
      | _ -> false
    with
      _ -> false

  method at_templ_param =
    try
      match self#bracket_stack_top with
      | BK_TEMPL_PARAM _ -> true
      | _ -> false
    with
      _ -> false

  method at_templ_param_2 =
    try
      match self#bracket_stack_2nd with
      | BK_TEMPL_PARAM _ -> true
      | _ -> false
    with
      _ -> false

  method at_templ_param_arg_expr_2 =
    try
      match self#bracket_stack_2nd with
      | BK_TEMPL_PARAM c | BK_TEMPL_ARG c when c.tpac_expr_flag -> true
      | _ -> false
    with
      _ -> false

  method private _at_paren =
    try
      match self#bracket_stack_top with
      | BK_PAREN _ -> true
      | _ -> false
    with
      _ -> true

  method at_arg_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_ARG -> true
      | _ -> false
    with
      _ -> false

  method at_arg_paren_2 =
    try
      match self#bracket_stack_2nd with
      | BK_PAREN PK_ARG -> true
      | _ -> false
    with
      _ -> false

  method at_macro_arg_paren_2 =
    try
      match self#bracket_stack_2nd with
      | BK_PAREN PK_MACRO -> true
      | _ -> false
    with
      _ -> false

  method _arg_paren_flag =
    try
      Stack.iter
        (function
          | PK_ARG -> raise Exit
          | _ -> ()
        ) paren_stack;
      false
    with
      Exit -> true

  method at_ps_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_PS -> true
      | _ -> false
    with
      _ -> false

  method at_type_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_TYPE _ -> true
      | _ -> false
    with
      _ -> false

  method at_type_paren_2 =
    try
      match self#bracket_stack_2nd with
      | BK_PAREN (PK_TYPE _) -> true
      | _ -> false
    with
      _ -> false

  method was_at_type_paren =
    try
      match stack_2nd paren_stack with
      | PK_TYPE _ -> true
      | _ -> false
    with
      _ -> false

  method at_fold_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_FOLD -> true
      | _ -> false
    with
      _ -> false

  method at_fold_paren_2 =
    try
      match self#bracket_stack_2nd with
      | BK_PAREN PK_FOLD -> true
      | _ -> false
    with
      _ -> false

  method at_macro_arg_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_MACRO | PK_SS -> true
      | _ -> false
    with
      _ -> false

  method at_ss_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_SS -> true
      | _ -> false
    with
      _ -> false

  method at_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_NORMAL _ -> true
      | _ -> false
    with
      _ -> false

  method at_paren_2 =
    try
      match self#bracket_stack_2nd with
      | BK_PAREN PK_NORMAL _ -> true
      | _ -> false
    with
      _ -> false

  method at_if_paren =
    self#_at_paren &&
    try
      match Stack.top paren_stack with
      | PK_NORMAL PKS_IF -> true
      | _ -> false
    with
      _ -> false

  method at_bracket =
    try
      match Stack.top paren_stack with
      | PK_BRACKET -> true
      | _ -> false
    with
      _ -> false

  method change_paren_kind pk =
    try
      let k = Stack.pop paren_stack in
      [%debug_log "%s -> %s" (paren_kind_to_string k) (paren_kind_to_string pk)];
      ignore k;
      Stack.push pk paren_stack
    with _ -> ()

  method get_paren_stack () = Stack.copy paren_stack

  method enter_top_stmts lv =
    [%debug_log "entering top_stmts (%d)" lv];
    Stack.push lv top_stmts_stack

  method exit_top_stmts () =
    [%debug_log "exitsing top_stmts..."];
    let lv = Stack.pop top_stmts_stack in
    let _ = lv in
    [%debug_log "top_stmts exited (%d)" lv]

  method top_stmts_flag =
    Stack.length top_stmts_stack > 0

  method top_stmts_top =
    let lv = Stack.top top_stmts_stack in
    [%debug_log "%d" lv];
    lv

  method enter_templ_param_arg () =
    if not self#dsl_flag then begin
      [%debug_log "entering templ_param_arg"];
      Stack.push self#paren_level templ_param_arg_stack
    end

  method exit_templ_param_arg () =
    if not self#dsl_flag then begin
      [%debug_log "exiting templ_param_arg"];
      let lv = Stack.pop templ_param_arg_stack in
      let _ = lv in
      [%debug_log "templ_param_arg exited (%d)" lv]
    end

  method templ_param_arg_level = Stack.length templ_param_arg_stack
  method templ_param_arg_stack_top = Stack.top templ_param_arg_stack
  method get_templ_param_arg_stack() = Stack.copy templ_param_arg_stack

  method enter_typename () =
    [%debug_log "entering typename"];
    typename_level <- typename_level + 1

  method exit_typename () =
    [%debug_log "exiting typename"];
    typename_level <- typename_level - 1

  method set_typename_level lv = typename_level <- lv
  method reset_typename_level () = typename_level <- 0

  method typename_level = typename_level
  method typename_flag = typename_level > 0

  method enter_braced_init () =
    [%debug_log "entering braced_init"];
    braced_init_level <- braced_init_level + 1

  method exit_braced_init () =
    [%debug_log "exiting braced_init"];
    braced_init_level <- braced_init_level - 1

  method set_braced_init_level lv = braced_init_level <- lv
  method reset_braced_init_level () = braced_init_level <- 0

  method braced_init_level = braced_init_level
  method braced_init_flag = braced_init_level > 0

  method enter__pp_if_section () =
    [%debug_log "entering _pp_if_section"];
    _pp_if_section_level <- _pp_if_section_level + 1

  method exit__pp_if_section () =
    [%debug_log "exiting _pp_if_section"];
    _pp_if_section_level <- _pp_if_section_level - 1

  method set__pp_if_section_level lv = _pp_if_section_level <- lv
  method reset__pp_if_section_level () = _pp_if_section_level <- 0

  method _pp_if_section_level = _pp_if_section_level
  method _pp_if_section_flag = _pp_if_section_level > 0

  method open_brace () =
    [%debug_log "opening brace"];
    Stack.push self#paren_level brace_stack

  method close_brace () =
    [%debug_log "closing brace"];
    let plv = Stack.pop brace_stack in
    let _ = plv in
    [%debug_log "brace closed (%d)" plv]

  method brace_level = Stack.length brace_stack

  method rel_paren_level =
    let lv =
      try
        self#paren_level - (Stack.top brace_stack)
      with
        _ -> 0
    in
    [%debug_log "%d" lv];
    lv

  method open_bracket () =
    [%debug_log "opening bracket"];
    bracket_level <- bracket_level + 1

  method close_bracket () =
    [%debug_log "closing bracket"];
    bracket_level <- bracket_level - 1

  method bracket_level = bracket_level
  method set_bracket_level lv = bracket_level <- lv

  method open_pp_paren () =
    [%debug_log "opening pp_paren"];
    pp_paren_level <- pp_paren_level + 1

  method close_pp_paren () =
    [%debug_log "closing pp_paren"];
    pp_paren_level <- pp_paren_level - 1

  method pp_paren_level = pp_paren_level
  method set_pp_paren_level lv = pp_paren_level <- lv

  method odd_brace_lv_stack_to_string =
    let buf = Buffer.create 0 in
    Stack.iter
      (fun oblv -> Buffer.add_string buf (odd_brace_lv_to_string oblv))
      odd_brace_lv_stack;
    Buffer.contents buf

  method open_odd_brace () =
    [%debug_log "odd_brace_lv_stack=%s" self#odd_brace_lv_stack_to_string];
    [%debug_log "brace_level=%d" self#brace_level];
    Stack.push {o_lv=self#brace_level;o_ini_lv=0} odd_brace_lv_stack

  method close_odd_brace () =
    [%debug_log "odd_brace_lv_stack=%s" self#odd_brace_lv_stack_to_string];
    let oblv = Stack.pop odd_brace_lv_stack in
    [%debug_log "brace_level=%s" (odd_brace_lv_to_string oblv)];
    ignore oblv

  method pp_odd_if_section_level = Stack.length odd_brace_lv_stack

  method odd_brace_level =
    try
      (Stack.top odd_brace_lv_stack).o_lv
    with
      _ -> 0

end (* class pstat *)
]

class dummy_pstat = object
  inherit pstat
  method! reset () = ()
  method! to_string = "<dummy_pstat>"
  method! copy = {<>}
  method! set_brace_level_marker_flag () = ()
  method! clear_brace_level_marker_flag () = ()
  method! brace_level_marker_flag = false
  method! set_brace_level_marker_unbalanced_flag () = ()
  method! clear_brace_level_marker_unbalanced_flag () = ()
  method! brace_level_marker_unbalanced_flag = false
  method! brace_level_marker = 0
  method! incr_brace_level_marker () = ()
  method! decr_brace_level_marker () = ()
  method! canceled_brace_level_marker = 0
  method! set_canceled_brace_level_marker _ = ()
  method! reset_canceled_brace_level_marker () = ()
  method! pp_line_rel_brace_level = 0
  method! incr_pp_line_rel_brace_level () = ()
  method! decr_pp_line_rel_brace_level () = ()
  method! reset_pp_group_rel_brace_level () = ()
  method! incr_pp_group_rel_brace_level () = ()
  method! decr_pp_group_rel_brace_level () = ()
  method! enter_templ_arg _ = ()
  method! exit_templ_arg () = ()
  method! templ_arg_flag = false
  method! ty_templ_id_flag = false
  method! last_ty_templ_id_flag = false
  method! set_for_flag () = ()
  method! clear_for_flag () = ()
  method! set_templ_flag () = ()
  method! clear_templ_flag () = ()
  method! for_flag = false
  method! templ_flag = false
  method! set_start_of_func_body_flag () = ()
  method! clear_start_of_func_body_flag () = ()
  method! start_of_func_body_flag = false
  method! set_end_of_old_param_decl_flag () = ()
  method! clear_end_of_old_param_decl_flag () = ()
  method! end_of_old_param_decl_flag = false
  method! set_old_param_decl_flag () = ()
  method! clear_old_param_decl_flag () = ()
  method! old_param_decl_flag = false
  method! set_end_of_class_spec_flag () = ()
  method! clear_end_of_class_spec_flag () = ()
  method! end_of_class_spec_flag = false
  method! set_end_of_enum_spec_flag () = ()
  method! clear_end_of_enum_spec_flag () = ()
  method! end_of_enum_spec_flag = false
  method! set_end_of_cast_type_flag () = ()
  method! clear_end_of_cast_type_flag () = ()
  method! end_of_cast_type_flag = false
  method! set_end_of_templ_head_flag () = ()
  method! clear_end_of_templ_head_flag () = ()
  method! end_of_templ_head_flag = false
  method! set_end_of_params_flag () = ()
  method! clear_end_of_params_flag () = ()
  method! end_of_params_flag = false
  method! set_end_of_req_params_flag () = ()
  method! clear_end_of_req_params_flag () = ()
  method! end_of_req_params_flag = false
  method! set_decl_stmt_block_flag () = ()
  method! clear_decl_stmt_block_flag () = ()
  method! decl_stmt_block_flag = false
  method! set_lambda_dtor_flag () = ()
  method! clear_lambda_dtor_flag () = ()
  method! lambda_dtor_flag = false
  method! set_asm_shader_flag () = ()
  method! clear_asm_shader_flag () = ()
  method! asm_shader_flag = false
  method! set_dsl_flag () = ()
  method! clear_dsl_flag () = ()
  method! dsl_flag = false
  method! enter_pp_ifx_d () = ()
  method! exit_pp_ifx_d () = ()
  method! pp_ifx_d_level = 0
  method! pp_ifx_d_flag = false
  method! set_objc_class_interface_flag () = ()
  method! clear_objc_class_interface_flag () = ()
  method! objc_class_interface_flag = false
  method! set_objc_protocol_decl_flag () = ()
  method! clear_objc_protocol_decl_flag () = ()
  method! objc_protocol_decl_flag = false
  method! set_objc_class_flag () = ()
  method! clear_objc_class_flag () = ()
  method! objc_class_flag = false
  method! enter_objc_message_expr () = ()
  method! exit_objc_message_expr () = ()
  method! objc_message_expr_level = 0
  method! in_objc_message_expr = false
  method! set_objc_block_flag () = ()
  method! clear_objc_block_flag () = ()
  method! objc_block_flag = false
  method! set_objc_sel_flag () = ()
  method! clear_objc_sel_flag () = ()
  method! objc_sel_flag = false
  method! set_objc_meth_sel_flag () = ()
  method! clear_objc_meth_sel_flag () = ()
  method! objc_meth_sel_flag = false
  method! set_objc_meth_decl_flag () = ()
  method! clear_objc_meth_decl_flag () = ()
  method! objc_meth_decl_flag = false
  method! set_objc_superclass_flag () = ()
  method! clear_objc_superclass_flag () = ()
  method! objc_superclass_flag = false
  method! set_objc_cat_flag () = ()
  method! clear_objc_cat_flag () = ()
  method! objc_cat_flag = false
  method! set_objc_protocol_ref_flag () = ()
  method! clear_objc_protocol_ref_flag () = ()
  method! objc_protocol_ref_flag = false
  method! set_dtor_flag () = ()
  method! clear_dtor_flag () = ()
  method! dtor_flag = false
  method! set_pp_func_body_odd_flag () = ()
  method! clear_pp_func_body_odd_flag () = ()
  method! pp_func_body_odd_flag = false
  method! set_class_name_flag () = ()
  method! clear_class_name_flag () = ()
  method! class_name_flag = false
  method! set_cast_head_flag () = ()
  method! clear_cast_head_flag () = ()
  method! cast_head_flag = false
  method! set_broken_flag () = ()
  method! clear_broken_flag () = ()
  method! broken_flag = false
  method! set_ns_alias_flag () = ()
  method! clear_ns_alias_flag () = ()
  method! ns_alias_flag = false
  method! set_end_of_objc_meth_sel_flag () = ()
  method! clear_end_of_objc_meth_sel_flag () = ()
  method! end_of_objc_meth_sel_flag = false
  method! set_end_of_objc_meth_type_flag () = ()
  method! clear_end_of_objc_meth_type_flag () = ()
  method! end_of_objc_meth_type_flag = false
  method! set_end_of_objc_property_attrs_decl_flag () = ()
  method! clear_end_of_objc_property_attrs_decl_flag () = ()
  method! end_of_objc_property_attrs_decl_flag = false
  method! set_end_of_objc_protocol_ref_list_flag () = ()
  method! clear_end_of_objc_protocol_ref_list_flag () = ()
  method! end_of_objc_protocol_ref_list_flag = false
  method! set_end_of_decl_spec_macro_call_flag () = ()
  method! clear_end_of_decl_spec_macro_call_flag () = ()
  method! end_of_decl_spec_macro_call_flag = false
  method! set_end_of_attr_macro_call_flag () = ()
  method! clear_end_of_attr_macro_call_flag () = ()
  method! end_of_attr_macro_call_flag = false
  method! set_end_of_type_macro_call_flag () = ()
  method! clear_end_of_type_macro_call_flag () = ()
  method! end_of_type_macro_call_flag = false
  method! set_str_flag () = ()
  method! clear_str_flag () = ()
  method! str_flag = false
  method! set_ty_param_rhs_flag () = ()
  method! clear_ty_param_rhs_flag () = ()
  method! ty_param_rhs_flag = false
  method! set_end_of_if_head_flag () = ()
  method! clear_end_of_if_head_flag () = ()
  method! end_of_if_head_flag = false
  method! set_trailing_retty_flag () = ()
  method! clear_trailing_retty_flag () = ()
  method! trailing_retty_flag = false
  method! set_end_of_id_macro_call_flag () = ()
  method! clear_end_of_id_macro_call_flag () = ()
  method! end_of_id_macro_call_flag = false
  method! set_end_of_literal_macro_call_flag () = ()
  method! clear_end_of_literal_macro_call_flag () = ()
  method! end_of_literal_macro_call_flag = false
  method! set_end_of_decltype_flag () = ()
  method! clear_end_of_decltype_flag () = ()
  method! end_of_decltype_flag = false
  method! set_end_of_noptr_dtor_paren_flag () = ()
  method! clear_end_of_noptr_dtor_paren_flag () = ()
  method! end_of_noptr_dtor_paren_flag = false
  method! set_end_of_sizeof_flag () = ()
  method! clear_end_of_sizeof_flag () = ()
  method! end_of_sizeof_flag = false
  method! set_end_of_handler_head_flag () = ()
  method! clear_end_of_handler_head_flag () = ()
  method! end_of_handler_head_flag = false
  method! set_end_of_broken_decl_section_flag () = ()
  method! clear_end_of_broken_decl_section_flag () = ()
  method! end_of_broken_decl_section_flag = false
  method! set_end_of_label_flag () = ()
  method! clear_end_of_label_flag () = ()
  method! end_of_label_flag = false
  method! set_end_of_mem_initializer_flag () = ()
  method! clear_end_of_mem_initializer_flag () = ()
  method! end_of_mem_initializer_flag = false
  method! set_attr_flag () = ()
  method! clear_attr_flag () = ()
  method! attr_flag = false
  method! set_linkage_spec_flag () = ()
  method! clear_linkage_spec_flag () = ()
  method! linkage_spec_flag = false
  method! set_condition_flag () = ()
  method! clear_condition_flag () = ()
  method! condition_flag = false
  method! set_mem_acc_flag () = ()
  method! clear_mem_acc_flag () = ()
  method! mem_acc_flag = false
  method! set_alias_flag () = ()
  method! clear_alias_flag () = ()
  method! alias_flag = false
  method! set_using_flag () = ()
  method! clear_using_flag () = ()
  method! using_flag = false
  method! set_mock_qualifier_flag () = ()
  method! clear_mock_qualifier_flag () = ()
  method! mock_qualifier_flag = false
  method! set_end_of_str_section_flag () = ()
  method! clear_end_of_str_section_flag () = ()
  method! end_of_str_section_flag = false
  method! set_new_flag () = ()
  method! clear_new_flag () = ()
  method! new_flag = false
  method! set_concept_flag () = ()
  method! clear_concept_flag () = ()
  method! concept_flag = false
  method! set_requires_clause_flag () = ()
  method! clear_requires_clause_flag () = ()
  method! requires_clause_flag = false
  method! set_rhs_flag () = ()
  method! clear_rhs_flag () = ()
  method! rhs_flag = false
  method! set_eq_init_flag () = ()
  method! clear_eq_init_flag () = ()
  method! eq_init_flag = false
  method! enter_sizeof_ty () = ()
  method! exit_sizeof_ty () = ()
  method! sizeof_ty_flag = false
  method! enter_lambda_intro () = ()
  method! exit_lambda_intro () = ()
  method! lambda_intro_flag = false
  method! enter_ctor_init () = ()
  method! exit_ctor_init () = ()
  method! ctor_init_flag = false
  method! enter_stmts () = ()
  method! exit_stmts () = ()
  method! stmts_flag = false
  method! enter_base_clause () = ()
  method! exit_base_clause () = ()
  method! base_clause_flag = false
  method! enter_asm _ = ()
  method! exit_asm () = ()
  method! asm_flag = false
  method! asm_paren_level = 0
  method! enter_braced_asm () = ()
  method! exit_braced_asm () = ()
  method! braced_asm_flag = false
  method! enter_asm_block () = ()
  method! exit_asm_block () = ()
  method! asm_block_flag = false
  method! enter_enum_head () = ()
  method! exit_enum_head () = ()
  method! enum_head_flag = false
  method! enter_ty_param () = ()
  method! exit_ty_param () = ()
  method! ty_param_flag = false
  method! enter_exec_config () = ()
  method! exit_exec_config () = ()
  method! exec_config_flag = false
  method! enter_decltype () = ()
  method! exit_decltype () = ()
  method! decltype_flag = false
  method! enter_alignas () = ()
  method! exit_alignas () = ()
  method! alignas_flag = false
  method! enter_alignof () = ()
  method! exit_alignof () = ()
  method! alignof_flag = false
  method! enter_noexcept () = ()
  method! exit_noexcept () = ()
  method! noexcept_flag = false
  method! enter_macro_arg () = ()
  method! exit_macro_arg () = ()
  method! macro_arg_level = 0
  method! macro_arg_flag = false
  method! enter_pp_line () = ()
  method! exit_pp_line () = ()
  method! pp_line_flag = false
  method! enter_pp_if () = ()
  method! exit_pp_if () = ()
  method! pp_if_flag = false
  method! enter_pp_ifdef () = ()
  method! exit_pp_ifdef () = ()
  method! pp_ifdef_flag = false
  method! enter_pp_group () = ()
  method! exit_pp_group ?(last=false) () = ignore last
  method! enter_pp_if_section _ _ _ _ = ()
  method! exit_pp_if_section ?(odd=false) () = ignore odd
  method! pp_if_section_stack = Stack.create()
  method! pp_group_rel_brace_level_stack = Stack.create()
  method! pp_if_section_level = 0
  method! pp_if_section_top_info = assert false
  method! last_pp_if_section_info = assert false
  method! pp_if_section_nth_info _ = assert false
  method! pp_if_section_rel_brace_level = 0
  method! pp_odd_if_section_rel_brace_level = 0
  method! pp_if_section_rel_paren_level = 0
  method! pp_top_label = L.DUMMY
  method! set_pp_top_label _ = ()
  method! pp_if_section_flag = false
  method! add_pp_elif () = ()
  method! pp_elif_flag = false
  method! add_pp_else () = ()
  method! clear_lbrace_info () = ()
  method! set_lbrace_info _ = ()
  method! get_lbrace_info () = 0
  method! incr_lbrace_info () = ()
  method! decr_lbrace_info () = ()
  method! clear_rbrace_info () = ()
  method! set_rbrace_info _ = ()
  method! get_rbrace_info () = 0
  method! incr_rbrace_info () = ()
  method! decr_rbrace_info () = ()
  method! set_odd_info () = ()
  method! set_odd_canceled_info () = ()
  method! get_odd_info () = false
  method! set_broken_info () = ()
  method! get_broken_info () = false
  method! set_paren_closing_info () = ()
  method! get_paren_closing_info () = false
  method! set_brace_paren_closing_info () = ()
  method! get_brace_paren_closing_info () = false
  method! set_brace_closing_info _ = ()
  method! incr_brace_closing_info() = ()
  method! get_brace_closing_info () = 0
  method! set_brace_opening_info () = ()
  method! clear_brace_opening_info () = ()
  method! get_brace_opening_info () = false
  method! set_func_head_info () = ()
  method! get_func_head_info () = false
  method! set_broken_func_head_info () = ()
  method! get_broken_func_head_info () = false
  method! set_templ_closing_info () = ()
  method! get_templ_closing_info () = false
  method! set_func_body_info () = ()
  method! get_func_body_info () = false
  method! set_semicolon_info () = ()
  method! clear_semicolon_info () = ()
  method! get_semicolon_info () = false
  method! set_comma_info () = ()
  method! get_comma_info () = false
  method! set_cond_expr_info () = ()
  method! get_cond_expr_info () = false
  method! set_cond_expr__info () = ()
  method! get_cond_expr__info () = false
  method! set_asm_info () = ()
  method! get_asm_info () = false
  method! set_begin_asm_info () = ()
  method! get_begin_asm_info () = false
  method! set_lack_of_dtor_info () = ()
  method! get_lack_of_dtor_info () = false
  method! set_class_brace_opening_info () = ()
  method! get_class_brace_opening_info () = false
  method! set_follows_comma_info () = ()
  method! get_follows_comma_info () = false
  method! get_pp_if_compl_info () = {Pinfo.c_brace=0;Pinfo.c_paren=0}
  method! get_pp_if_compl_brace_info () = 0
  method! get_pp_if_compl_paren_info () = 0
  method! reset_pp_if_compl_info () = ()
  method! set_cond_sub_info _ = ()
  method! get_cond_sub_info () = Pinfo.PP_NONE
  method! pp_else_flag = false
  method! alt_pp_branch_flag = false
  method! check_pp_branch_cond _ = false
  method! bracket_stack = Stack.create()
  method! bracket_stack_top = BK_SUBSCR
  method! bracket_stack_to_string = ""
  method! _open_bracket (_ : bracket_kind) = ()
  method! _close_bracket () = ()
  method! open_paren _ = ()
  method! open_paren_normal ?(kind=PKS_NONE) () = ignore kind
  method! open_paren_arg () = ()
  method! close_paren ?(pseudo=false) () = ignore pseudo
  method! paren_level = 0
  method! paren_stack_top = PK_NORMAL PKS_NONE
  method! at_arg_paren = false
  method! at_arg_paren_2 = false
  method! _arg_paren_flag = false
  method! at_type_paren = false
  method! at_type_paren_2 = false
  method! at_fold_paren = false
  method! at_fold_paren_2 = false
  method! at_macro_arg_paren = false
  method! at_macro_arg_paren_2 = false
  method! at_paren = false
  method! at_paren_2 = false
  method! at_if_paren = false
  method! at_bracket = false
  method! change_paren_kind _ = ()
  method! get_paren_stack () = Stack.create()
  method! enter_top_stmts _ = ()
  method! exit_top_stmts () = ()
  method! top_stmts_flag = false
  method! top_stmts_top = 0
  method! enter_templ_param_arg () = ()
  method! exit_templ_param_arg () = ()
  method! templ_param_arg_level = 0
  method! templ_param_arg_stack_top = 0
  method! get_templ_param_arg_stack() = Stack.create()
  method! enter_typename () = ()
  method! exit_typename () = ()
  method! set_typename_level _ = ()
  method! reset_typename_level () = ()
  method! typename_level = 0
  method! typename_flag = false
  method! enter_braced_init () = ()
  method! exit_braced_init () = ()
  method! set_braced_init_level _ = ()
  method! reset_braced_init_level () = ()
  method! braced_init_level = 0
  method! braced_init_flag = false
  method! enter__pp_if_section () = ()
  method! exit__pp_if_section () = ()
  method! set__pp_if_section_level _ = ()
  method! reset__pp_if_section_level () = ()
  method! _pp_if_section_level = 0
  method! _pp_if_section_flag = false
  method! open_brace () = ()
  method! close_brace () = ()
  method! brace_level = 0
  method! rel_paren_level = 0
  method! open_bracket () = ()
  method! close_bracket () = ()
  method! bracket_level = 0
  method! set_bracket_level _ = ()
  method! open_pp_paren () = ()
  method! close_pp_paren () = ()
  method! pp_paren_level = 0
  method! set_pp_paren_level _ = ()
  method! odd_brace_lv_stack_to_string = ""
  method! open_odd_brace () = ()
  method! close_odd_brace () = ()
  method! pp_odd_if_section_level = 0
  method! odd_brace_level = 0

end

class dummy_stack = object (self)
  inherit N.stack

  method! enter_block ?(prefix="") ?(qname="") ?(no_tweak=false) _ =
    ignore prefix; ignore qname; ignore no_tweak

  method! exit_block () = ()
  method! enter_class _ = ()
  method! exit_class () = ()
  method! enter_template () = ()
  method! exit_template () = ()
  method! enter_namespace _ = ()
  method! exit_namespace () = self#top
  method! enter_enum _ = ()
  method! exit_enum () = ()
end

[%%capture_path
class env = object (self)
  inherit [Source.c] Env_base.c as super

  val bidgen = new BID.generator

  val mutable stack = new N.stack
  val mutable saved_stack = new N.stack
  val mutable top_frame = new N.stack_frame N.Scope.Top
  val mutable dtor_node = Ast.dummy_node

  val mutable lex_line_head_flag = true
  val mutable lex_pp_line_flag = false
  val mutable lex_ms_asm_line_flag = false
  val mutable pp_define_flag = false
  val mutable pp_define_body_flag = false
  val mutable pp_odd_flag = false
  val mutable pp_params_flag = false
  val mutable body_head_flag = false
  val mutable cast_key_flag = false
  val mutable conv_func_id_flag = false
  val mutable expr_flag = false
  val mutable for_range_init_flag = false
  val mutable in_body_brace_flag = false
  val mutable init_flag = false
  val mutable param_head_flag = false
  val mutable ty_param_key_flag = false
  val mutable typedef_flag = false
  val mutable using_ns_flag = false
  val mutable virtual_func_flag = false
  val mutable value_flag = false
  val mutable dtor_if_section_flag = false
  val mutable objc_flag = false

  val templ_head_stack = (Stack.create() : int Stack.t)
  val const_stack = Stack.create()

  val mutable in_body_brace_level = 0

  val mutable pstat = new pstat

  val pending_macro_tbl = (Hashtbl.create 0 :
                             (string, Ast.node * L.macro_kind * Obj.t) Hashtbl.t)

  val resolved_macro_tbl = (Hashtbl.create 0 : (string, Ast.node) Hashtbl.t)

  val malformed_macro_names = (Xset.create 0 : string Xset.t)

  val mutable access_spec_opt = (None : N.Spec.access_spec option)

  val mutable scanner_keep_flag = false
  val mutable scanner_replay_flag = false

  val inline_asm_functions = (Xset.create 0 : string Xset.t)

  val mutable unqualified_name = ""
  val mutable function_name = ""
  val mutable name_prefix = ""

  val mutable dump_tokens_flag = false
  val mutable parse_tokens_flag = false

  initializer
    stack#push top_frame

  method set_dump_tokens_flag () =
    dump_tokens_flag <- true

  method dump_tokens_flag = dump_tokens_flag

  method set_parse_tokens_flag () =
    parse_tokens_flag <- true;
    pstat <- new dummy_pstat;
    stack <- new dummy_stack;
    stack#push top_frame

  method parse_tokens_flag = parse_tokens_flag

  method set_top_frame frm = top_frame <- frm

  method reset_name_prefix () = name_prefix <- ""
  method name_prefix = name_prefix
  method _set_name_prefix p =
    [%debug_log "p=%s" p];
    name_prefix <- p
  method set_name_prefix nd =
    let p = Ast.encode_nested_name_spec nd in
    [%debug_log "p=%s" p];
    name_prefix <- p

  method set_dtor_node nd =
    [%debug_log "@"];
    dtor_node <- nd

  method reset_dtor_node () =
    [%debug_log "@"];
    dtor_node <- Ast.dummy_node

  method get_dtor_prefix () =
    if self#stack#after_params then begin
      if dtor_node != Ast.dummy_node then
        let _q, _ = Ast.qn_wrap_of_declarator dtor_node in
        let q = Ast.prefix_of_encoded _q in
        q
      else
        ""
    end
    else
      ""

  method get_dtor_prefix_and_qn () =
    if self#stack#after_params then begin
      if dtor_node != Ast.dummy_node then
        let q, _ = Ast.qn_wrap_of_declarator dtor_node in
        let p = Ast.prefix_of_encoded q in
        p, q
      else
        "", ""
    end
    else
      "", ""

  method scanner_keep_flag = scanner_keep_flag
  method set_scanner_keep_flag() = scanner_keep_flag <- true
  method clear_scanner_keep_flag() = scanner_keep_flag <- false

  method scanner_replay_flag = scanner_replay_flag
  method set_scanner_replay_flag() = scanner_replay_flag <- true
  method clear_scanner_replay_flag() = scanner_replay_flag <- false

  method access_spec_opt = access_spec_opt

  method set_access_spec a =
    [%debug_log "%s -> %s"
      (opt_to_string N.Spec.access_spec_to_string access_spec_opt)
      (N.Spec.access_spec_to_string a)];
    access_spec_opt <- Some a

  method reset_access_spec () =
    [%debug_log "%s ->" (opt_to_string N.Spec.access_spec_to_string access_spec_opt)];
    access_spec_opt <- None

  method lookup_name ?(filt=fun _ -> true) n =
    stack#find_name ~filt n

  method lookup_namespace n =
    stack#find_namespace n

  method lookup_obj n =
    stack#find_obj n

  method lookup_type n =
    stack#find_type n

  method set_obj_external_name ?(prefix="") i (nd : Ast.node) =
    let p = stack#get_prefix ~prefix ~ns_only:true () in
    let qn = p^prefix^i in
    let info = I.from_name qn in
    [%debug_log "%s => %s" i (I.to_string info)];
    nd#set_info info

  method set_obj_binding ?(prefix="") i (nd : Ast.node) =
    try
      let spec = self#lookup_obj (prefix^i) in
      match spec#bid_opt with
      | Some bid -> begin
          let loc_opt =
            Some (UID.of_int spec#iod, conv_loc spec#lod)
          in
          let b = B.make_use ~loc_opt bid in
          [%debug_log "%s => %s" i (B.to_string b)];
          nd#set_binding b
      end
      | None -> ()
    with
      Not_found -> self#set_obj_external_name ~prefix i nd

  method set_type_external_name ?(prefix="") i (nd : Ast.node) =
    let p = stack#get_prefix ~prefix ~ns_only:true () in
    let qn = p^prefix^i in
    let info = I.from_name qn in
    [%debug_log "%s => %s" i (I.to_string info)];
    nd#set_info info

  method set_type_binding ?(prefix="") i (nd : Ast.node) =
    try
      let spec = self#lookup_type (prefix^i) in
      match spec#bid_opt with
      | Some bid -> begin
          let loc_opt =
            Some (UID.of_int spec#iod, conv_loc spec#lod)
          in
          let b = B.make_use ~loc_opt bid in
          [%debug_log "%s => %s" i (B.to_string b)];
          nd#set_binding b
      end
      | None -> ()
    with
      Not_found -> begin
        if not self#scanner_keep_flag && not self#scanner_replay_flag then begin
          self#set_type_external_name ~prefix i nd;
          (*!!!NG!!!let spec = new N.Spec.c ~prefix Ast.Loc.dummy 0 i N.Spec.Type in
          top_frame#register i spec*)
        end
      end

  method save_stack () =
    saved_stack <- stack;
    stack <- saved_stack#copy

  method restore_stack () =
    stack <- saved_stack#copy

  method reset_pstat () =
    pstat#reset()

  method! init =
    super#init;
    self#reset_pstat()

  method stack = stack
  method pstat = pstat
  method set_pstat s = pstat <- s
  method get_pstat () = pstat

  method _open_bracket = pstat#_open_bracket
  method __close_bracket = pstat#__close_bracket
  method _close_bracket = pstat#_close_bracket

  method open_paren x =
    if self#pp_line_flag then
      pstat#open_pp_paren()
    else
      pstat#open_paren x
  method paren_stack_top = pstat#paren_stack_top
  method close_paren ?(pseudo=false) () =
    if self#pp_line_flag then
      pstat#close_pp_paren()
    else
      pstat#close_paren ~pseudo ()
  method change_paren_kind = pstat#change_paren_kind
  method paren_level = pstat#paren_level
  method pp_paren_level = pstat#pp_paren_level
  method at_ini_brace = pstat#at_ini_brace
  method at_ini_brace_2 = pstat#at_ini_brace_2
  method at_class_brace = pstat#at_class_brace
  method at_brace = pstat#at_brace
  method at_brace_2 = pstat#at_brace_2
  method at_req_brace = pstat#at_req_brace
  method at_objc_msg = pstat#at_objc_msg
  method at_attr = pstat#at_attr
  method at_lam_intr = pstat#at_lam_intr
  method at_subscr = pstat#at_subscr
  method at_templ_arg = pstat#at_templ_arg
  method at_templ_arg_2 = pstat#at_templ_arg_2
  method at_templ_param = pstat#at_templ_param
  method at_templ_param_2 = pstat#at_templ_param_2
  method at_templ_param_arg_expr_2 = pstat#at_templ_param_arg_expr_2
  method at_arg_paren = pstat#at_arg_paren
  method at_arg_paren_2 = pstat#at_arg_paren_2
  method _arg_paren_flag = pstat#_arg_paren_flag
  method at_type_paren = pstat#at_type_paren
  method at_type_paren_2 = pstat#at_type_paren_2
  method at_fold_paren = pstat#at_fold_paren
  method at_fold_paren_2 = pstat#at_fold_paren_2
  method at_paren = pstat#at_paren
  method at_paren_2 = pstat#at_paren_2
  method at_if_paren = pstat#at_if_paren
  method at_macro_arg_paren = pstat#at_macro_arg_paren
  method at_macro_arg_paren_2 = pstat#at_macro_arg_paren_2
  method at_bracket = pstat#at_bracket
  method enter_templ_param_arg = pstat#enter_templ_param_arg
  method exit_templ_param_arg = pstat#exit_templ_param_arg
  method templ_param_arg_stack_top = pstat#templ_param_arg_stack_top
  method get_templ_param_arg_stack = pstat#get_templ_param_arg_stack
  method templ_param_arg_level = pstat#templ_param_arg_level
  method enter_typename = pstat#enter_typename
  method exit_typename = pstat#exit_typename
  method reset_typename_level = pstat#reset_typename_level
  method typename_level = pstat#typename_level
  method typename_flag = pstat#typename_flag
  method enter_braced_init = pstat#enter_braced_init
  method exit_braced_init = pstat#exit_braced_init
  method reset_braced_init_level = pstat#reset_braced_init_level
  method braced_init_level = pstat#braced_init_level
  method braced_init_flag = pstat#braced_init_flag
  method enter__pp_if_section = pstat#enter__pp_if_section
  method exit__pp_if_section = pstat#exit__pp_if_section
  method reset__pp_if_section_level = pstat#reset__pp_if_section_level
  method _pp_if_section_level = pstat#_pp_if_section_level
  method _pp_if_section_flag = pstat#_pp_if_section_flag
  method open_brace () = if self#pp_line_flag then () else pstat#open_brace()
  method close_brace () = if self#pp_line_flag then () else pstat#close_brace()
  method brace_level = pstat#brace_level
  method rel_paren_level = pstat#rel_paren_level
  method open_odd_brace () = pstat#open_odd_brace()
  method close_odd_brace () = pstat#close_odd_brace()
  method odd_brace_level = pstat#odd_brace_level
  method open_bracket = pstat#open_bracket
  method close_bracket = pstat#close_bracket
  method bracket_level = pstat#bracket_level
  method open_pp_paren = pstat#open_pp_paren
  method close_pp_paren = pstat#close_pp_paren
  method enter_top_stmts = pstat#enter_top_stmts
  method exit_top_stmts = pstat#exit_top_stmts
  method top_stmts_flag = pstat#top_stmts_flag
  method top_stmts_top = pstat#top_stmts_top

  val mutable current_source_digest_opt = None

  method! enter_source src =
    let x = super#enter_source src in
    current_source_digest_opt <- None;
    x

  method get_global_bid loc =
    let digest =
      match current_source_digest_opt with
      | Some d -> d
      | None ->
        let filename = self#current_filename in
        [%debug_log "filename=\"%s\"" filename];
        let stree = self#current_source#tree in
        let d = Xhash.to_hex (stree#get_entry filename)#file_digest in
        current_source_digest_opt <- (Some d);
        d
    in
    let s = sprintf "%s-%d_%d" digest loc.Astloc.start_offset loc.Astloc.end_offset in
    BID.make_global s

  method make_local_bid () =
    bidgen#gen

  method register_global_type i st ed =
    [%debug_log "i=%s" i];
    let loc = (Ast.lloc_of_lexposs st ed)#get_loc in
    let spec = new N.Spec.c loc Ast.dummy_node_id i N.Spec.Type in
    top_frame#register ~replace:true i spec

  method register_macro_obj i (nd : Ast.node) =
    [%debug_log "i=%s %s" i nd#to_string];
    let spec = new N.Spec.c nd#loc nd#id i N.Spec.MacroObj in
    top_frame#register ~replace:true i spec

  method register_macro_fun i (nd : Ast.node) =
    [%debug_log "i=%s %s" i nd#to_string];
    let spec = new N.Spec.c nd#loc nd#id i N.Spec.MacroFun in
    top_frame#register ~replace:true i spec

  method register_id_macro_fun i (nd : Ast.node) =
    [%debug_log "i=%s" i];
    let spec = new N.Spec.c nd#loc nd#id i N.Spec.IdMacroFun in
    top_frame#register ~replace:false i spec

  method undef_macro i =
    top_frame#remove_macro (Ast.mk_macro_call_id i);
    top_frame#remove_macro (Ast.mk_macro_id i)

  method register_namespace i (nd : Ast.node) (frm : N.stack_frame) =
    [%debug_log "i=%s" i];
    let spec =
      new N.Spec.c nd#loc nd#id i (N.Spec.Namespace (self#stack#make_def_adder frm))
    in
    frm#register i spec

  method register_using_decls nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let frm = stack#top in
    let lod = nd#loc in
    let iod = nd#id in
    List.iter
      (fun (p, u) ->
        let spec = new N.Spec.c ~prefix:p lod iod u N.Spec.UsingDecl in
        frm#register u spec
      ) (Ast.qn_list_of_using_declaration nd)

  method register_using_enum_decls nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let frm = stack#top in
    let lod = nd#loc in
    let iod = nd#id in
    List.iter
      (fun (p, u) ->
        let spec = new N.Spec.c ~prefix:p lod iod u N.Spec.UsingEnumDecl in
        frm#register u spec
      ) (Ast.qn_list_of_using_enum_declaration nd)

  method register_type_param nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let i, tp_spec = Ast.ident_type_param_spec_of_type_param nd in
    let uqn = I.encode_ident i in
    let frm = stack#top in
    let spec = new N.Spec.c nd#loc nd#id uqn (N.Spec.make_typaram tp_spec) in
    nd#set_info (I.from_spec spec);
    frm#register uqn spec

  method register_elaborated_type (nd : Ast.node) =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let ok =
      try
        match (List.hd (nd#nth_children 2))#label with
        | L.IdentifierMacroInvocation _ -> false
        | _ -> true
      with _ -> true
    in
    if ok then
    let frm = stack#top in
    let p = stack#get_prefix() in
    let qn =
      match nd#label with
      | ElaboratedTypeSpecifierClass i
      | ElaboratedTypeSpecifierStruct i
      | ElaboratedTypeSpecifierUnion i
      | ElaboratedTypeSpecifierEnum i -> i
      | _ -> assert false
    in
    let spec = new N.Spec.c ~prefix:p nd#loc nd#id qn N.Spec.Type in
    nd#set_info (I.from_spec spec);
    frm#register qn spec

  method register_class_head nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let ns = stack#get_prefix ~ns_only:true () in
    let qn, s = Ast.qn_class_spec_of_class ns nd in
    if qn = "" then
      ""
    else begin
      let frm = stack#top in
      let p = stack#get_prefix() in
      let k =
        match nd#label with
        | ClassHeadClass  -> N.Spec.Class s
        | ClassHeadStruct -> N.Spec.Struct s
        | ClassHeadUnion  -> N.Spec.Union s
        | ClassHeadMacro _ -> N.Spec.Class s
        | ClassHeadMacroInvocation _ -> N.Spec.Class s
        | ClassHeadMsRefClass -> N.Spec.Class s
        | _ -> assert false
      in
      let spec = new N.Spec.c ~prefix:p nd#loc nd#id qn k in
      nd#set_info (I.from_spec spec);
      frm#register qn spec;
      qn
    end

  method register_enum_head nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let ns = stack#get_prefix ~ns_only:true () in
    let qn, s = Ast.qn_enum_spec_of_enum ns nd in
    if qn = "" then
      ""
    else begin
      let frm = stack#top in
      let p = stack#get_prefix() in
      let k =
        match nd#label with
        | EnumHeadEnum | OpaqueEnumDeclaration -> N.Spec.Enum s
        | EnumHeadEnumClass | OpaqueEnumDeclarationClass -> N.Spec.EnumClass s
        | EnumHeadEnumStruct | OpaqueEnumDeclarationStruct -> N.Spec.EnumStruct s
        | EnumHeadEnumMacro i | OpaqueEnumDeclarationMacro i -> N.Spec.EnumMacro(i, s)
        | _ -> assert false
      in
      let spec = new N.Spec.c ~prefix:p nd#loc nd#id qn k in
      nd#set_info (I.from_spec spec);
      frm#register qn spec;
      qn
    end

  method register_function nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let qn, ty = Ast.qn_type_of_func_def nd in
    [%debug_log "qn=%s" qn];
    let frm = stack#top in
    let p = stack#get_prefix() in
    let bid = self#get_global_bid nd#loc in
    let kind =
      match self#access_spec_opt with
      | Some _ -> N.Spec.make_member self#access_spec_opt ty
      | None   -> N.Spec.make_function ty
    in
    let spec = new N.Spec.c ~bid_opt:(Some bid) ~prefix:p nd#loc nd#id qn kind in
    nd#set_info (I.from_spec spec);
    frm#register qn spec;
    qn

  method register_param_decl_clause (nd : Ast.node) =
    [%debug_log "%s" (L.to_string nd#label)];
    match nd#label with
    | ParameterDeclarationClause _ -> begin
        let rec doit index = function
          | [] -> ()
          | h::t -> begin
              let itl = self#register_fparam h in
              List.iter
                (fun (i, ty) ->
                  let pred = function L.Identifier x -> x = i | _ -> false in
                  let maxL = ref 0 in
                  List.iter
                    (fun (r : Ast.node) ->
                      List.iter
                        (fun (y : Ast.node) ->
                          let count = ref 0 in
                          let decltype_flag = ref false in
                          let count_scope (x : Ast.node) =
                            match x#label with
                            | DeclaratorFunc | NoptrDeclaratorFunc
                            | AbstractDeclaratorFunc | NoptrAbstractDeclaratorFunc
                              -> incr count
                            | TrailingReturnType -> decr count
                            | ParameterDeclaration _ when not !decltype_flag -> raise Exit
                            | DecltypeSpecifier -> decltype_flag := true
                            | _ -> ()
                          in
                          begin
                            try
                              y#iter_parents ~upto:(Some r) count_scope;
                            with
                              Exit -> ()
                          end;
                          let _L = !count + 1 in
                          if _L > !maxL then
                            maxL := _L
                        ) (Ast.find_nodes pred r);
                    ) t;
                  let prefix =
                    if !maxL > 0 then
                      sprintf "fL%dp" (!maxL-1)
                    else
                      "fp"
                  in
                  let cvq =
                    let stys = Type.get_top_level_type ty in
                    let l =
                      match stys with
                      | sty::_ -> Type.get_cv_qualifiers_of_simple_ty sty (* !!! *)
                      | _ -> assert false
                    in
                    String.concat ""
                      (List.fast_sort compare (List.map I.CvQualifier.encode l))
                  in
                  let encoded =
                    let rest =
                      if index = 0 then
                        "_"
                      else if index > 0 then
                        sprintf "%d_" (index-1)
                      else
                        assert false
                    in
                    sprintf "%s%s%s" prefix cvq rest
                  in
                  h#set_encoded encoded) itl;
              doit (index+1) t
          end
        in
        doit 0 nd#children
    end
    | _ -> invalid_arg "Cpp.Parser_aux.env#register_fparams"

  method register_templ_param (nd : Ast.node) =
    match nd#label with
    | TypeParameter _ -> self#register_type_param nd
    | TemplParamMacroInvocation _ -> ()
    | _ -> self#register_param nd

  method register_templ_params nds =
    List.iteri
      (fun index x ->
        self#register_templ_param x;
        let encoded =
          if index = 0 then
            "T_"
          else if index > 0 then
            sprintf "T%d_" (index-1)
          else
            assert false
        in
        x#set_encoded encoded
      ) nds

  method register_fparam nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    List.fold_left
      (fun l (n, qn, ty) ->
        if qn <> "" then begin
          let frm = stack#top in
          let bid = self#make_local_bid() in
          let spec = new N.Spec.c ~bid_opt:(Some bid) n#loc n#id qn (N.Spec.make_fparam ty) in
          n#set_info (I.from_spec spec);
          frm#register qn spec;
          (qn, ty)::l
        end
        else
          l
      ) [] (Ast.qn_type_list_of_param_decl nd)

  method register_param nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    List.iter
      (fun (n, qn, ty) ->
        if qn <> "" then begin
          let frm = stack#top in
          let bid = self#make_local_bid() in
          let spec = new N.Spec.c ~bid_opt:(Some bid) n#loc n#id qn (N.Spec.make_param ty) in
          n#set_info (I.from_spec spec);
          frm#register qn spec
        end
      ) (Ast.qn_type_list_of_param_decl nd)

  method register_exc_decl nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    try
      let n, qn, ty = Ast.qn_type_of_exc_decl nd in
      if qn <> "" then begin
        let frm = stack#top in
        let bid = self#make_local_bid() in
        let spec = new N.Spec.c ~bid_opt:(Some bid) n#loc n#id qn (N.Spec.make_param ty) in
        n#set_info (I.from_spec spec);
        frm#register qn spec
      end
    with
      Ast.Type_not_found -> ()

  method register_enumerator (nd : Ast.node) =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let frm = stack#top in
    let scope = frm#scope in
    let p = stack#get_prefix() in
    try
      List.iter
        (fun (n, qn, ty) ->
          let kind = N.Spec.make_enumerator ty in
          let spec = new N.Spec.c ~prefix:p n#loc n#id qn kind in
          n#set_info (I.from_spec spec);
          frm#register qn spec
        ) (Ast.qn_type_list_of_enumerator scope nd)
    with
      _ -> ()

  method register_members nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let frm = stack#top in
    let p = stack#get_prefix() in
    List.iter
      (fun (n, qn, ty) ->
        let spec =
          new N.Spec.c ~prefix:p n#loc n#id qn (N.Spec.make_member self#access_spec_opt ty)
        in
        n#set_info (I.from_spec spec);
        frm#register qn spec
      ) (Ast.qn_type_list_of_mem_decl nd)

  method register_variables nd =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let frm = stack#top in
    let is_local =
      match frm#scope with
      | Block _ | Params -> true
      | _ -> false
    in
    [%debug_log "is_local=%B" is_local];
    let p =
      if is_local then
        ""
      else
        stack#get_prefix()
    in
    List.iter
      (fun (n, qn, ty) ->
        [%debug_log "qn=%s ty=%s" qn (Type.to_string ty)];
        let t = Type.wrap ty in
        Type.hoist_typedef t;
        let typedef_flag = t.Type.t_typedef in
        [%debug_log "typedef_flag=%B" typedef_flag];
        let bid =
          if is_local then
            self#make_local_bid()
          else
            self#get_global_bid n#loc
        in
        let bid_opt = Some bid in
        let section_info_opt =
          try
            Some self#pp_if_section_top_info
          with
            _ -> None
        in
        let lod = n#loc in
        let iod = n#id in
        let kind =
          if typedef_flag then
            N.Spec.Type
          else
            N.Spec.make_variable ty
        in
        let spec =
          new N.Spec.c ~bid_opt ~prefix:p ~is_local ~section_info_opt lod iod qn kind
        in
        n#set_info (I.from_spec spec);
        if is_local then begin
          n#set_binding (B.make_unknown_def bid is_local)
        end;
        frm#register qn spec;
        begin
          let name = I.decode_ident qn in
          let flag, lab =
            match (n#label : L.t) with
            | InitDeclarator _ -> true, L.InitDeclarator name
            | ParameterDeclaration _ -> true, L.ParameterDeclaration name
            | x -> false, x
          in
          if flag then
            n#relab lab
        end
      ) (Ast.qn_type_list_of_simple_decl nd)

  method register_label ?(replace=false) (nd : Ast.node) =
    [%debug_log "nd=%s" (L.to_string nd#label)];
    let frm = stack#top in
    let i = nd#get_name in
    if replace || try (frm#find i)#kind != N.Spec.Label with _ -> true then begin
      let spec = new N.Spec.c nd#loc nd#id i N.Spec.Label in
      frm#register ~replace i spec
    end

  method register_resolved_macro name nd =
    [%debug_log "%s -> %s" name (L.to_string nd#label)];
    Hashtbl.add resolved_macro_tbl name nd

  method find_resolved_macro name =
    [%debug_log "%s" name];
    Hashtbl.find resolved_macro_tbl name

  method find_all_resolved_macro name =
    [%debug_log "%s" name];
    Hashtbl.find_all resolved_macro_tbl name

  method register_pending_macro name parent_nd macro_kind tok_lst =
    [%debug_log "%s: %s" name (L.macro_kind_to_string macro_kind)];
    Hashtbl.add pending_macro_tbl name (parent_nd, macro_kind, tok_lst)

  method iter_pending_macro f =
    Hashtbl.iter f pending_macro_tbl

  method find_pending_macro name =
    [%debug_log "%s" name];
    Hashtbl.find pending_macro_tbl name

  method register_malformed_macro name =
    [%debug_log "%s" name];
    Xset.add malformed_macro_names name

  method is_malformed_macro name =
    [%debug_log "%s" name];
    Xset.mem malformed_macro_names name

  method register_inline_asm_function name =
    [%debug_log "%s" name];
    Xset.add inline_asm_functions name

  method is_inline_asm_function name =
    let b = Xset.mem inline_asm_functions name in
    [%debug_log "%s -> %B" name b];
    b

  method get_unqualified_name() = unqualified_name
  method set_unqualified_name n =
    [%debug_log "%s" n];
    unqualified_name <- n
  method clear_unqualified_name() = [%debug_log "called"]; unqualified_name <- ""

  method get_function_name() = function_name
  method set_function_name() =
    let n = self#get_unqualified_name() in
    [%debug_log "%s" n];
    function_name <- n
  method clear_function_name() = [%debug_log "called"]; function_name <- ""

  method set_lex_line_head_flag () =
    [%debug_log "lex_line_head_flag set"];
    lex_line_head_flag <- true

  method clear_lex_line_head_flag () =
    [%debug_log "lex_line_head_flag cleared"];
    lex_line_head_flag <- false

  method lex_line_head_flag = lex_line_head_flag

  method enter_lex_pp_line () =
    [%debug_log "entering lex_pp_line"];
    lex_pp_line_flag <- true

  method exit_lex_pp_line () =
    if lex_pp_line_flag then begin
      [%debug_log "exiting lex_pp_line"];
      lex_pp_line_flag <- false
    end

  method lex_pp_line_flag = lex_pp_line_flag

  method enter_lex_ms_asm_line () =
    [%debug_log "entering lex_ms_asm_line"];
    lex_ms_asm_line_flag <- true

  method exit_lex_ms_asm_line () =
    if lex_ms_asm_line_flag then begin
      [%debug_log "exiting lex_ms_asm_line"];
      lex_ms_asm_line_flag <- false
    end

  method lex_ms_asm_line_flag = lex_ms_asm_line_flag

  method pp_line_flag = pstat#pp_line_flag
  method enter_pp_line = pstat#enter_pp_line
  method exit_pp_line = pstat#exit_pp_line

  method pp_if_flag = pstat#pp_if_flag
  method enter_pp_if = pstat#enter_pp_if
  method exit_pp_if = pstat#exit_pp_if

  method pp_ifdef_flag = pstat#pp_ifdef_flag
  method enter_pp_ifdef = pstat#enter_pp_ifdef
  method exit_pp_ifdef = pstat#exit_pp_ifdef

  method enter_pp_define () =
    [%debug_log "entering pp_define"];
    pp_define_flag <- true

  method exit_pp_define () =
    [%debug_log "exiting pp_define"];
    pp_define_flag <- false

  method pp_define_flag = pp_define_flag

  method enter_pp_define_body () =
    [%debug_log "entering pp_define_body"];
    pp_define_body_flag <- true

  method exit_pp_define_body () =
    [%debug_log "exiting pp_define_body"];
    pp_define_body_flag <- false

  method pp_define_body_flag = pp_define_body_flag

  method enter_templ_head lv =
    [%debug_log "entering templ_head (lv=%d)" lv];
    Stack.push lv templ_head_stack

  method exit_templ_head () =
    [%debug_log "exiting templ_head..."];
    let lv = Stack.pop templ_head_stack in
    let _ = lv in
    [%debug_log "templ_head exited (lv=%d)" lv]

  method templ_head_level = Stack.length templ_head_stack
  method templ_head_lv = Stack.top templ_head_stack
  method templ_head_flag = not (Stack.is_empty templ_head_stack)

  method enter_pp_group = pstat#enter_pp_group
  method exit_pp_group = pstat#exit_pp_group
  method enter_pp_if_section = pstat#enter_pp_if_section
  method exit_pp_if_section = pstat#exit_pp_if_section
  method pp_if_section_level = pstat#pp_if_section_level
  method pp_if_section_top_info = pstat#pp_if_section_top_info
  method pp_if_section_nth_info = pstat#pp_if_section_nth_info

  method pp_odd_if_section_level = pstat#pp_odd_if_section_level

  method pp_if_section_rel_brace_level = pstat#pp_if_section_rel_brace_level
  method pp_if_section_rel_paren_level = pstat#pp_if_section_rel_paren_level
  method pp_odd_if_section_rel_brace_level = pstat#pp_odd_if_section_rel_brace_level
  method pp_if_section_flag = pstat#pp_if_section_flag

  method enter_templ_arg = pstat#enter_templ_arg
  method exit_templ_arg = pstat#exit_templ_arg
  method templ_arg_flag = pstat#templ_arg_flag
  method ty_templ_id_flag = pstat#ty_templ_id_flag
  method last_ty_templ_id_flag = pstat#last_ty_templ_id_flag

  method set_for_flag = pstat#set_for_flag
  method clear_for_flag = pstat#clear_for_flag
  method for_flag = pstat#for_flag

  method set_templ_flag = pstat#set_templ_flag
  method clear_templ_flag = pstat#clear_templ_flag
  method templ_flag = pstat#templ_flag

  method set_start_of_func_body_flag = pstat#set_start_of_func_body_flag
  method clear_start_of_func_body_flag = pstat#clear_start_of_func_body_flag
  method start_of_func_body_flag = pstat#start_of_func_body_flag

  method set_end_of_old_param_decl_flag = pstat#set_end_of_old_param_decl_flag
  method clear_end_of_old_param_decl_flag = pstat#clear_end_of_old_param_decl_flag
  method end_of_old_param_decl_flag = pstat#end_of_old_param_decl_flag

  method set_end_of_lambda_templ_flag = pstat#set_end_of_lambda_templ_flag
  method clear_end_of_lambda_templ_flag = pstat#clear_end_of_lambda_templ_flag
  method end_of_lambda_templ_flag = pstat#end_of_lambda_templ_flag

  method set_old_param_decl_flag = pstat#set_old_param_decl_flag
  method clear_old_param_decl_flag = pstat#clear_old_param_decl_flag
  method old_param_decl_flag = pstat#old_param_decl_flag

  method set_end_of_class_spec_flag = pstat#set_end_of_class_spec_flag
  method clear_end_of_class_spec_flag = pstat#clear_end_of_class_spec_flag
  method end_of_class_spec_flag = pstat#end_of_class_spec_flag

  method set_end_of_enum_spec_flag = pstat#set_end_of_enum_spec_flag
  method clear_end_of_enum_spec_flag = pstat#clear_end_of_enum_spec_flag
  method end_of_enum_spec_flag = pstat#end_of_enum_spec_flag

  method set_end_of_cast_type_flag = pstat#set_end_of_cast_type_flag
  method clear_end_of_cast_type_flag = pstat#clear_end_of_cast_type_flag
  method end_of_cast_type_flag = pstat#end_of_cast_type_flag

  method set_end_of_templ_head_flag = pstat#set_end_of_templ_head_flag
  method clear_end_of_templ_head_flag = pstat#clear_end_of_templ_head_flag
  method end_of_templ_head_flag = pstat#end_of_templ_head_flag

  method set_end_of_params_flag = pstat#set_end_of_params_flag
  method clear_end_of_params_flag = pstat#clear_end_of_params_flag
  method end_of_params_flag = pstat#end_of_params_flag

  method set_end_of_req_params_flag = pstat#set_end_of_req_params_flag
  method clear_end_of_req_params_flag = pstat#clear_end_of_req_params_flag
  method end_of_req_params_flag = pstat#end_of_req_params_flag

  method set_decl_stmt_block_flag = pstat#set_decl_stmt_block_flag
  method clear_decl_stmt_block_flag = pstat#clear_decl_stmt_block_flag
  method decl_stmt_block_flag = pstat#decl_stmt_block_flag

  method set_lambda_dtor_flag = pstat#set_lambda_dtor_flag
  method clear_lambda_dtor_flag = pstat#clear_lambda_dtor_flag
  method lambda_dtor_flag = pstat#lambda_dtor_flag

  method set_asm_shader_flag = pstat#set_asm_shader_flag
  method clear_asm_shader_flag = pstat#clear_asm_shader_flag
  method asm_shader_flag = pstat#asm_shader_flag

  method set_dsl_flag = pstat#set_dsl_flag
  method clear_dsl_flag = pstat#clear_dsl_flag
  method dsl_flag = pstat#dsl_flag

  method set_objc_class_interface_flag () =
    pstat#set_objc_class_interface_flag();
    objc_flag <- true
  method clear_objc_class_interface_flag = pstat#clear_objc_class_interface_flag
  method objc_class_interface_flag = pstat#objc_class_interface_flag

  method set_objc_protocol_decl_flag () =
    pstat#set_objc_protocol_decl_flag();
    objc_flag <- true
  method clear_objc_protocol_decl_flag = pstat#clear_objc_protocol_decl_flag
  method objc_protocol_decl_flag = pstat#objc_protocol_decl_flag

  method set_objc_class_flag () =
    pstat#set_objc_class_flag();
    objc_flag <- true
  method clear_objc_class_flag = pstat#clear_objc_class_flag
  method objc_class_flag = pstat#objc_class_flag

  method enter_objc_message_expr = pstat#enter_objc_message_expr
  method exit_objc_message_expr = pstat#exit_objc_message_expr
  method objc_message_expr_level = pstat#objc_message_expr_level
  method in_objc_message_expr = pstat#in_objc_message_expr

  method set_objc_block_flag = pstat#set_objc_block_flag
  method clear_objc_block_flag = pstat#clear_objc_block_flag
  method objc_block_flag = pstat#objc_block_flag

  method set_objc_sel_flag = pstat#set_objc_sel_flag
  method clear_objc_sel_flag = pstat#clear_objc_sel_flag
  method objc_sel_flag = pstat#objc_sel_flag

  method set_objc_meth_sel_flag = pstat#set_objc_meth_sel_flag
  method clear_objc_meth_sel_flag = pstat#clear_objc_meth_sel_flag
  method objc_meth_sel_flag = pstat#objc_meth_sel_flag

  method set_objc_meth_decl_flag = pstat#set_objc_meth_decl_flag
  method clear_objc_meth_decl_flag = pstat#clear_objc_meth_decl_flag
  method objc_meth_decl_flag = pstat#objc_meth_decl_flag

  method set_objc_superclass_flag = pstat#set_objc_superclass_flag
  method clear_objc_superclass_flag = pstat#clear_objc_superclass_flag
  method objc_superclass_flag = pstat#objc_superclass_flag

  method set_objc_cat_flag = pstat#set_objc_cat_flag
  method clear_objc_cat_flag = pstat#clear_objc_cat_flag
  method objc_cat_flag = pstat#objc_cat_flag

  method set_objc_protocol_ref_flag = pstat#set_objc_protocol_ref_flag
  method clear_objc_protocol_ref_flag = pstat#clear_objc_protocol_ref_flag
  method objc_protocol_ref_flag = pstat#objc_protocol_ref_flag

  method set_dtor_flag = pstat#set_dtor_flag
  method clear_dtor_flag = pstat#clear_dtor_flag
  method dtor_flag = pstat#dtor_flag

  method set_pp_func_body_odd_flag = pstat#set_pp_func_body_odd_flag
  method clear_pp_func_body_odd_flag = pstat#clear_pp_func_body_odd_flag
  method pp_func_body_odd_flag = pstat#pp_func_body_odd_flag

  method set_class_name_flag = pstat#set_class_name_flag
  method clear_class_name_flag = pstat#clear_class_name_flag
  method class_name_flag = pstat#class_name_flag

  method set_cast_head_flag = pstat#set_cast_head_flag
  method clear_cast_head_flag = pstat#clear_cast_head_flag
  method cast_head_flag = pstat#cast_head_flag

  method set_broken_flag = pstat#set_broken_flag
  method clear_broken_flag = pstat#clear_broken_flag
  method broken_flag = pstat#broken_flag

  method set_ns_alias_flag = pstat#set_ns_alias_flag
  method clear_ns_alias_flag = pstat#clear_ns_alias_flag
  method ns_alias_flag = pstat#ns_alias_flag

  method set_end_of_objc_meth_sel_flag = pstat#set_end_of_objc_meth_sel_flag
  method clear_end_of_objc_meth_sel_flag = pstat#clear_end_of_objc_meth_sel_flag
  method end_of_objc_meth_sel_flag = pstat#end_of_objc_meth_sel_flag

  method set_end_of_objc_meth_type_flag = pstat#set_end_of_objc_meth_type_flag
  method clear_end_of_objc_meth_type_flag = pstat#clear_end_of_objc_meth_type_flag
  method end_of_objc_meth_type_flag = pstat#end_of_objc_meth_type_flag

  method set_end_of_objc_property_attrs_decl_flag = pstat#set_end_of_objc_property_attrs_decl_flag
  method clear_end_of_objc_property_attrs_decl_flag = pstat#clear_end_of_objc_property_attrs_decl_flag
  method end_of_objc_property_attrs_decl_flag = pstat#end_of_objc_property_attrs_decl_flag

  method set_end_of_objc_protocol_ref_list_flag = pstat#set_end_of_objc_protocol_ref_list_flag
  method clear_end_of_objc_protocol_ref_list_flag = pstat#clear_end_of_objc_protocol_ref_list_flag
  method end_of_objc_protocol_ref_list_flag = pstat#end_of_objc_protocol_ref_list_flag

  method set_end_of_decl_spec_macro_call_flag = pstat#set_end_of_decl_spec_macro_call_flag
  method clear_end_of_decl_spec_macro_call_flag = pstat#clear_end_of_decl_spec_macro_call_flag
  method end_of_decl_spec_macro_call_flag = pstat#end_of_decl_spec_macro_call_flag

  method set_end_of_attr_macro_call_flag = pstat#set_end_of_attr_macro_call_flag
  method clear_end_of_attr_macro_call_flag = pstat#clear_end_of_attr_macro_call_flag
  method end_of_attr_macro_call_flag = pstat#end_of_attr_macro_call_flag

  method set_end_of_type_macro_call_flag = pstat#set_end_of_type_macro_call_flag
  method clear_end_of_type_macro_call_flag = pstat#clear_end_of_type_macro_call_flag
  method end_of_type_macro_call_flag = pstat#end_of_type_macro_call_flag

  method set_str_flag = pstat#set_str_flag
  method clear_str_flag = pstat#clear_str_flag
  method str_flag = pstat#str_flag

  method set_ty_param_rhs_flag = pstat#set_ty_param_rhs_flag
  method clear_ty_param_rhs_flag = pstat#clear_ty_param_rhs_flag
  method ty_param_rhs_flag = pstat#ty_param_rhs_flag

  method set_end_of_if_head_flag = pstat#set_end_of_if_head_flag
  method clear_end_of_if_head_flag = pstat#clear_end_of_if_head_flag
  method end_of_if_head_flag = pstat#end_of_if_head_flag

  method set_end_of_id_macro_call_flag = pstat#set_end_of_id_macro_call_flag
  method clear_end_of_id_macro_call_flag = pstat#clear_end_of_id_macro_call_flag
  method end_of_id_macro_call_flag = pstat#end_of_id_macro_call_flag

  method set_end_of_literal_macro_call_flag = pstat#set_end_of_literal_macro_call_flag
  method clear_end_of_literal_macro_call_flag = pstat#clear_end_of_literal_macro_call_flag
  method end_of_literal_macro_call_flag = pstat#end_of_literal_macro_call_flag

  method set_end_of_decltype_flag = pstat#set_end_of_decltype_flag
  method clear_end_of_decltype_flag = pstat#clear_end_of_decltype_flag
  method end_of_decltype_flag = pstat#end_of_decltype_flag

  method set_end_of_noptr_dtor_paren_flag = pstat#set_end_of_noptr_dtor_paren_flag
  method clear_end_of_noptr_dtor_paren_flag = pstat#clear_end_of_noptr_dtor_paren_flag
  method end_of_noptr_dtor_paren_flag = pstat#end_of_noptr_dtor_paren_flag

  method set_end_of_sizeof_flag = pstat#set_end_of_sizeof_flag
  method clear_end_of_sizeof_flag = pstat#clear_end_of_sizeof_flag
  method end_of_sizeof_flag = pstat#end_of_sizeof_flag

  method set_end_of_handler_head_flag = pstat#set_end_of_handler_head_flag
  method clear_end_of_handler_head_flag = pstat#clear_end_of_handler_head_flag
  method end_of_handler_head_flag = pstat#end_of_handler_head_flag

  method set_end_of_broken_decl_section_flag = pstat#set_end_of_broken_decl_section_flag
  method clear_end_of_broken_decl_section_flag = pstat#clear_end_of_broken_decl_section_flag
  method end_of_broken_decl_section_flag = pstat#end_of_broken_decl_section_flag

  method set_end_of_label_flag = pstat#set_end_of_label_flag
  method clear_end_of_label_flag = pstat#clear_end_of_label_flag
  method end_of_label_flag = pstat#end_of_label_flag

  method set_end_of_mem_initializer_flag = pstat#set_end_of_mem_initializer_flag
  method clear_end_of_mem_initializer_flag = pstat#clear_end_of_mem_initializer_flag
  method end_of_mem_initializer_flag = pstat#end_of_mem_initializer_flag

  method set_attr_flag = pstat#set_attr_flag
  method clear_attr_flag = pstat#clear_attr_flag
  method attr_flag = pstat#attr_flag

  method set_linkage_spec_flag = pstat#set_linkage_spec_flag
  method clear_linkage_spec_flag = pstat#clear_linkage_spec_flag
  method linkage_spec_flag = pstat#linkage_spec_flag

  method set_condition_flag = pstat#set_condition_flag
  method clear_condition_flag = pstat#clear_condition_flag
  method condition_flag = pstat#condition_flag

  method set_mem_acc_flag = pstat#set_mem_acc_flag
  method clear_mem_acc_flag = pstat#clear_mem_acc_flag
  method mem_acc_flag = pstat#mem_acc_flag

  method set_using_flag = pstat#set_using_flag
  method clear_using_flag = pstat#clear_using_flag
  method using_flag = pstat#using_flag

  method set_mock_qualifier_flag = pstat#set_mock_qualifier_flag
  method clear_mock_qualifier_flag = pstat#clear_mock_qualifier_flag
  method mock_qualifier_flag = pstat#mock_qualifier_flag

  method set_end_of_str_section_flag = pstat#set_end_of_str_section_flag
  method clear_end_of_str_section_flag = pstat#clear_end_of_str_section_flag
  method end_of_str_section_flag = pstat#end_of_str_section_flag

  method set_new_flag = pstat#set_new_flag
  method clear_new_flag = pstat#clear_new_flag
  method new_flag = pstat#new_flag

  method set_concept_flag = pstat#set_concept_flag
  method clear_concept_flag = pstat#clear_concept_flag
  method concept_flag = pstat#concept_flag

  method set_requires_clause_flag = pstat#set_requires_clause_flag
  method clear_requires_clause_flag = pstat#clear_requires_clause_flag
  method requires_clause_flag = pstat#requires_clause_flag

  method set_rhs_flag = pstat#set_rhs_flag
  method clear_rhs_flag = pstat#clear_rhs_flag
  method rhs_flag = pstat#rhs_flag

  method set_eq_init_flag = pstat#set_eq_init_flag
  method clear_eq_init_flag = pstat#clear_eq_init_flag
  method eq_init_flag = pstat#eq_init_flag

  method set_alias_flag = pstat#set_alias_flag
  method clear_alias_flag = pstat#clear_alias_flag
  method alias_flag = pstat#alias_flag

  method set_trailing_retty_flag = pstat#set_trailing_retty_flag
  method clear_trailing_retty_flag = pstat#clear_trailing_retty_flag
  method trailing_retty_flag = pstat#trailing_retty_flag

  method enter_pp_ifx_d = pstat#enter_pp_ifx_d
  method exit_pp_ifx_d = pstat#exit_pp_ifx_d
  method pp_ifx_d_flag = pstat#pp_ifx_d_flag

  method pp_top_label = pstat#pp_top_label
  method set_pp_top_label = pstat#set_pp_top_label

  method add_pp_elif = pstat#add_pp_elif
  method pp_elif_flag = pstat#pp_elif_flag

  method add_pp_else = pstat#add_pp_else
  method pp_else_flag = pstat#pp_else_flag

  method clear_lbrace_info = pstat#clear_lbrace_info
  method set_lbrace_info = pstat#set_lbrace_info
  method get_lbrace_info = pstat#get_lbrace_info
  method incr_lbrace_info = pstat#incr_lbrace_info
  method decr_lbrace_info = pstat#decr_lbrace_info
  method clear_rbrace_info = pstat#clear_rbrace_info
  method set_rbrace_info = pstat#set_rbrace_info
  method get_rbrace_info = pstat#get_rbrace_info
  method incr_rbrace_info = pstat#incr_rbrace_info
  method decr_rbrace_info = pstat#decr_rbrace_info
  method set_odd_info = pstat#set_odd_info
  method get_odd_info = pstat#get_odd_info
  method set_broken_info = pstat#set_broken_info
  method get_broken_info = pstat#get_broken_info
  method set_paren_closing_info = pstat#set_paren_closing_info
  method get_paren_closing_info = pstat#get_paren_closing_info
  method set_brace_paren_closing_info = pstat#set_brace_paren_closing_info
  method get_brace_paren_closing_info = pstat#get_brace_paren_closing_info
  method set_brace_closing_info = pstat#set_brace_closing_info
  method incr_brace_closing_info = pstat#incr_brace_closing_info
  method get_brace_closing_info = pstat#get_brace_closing_info
  method set_brace_opening_info = pstat#set_brace_opening_info
  method clear_brace_opening_info = pstat#clear_brace_opening_info
  method get_brace_opening_info = pstat#get_brace_opening_info
  method set_func_head_info = pstat#set_func_head_info
  method get_func_head_info = pstat#get_func_head_info
  method set_broken_func_head_info = pstat#set_broken_func_head_info
  method get_broken_func_head_info = pstat#get_broken_func_head_info
  method set_templ_closing_info = pstat#set_templ_closing_info
  method get_templ_closing_info = pstat#get_templ_closing_info
  method set_func_body_info = pstat#set_func_body_info
  method get_func_body_info = pstat#get_func_body_info
  method set_semicolon_info = pstat#set_semicolon_info
  method clear_semicolon_info = pstat#clear_semicolon_info
  method get_semicolon_info = pstat#get_semicolon_info
  method set_comma_info = pstat#set_comma_info
  method get_comma_info = pstat#get_comma_info
  method set_cond_expr_info = pstat#set_cond_expr_info
  method get_cond_expr_info = pstat#get_cond_expr_info
  method set_cond_expr__info = pstat#set_cond_expr__info
  method get_cond_expr__info = pstat#get_cond_expr__info
  method set_asm_info = pstat#set_asm_info
  method get_asm_info = pstat#get_asm_info
  method set_begin_asm_info = pstat#set_begin_asm_info
  method get_begin_asm_info = pstat#get_begin_asm_info
  method set_lack_of_dtor_info = pstat#set_lack_of_dtor_info
  method get_lack_of_dtor_info = pstat#get_lack_of_dtor_info
  method set_class_brace_opening_info = pstat#set_class_brace_opening_info
  method get_class_brace_opening_info = pstat#get_class_brace_opening_info
  method set_follows_comma_info = pstat#set_follows_comma_info
  method get_follows_comma_info = pstat#get_follows_comma_info
  method set_cond_sub_info = pstat#set_cond_sub_info
  method get_cond_sub_info = pstat#get_cond_sub_info
  method get_pp_if_compl_info = pstat#get_pp_if_compl_info
  method get_pp_if_compl_brace_info = pstat#get_pp_if_compl_brace_info
  method get_pp_if_compl_paren_info = pstat#get_pp_if_compl_paren_info
  method reset_pp_if_compl_info = pstat#reset_pp_if_compl_info

  method alt_pp_branch_flag = pstat#alt_pp_branch_flag

  method set_in_body_brace_flag () =
    [%debug_log "in_body_brace_flag set"];
    in_body_brace_flag <- true;
    in_body_brace_level <- 0

  method clear_in_body_brace_flag () =
    [%debug_log "in_body_brace_flag_cleared"];
    in_body_brace_flag <- false;
    in_body_brace_level <- 0

  method in_body_brace_flag = in_body_brace_flag

  method open_in_body_brace () =
    if in_body_brace_flag then begin
      [%debug_log "opening in_body_brace"];
      in_body_brace_level <- in_body_brace_level + 1
    end

  method close_in_body_brace () =
    if in_body_brace_flag && in_body_brace_level > 0 then begin
      [%debug_log "closing in_body_brace"];
      in_body_brace_level <- in_body_brace_level - 1
    end

  method in_body_brace_level = in_body_brace_level

  method enter_sizeof_ty = pstat#enter_sizeof_ty
  method exit_sizeof_ty = pstat#exit_sizeof_ty
  method sizeof_ty_flag = pstat#sizeof_ty_flag

  method enter_lambda_intro = pstat#enter_lambda_intro
  method exit_lambda_intro = pstat#exit_lambda_intro
  method lambda_intro_flag = pstat#lambda_intro_flag

  method enter_ctor_init = pstat#enter_ctor_init
  method exit_ctor_init = pstat#exit_ctor_init
  method ctor_init_flag = pstat#ctor_init_flag

  method enter_stmts = pstat#enter_stmts
  method exit_stmts = pstat#exit_stmts
  method stmts_flag = pstat#stmts_flag

  method enter_base_clause = pstat#enter_base_clause
  method exit_base_clause = pstat#exit_base_clause
  method base_clause_flag = pstat#base_clause_flag

  method enter_asm = pstat#enter_asm
  method exit_asm = pstat#exit_asm
  method asm_flag = pstat#asm_flag
  method asm_paren_level = pstat#asm_paren_level

  method enter_braced_asm = pstat#enter_braced_asm
  method exit_braced_asm = pstat#exit_braced_asm
  method braced_asm_flag = pstat#braced_asm_flag

  method enter_asm_block = pstat#enter_asm_block
  method exit_asm_block = pstat#exit_asm_block
  method asm_block_flag = pstat#asm_block_flag

  method enter_enum_head = pstat#enter_enum_head
  method exit_enum_head = pstat#exit_enum_head
  method enum_head_flag = pstat#enum_head_flag

  method enter_ty_param = pstat#enter_ty_param
  method exit_ty_param = pstat#exit_ty_param
  method ty_param_flag = pstat#ty_param_flag

  method enter_exec_config = pstat#enter_exec_config
  method exit_exec_config = pstat#exit_exec_config
  method exec_config_flag = pstat#exec_config_flag

  method enter_decltype = pstat#enter_decltype
  method exit_decltype = pstat#exit_decltype
  method decltype_flag = pstat#decltype_flag

  method enter_alignas = pstat#enter_alignas
  method exit_alignas = pstat#exit_alignas
  method alignas_flag = pstat#alignas_flag

  method enter_alignof = pstat#enter_alignof
  method exit_alignof = pstat#exit_alignof
  method alignof_flag = pstat#alignof_flag

  method enter_noexcept = pstat#enter_noexcept
  method exit_noexcept = pstat#exit_noexcept
  method noexcept_flag = pstat#noexcept_flag

  method enter_macro_arg = pstat#enter_macro_arg
  method exit_macro_arg = pstat#exit_macro_arg
  method macro_arg_flag = pstat#macro_arg_flag
  method macro_arg_level = pstat#macro_arg_level

  method set_body_head_flag () =
    [%debug_log "body_head_flag set"];
    body_head_flag <- true

  method clear_body_head_flag () =
    if body_head_flag then begin
      [%debug_log "body_head_flag cleared"];
      body_head_flag <- false
    end

  method body_head_flag = body_head_flag

  method set_typedef_flag () =
    [%debug_log "typedef_flag set"];
    typedef_flag <- true

  method clear_typedef_flag () =
    if typedef_flag then begin
      [%debug_log "typedef_flag cleared"];
      typedef_flag <- false
    end

  method typedef_flag = typedef_flag

  method set_for_range_init_flag () =
    [%debug_log "for_range_init_flag set"];
    for_range_init_flag <- true

  method clear_for_range_init_flag () =
    if for_range_init_flag then begin
      [%debug_log "for_range_init_flag cleared"];
      for_range_init_flag <- false
    end

  method for_range_init_flag = for_range_init_flag

  method set_ty_param_key_flag () =
    [%debug_log "ty_param_key_flag set"];
    ty_param_key_flag <- true

  method clear_ty_param_key_flag () =
    if ty_param_key_flag then begin
      [%debug_log "ty_param_key_flag cleared"];
      ty_param_key_flag <- false
    end

  method ty_param_key_flag = ty_param_key_flag

  method set_param_head_flag () =
    [%debug_log "param_head_flag set"];
    param_head_flag <- true

  method clear_param_head_flag () =
    if param_head_flag then begin
      [%debug_log "param_head_flag cleared"];
      param_head_flag <- false
    end

  method param_head_flag = param_head_flag

  method set_cast_key_flag () =
    if not self#pp_line_flag then begin
      [%debug_log "cast_key_flag set"];
      cast_key_flag <- true
    end

  method clear_cast_key_flag () =
    if cast_key_flag then begin
      [%debug_log "cast_key_flag cleared"];
      cast_key_flag <- false
    end

  method cast_key_flag = cast_key_flag

  method set_conv_func_id_flag () =
    [%debug_log "conv_func_id_flag set"];
    conv_func_id_flag <- true

  method clear_conv_func_id_flag () =
    if conv_func_id_flag then begin
      [%debug_log "conv_func_id_flag cleared"];
      conv_func_id_flag <- false
    end

  method conv_func_id_flag = conv_func_id_flag

  method set_init_flag () =
    [%debug_log "init_flag set"];
    init_flag <- true

  method clear_init_flag () =
    if init_flag then begin
      [%debug_log "init_flag cleared"];
      init_flag <- false
    end

  method init_flag = init_flag

  method set_pp_odd_flag () =
    [%debug_log "pp_odd_flag set"];
    pp_odd_flag <- true

  method clear_pp_odd_flag () =
    if pp_odd_flag then begin
      [%debug_log "pp_odd_flag cleared"];
      pp_odd_flag <- false
    end

  method pp_odd_flag = pp_odd_flag

  method set_expr_flag () =
    [%debug_log "expr_flag set"];
    expr_flag <- true;
    try
      match self#pstat#bracket_stack_top with
      | BK_TEMPL_PARAM c | BK_TEMPL_ARG c -> c.tpac_expr_flag <- true
      | _ -> ()
    with
      _ -> ()


  method clear_expr_flag () =
    if expr_flag then begin
      [%debug_log "expr_flag cleared"];
      expr_flag <- false
    end

  method expr_flag = expr_flag

  method set_virtual_func_flag () =
    [%debug_log "virtual_func_flag set"];
    virtual_func_flag <- true

  method clear_virtual_func_flag () =
    if virtual_func_flag then begin
      [%debug_log "virtual_func_flag cleared"];
      virtual_func_flag <- false
    end

  method virtual_func_flag = virtual_func_flag

  method set_value_flag () =
    [%debug_log "value_flag set"];
    value_flag <- true

  method clear_value_flag () =
    if value_flag then begin
      [%debug_log "value_flag cleared"];
      value_flag <- false
    end

  method value_flag = value_flag

  method set_dtor_if_section_flag () =
    [%debug_log "dtor_if_section_flag set"];
    dtor_if_section_flag <- true

  method clear_dtor_if_section_flag () =
    if dtor_if_section_flag then begin
      [%debug_log "dtor_if_section_flag cleared"];
      dtor_if_section_flag <- false
    end

  method dtor_if_section_flag = dtor_if_section_flag

  method objc_flag = objc_flag

  method set_using_ns_flag () =
    [%debug_log "using_ns_flag set"];
    using_ns_flag <- true

  method clear_using_ns_flag () =
    if using_ns_flag then begin
      [%debug_log "using_ns_flag cleared"];
      using_ns_flag <- false
    end

  method using_ns_flag = using_ns_flag

  method set_pp_params_flag () =
    [%debug_log "pp_params_flag set"];
    pp_params_flag <- true

  method clear_pp_params_flag () =
    if pp_params_flag then begin
      [%debug_log "pp_params_flag cleared"];
      pp_params_flag <- false
    end

  method pp_params_flag = pp_params_flag

  method enter_const () =
    let tlv = self#templ_param_arg_level in
    let plv = self#paren_level in
    Stack.push (tlv, plv) const_stack;
    [%debug_log "entering const (tlv:%d,plv%d)" tlv plv]

  method exit_const () =
    try
      let (tlv, plv) = Stack.top const_stack in
      if tlv = self#templ_param_arg_level && plv = self#paren_level then begin
        [%debug_log "exiting const..."];
        let (t, p) = Stack.pop const_stack in
        let _ = t in
        let _ = p in
        [%debug_log "const exited (tlv:%d,plv:%d)" t p];
      end
    with
      Stack.Empty -> ()

  method const_flag = not (Stack.is_empty const_stack)

end (* of class env *)
]

module type STATE_T = sig
  val env           : env
end


module F (Stat : STATE_T) = struct

  include Stat

end (* of functor Parser_aux.F *)
