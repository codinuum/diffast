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

module Parserlib_base = Langs_common.Parserlib_base

module T = Tokens_
module Aux = Parser_aux
module C = Context

type token = T.token Parserlib_base.token

type mode = Aux.parsing_mode

(*
val is_type_name : string -> bool
val templ_param_arg_balanced : ?level:int -> T.token list -> bool
val filt_at_level0 : ?rev:bool -> T.token list -> (T.token -> bool) -> bool
val mem_at_level0 : ?rev:bool -> T.token list -> T.token -> bool
val split_at_comma : T.token list -> T.token list list
val contained_in_list : T.token list -> T.token list -> bool
*)
val is_pp_elif_else_like : Aux.env -> T.token -> bool
val is_pp_elif_else_endif_like : Aux.env -> T.token -> bool
val is_pp_control_line : T.token -> bool

val is_params_body_macro : string -> bool
val is_params_body_macro_ident : string -> bool

type name_kind = K_NONE | K_TYPE | K_TYPE_OR_FPARAM | K_OBJ | K_TEMPL | K_TEMPL_OR_FPARAM

class type c_t = object
  method keep_flag : bool
  method clear_keep_flag : unit -> unit

  method get_token : unit -> token

  method prev_endofs : int
  method prev_endln : int
  method prev_edp : Lexing.position
  method prev_indent2 : int
  method prev_indent_rawtoken2 : T.token
  method prev_indent : int
  method prev_indent_rawtoken : T.token
  method prev_indent_rawtoken_prev : T.token
  method prev_rawtoken : T.token
  method prev_rawtoken2 : T.token
  method prev_rawtoken3 : T.token
  method prev_rawtoken4 : T.token

  method _current_rawtoken : T.token
  method current_token : token
  method current_loc : Ast.Loc.t

  method enter_block : ?no_tweak:bool -> unit -> unit
  method set_body_flag : unit -> unit
  method reset_body_name : unit -> unit

  method peek : unit -> token
  method peek_nth : int -> token
  method peek_rawtoken : unit -> T.token
  method peek_nth_rawtoken : int -> T.token
  method peek_rawtoken_up_to : ?limit:int -> ?filt:(T.token -> bool) -> ?from:int -> ?skip_pp_control_line:bool -> ?is_target:(T.token -> bool) -> T.token list -> int * T.token list
  method peek_rawtoken_up_to_rparen :
      ?from:int -> ?level:int -> ?filt:(T.token -> bool) -> T.token option -> bool * int * T.token list
  method peek_rawtoken_up_to_rparen_none : unit -> int * T.token list
  method peek_rawtoken_up_to_group_end :
      ?limit:int -> ?from:int -> ?filt:(T.token -> bool) -> ?until:(T.token -> bool) -> ?regard_pp_if:bool
        -> unit -> int * T.token list
  method peek_rawtoken_up_to_section_end : ?nth_head_list_ref_opt:(int list ref option) -> ?nth_list_ref_opt:(int list ref option) -> ?from:int -> unit -> int
  method peek_rawtoken_up_to_end_of_qualified_id : ?from:int -> ?ini_tlv:int -> unit -> int
  method peek_rawtoken_up_to_rparen_split_at_comma :
      ?from:int -> ?ignore_pp:bool -> ?ignore_templ_lv:bool -> ?lv_ofs:int -> ?filt:(T.token list -> bool) ->
        unit -> int * T.token list list
  method peek_rawtoken_up_to_rbrace : ?noexcept:bool ->
      ?from:int -> ?lv_ofs:int -> ?filt:(T.token -> bool) -> unit -> int * T.token list
  method peek_rawtoken_up_to_rbrace_split_at_comma :
      ?from:int -> ?ignore_pp:bool -> ?ignore_templ_lv:bool -> ?lv_ofs:int -> ?filt:(T.token list -> bool) ->
        ?check_semicolon:bool -> unit -> int * T.token list list
  method peek_rawtoken_up_to_rbracket :
      ?from:int -> ?lv_ofs:int -> ?filt:(T.token -> bool) -> unit -> int * T.token list

  method reg_macro_spec : string -> (int * int * T.token) -> unit
  method find_macro_spec : string -> int * int * T.token

  method reg_ident_conv : string -> T.token -> unit
  method find_ident_conv : string -> T.token

  method lookup_name : ?kind:name_kind -> ?prefix:string -> string -> Pinfo.Name.Spec.c
  method is_type : ?qualified:bool -> ?prefix:string -> ?defined:bool -> ?weak:bool -> string -> bool
  method is_label : string -> bool
  method is_templ : ?prefix:string -> string -> bool
  method is_val : ?qualified:bool -> ?prefix:string -> ?weak:bool -> string -> bool
  method _is_val : string -> bool
  method is_macro_fun : string -> bool
  method is_id_macro_fun : string -> bool
  method is_macro_obj : string -> bool

  method reg_macro_fun : string -> unit

  method is_ty : ?strong:bool -> ?defined:bool -> ?weak:bool -> T.token -> bool
  method check_double_paren : int -> bool
  method skip_pp_control_line : ?from:int -> unit -> int
  method followed_by_blank_lines : int -> bool
  method check_if_param : ?strict:bool -> ?weak:bool -> ?at_type_paren:bool -> ?no_lookup:bool -> T.token list -> bool
  method check_if_params : ?strict:bool -> ?weak:bool -> ?at_type_paren:bool -> ?no_lookup:bool -> T.token list list -> bool
  method check_if_noptr_dtor : ?weak:bool -> T.token list -> bool
  method check_if_noptr_dtor_ : ?weak:bool -> T.token list -> bool
  method check_if_macro_arg : T.token list -> bool
  method check_if_macro_args : T.token list list -> bool
  method check_if_arg_macro : unit -> bool
  method check_if_abst_dtor_ident : ?weak:bool -> ?nth:int -> unit -> bool

  method is_func_head : ?from:int -> ?head:T.token -> unit -> bool
  method is_ps_lparen : ?from:int -> unit -> bool
  method is_lparen : ?from:int -> ?ignore_pp:bool -> unit -> bool

  method skip_pp : ?limit:int -> int -> int

  method prepend_token : token -> unit
  method discard_token : unit -> token
  method discard_nth_token : int -> token
  method queue_token : token -> unit
  method reset : unit -> unit

  method conv_next_n_tokens : (token -> token) -> int -> unit
  method conv_nth_token : (token -> token) -> int -> unit

  method check_top_stmts_flag : bool
  method set_check_top_stmts_flag : unit -> unit
  method clear_check_top_stmts_flag : unit -> unit

  method macro_body_parsing_flag : bool
  method set_macro_body_parsing_flag : unit -> unit
  method clear_macro_body_parsing_flag : unit -> unit

  method is_opening_stmt_macro : string -> bool

  method context : C.t
  method sub_context : C.sub
  method top_context : C.t
  method second_top_context : C.t
  method top_sub_context : C.sub
  method push_context : unit -> unit
  method push_sub_context : unit -> unit
  method pop_context : unit -> unit
  method pop_sub_context : unit -> unit
  method ctx_reset : unit -> unit
  method ctx_ty : unit -> unit
  method ctx_expr : ?force:bool -> unit -> unit
  method ctx_stmt : unit -> unit
  method ctx_enum : unit -> unit
  method ctx_class : unit -> unit
  method ctx_mem : unit -> unit
  method ctx_new : unit -> unit
  method ctx_top : unit -> unit
  method ctx_ini : unit -> unit
  method ctx_mem_init : unit -> unit
  method ctx_in_case_label : unit -> unit
  method ctx_in_expr : unit -> unit
  method ctx_end_of_ty_spec : unit -> unit
  method ctx_start_of_stmt : int -> unit
  method ctx_end_of_lam_intro : unit -> unit
  method ctx_end_of_dtor : unit -> unit
  method ctx_end_of_id_expr : unit -> unit
  method ctx_end_of_stmt : unit -> unit
  method ctx_in_simple_templ_id : unit -> unit
  method sync_ctx_with_info : Pinfo.pp_if_section_info -> unit

  method replay_queue_length : int
  method init_replay_queue : int -> Aux.pstat -> token list -> unit
  method setup_replay : unit -> unit
  method stop_replay_queue : unit -> unit
  method register_replay_success_callback : (unit -> unit) -> unit
  method has_alternative_tokens : bool
  method clear_alternative_tokens : unit -> unit

  method restore_context : unit -> unit
  method restore_state : unit -> unit
  method state_number : int

  method show_token_hist : unit -> unit
  method set_token_hist_flag : unit -> unit

  method set_dump_tokens_flag : unit -> unit

  method pp_restore_context : unit -> unit

  method mode : mode
  method set_mode : mode -> unit

  method token_seq : Token_seq.c

  method dump_stats_flag : bool
  method set_dump_stats_flag : unit -> unit
  method incr_count : string -> unit
  method dump_stats : unit -> unit
end

val conv_token : Aux.env -> c_t -> token -> token

module F : functor (Stat : Aux.STATE_T) -> sig

  class c : Aux.env -> c_t

end
