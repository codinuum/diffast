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

module Xlist = Diffast_misc.Xlist
module Xqueue = Diffast_misc.Xqueue
module Xprint = Diffast_misc.Xprint
module Storage = Diffast_misc.Storage
module Parserlib_base = Langs_common.Parserlib_base
module Astloc = Langs_common.Astloc

module Aux = Parser_aux
module PB = Parserlib_base
module C = Context
module T = Tokens_
module L = Label

let printf = Printf.printf
(*let fprintf = Printf.fprintf*)
let sprintf = Printf.sprintf

type token = Scanner.token
(*type mode = Scanner.mode*)

exception Failed_to_parse of Lexing.position
exception Found

[%%capture_path
class parser_c = object
  inherit [Source.c, Tokens_.token, Ast.c] PB.c (new Aux.env)

  val mutable token_hist_flag = false
  val mutable parse_macro_defs_flag = true
  val mutable dump_tokens_flag = false
  val mutable dump_stats_flag = false

  val mutable scanner = Obj.magic ()
  val mutable _parse = fun () -> Obj.magic ()

  val mutable mode = Aux.M_NORMAL

  val mutable tokens_read = 0

  method set_token_hist_flag () =
    token_hist_flag <- true;
    scanner#set_token_hist_flag()

  method clear_parse_macro_defs_flag () =
    parse_macro_defs_flag <- false

  method set_dump_tokens_flag () =
    dump_tokens_flag <- true;
    env#set_dump_tokens_flag();
    scanner#set_dump_tokens_flag()

  method set_dump_stats_flag () =
    dump_stats_flag <- true;
    scanner#set_dump_stats_flag()

  method make_source file  = new Source.c file
  method make_source_stdin = new Source.c Storage.stdin
  method _parse = _parse()

  method! lines_read = env#current_pos_mgr#lines_read

  method stmts_mode () = mode <- M_STMTS

  method tokens_read = tokens_read

  initializer
    let module S = struct
      let env = env
    end
    in
    let module P = Parser.Make (S) in
    let module I = P.MenhirInterpreter in
    let module Scan = Scanner.F (S) in

    let menv_backup_obj = ref None in

    scanner <- new Scan.c env;

    let token_seq = scanner#token_seq in

    let replay_success_callback () =
      [%debug_log "called"];
      (*menv_backup_obj := None*)
    in
    scanner#register_replay_success_callback replay_success_callback;

    let terminal_to_string : type a . a I.terminal -> string = function
      | T_ACC_SPEC_MACRO -> "ACC_SPEC_MACRO"
      | T_ALIGNAS -> "ALIGNAS"
      | T_ALIGNOF -> "ALIGNOF"
      | T_AMP -> "AMP"
      | T_AMP_AMP -> "AMP_AMP"
      | T_AMP_AMP_BROKEN -> "AMP_AMP_BROKEN"
      | T_AMP_EQ -> "AMP_EQ"
      | T_AND -> "AND"
      | T_AND_EQ -> "AND_EQ"
      | T_ARG_MACRO -> "ARG_MACRO"
      | T_ARGS_MACRO -> "ARGS_MACRO"
      | T_ASM -> "ASM"
      | T_ASM_SHADER -> "ASM_SHADER"
      | T_ASSERT -> "ASSERT"
      | T_AT -> "AT"
      | T_ATTR_LBRACKET -> "ATTR_LBRACKET"
      | T_ATTR_MACRO -> "ATTR_MACRO"
      | T_AUDIT -> "AUDIT"
      | T_AUTO -> "AUTO"
      | T_AXIOM -> "AXIOM"
      | T_BAR -> "BAR"
      | T_BAR_BAR -> "BAR_BAR"
      | T_BAR_BAR_BROKEN -> "BAR_BAR_BROKEN"
      | T_BAR_EQ -> "BAR_EQ"
      | T_BASE_COLON -> "BASE_COLON"
      | T_BEGIN_ASM -> "BEGIN_ASM"
      | T_BEGIN_ETORS -> "BEGIN_ETORS"
      | T_BEGIN_QPROP -> "BEGIN_QPROP"
      | T_BEGIN_STMTS -> "BEGIN_STMTS"
      | T_BITAND -> "BITAND"
      | T_BITOR -> "BITOR"
      | T_BLOCK_HEAD_MACRO -> "BLOCK_HEAD_MACRO"
      | T_BLOCK_END_MACRO -> "BLOCK_END_MACRO"
      | T_BODY_MACRO -> "T_BODY_MACRO"
      | T_BOOL -> "BOOL"
      | T_BOOL_LITERAL -> "BOOL_LITERAL"
      | T_BRACE_LEVEL -> "BRACE_LEVEL"
      | T_BRACE_PAREN_MARKER -> "BRACE_PAREN_MARKER"
      | T_BREAK -> "BREAK"
      | T_BS -> "BS"
      | T_BS_IDENT -> "BS_IDENT"
      | T_CASE -> "CASE"
      | T_CAST_HEAD_MACRO -> "CAST_HEAD_MACRO"
      | T_CATCH -> "CATCH"
      | T_CC_MACRO -> "CC_MACRO"
      | T_CHAR -> "CHAR"
      | T_CHAR16_T -> "CHAR16_T"
      | T_CHAR32_T -> "CHAR32_T"
      | T_CHAR8_T -> "CHAR8_T"
      | T_CHAR_LITERAL -> "CHAR_LITERAL"
      | T_CLASS -> "CLASS"
      | T_CLASS_BODY_HEAD_MACRO -> "CLASS_BODY_HEAD_MACRO"
      | T_CLASS_BODY_END_MACRO -> "CLASS_BODY_END_MACRO"
      | T_CLASS_HEAD_MACRO -> "CLASS_HEAD_MACRO"
      | T_CLASS_LBRACE -> "CLASS_LBRACE"
      | T_COLON -> "COLON"
      | T_COLON_COLON -> "COLON_COLON"
      | T_COLON_GT -> "COLON_GT"
      | T_COMMA -> "COMMA"
      | T_COMMA_BROKEN -> "COMMA_BROKEN"
      | T_COMMA_BROKEN2 -> "COMMA_BROKEN2"
      | T_COMPL -> "COMPL"
      | T_CONCEPT -> "CONCEPT"
      | T_COND_MARKER -> "COND_MARKER"
      | T_CONFLICT_MARKER -> "CONFLICT_MARKER"
      | T_CONST -> "CONST"
      | T_CONSTEVAL -> "CONSTEVAL"
      | T_CONSTEXPR -> "CONSTEXPR"
      | T_CONSTINIT -> "CONSTINIT"
      | T_CONST_CAST -> "CONST_CAST"
      | T_CONTINUE -> "CONTINUE"
      | T_CO_AWAIT -> "CO_AWAIT"
      | T_CO_RETURN -> "CO_RETURN"
      | T_CO_YIELD -> "CO_YIELD"
      | T_CUDA_GT_GT_GT -> "CUDA_GT_GT_GT"
      | T_CUDA_LT_LT_LT -> "CUDA_LT_LT_LT"
      | T_CV_MACRO -> "CV_MACRO"
      | T_DECLTYPE -> "DECLTYPE"
      | T_DECL_MACRO -> "DECL_MACRO"
      | T_DECL_SPEC_MACRO -> "DECL_SPEC_MACRO"
      | T_DEFAULT -> "DEFAULT"
      | T_DEFINED -> "DEFINED"
      | T_DELETE -> "DELETE"
      | T_DELIM_MACRO -> "DELIM_MACRO"
      | T_DO -> "DO"
      | T_DOT -> "DOT"
      | T_DOT_STAR -> "DOT_STAR"
      | T_DOUBLE -> "DOUBLE"
      | T_DOXYGEN_CMD -> "DOXYGEN_CMD"
      | T_DOXYGEN_LINE -> "DOXYGEN_LINE"
      | T_DQ -> "DQ"
      | T_DTOR_MACRO -> "DTOR_MACRO"
      | T_DUMMY_BODY -> "DUMMY_BODY"
      | T_DUMMY_DTOR -> "DUMMY_DTOR"
      | T_DUMMY_OP -> "DUMMY_OP"
      | T_DUMMY_EXPR -> "DUMMY_EXPR"
      | T_DUMMY_STMT -> "DUMMY_STMT"
      | T_DUMMY_TYPE -> "DUMMY_TYPE"
      | T_DYNAMIC_CAST -> "DYNAMIC_CAST"
      | T_ELAB_CLASS -> "ELAB_CLASS"
      | T_ELAB_ENUM -> "ELAB_ENUM"
      | T_ELLIPSIS -> "ELLIPSIS"
      | T_ELLIPSIS_ -> "ELLIPSIS_"
      | T_ELSE -> "ELSE"
      | T_EMPTY_MACRO -> "EMPTY_MACRO"
      | T_END_ASM -> "END_ASM"
      | T_END_ETORS -> "END_ETORS"
      | T_END_QPROP -> "END_QPROP"
      | T_END_STMTS -> "END_STMTS"
      | T_ENSURES -> "ENSURES"
      | T_ENUM -> "ENUM"
      | T_EOF -> "EOF"
      | T_EQ -> "EQ"
      | T_EQ_EQ -> "EQ_EQ"
      | T_EQ_EQ_EQ -> "EQ_EQ_EQ"
      | T_EXCLAM -> "EXCLAM"
      | T_EXCLAM_EQ -> "EXCLAM_EQ"
      | T_EXPECTS -> "EXPECTS"
      | T_EXPLICIT -> "EXPLICIT"
      | T_EXPORT -> "EXPORT"
      | T_EXTERN -> "EXTERN"
      | T_EXTERN_X -> "EXTERN_X"
      | T_FALSE -> "FALSE"
      | T_FINAL -> "FINAL"
      | T_FLOAT -> "FLOAT"
      | T_FLOAT_LITERAL -> "FLOAT_LITERAL"
      | T_FOLD_LPAREN -> "FOLD_LPAREN"
      | T_FOR -> "FOR"
      | T_FRIEND -> "FRIEND"
      | T_FUNC_HEAD_MACRO -> "FUNC_HEAD_MACRO"
      | T_GNU_ASM -> "GNU_ASM"
      | T_GNU_ATTR -> "GNU_ATTR"
      | T_GOTO -> "GOTO"
      | T_GT -> "GT"
      | T_GT_7 -> "GT_7"
      | T_GT_EQ -> "GT_EQ"
      | T_GT_GT -> "GT_GT"
      | T_GT_GT_EQ -> "GT_GT_EQ"
      | T_GT_GT_GT -> "GT_GT_GT"
      | T_HAS_CPP_ATTRIBUTE -> "HAS_CPP_ATTRIBUTE"
      | T_HAS_INCLUDE -> "HAS_INCLUDE"
      | T_HAT -> "HAT"
      | T_HAT_EQ -> "HAT_EQ"
      | T_HEAD_COLON_COLON -> "HEAD_COLON_COLON"
      | T_IDENT -> "IDENT"
      | T_IDENT_ -> "IDENT_"
      | T_IDENT_AGM -> "IDENT_AGM"
      | T_IDENT_AGSM -> "IDENT_AGSM"
      | T_IDENT_AM -> "IDENT_AM"
      | T_IDENT_B -> "IDENT_B"
      | T_IDENT_BEM -> "IDENT_BEM"
      | T_IDENT_BFM -> "IDENT_BFM"
      | T_IDENT_BHM -> "IDENT_BHM"
      | T_IDENT_BIM -> "IDENT_BIM"
      | T_IDENT_BM -> "IDENT_BM"
      | T_IDENT_BSM -> "IDENT_BSM"
      | T_IDENT_C -> "IDENT_C"
      | T_IDENT_CBEM -> "IDENT_CBEM"
      | T_IDENT_CBHM -> "IDENT_CBHM"
      | T_IDENT_CHM -> "IDENT_CHM"
      | T_IDENT_CTM -> "IDENT_CTM"
      | T_IDENT_CM -> "IDENT_CM"
      | T_IDENT_DLM -> "IDENT_DLM"
      | T_IDENT_DM -> "IDENT_DM"
      | T_IDENT_DSL -> "IDENT_DSL"
      | T_IDENT_DSM -> "IDENT_DSM"
      | T_IDENT_E -> "IDENT_E"
      | T_IDENT_EM -> "IDENT_EM"
      | T_IDENT_IEM -> "IDENT_IEM"
      | T_IDENT_IHM -> "IDENT_IHM"
      | T_IDENT_IM -> "IDENT_IM"
      | T_IDENT_LM -> "IDENT_LM"
      | T_IDENT_LOM -> "IDENT_LOM"
      | T_IDENT_LPAREN -> "IDENT_LPAREN"
      | T_IDENT_OM -> "IDENT_OM"
      | T_IDENT_PBM -> "IDENT_PBM"
      | T_IDENT_PDM -> "IDENT_PDM"
      | T_IDENT_PGM -> "IDENT_PGM"
      | T_IDENT_PM -> "IDENT_PM"
      | T_IDENT_SM -> "IDENT_SM"
      | T_IDENT_SXM -> "IDENT_SXM"
      | T_IDENT_TM -> "IDENT_TM"
      | T_IDENT_TPM -> "IDENT_TPM"
      | T_IDENT_NSM -> "IDENT_NSM"
      | T_IDENT_V -> "IDENT_V"
      | T_IDENT_VM -> "IDENT_VM"
      | T_IF -> "IF"
      | T_IMPORT -> "IMPORT"
      | T_IN -> "IN"
      | T_INI_LBRACE -> "INI_LBRACE"
      | T_INLINE -> "INLINE"
      | T_INT -> "INT"
      | T_INT_LITERAL -> "INT_LITERAL"
      | T_INT_MACRO -> "INT_MACRO"
      | T_LAM_LBRACKET -> "LAM_LBRACKET"
      | T_LAM_MACRO -> "LAM_MACRO"
      | T_LAM_MARKER -> "LAM_MARKER"
      | T_LBRACE -> "LBRACE"
      | T_LBRACKET -> "LBRACKET"
      | T_LONG -> "LONG"
      | T_LPAREN -> "LPAREN"
      | T_LT -> "LT"
      | T_LT_COLON -> "LT_COLON"
      | T_LT_EQ -> "LT_EQ"
      | T_LT_EQ_GT -> "LT_EQ_GT"
      | T_LT_LT -> "LT_LT"
      | T_LT_LT_EQ -> "LT_LT_EQ"
      | T_LT_PERC -> "LT_PERC"
      | T_MARKER -> "MARKER"
      | T_MINUS -> "MINUS"
      | T_MINUS_EQ -> "MINUS_EQ"
      | T_MINUS_GT -> "MINUS_GT"
      | T_MINUS_GT_STAR -> "MINUS_GT_STAR"
      | T_MINUS_MINUS -> "MINUS_MINUS"
      | T_MOCK_MARKER -> "MOCK_MARKER"
      | T_MS_ASM -> "MS_ASM"
      | T_MS_ATTR_LBRACKET -> "MS_ATTR_LBRACKET"
      | T_MS_CDECL -> "MS_CDECL"
      | T_MS_PRAGMA -> "MS_PRAGMA"
      | T_MS_PROPERTY -> "MS_PROPERTY"
      | T_MS_SEALED -> "MS_SEALED"
      | T_MS_REF -> "MS_REF"
      | T_MS_STDCALL -> "MS_STDCALL"
      | T_MUTABLE -> "MUTABLE"
      | T_NAMESPACE -> "NAMESPACE"
      | T_NEW -> "NEW"
      | T_NEWLINE -> "NEWLINE"
      | T_NEW_INIT_MACRO -> "NEW_INIT_MACRO"
      | T_NOEXCEPT -> "NOEXCEPT"
      | T_NOEXCEPT_MACRO -> "NOEXCEPT_MACRO"
      | T_NOT -> "NOT"
      | T_NOT_EQ -> "NOT_EQ"
      | T_NS_MACRO -> "NS_MACRO"
      | T_NULLPTR -> "NULLPTR"
      | T_OBJC_AUTORELEASEPOOL -> "OBJC_AUTORELEASEPOOL"
      | T_OBJC_AVAILABLE    -> "OBJC_AVAILABLE"
      | T_OBJC_CATCH        -> "OBJC_CATCH"
      | T_OBJC_CLASS        -> "OBJC_CLASS"
      | T_OBJC_DEFS         -> "OBJC_DEFS"
      | T_OBJC_DYNAMIC      -> "OBJC_DYNAMIC"
      | T_OBJC_ENCODE       -> "OBJC_ENCODE"
      | T_OBJC_END          -> "OBJC_END"
      | T_OBJC_FINALLY      -> "OBJC_FINALLY"
      | T_OBJC_INTERFACE    -> "OBJC_INTERFACE"
      | T_OBJC_LBRACKET     -> "OBJC_LBRACKET"
      | T_OBJC_MINUS        -> "OBJC_MINUS"
      | T_OBJC_OPTIONAL     -> "OBJC_OPTIONAL"
      | T_OBJC_PACKAGE      -> "OBJC_PACKAGE"
      | T_OBJC_PLUS         -> "OBJC_PLUS"
      | T_OBJC_PRIVATE      -> "OBJC_PRIVATE"
      | T_OBJC_PROPERTY     -> "OBJC_PROPERTY"
      | T_OBJC_PROTECTED    -> "OBJC_PROTECTED"
      | T_OBJC_PROTOCOL     -> "OBJC_PROTOCOL"
      | T_OBJC_PROTOCOL_REF_LIST_MACRO -> "OBJC_PROTOCOL_REF_LIST_MACRO"
      | T_OBJC_PUBLIC       -> "OBJC_PUBLIC"
      | T_OBJC_REQUIRED     -> "OBJC_REQUIRED"
      | T_OBJC_SEL_MACRO    -> "OBJC_SEL_MACRO"
      | T_OBJC_SELECTOR     -> "OBJC_SELECTOR"
      | T_OBJC_SYNCHRONIZED -> "OBJC_SYNCHRONIZED"
      | T_OBJC_SYNTHESIZE   -> "OBJC_SYNTHESIZE"
      | T_OBJC_THROW        -> "OBJC_THROW"
      | T_OBJC_TRY          -> "OBJC_TRY"
      | T_OBJC_UNKNOWN      -> "OBJC_UNKNOWN"
      | T_ODD_ELSE -> "ODD_ELSE"
      | T_ODD_FOR -> "ODD_FOR"
      | T_ODD_LBRACE -> "ODD_LBRACE"
      | T_ODD_RBRACE -> "ODD_RBRACE"
      | T_OPERATOR -> "OPERATOR"
      | T_OP_MACRO -> "OP_MACRO"
      | T_OR -> "OR"
      | T_OR_EQ -> "OR_EQ"
      | T_OVERRIDE -> "OVERRIDE"
      | T_PARAM_DECL_MACRO -> "PARAM_DECL_MACRO"
      | T_PARAMS_BODY_MACRO -> "PARAMS_BODY_MACRO"
      | T_PARAMS_MACRO -> "PARAMS_MACRO"
      | T_PERC -> "PERC"
      | T_PERC_COLON -> "PERC_COLON"
      | T_PERC_COLON_PERC_COLON -> "PERC_COLON_PERC_COLON"
      | T_PERC_EQ -> "PERC_EQ"
      | T_PERC_GT -> "PERC_GT"
      | T_PLUS -> "PLUS"
      | T_PLUS_EQ -> "PLUS_EQ"
      | T_PLUS_PLUS -> "PLUS_PLUS"
      | T_PMODE -> "PMODE"
      | T_PP_ -> "PP_"
      | T_PP_DEFINE -> "PP_DEFINE"
      | T_PP_ELIF -> "PP_ELIF"
      | T_PP_ELSE -> "PP_ELSE"
      | T_PP_ENDIF -> "PP_ENDIF"
      | T_PP_ENDIF_ -> "PP_ENDIF_"
      | T_PP_ERROR -> "PP_ERROR"
      | T_PP_IF -> "PP_IF"
      | T_PP_IFDEF -> "PP_IFDEF"
      | T_PP_IFDEF_A -> "PP_IFDEF_A"
      | T_PP_IFDEF_ATTR -> "PP_IFDEF_ATTR"
      | T_PP_IFDEF_B -> "PP_IFDEF_B"
      | T_PP_IFDEF_BROKEN -> "PP_IFDEF_BROKEN"
      | T_PP_IFDEF_C -> "PP_IFDEF_C"
      | T_PP_IFDEF_CB -> "PP_IFDEF_CB"
      | T_PP_IFDEF_CLOSE_OPEN -> "PP_IFDEF_CLOSE_OPEN"
      | T_PP_IFDEF_CLOSING -> "PP_IFDEF_CLOSING"
      | T_PP_IFDEF_COND -> "PP_IFDEF_COND"
      | T_PP_IFDEF_COND_ -> "PP_IFDEF_COND_"
      | T_PP_IFDEF_D -> "PP_IFDEF_D"
      | T_PP_IFDEF_E -> "PP_IFDEF_E"
      | T_PP_IFDEF_EH -> "PP_IFDEF_EH"
      | T_PP_IFDEF_H -> "PP_IFDEF_H"
      | T_PP_IFDEF_I -> "PP_IFDEF_I"
      | T_PP_IFDEF_O -> "PP_IFDEF_O"
      | T_PP_IFDEF_P -> "PP_IFDEF_P"
      | T_PP_IFDEF_S -> "PP_IFDEF_S"
      | T_PP_IFDEF_SHIFT -> "PP_IFDEF_SHIFT"
      | T_PP_IFDEF_X -> "PP_IFDEF_X"
      | T_PP_IFNDEF -> "PP_IFNDEF"
      | T_PP_IFNDEF_A -> "PP_IFNDEF_A"
      | T_PP_IFNDEF_ATTR -> "PP_IFNDEF_ATTR"
      | T_PP_IFNDEF_B -> "PP_IFNDEF_B"
      | T_PP_IFNDEF_BROKEN -> "PP_IFNDEF_BROKEN"
      | T_PP_IFNDEF_C -> "PP_IFNDEF_C"
      | T_PP_IFNDEF_CB -> "PP_IFNDEF_CB"
      | T_PP_IFNDEF_CLOSE_OPEN -> "PP_IFNDEF_CLOSE_OPEN"
      | T_PP_IFNDEF_CLOSING -> "PP_IFNDEF_CLOSING"
      | T_PP_IFNDEF_COND -> "PP_IFNDEF_COND"
      | T_PP_IFNDEF_COND_ -> "PP_IFNDEF_COND_"
      | T_PP_IFNDEF_D -> "PP_IFNDEF_D"
      | T_PP_IFNDEF_E -> "PP_IFNDEF_E"
      | T_PP_IFNDEF_EH -> "PP_IFNDEF_EH"
      | T_PP_IFNDEF_H -> "PP_IFNDEF_H"
      | T_PP_IFNDEF_I -> "PP_IFNDEF_I"
      | T_PP_IFNDEF_O -> "PP_IFNDEF_O"
      | T_PP_IFNDEF_P -> "PP_IFNDEF_P"
      | T_PP_IFNDEF_S -> "PP_IFNDEF_S"
      | T_PP_IFNDEF_SHIFT -> "PP_IFNDEF_SHIFT"
      | T_PP_IFNDEF_X -> "PP_IFNDEF_X"
      | T_PP_IF_A -> "PP_IF_A"
      | T_PP_IF_ATTR -> "PP_IF_ATTR"
      | T_PP_IF_B -> "PP_IF_B"
      | T_PP_IF_BROKEN -> "PP_IF_BROKEN"
      | T_PP_IF_C -> "PP_IF_C"
      | T_PP_IF_CB -> "PP_IF_CB"
      | T_PP_IF_CLOSE_OPEN -> "PP_IF_CLOSE_OPEN"
      | T_PP_IF_CLOSING -> "PP_IF_CLOSING"
      | T_PP_IF_COND -> "PP_IF_COND"
      | T_PP_IF_COND_ -> "PP_IF_COND_"
      | T_PP_IF_D -> "PP_IF_D"
      | T_PP_IF_E -> "PP_IF_E"
      | T_PP_IF_EH -> "PP_IF_EH"
      | T_PP_IF_H -> "PP_IF_H"
      | T_PP_IF_I -> "PP_IF_I"
      | T_PP_IF_O -> "PP_IF_O"
      | T_PP_IF_P -> "PP_IF_P"
      | T_PP_IF_S -> "PP_IF_S"
      | T_PP_IF_SHIFT -> "PP_IF_SHIFT"
      | T_PP_IF_X -> "PP_IF_X"
      | T_PP_IMPORT -> "PP_IMPORT"
      | T_PP_INCLUDE -> "PP_INCLUDE"
      | T_PP_LINE -> "PP_LINE"
      | T_PP_LPAREN -> "PP_LPAREN"
      | T_PP_MARKER -> "PP_MARKER"
      | T_PP_ODD_ELIF -> "PP_ODD_ELIF"
      | T_PP_ODD_ELSE -> "PP_ODD_ELSE"
      | T_PP_ODD_ENDIF -> "PP_ODD_ENDIF"
      | T_PP_ODD_IF -> "PP_ODD_IF"
      | T_PP_ODD_IFDEF -> "PP_ODD_IFDEF"
      | T_PP_ODD_IFNDEF -> "PP_ODD_IFNDEF"
      | T_PP_PRAGMA -> "PP_PRAGMA"
      | T_PP_STRINGIZED -> "PP_STRINGIZED"
      | T_PP_UNDEF -> "PP_UNDEF"
      | T_PP_UNKNOWN -> "PP_UNKNOWN"
      | T_PRAGMA_MACRO -> "PRAGMA_MACRO"
      | T_PRIVATE -> "PRIVATE"
      | T_PROTECTED -> "PROTECTED"
      | T_PS_LPAREN -> "PS_LPAREN"
      | T_PTR_AMP -> "PTR_AMP"
      | T_PTR_AMP_AMP -> "PTR_AMP_AMP"
      | T_PTR_DTOR_MACRO -> "PTR_DTOR_MACRO"
      | T_PTR_HAT -> "PTR_HAT"
      | T_PTR_MACRO -> "PTR_MACRO"
      | T_PTR_STAR -> "PTR_STAR"
      | T_PUBLIC -> "PUBLIC"
      | T_PURE_ZERO -> "PURE_ZERO"
      | T_QUEST -> "QUEST"
      | T_RBRACE -> "RBRACE"
      | T_RBRACKET -> "RBRACKET"
      | T_REF_MACRO -> "REF_MACRO"
      | T_REGISTER -> "REGISTER"
      | T_REINTERPRET_CAST -> "REINTERPRET_CAST"
      | T_REQUIRES -> "REQUIRES"
      | T_RESTRICT -> "RESTRICT"
      | T_RETURN -> "RETURN"
      | T_RPAREN -> "RPAREN"
      | T_SECTION_MARKER -> "SECTION_MARKER"
      | T_SEMICOLON -> "SEMICOLON"
      | T_SEMICOLON_ -> "SEMICOLON_"
      | T_SHARP -> "SHARP"
      | T_SHARP_SHARP -> "SHARP_SHARP"
      | T_SHORT -> "SHORT"
      | T_SIGNED -> "SIGNED"
      | T_SIZEOF -> "SIZEOF"
      | T_SLASH -> "SLASH"
      | T_SLASH_EQ -> "SLASH_EQ"
      | T_S_LPAREN -> "S_LPAREN"
      | T_S_RPAREN -> "S_RPAREN"
      | T_SS_LPAREN -> "SS_LPAREN"
      | T_STAR -> "STAR"
      | T_STAR_EQ -> "STAR_EQ"
      | T_STATIC -> "STATIC"
      | T_STATIC_ASSERT -> "STATIC_ASSERT"
      | T_STATIC_CAST -> "STATIC_CAST"
      | T_STMT_MACRO -> "STMT_MACRO"
      (*| T_STMT_MARKER -> "STMT_MARKER"*)
      | T_STRUCT -> "STRUCT"
      | T_STR_LITERAL -> "STR_LITERAL"
      | T_STR_MACRO -> "STR_MACRO"
      | T_STR_MARKER -> "STR_MARKER"
      | T_SUB_REQUIRES -> "SUB_REQUIRES"
      | T_SUFFIX_MACRO -> "SUFFIX_MACRO"
      | T_SUFFIX_MARKER -> "SUFFIX_MARKER"
      | T_SWITCH -> "SWITCH"
      | T_TEMPLATE -> "TEMPLATE"
      | T_TEMPL_GT -> "TEMPL_GT"
      | T_TEMPL_LT -> "TEMPL_LT"
      | T_TEMPL_LT_ -> "TEMPL_LT_"
      | T_THIS -> "THIS"
      | T_THREAD_LOCAL -> "THREAD_LOCAL"
      | T_THROW -> "THROW"
      | T_THROW_ -> "THROW_"
      | T_TILDE -> "TILDE"
      | T_TRUE -> "TRUE"
      | T_TRY -> "TRY"
      | T_TYPEDEF -> "TYPEDEF"
      | T_TYPEID -> "TYPEID"
      | T_TYPENAME -> "TYPENAME"
      | T_TY_HAT -> "TY_HAT"
      | T_TY_LPAREN -> "TY_LPAREN"
      | T_TY_LPAREN_ -> "TY_LPAREN_"
      | T_TYPE_MACRO -> "TYPE_MACRO"
      | T_BASE_MACRO -> "BASE_MACRO"
      | T_BASE_SPEC_MACRO -> "BASE_SPEC_MACRO"
      | T_TY_TEMPL_GT -> "TY_TEMPL_GT"
      | T_TY_TEMPL_GT_ -> "TY_TEMPL_GT_"
      | T_TY_TILDE -> "TY_TILDE"
      | T_UNION -> "UNION"
      | T_UNSIGNED -> "UNSIGNED"
      | T_USER_CHAR_LITERAL -> "USER_CHAR_LITERAL"
      | T_USER_FLOAT_LITERAL -> "USER_FLOAT_LITERAL"
      | T_USER_INT_LITERAL -> "USER_INT_LITERAL"
      | T_USER_STR_LITERAL -> "USER_STR_LITERAL"
      | T_USING -> "USING"
      | T_VAX_GLOBALDEF -> "VAX_GLOBALDEF"
      | T_VIRTUAL -> "VIRTUAL"
      | T_VIRT_SPEC_MACRO -> "VIRT_SPEC_MACRO"
      | T_VOID -> "VOID"
      | T_VOLATILE -> "VOLATILE"
      | T_WCHAR_T -> "WCHAR_T"
      | T_WHILE -> "WHILE"
      | T_XOR -> "XOR"
      | T_XOR_EQ -> "XOR_EQ"
      | T_error -> "error"
(*      | _ -> "???"*)
    in
    let nonterminal_to_string : type a . a I.nonterminal -> string = function
      | N___initializer_list -> "__initializer_list"
      | N__alias_declaration -> "_alias_declaration"
      | N__asm_declaration -> "_asm_declaration"
      | N__block_declaration -> "_block_declaration"
      | N__designated_initializer_list -> "_designated_initializer_list"
      | N__init_statement -> "_init_statement"
      | N__initializer_list -> "_initializer_list"
      | N__namespace_alias_definition -> "_namespace_alias_definition"
      | N__lambda_expression -> "_lambda_expression"
      | N__odd_stmt -> "_odd_stmt"
      | N__opaque_enum_declaration -> "_opaque_enum_declaration"
      | N__pp_control_line -> "_pp_control_line"
      | N__pp_define -> "_pp_define"
      | N__pp_dinit_if_section_list -> "_pp_dinit_if_section_list"
      | N__pp_func_head_elif_group -> "_pp_func_head_elif_group"
      | N__pp_func_head_else_group -> "_pp_func_head_else_group"
      | N__pp_func_head_if_group -> "_pp_func_head_if_group"
      | N__pp_func_head_if_section -> "_pp_func_head_if_section"
      | N__pp_idtor_if_section -> "_pp_idtor_if_section"
      | N__pp_eor_elif_group -> "_pp_ior_elif_group"
      | N__pp_ior_elif_group -> "_pp_ior_elif_group"
      | N__pp_eor_else_group -> "_pp_ior_else_group"
      | N__pp_ior_else_group -> "_pp_ior_else_group"
      | N__pp_eor_if_group -> "_pp_ior_if_group"
      | N__pp_ior_if_group -> "_pp_ior_if_group"
      | N__pp_eor_if_section -> "_pp_ior_if_section"
      | N__pp_ior_if_section -> "_pp_ior_if_section"
      | N__pp_land_elif_group -> "_pp_land_elif_group"
      | N__pp_land_else_group -> "_pp_land_else_group"
      | N__pp_land_if_group -> "_pp_land_if_group"
      | N__pp_land_if_section -> "_pp_land_if_section"
      | N__pp_lor_elif_group -> "_pp_lor_elif_group"
      | N__pp_lor_else_group -> "_pp_lor_else_group"
      | N__pp_lor_if_group -> "_pp_lor_if_group"
      | N__pp_lor_if_section -> "_pp_lor_if_section"
      | N__pp_param_list -> "pp_param_list"
      | N__simple_declaration -> "_simple_declaration"
      | N__statement_seq -> "_statement_seq"
      | N__static_assert_declaration -> "_static_assert_declaration"
      | N__type_specifier_seq -> "_type_specifier_seq"
      | N__using_declaration -> "_using_declaration"
      | N__using_enum_declaration -> "_using_enum_declaration"
      | N__using_directive -> "_using_directive"
      | N_abstract_declarator -> "abstract_declarator"
      | N_abstract_pack_declarator -> "abstract_pack_declarator"
      | N_acc_annot -> "acc_annot"
      | N_access_specifier -> "access_specifier"
      | N_additive_expression -> "additive_expression"
      | N_alias_declaration -> "alias_declaration"
      | N_alignment_specifier -> "alignment_specifier"
      | N_and_expression -> "and_expression"
      | N_asm_block -> "asm_block"
      | N_asm_token -> "asm_token"
      | N_assignment_expression -> "assignment_expression"
      | N_assignment_operator -> "assignment_operator"
      | N_attr_macro_call -> "attr_macro_call"
      | N_attribute -> "attribute"
      | N_attribute_argument_clause -> "attribute_argument_clause"
      | N_attribute_argument_clause_opt -> "attribute_argument_clause_opt"
      | N_attribute_declaration -> "attribute_declaration"
      | N_attribute_list -> "attribute_list"
      | N_attribute_namespace_seq -> "attribute_namespace_seq"
      | N_attribute_scoped_token -> "attribute_scoped_token"
      | N_attribute_specifier -> "attribute_specifier"
      | N_attribute_specifier_seq -> "attribute_specifier_seq"
      | N_attribute_token -> "attribute_token"
      | N_attribute_using_prefix -> "attribute_using_prefix"
      | N_await_expression -> "await_expression"
      | N_balanced_token -> "balanced_token"
      | N_balanced_token_seq -> "balanced_token_seq"
      | N_balanced_token_seq_opt -> "balanced_token_seq_opt"
      | N_base_clause -> "base_clause"
      | N_base_specifier -> "base_specifier"
      | N_base_specifier_list -> "base_specifier_list"
      | N_bit_field_macro_call -> "bit_field_macro_call"
      | N_block_declaration -> "block_declaration"
      | N_block_end_macro -> "block_end_macro"
      | N_block_head_macro -> "block_head_macro"
      | N_block_literal_expression -> "block_literal_expression"
      | N_brace_or_equal_initializer -> "brace_or_equal_initializer"
      | N_braced_init_list -> "braced_init_list"
      | N_capture -> "capture"
      | N_capture_default -> "capture_default"
      | N_capture_list -> "capture_list"
      | N_capture_macro_call -> "capture_macro_call"
      | N_cast_expression -> "cast_expression"
      | N_cast_key -> "cast_key"
      | N_char_literal -> "char_literal"
      | N_class_body_end_macro -> "class_body_end_macro"
      | N_class_body_head_macro -> "class_body_head_macro"
      | N_class_head -> "class_head"
      | N_class_head_name -> "class_head_name"
      | N_class_key -> "class_key"
      | N_class_name -> "class_name"
      | N_class_or_decltype -> "class_or_decltype"
      | N_class_specifier -> "class_specifier"
      | N_class_virt_specifier -> "class_virt_specifier"
      | N_compare_expression -> "compare_expression"
      | N_compound_requirement -> "compound_requirement"
      | N_compound_statement -> "compound_statement"
      | N_concept_definition -> "concept_definition"
      | N_cond_unit_seq -> "cond_unit_seq"
      | N_condition -> "condition"
      | N_conditional_expression -> "conditional_expression"
      | N_constant_expression -> "constant_expression"
      | N_constraint_expression -> "constraint_expression"
      | N_constraint_logical_and_expression -> "constraint_logical_and_expression"
      | N_constraint_logical_or_expression -> "constraint_logical_or_expression"
      | N_contract_attribute_specifier -> "contract_attribute_specifier"
      | N_contract_level -> "contract_level"
      | N_contract_level_opt -> "contract_level_opt"
      | N_conversion_declarator -> "conversion_declarator"
      | N_conversion_function_id -> "conversion_function_id"
      | N_conversion_type_id -> "conversion_type_id"
      | N_ctor_initializer -> "ctor_initializer"
      | N_cuda_exec_config -> "cuda_exec_config"
      | N_cv_qualifier -> "cv_qualifier"
      | N_cv_qualifier_seq -> "cv_qualifier_seq"
      | N_decl_OR_expr -> "decl_OR_expr"
      | N_decl_OR_stmt_macro_call -> "decl_OR_stmt_macro_call"
      | N_decl_macro_call_ -> "decl_macro_call_"
      | N_decl_spec_macro -> "decl_spec_macro"
      | N_decl_spec_macro_call -> "decl_spec_macro_call"
      | N_decl_specifier -> "decl_specifier"
      | N_decl_specifier_seq -> "decl_specifier_seq"
      | N_declaration -> "declaration"
      | N_declaration_seq -> "declaration_seq"
      | N_declarator -> "declarator"
      | N_declarator_id -> "declarator_id"
      | N_decls_sub -> "decls_sub"
      | N_decltype_specifier -> "decltype_specifier"
      | N_deduction_guide -> "deduction_guide"
      | N_defined_macro_expression -> "defined_macro_expression"
      | N_defining_type_id -> "defining_type_id"
      | N_defining_type_specifier -> "defining_type_specifier"
      | N_defining_type_specifier_seq -> "defining_type_specifier_seq"
      | N_delete_expression -> "delete_expression"
      | N_delim -> "delim"
      | N_delim_macro -> "delim_macro"
      | N_delim_macro_call -> "delim_macro_call"
      | N_designated_initializer_clause -> "designated_initializer_clause"
      | N_designator -> "designator"
      | N_dsl_macro -> "dsl_macro"
      | N_dsl_macro_args -> "dsl_macro_args"
      | N_dtors_sub -> "dtors_sub"
      | N_elaborated_type_specifier -> "elaborated_type_specifier"
      | N_empty_declaration -> "empty_declaration"
      | N_enclosing_namespace_specifier -> "enclosing_namespace_specifier"
      | N_enum_base -> "enum_base"
      | N_enum_head -> "enum_head"
      | N_enum_key -> "enum_key"
      | N_enum_specifier -> "enum_specifier"
      | N_enumerator -> "enumerator"
      | N_enumerator_definition -> "enumerator_definition"
      | N_enumerator_list -> "enumerator_list"
      | N_equality_expression -> "equality_expression"
      | N_error_token -> "error_token"
      | N_error_token_seq -> "error_token_seq"
      | N_etors_sub -> "etors_sub"
      | N_exception_declaration -> "exception_declaration"
      | N_exclusive_or_expression -> "exclusive_or_expression"
      | N_explicit_instantiation -> "explicit_instantiation"
      | N_explicit_specialization -> "explicit_specialization"
      | N_explicit_specifier -> "explicit_specifier"
      | N_export_declaration -> "export_declaration"
      | N_expr_macro_call -> "expr_macro_call"
      | N_expr_or_braced_init_list -> "expr_or_braced_init_list"
      | N_expr_sub -> "expr_sub"
      | N_expression -> "expression"
      | N_expression_list -> "expression_list"
      | N_expression_list_opt -> "expression_list_opt"
      | N_extra_keyword -> "extra_keyword"
      | N_fold_expression -> "fold_expression"
      | N_fold_operator -> "fold_operator"
      | N_for_range_declaration -> "for_range_declaration"
      | N_for_range_initializer -> "for_range_initializer"
      | N_function_body -> "function_body"
      | N_function_definition -> "function_definition"
      | N_function_specifier -> "function_specifier"
      | N_function_try_block -> "function_try_block"
      | N_gnu_asm_attr -> "gnu_asm_attr"
      | N_gnu_asm_frag_seq -> "gnu_asm_frag_seq"
      | N_gnu_asm_token -> "gnu_asm_token"
      | N_gnu_attribute -> "gnu_attribute"
      | N_gnu_attribute_seq -> "gnu_attribute_seq"
      | N_handler -> "handler"
      | N_header_name_token -> "header_name_token"
      | N_handler_seq -> "handler_seq"
      | N_has_attribute_expression -> "has_attribute_expression"
      | N_has_include_expression -> "has_include_expression"
      | N_id_expression -> "id_expression"
      | N_id_macro_call -> "id_macro_call"
      | N_identifier_list -> "identifier_list"
      | N_inclusive_or_expression -> "inclusive_or_expression"
      | N_init_capture -> "init_capture"
      | N_init_declarator -> "init_declarator"
      | N_init_declarator_list -> "init_declarator_list"
      | N_init_end_macro -> "init_end_macro"
      | N_init_head_macro -> "init_head_macro"
      | N_init_statement -> "init_statement"
      | N_init_sub -> "init_sub"
      | N_initializer_ -> "initializer_"
      | N_initializer_clause -> "initializer_clause"
      | N_initializer_list -> "initializer_list"
      | N_ior_unit_seq -> "ior_unit_seq"
      | N_iteration_macro -> "iteration_macro"
      | N_iteration_statement -> "iteration_statement"
      | N_jump_statement -> "jump_statement"
      | N_label -> "label"
      | N_label_seq -> "label_seq"
      | N_labeled_statement -> "labeled_statement"
      | N_lambda_capture -> "lambda_capture"
      | N_lambda_declarator -> "lambda_declarator"
      | N_lambda_expression -> "lambda_expression"
      | N_lambda_introducer -> "lambda_introducer"
      | N_land_unit_seq -> "land_unit_seq"
      | N_linkage_specification -> "linkage_specification"
      | N_list_INT_LITERAL_ -> "list(INT_LITERAL)"
      | N_list__pp_func_head_elif_group_ -> "list(_pp_func_head_elif_group)"
      | N_list__pp_eor_elif_group_ -> "list(_pp_eor_elif_group)"
      | N_list__pp_ior_elif_group_ -> "list(_pp_ior_elif_group)"
      | N_list__pp_land_elif_group_ -> "list(_pp_land_elif_group)"
      | N_list__pp_lor_elif_group_ -> "list(_pp_lor_elif_group)"
      | N_list_asm_token_ -> "list(asm_token)"
      | N_list_gnu_asm_token_ -> "list(asm_token)"
      | N_list_pp_a_elif_group_ -> "list(pp_a_elif_group)"
      | N_list_pp_aexpr_elif_group_ -> "list(pp_aexpr_elif_group)"
      | N_list_pp_aexpr_elif_group_closing_ -> "list(pp_aexpr_elif_group)"
      | N_list_pp_args_elif_group_close_open_ -> "list(pp_args_elif_group_close_open)"
      | N_list_pp_args_elif_group_closing_ -> "list(pp_args_elif_group_closing)"
      | N_list_pp_attr_elif_group_ -> "list(pp_attr_elif_group)"
      | N_list_pp_base_clause_elif_group_ -> "list(pp_base_clause_elif_group)"
      | N_list_pp_capture_elif_group_ -> "list(pp_capture_elif_group)"
      | N_list_pp_cc_elif_group_ -> "list(pp_cc_elif_group)"
      | N_list_pp_class_body_elif_group_ -> "list(pp_class_body_elif_group)"
      | N_list_pp_class_head_elif_group_ -> "list(pp_class_head_elif_group)"
      | N_list_pp_class_head_elif_group_broken_ -> "list(pp_class_head_elif_group_broken)"
      | N_list_pp_cond_elif_group_ -> "list(pp_cond_elif_group)"
      | N_list_pp_cond_hd_elif_group_ -> "list(pp_cond_hd_elif_group)"
      | N_list_pp_cond_tl_elif_group_ -> "list(pp_cond_tl_elif_group)"
      | N_list_pp_control_line_ -> "list(pp_control_line)"
      | N_list_pp_ctor_init_elif_group_ -> "list(pp_ctor_init_elif_group)"
      | N_list_pp_decl_elif_group_ -> "list(pp_decl_elif_group)"
      | N_list_pp_decl_elif_group_broken_ -> "list(pp_decl_elif_group_broken)"
      | N_list_pp_decl_spec_elif_group_ -> "list(pp_decl_spec_elif_group)"
      | N_list_pp_dinit_elif_group_ -> "list(pp_dinit_elif_group)"
      | N_list_pp_dtor_elif_group_ -> "list(pp_dtor_elif_group)"
      | N_list_pp_dtor_elif_group_broken_ -> "list(pp_dtor_elif_group_broken)"
      | N_list_pp_edef_elif_group_ -> "list(pp_edef_elif_group)"
      | N_list_pp_enum_elif_group_closing_ -> "list(pp_enum_elif_group_closing)"
      | N_list_pp_enum_head_elif_group_ -> "list(pp_enum_head_elif_group)"
      | N_list_pp_expr_elif_group_ -> "list(pp_expr_elif_group)"
      | N_list_pp_expr_elif_group_broken_ -> "list(pp_expr_elif_group_broken)"
      | N_list_pp_expr_elif_group_broken2_ -> "list(pp_expr_elif_group_broken2)"
      | N_list_pp_func_body_elif_group_ -> "list(pp_func_body_elif_group)"
      | N_list_pp_func_head_elif_group_broken_ -> "list(pp_func_head_elif_group_broken)"
      | N_list_pp_gnu_asm_elif_group_ -> "list(pp_gnu_asm_elif_group)"
      | N_list_pp_handler_elif_group_ -> "list(pp_handler_elif_group)"
      | N_list_pp_handler_elif_group_broken_ -> "list(pp_handler_elif_group_broken)"
      | N_list_pp_idtor_elif_group_ -> "list(pp_idtor_elif_group)"
      | N_list_pp_ifstmt_elif_group_closing_ -> "list(pp_ifstmt_elif_group_closing)"
      | N_list_pp_init_elif_group_ -> "list(pp_init_elif_group)"
      | N_list_pp_init_elif_group_closing_ -> "list(pp_init_elif_group_closing)"
      | N_list_pp_ior_elif_group_ -> "list(pp_ior_elif_group)"
      | N_list_pp_lambda_head_elif_group_broken_ -> "list(pp_lambda_head_elif_group_broken)"
      | N_list_pp_land_elif_group_ -> "list(pp_land_elif_group)"
      | N_list_pp_lor_elif_group_ -> "list(pp_lor_elif_group)"
      | N_list_pp_mdecl_elif_group_ -> "list(pp_mdecl_elif_group)"
      | N_list_pp_mdecl_elif_group_broken_ -> "list(pp_mdecl_elif_group_broken)"
      | N_list_pp_minit_elif_group_ -> "list(pp_minit_elif_group)"
      | N_list_pp_minit_elif_group_broken_ -> "list(pp_minit_elif_group_broken)"
      | N_list_pp_objc_category_interface_head_elif_group_ -> "list(objc_category_interface_head_elif_group)"
      | N_list_pp_objc_class_interface_head_elif_group_ -> "list(objc_class_interface_head_elif_group)"
      | N_list_pp_objc_idecl_elif_group_ -> "list(objc_idecl_elif_group)"
      | N_list_pp_objc_ivar_decl_elif_group_ -> "list(objc_ivar_decl_elif_group)"
      | N_list_pp_objc_proto_name_elif_group_ -> "list(objc_proto_name_elif_group)"
      | N_list_pp_objc_protocol_ref_list_elif_group_ -> "list(objc_protocol_ref_list_elif_group)"
      | N_list_pp_p_elif_group_ -> "list(pp_p_elif_group)"
      | N_list_pp_old_param_decl_list_elif_group_ -> "list(pp_old_param_decl_list_elif_group)"
      | N_list_pp_param_elif_group_ -> "list(pp_param_elif_group)"
      | N_list_pp_stmt_elif_group_ -> "list(pp_stmt_elif_group)"
      | N_list_pp_stmt_elif_group_broken_ -> "list(pp_stmt_elif_group_broken)"
      | N_list_pp_stmt_elif_group_close_open_ -> "list(pp_stmt_elif_group_close_open)"
      | N_list_pp_stmt_elif_group_closing_ -> "list(pp_stmt_elif_group_closing)"
      | N_list_pp_spec_elif_group_ -> "list(pp_spec_elif_group)"
      | N_list_pp_str_elif_group_ -> "list(pp_str_elif_group)"
      | N_list_pp_templ_arg_elif_group_ -> "list(pp_templ_arg_elif_group)"
      | N_list_pp_templ_param_elif_group_ -> "list(pp_templ_param_elif_group)"
      | N_list_str__ -> "list(str_)"
      | N_literal -> "literal"
      | N_literal_macro_call -> "literal_macro_call"
      | N_literal_operator_id -> "literal_operator_id"
      | N_logical_and_expression -> "logical_and_expression"
      | N_logical_or_expression -> "logical_or_expression"
      | N_lor_macro_call -> "lor_macro_call"
      | N_lor_unit_seq -> "lor_unit_seq"
      | N_macro_arg -> "macro_arg"
      | N_macro_arg_list -> "macro_arg_list"
      | N_macro_fun_head -> "macro_fun_head"
      | N_main -> "main"
      | N_mem_access_spec -> "mem_access_spec"
      | N_mem_access_spec_head -> "mem_access_spec_head"
      | N_mem_decl_seq -> "mem_decl_seq"
      | N_mem_decls_sub -> "mem_decls_sub"
      | N_mem_init_macro_call -> "mem_init_macro_call"
      | N_mem_initializer -> "mem_initializer"
      | N_mem_initializer_id -> "mem_initializer_id"
      | N_mem_initializer_list -> "mem_initializer_list"
      | N_member_declaration -> "member_declaration"
      | N_member_declarator -> "member_declarator"
      | N_member_declarator_list -> "member_declarator_list"
      | N_member_specification -> "member_specification"
      | N_mid_paren_close -> "mid_paren_close"
      | N_mid_brace_close -> "mid_brace_close"
      | N_mid_brace_open -> "mid_brace_open"
      | N_mid_init -> "mid_init"
      | N_mid_objc_cat_iface -> "mid_objc_cat_iface"
      | N_mid_paren_open -> "mid_paren_open"
      | N_mid_templ_decl -> "mid_templ_decl"
      | N_mid_templ_head -> "mid_templ_head"
      | N_mid_typaram -> "mid_typaram"
      | N_module_import_declaration -> "module_import_declaration"
      | N_mock_qualifier -> "mock_qualifier"
      | N_ms_attr -> "ms_attr"
      | N_ms_warn_spec -> "ms_warn_spec"
      | N_ms_warn_spec_list -> "ms_warn_spec_list"
      | N_multiplicative_expression -> "multiplicative_expression"
      | N_named_namespace_definition -> "named_namespace_definition"
      | N_named_namespace_definition_head -> "named_namespace_definition_head"
      | N_namespace_body -> "namespace_body"
      | N_namespace_definition -> "namespace_definition"
      | N_nested_name_specifier -> "nested_name_specifier"
      | N_nested_namespace_definition -> "nested_namespace_definition"
      | N_nested_namespace_definition_head -> "nested_namespace_definition_head"
      | N_nested_requirement -> "nested_requirement"
      | N_new_declarator -> "new_declarator"
      | N_new_expression -> "new_expression"
      | N_new_initializer -> "new_initializer"
      | N_new_placement -> "new_placement"
      | N_new_type_id -> "new_type_id"
      | N_nodeclspec_function_definition -> "nodeclspec_function_definition"
      | N_noexcept_expression -> "noexcept_expression"
      | N_noexcept_specifier -> "noexcept_specifier"
      (*| N_nonempty_list_arg_macro_ -> "nonempty_list(arg_macro)"*)
      | N_nonempty_list__pp_lor_if_section_ -> "nonempty_list(_pp_lor_if_section)"
      | N_nonempty_list_additive_unit_ -> "nonempty_list(additive_unit)"
      | N_nonempty_list_char_literal_ -> "nonempty_list(char_literal)"
      | N_nonempty_list_designator_ -> "nonempty_list(designator)"
      | N_nonempty_list_error_token_ -> "nonempty_list(error_token)"
      | N_nonempty_list_int_literal_ -> "nonempty_list(int_literal)"
      | N_nonempty_list_gnu_asm_token_ -> "nonempty_list(gnu_asm_token)"
      | N_nonempty_list_header_name_token_ -> "nonempty_list(header_name_token)"
      | N_nonempty_list_multiplicative_unit_ -> "nonempty_list(multiplicative_unit)"
      | N_nonempty_list_namespace_definition_ -> "nonempty_list(namespace_definition)"
      | N_nonempty_list_objc_catch_clause_ -> "nonempty_list(objc_catch_clause)"
      | N_nonempty_list_objc_instance_var_decl_ -> "nonempty_list(objc_instance_var_decl)"
      | N_nonempty_list_objc_keyword_arg_ -> "nonempty_list(objc_keyword_arg)"
      | N_nonempty_list_objc_keyword_dtor_ -> "nonempty_list(objc_keyword_dtor)"
      | N_nonempty_list_odd_else_stmt_ -> "nonempty_list(odd_else_stmt)"
      | N_nonempty_list_pp_base_clause_if_section_ -> "nonempty_list(pp_base_clause_if_section)"
      | N_nonempty_list_pp_control_line_ -> "nonempty_list(pp_control_line)"
      | N_nonempty_list_pp_idtor_if_section_ -> "nonempty_list(pp_idtor_if_section)"
      | N_nonempty_list_pp_param_if_section_ -> "nonempty_list(pp_param_if_section)"
      | N_nonempty_list_QUEST_ -> "nonempty_list(QUEST)"
      | N_nonempty_list_q_prop_token_ -> "nonempty_list(q_prop_token)"
      | N_nonempty_list_RBRACE_ -> "nonempty_list(RBRACE)"
      | N_nonempty_list_s_token_ -> "nonempty_list(s_token)"
      | N_nonempty_list_swift_arg_ -> "nonempty_list(swift_arg)"
      | N_nonempty_list_token_ -> "nonempty_list(token)"
      | N_noptr_abstract_declarator -> "noptr_abstract_declarator"
      | N_noptr_abstract_pack_declarator -> "noptr_abstract_pack_declarator"
      | N_noptr_declarator -> "noptr_declarator"
      | N_noptr_new_declarator -> "noptr_new_declarator"
      | N_objc_array -> "objc_array"
      | N_objc_avail_item -> "objc_avail_item"
      | N_objc_available -> "objc_available"
      | N_objc_class_decl_list -> "objc_class_declaration_list"
      | N_objc_catch_clause -> "objc_catch_clause"
      | N_objc_category_interface -> "objc_category_interface"
      | N_objc_class_interface -> "objc_class_interface"
      | N_objc_class_name -> "objc_class_name"
      | N_objc_decls_sub -> "objc_decls_sub"
      | N_objc_dict -> "objc_dict"
      | N_objc_encode_expr -> "objc_encode_expr"
      | N_objc_finally -> "objc_finally"
      | N_objc_idecl_seq -> "objc_idecl_seq"
      | N_objc_identifier -> "objc_identifier"
      | N_objc_instance_var_decl -> "objc_instance_var_decl"
      | N_objc_instance_vars -> "objc_instance_vars"
      | N_objc_interface_decl -> "objc_interface_decl"
      | N_objc_key_value -> "objc_key_value"
      | N_objc_keyword_arg -> "objc_keyword_arg"
      | N_objc_keyword_dtor -> "objc_keyword_dtor"
      | N_objc_keyword_name -> "objc_keyword_arg_name"
      | N_objc_keyword_name_list -> "objc_keyword_arg_name_list"
      | N_objc_keyword_selector -> "objc_keyword_selector"
      | N_objc_literal -> "objc_literal"
      | N_objc_message_expr -> "objc_message_expr"
      | N_objc_message_selector -> "objc_message_selector"
      | N_objc_method_decl -> "objc_method_decl"
      | N_objc_method_selector -> "objc_method_selector"
      | N_objc_method_type -> "objc_method_type"
      | N_objc_odd_decl -> "objc_odd_decl"
      | N_objc_property_attr -> "objc_property_attr"
      | N_objc_property_attrs_decl -> "objc_property_attrs_decl"
      | N_objc_property_decl -> "objc_property_decl"
      | N_objc_protocol_decl -> "objc_protocol_decl"
      | N_objc_protocol_decl_list -> "objc_protocol_decl_list"
      | N_objc_protocol_expr -> "objc_protocol_expr"
      | N_objc_protocol_name -> "objc_protocol_name"
      | N_objc_protocol_name_list -> "objc_protocol_name_list"
      | N_objc_protocol_ref_list -> "objc_protocol_ref_list"
      | N_objc_qualified_idecl_seq -> "objc_qualified_idecl_seq"
      | N_objc_qualified_interface_decl -> "objc_qualified_interface_decl"
      | N_objc_selector -> "objc_selector"
      | N_objc_selector_expr -> "objc_selector_expr"
      | N_objc_struct_decl -> "objc_struct_decl"
      | N_objc_struct_dtor -> "objc_struct_dtor"
      | N_objc_superclass -> "objc_superclass"
      | N_objc_try_block -> "objc_try_block"
      | N_objc_try -> "objc_try"
      | N_objc_visibility_spec -> "objc_visibility_spec"
      | N_odd_decl -> "odd_decl"
      | N_odd_else_stmt -> "odd_else_stmt"
      | N_odd_expr -> "odd_expr"
      | N_odd_if_stmt_open -> "odd_if_stmt_open"
      | N_odd_mult_expr -> "odd_mult_expr"
      | N_odd_mem_decl -> "odd_mem_decl"
      | N_odd_stmt -> "odd_stmt"
      | N_old_init_decl_list -> "old_init_decl_list"
      | N_old_param_decl -> "old_param_decl"
      | N_old_param_decl_list -> "old_param_decl_list"
      | N_op_macro_call -> "op_macro_call"
      | N_opaque_enum_declaration -> "opaque_enum_declaration"
      | N_operator -> "operator"
      | N_operator_function_id -> "operator_function_id"
      | N_parameter_declaration -> "parameter_declaration"
      | N_parameter_declaration_clause -> "parameter_declaration_clause"
      | N_parameter_declaration_list -> "parameter_declaration_list"
      | N_parameters_and_qualifiers -> "parameters_and_qualifiers"
      | N_params_body_macro -> "params_body_macro"
      | N_params_body_macro_call -> "params_body_macro_call"
      | N_params_list -> "params_list"
      | N_placeholder_type_specifier -> "placeholder_type_specifier"
      | N_pm_expression -> "pm_expression"
      | N_postfix_expression -> "postfix_expression"
      | N_pp_a_elif_group -> "pp_a_elif_group"
      | N_pp_a_else_group -> "pp_a_else_group"
      | N_pp_a_if_group -> "pp_a_if_group"
      | N_pp_a_if_section -> "pp_a_if_section"

      | N_pp_aexpr_elif_group -> "pp_aexpr_elif_group"
      | N_pp_aexpr_else_group -> "pp_aexpr_else_group"
      | N_pp_aexpr_if_group -> "pp_aexpr_if_group"
      | N_pp_aexpr_if_section -> "pp_aexpr_if_section"

      | N_pp_aexpr_elif_group_closing -> "pp_aexpr_elif_group_closing"
      | N_pp_aexpr_else_group_closing -> "pp_aexpr_else_group_closing"
      | N_pp_aexpr_if_group_closing -> "pp_aexpr_if_group_closing"
      | N_pp_aexpr_if_section_closing -> "pp_aexpr_if_section_closing"

      | N_pp_args_elif_group_close_open -> "pp_args_elif_group_close_open"
      | N_pp_args_elif_group_closing -> "pp_args_elif_group_closing"
      | N_pp_args_else_group_close_open -> "pp_args_else_group_close_open"
      | N_pp_args_else_group_closing -> "pp_args_else_group_closing"
      | N_pp_args_if_group_close_open -> "pp_args_if_group_close_open"
      | N_pp_args_if_group_closing -> "pp_args_if_group_closing"
      | N_pp_args_if_section_close_open -> "pp_args_if_section_close_open"
      | N_pp_args_if_section_closing -> "pp_args_if_section_closing"
      | N_pp_attr_elif_group -> "pp_attr_elif_group"
      | N_pp_attr_else_group -> "pp_attr_else_group"
      | N_pp_attr_if_group -> "pp_attr_if_group"
      | N_pp_attr_if_section -> "pp_attr_if_section"
      | N_pp_base_clause_elif_group -> "pp_base_clause_elif_group"
      | N_pp_base_clause_else_group -> "pp_base_clause_else_group"
      | N_pp_base_clause_if_group -> "pp_base_clause_if_group"
      | N_pp_base_clause_if_section -> "pp_base_clause_if_section"
      | N_pp_capture_elif_group -> "pp_capture_elif_group"
      | N_pp_capture_else_group -> "pp_capture_else_group"
      | N_pp_capture_if_group -> "pp_capture_if_group"
      | N_pp_capture_if_section -> "pp_capture_if_section"
      | N_pp_cc_elif_group -> "pp_cc_elif_group"
      | N_pp_cc_else_group -> "pp_cc_else_group"
      | N_pp_cc_if_group -> "pp_cc_if_group"
      | N_pp_cc_if_section -> "pp_cc_if_section"
      | N_pp_class_body_elif_group -> "pp_class_body_elif_group"
      | N_pp_class_body_else_group -> "pp_class_body_else_group"
      | N_pp_class_body_if_group -> "pp_class_body_if_group"
      | N_pp_class_body_if_section -> "pp_class_body_if_section"
      | N_pp_class_head_elif_group -> "pp_class_head_elif_group"
      | N_pp_class_head_else_group -> "pp_class_head_else_group"
      | N_pp_class_head_if_group -> "pp_class_head_if_group"
      | N_pp_class_head_if_section -> "pp_class_head_if_section"
      | N_pp_class_head_elif_group_broken -> "pp_class_head_elif_group_broken"
      | N_pp_class_head_else_group_broken -> "pp_class_head_else_group_broken"
      | N_pp_class_head_if_group_broken -> "pp_class_head_if_group_broken"
      | N_pp_class_head_if_section_broken -> "pp_class_head_if_section_broken"
      | N_pp_concat -> "pp_concat"
      | N_pp_cond_elif_group -> "pp_cond_elif_group"
      | N_pp_cond_else_group -> "pp_cond_else_group"
      | N_pp_cond_if_group -> "pp_cond_if_group"
      | N_pp_cond_if_section -> "pp_cond_if_section"
      | N_pp_cond_hd_elif_group -> "pp_cond_hd_elif_group"
      | N_pp_cond_hd_else_group -> "pp_cond_hd_else_group"
      | N_pp_cond_hd_if_group -> "pp_cond_hd_if_group"
      | N_pp_cond_hd_if_section -> "pp_cond_hd_if_section"
      | N_pp_cond_tl_elif_group -> "pp_cond_tl_elif_group"
      | N_pp_cond_tl_else_group -> "pp_cond_tl_else_group"
      | N_pp_cond_tl_if_group -> "pp_cond_tl_if_group"
      | N_pp_cond_tl_if_section -> "pp_cond_tl_if_section"
      | N_pp_control_line -> "pp_control_line"
      | N_pp_ctor_init_elif_group -> "pp_ctor_init_elif_group"
      | N_pp_ctor_init_else_group -> "pp_ctor_init_else_group"
      | N_pp_ctor_init_if_group -> "pp_ctor_init_if_group"
      | N_pp_ctor_init_if_section -> "pp_ctor_init_if_section"
      | N_pp_decl_elif_group -> "pp_decl_elif_group"
      | N_pp_decl_elif_group_broken -> "pp_decl_elif_group_broken"
      | N_pp_decl_else_group -> "pp_decl_else_group"
      | N_pp_decl_else_group_broken -> "pp_decl_else_group_broken"
      | N_pp_decl_if_group -> "pp_decl_if_group"
      | N_pp_decl_if_group_broken -> "pp_decl_if_group_broken"
      | N_pp_decl_if_section -> "pp_decl_if_section"
      | N_pp_decl_if_section_broken -> "pp_decl_if_section_broken"
      | N_pp_decl_spec_elif_group -> "pp_decl_spec_elif_group"
      | N_pp_decl_spec_else_group -> "pp_decl_spec_else_group"
      | N_pp_decl_spec_if_group -> "pp_decl_spec_if_group"
      | N_pp_decl_spec_if_section -> "pp_decl_spec_if_section"
      | N_pp_dinit_elif_group -> "pp_dinit_elif_group"
      | N_pp_dinit_else_group -> "pp_dinit_else_group"
      | N_pp_dinit_if_group -> "pp_dinit_if_group"
      | N_pp_dinit_if_section -> "pp_dinit_if_section"
      | N_pp_dtor_elif_group -> "pp_dtor_elif_group"
      | N_pp_dtor_else_group -> "pp_dtor_else_group"
      | N_pp_dtor_if_group -> "pp_dtor_if_group"
      | N_pp_dtor_if_section -> "pp_dtor_if_section"
      | N_pp_dtor_elif_group_broken -> "pp_dtor_elif_group_broken"
      | N_pp_dtor_else_group_broken -> "pp_dtor_else_group_broken"
      | N_pp_dtor_if_group_broken -> "pp_dtor_if_group_broken"
      | N_pp_dtor_if_section_broken -> "pp_dtor_if_section_broken"
      | N_pp_edef_elif_group -> "pp_edef_elif_group"
      | N_pp_edef_else_group -> "pp_edef_else_group"
      | N_pp_edef_if_group -> "pp_edef_if_group"
      | N_pp_edef_if_section -> "pp_edef_if_section"
      | N_pp_elif -> "pp_elif"
      | N_pp_else -> "pp_else"
      | N_pp_endif -> "pp_endif"
      | N_pp_enum_head_elif_group -> "pp_enum_head_elif_group"
      | N_pp_enum_head_else_group -> "pp_enum_head_else_group"
      | N_pp_enum_head_if_group -> "pp_enum_head_if_group"
      | N_pp_enum_head_if_section -> "pp_enum_head_if_section"
      | N_pp_enum_elif_group_closing -> "pp_enum_elif_group_closing"
      | N_pp_enum_else_group_closing -> "pp_enum_else_group_closing"
      | N_pp_enum_if_group_closing -> "pp_enum_if_group_closing"
      | N_pp_enum_if_section_closing -> "pp_enum_if_section_closing"
      | N_pp_expr_elif_group -> "pp_expr_elif_group"
      | N_pp_expr_else_group -> "pp_expr_else_group"
      | N_pp_expr_if_group -> "pp_expr_if_group"
      | N_pp_expr_if_section -> "pp_expr_if_section"
      | N_pp_expr_elif_group_broken -> "pp_expr_elif_group_broken"
      | N_pp_expr_elif_group_broken2 -> "pp_expr_elif_group_broken2"
      | N_pp_expr_else_group_broken -> "pp_expr_else_group_broken"
      | N_pp_expr_else_group_broken2 -> "pp_expr_else_group_broken2"
      | N_pp_expr_if_group_broken -> "pp_expr_if_group_broken"
      | N_pp_expr_if_group_broken2 -> "pp_expr_if_group_broken2"
      | N_pp_expr_if_section_broken -> "pp_expr_if_section_broken"
      | N_pp_expr_if_section_broken2 -> "pp_expr_if_section_broken2"
      | N_pp_func_body_elif_group -> "pp_func_body_elif_group"
      | N_pp_func_body_else_group -> "pp_func_body_else_group"
      | N_pp_func_body_if_group -> "pp_func_body_if_group"
      | N_pp_func_body_if_section -> "pp_func_body_if_section"
      | N_pp_func_head_elif_group_broken -> "pp_func_head_elif_group_broken"
      | N_pp_func_head_else_group_broken -> "pp_func_head_else_group_broken"
      | N_pp_func_head_if_group_broken -> "pp_func_head_if_group_broken"
      | N_pp_func_head_if_section_broken -> "pp_func_head_if_section_broken"
      | N_pp_gnu_asm_elif_group -> "pp_gnu_asm_elif_group"
      | N_pp_gnu_asm_else_group -> "pp_gnu_asm_else_group"
      | N_pp_gnu_asm_if_group -> "pp_gnu_asm_if_group"
      | N_pp_gnu_asm_if_section -> "pp_gnu_asm_if_section"
      | N_pp_handler_elif_group -> "pp_handler_elif_group"
      | N_pp_handler_else_group -> "pp_handler_else_group"
      | N_pp_handler_if_group -> "pp_handler_if_group"
      | N_pp_handler_if_section -> "pp_handler_if_section"
      | N_pp_handler_elif_group_broken -> "pp_handler_elif_group_broken"
      | N_pp_handler_else_group_broken -> "pp_handler_else_group_broken"
      | N_pp_handler_if_group_broken -> "pp_handler_if_group_broken"
      | N_pp_handler_if_section_broken -> "pp_handler_if_section_broken"
      | N_pp_idtor_elif_group -> "pp_idtor_elif_group"
      | N_pp_idtor_else_group -> "pp_idtor_else_group"
      | N_pp_idtor_if_group -> "pp_idtor_if_group"
      | N_pp_idtor_if_section -> "pp_idtor_if_section"
      | N_pp_ifstmt_elif_group_closing -> "pp_ifstmt_elif_group_closing"
      | N_pp_ifstmt_else_group_closing -> "pp_ifstmt_else_group_closing"
      | N_pp_ifstmt_if_group_closing -> "pp_ifstmt_if_group_closing"
      | N_pp_ifstmt_if_section_closing -> "pp_ifstmt_if_section_closing"
      | N_pp_ifx -> "pp_ifx"
      | N_pp_ifx_a -> "pp_ifx_a"
      | N_pp_ifx_attr -> "pp_ifx_attr"
      | N_pp_ifx_b -> "pp_ifx_b"
      | N_pp_ifx_broken -> "pp_ifx_broken"
      | N_pp_ifx_c -> "pp_ifx_c"
      | N_pp_ifx_cb -> "pp_ifx_cb"
      | N_pp_ifx_close_open -> "pp_ifx_close_open"
      | N_pp_ifx_closing -> "pp_ifx_closing"
      | N_pp_ifx_cond -> "pp_ifx_cond"
      | N_pp_ifx_cond_ -> "pp_ifx_cond_"
      | N_pp_ifx_d -> "pp_ifx_d"
      | N_pp_ifx_e -> "pp_ifx_e"
      | N_pp_ifx_eh -> "pp_ifx_eh"
      | N_pp_ifx_h -> "pp_ifx_h"
      | N_pp_ifx_i -> "pp_ifx_i"
      | N_pp_ifx_o -> "pp_ifx_o"
      | N_pp_ifx_p -> "pp_ifx_p"
      | N_pp_ifx_s -> "pp_ifx_s"
      | N_pp_ifx_shift -> "pp_ifx_shift"
      | N_pp_ifx_x -> "pp_ifx_x"
      | N_pp_init_elif_group -> "pp_init_elif_group"
      | N_pp_init_elif_group_closing -> "pp_init_elif_group_closing"
      | N_pp_init_else_group -> "pp_init_else_group"
      | N_pp_init_else_group_closing -> "pp_init_else_group_closing"
      | N_pp_init_if_group -> "pp_init_if_group"
      | N_pp_init_if_group_closing -> "pp_init_if_group_closing"
      | N_pp_init_if_section -> "pp_init_if_section"
      | N_pp_init_if_section_closing -> "pp_init_if_section_closing"
      | N_pp_ior_elif_group -> "pp_ior_elif_group"
      | N_pp_ior_else_group -> "pp_ior_else_group"
      | N_pp_ior_if_group -> "pp_ior_if_group"
      | N_pp_ior_if_section -> "pp_ior_if_section"
      | N_pp_ior_if_section_seq -> "pp_ior_if_section_seq"
      | N_pp_lambda_head_elif_group_broken -> "pp_lambda_head_elif_group_broken"
      | N_pp_lambda_head_else_group_broken -> "pp_lambda_head_else_group_broken"
      | N_pp_lambda_head_if_group_broken -> "pp_lambda_head_if_group_broken"
      | N_pp_lambda_head_if_section_broken -> "pp_lambda_head_if_section_broken"
      | N_pp_land_elif_group -> "pp_land_elif_group"
      | N_pp_land_else_group -> "pp_land_else_group"
      | N_pp_land_if_group -> "pp_land_if_group"
      | N_pp_land_if_section -> "pp_land_if_section"
      | N_pp_lor_elif_group -> "pp_lor_elif_group"
      | N_pp_lor_else_group -> "pp_lor_else_group"
      | N_pp_lor_if_group -> "pp_lor_if_group"
      | N_pp_lor_if_section -> "pp_lor_if_section"
      | N_pp_mdecl_elif_group -> "pp_mdecl_elif_group"
      | N_pp_mdecl_else_group -> "pp_mdecl_else_group"
      | N_pp_mdecl_if_group -> "pp_mdecl_if_group"
      | N_pp_mdecl_if_section -> "pp_mdecl_if_section"
      | N_pp_mdecl_elif_group_broken -> "pp_mdecl_elif_group_broken"
      | N_pp_mdecl_else_group_broken -> "pp_mdecl_else_group_broken"
      | N_pp_mdecl_if_group_broken -> "pp_mdecl_if_group_broken"
      | N_pp_mdecl_if_section_broken -> "pp_mdecl_if_section_broken"
      | N_pp_minit_elif_group_broken -> "pp_minit_elif_group_broken"
      | N_pp_minit_else_group_broken -> "pp_minit_else_group_broken"
      | N_pp_minit_if_group_broken -> "pp_minit_if_group_broken"
      | N_pp_minit_if_section_broken -> "pp_minit_if_section_broken"
      | N_pp_minit_elif_group -> "pp_minit_elif_group"
      | N_pp_minit_else_group -> "pp_minit_else_group"
      | N_pp_minit_if_group -> "pp_minit_if_group"
      | N_pp_minit_if_section -> "pp_minit_if_section"
      | N_pp_objc_category_interface_head_elif_group -> "pp_objc_category_interface_head_elif_group"
      | N_pp_objc_category_interface_head_else_group -> "pp_objc_category_interface_head_else_group"
      | N_pp_objc_category_interface_head_if_group -> "pp_objc_category_interface_head_if_group"
      | N_pp_objc_category_interface_head_if_section -> "pp_objc_category_interface_head_if_section"
      | N_pp_objc_class_interface_head_elif_group -> "pp_objc_class_interface_head_elif_group"
      | N_pp_objc_class_interface_head_else_group -> "pp_objc_class_interface_head_else_group"
      | N_pp_objc_class_interface_head_if_group -> "pp_objc_class_interface_head_if_group"
      | N_pp_objc_class_interface_head_if_section -> "pp_objc_class_interface_head_if_section"
      | N_pp_objc_idecl_elif_group -> "pp_objc_idecl_elif_group"
      | N_pp_objc_idecl_else_group -> "pp_objc_idecl_else_group"
      | N_pp_objc_idecl_if_section -> "pp_objc_idecl_if_section"
      | N_pp_objc_idecl_if_group -> "pp_objc_idecl_if_group"
      | N_pp_objc_ivar_decl_elif_group -> "pp_objc_ivar_decl_elif_group"
      | N_pp_objc_ivar_decl_else_group -> "pp_objc_ivar_decl_else_group"
      | N_pp_objc_ivar_decl_if_section -> "pp_objc_ivar_decl_if_section"
      | N_pp_objc_ivar_decl_if_group -> "pp_objc_ivar_decl_if_group"
      | N_pp_objc_proto_name_elif_group -> "pp_objc_proto_name_elif_group"
      | N_pp_objc_proto_name_else_group -> "pp_objc_proto_name_else_group"
      | N_pp_objc_proto_name_if_group -> "pp_objc_proto_name_if_group"
      | N_pp_objc_proto_name_if_section -> "pp_objc_proto_name_if_section"
      | N_pp_objc_protocol_ref_list_elif_group -> "pp_objc_protocol_ref_list_elif_group"
      | N_pp_objc_protocol_ref_list_else_group -> "pp_objc_protocol_ref_list_else_group"
      | N_pp_objc_protocol_ref_list_if_section -> "pp_objc_protocol_ref_list_if_section"
      | N_pp_old_param_decl_list_elif_group -> "pp_old_param_decl_list_elif_group"
      | N_pp_old_param_decl_list_else_group -> "pp_old_param_decl_list_else_group"
      | N_pp_old_param_decl_list_if_group -> "pp_old_param_decl_list_if_group"
      | N_pp_old_param_decl_list_if_section -> "pp_old_param_decl_list_if_section"
      | N_pp_p_elif_group -> "pp_p_elif_group"
      | N_pp_p_else_group -> "pp_p_else_group"
      | N_pp_p_if_group -> "pp_p_if_group"
      | N_pp_p_if_section -> "pp_p_if_section"
      | N_pp_param_elif_group -> "pp_param_elif_group"
      | N_pp_param_else_group -> "pp_param_else_group"
      | N_pp_param_if_group -> "pp_param_if_group"
      | N_pp_param_if_section -> "pp_param_if_section"
      | N_pp_param_list -> "pp_param_list"
      | N_pp_spec_elif_group -> "pp_spec_elif_group"
      | N_pp_spec_else_group -> "pp_spec_else_group"
      | N_pp_spec_if_group -> "pp_spec_if_group"
      | N_pp_spec_if_section -> "pp_spec_if_section"
      | N_pp_stmt_elif_group -> "pp_stmt_elif_group"
      | N_pp_stmt_elif_group_broken -> "pp_stmt_elif_group_broken"
      | N_pp_stmt_elif_group_close_open -> "pp_stmt_elif_group_close_open"
      | N_pp_stmt_elif_group_closing -> "pp_stmt_elif_group_closing"
      | N_pp_stmt_else_group -> "pp_stmt_else_group"
      | N_pp_stmt_else_group_broken -> "pp_stmt_else_group_broken"
      | N_pp_stmt_else_group_close_open -> "pp_stmt_else_group_close_open"
      | N_pp_stmt_else_group_closing -> "pp_stmt_else_group_closing"
      | N_pp_stmt_if_group -> "pp_stmt_if_group"
      | N_pp_stmt_if_group_broken -> "pp_stmt_if_group_broken"
      | N_pp_stmt_if_group_close_open -> "pp_stmt_if_group_close_open"
      | N_pp_stmt_if_group_closing -> "pp_stmt_if_group_closing"
      | N_pp_stmt_if_section -> "pp_stmt_if_section"
      | N_pp_stmt_if_section_broken -> "pp_stmt_if_section_broken"
      | N_pp_stmt_if_section_close_open -> "pp_stmt_if_section_close_open"
      | N_pp_stmt_if_section_closing -> "pp_stmt_if_section_closing"
      | N_pp_str_elif_group -> "pp_str_elif_group"
      | N_pp_str_else_group -> "pp_str_else_group"
      | N_pp_str_if_group -> "pp_str_if_group"
      | N_pp_str_if_section -> "pp_str_if_section"
      | N_pp_templ_arg_elif_group -> "pp_templ_arg_elif_group"
      | N_pp_templ_arg_else_group -> "pp_templ_arg_else_group"
      | N_pp_templ_arg_if_group -> "pp_templ_arg_if_group"
      | N_pp_templ_arg_if_section -> "pp_templ_arg_if_section"
      | N_pp_templ_param_elif_group -> "pp_templ_param_elif_group"
      | N_pp_templ_param_else_group -> "pp_templ_param_else_group"
      | N_pp_templ_param_if_group -> "pp_templ_param_if_group"
      | N_pp_templ_param_if_section -> "pp_templ_param_if_section"
      | N_primary_expression -> "primary_expression"
      | N_ptr_abstract_declarator -> "ptr_abstract_declarator"
      | N_ptr_declarator -> "ptr_declarator"
      | N_ptr_operator -> "ptr_operator"
      | N_pure_specifier -> "pure_specifier"
      | N_q_prop_token -> "q_prop_token"
      | N_qualified_id -> "qualified_id"
      | N_quasi_keyword -> "quasi_keyword"
      | N_ref_qualifier -> "ref_qualifier"
      | N_relational_expression -> "relational_expression"
      | N_requirement -> "requirement"
      | N_requirement_body -> "requirement_body"
      | N_requirement_parameter_list -> "requirement_parameter_list"
      | N_requirement_seq -> "requirement_seq"
      | N_requires_clause -> "requires_clause"
      | N_requires_expression -> "requires_expression"
      | N_restricted_add_expr -> "restricted_add_expr"
      | N_restricted_and_expr -> "restricted_and_expr"
      | N_restricted_assign_expr -> "restricted_assign_expr"
      | N_restricted_cast_expr -> "restricted_cast_expr"
      | N_restricted_comp_expr -> "restricted_comp_expr"
      | N_restricted_cond_expr -> "restricted_cond_expr"
      | N_restricted_decl -> "restricted_decl"
      | N_restricted_decls -> "restricted_decls"
      | N_restricted_eq_expr -> "restricted_eq_expr"
      | N_restricted_expr -> "restricted_expr"
      | N_restricted_ior_expr -> "restricted_ior_expr"
      | N_restricted_land_expr -> "restricted_land_expr"
      | N_restricted_lor_expr -> "restricted_lor_expr"
      | N_restricted_mult_expr -> "restricted_mult_expr"
      | N_restricted_pm_expr -> "restricted_pm_expr"
      | N_restricted_postfix_expr -> "restricted_postfix_expr"
      | N_restricted_prim_expr -> "restricted_prim_expr"
      | N_restricted_rel_expr -> "restricted_rel_expr"
      | N_restricted_shift_expr -> "restricted_shift_expr"
      | N_restricted_unary_expr -> "restricted_unary_expr"
      | N_restricted_xor_expr -> "restricted_xor_expr"
      | N_return_type_requirement -> "return_type_requirement"
      | N_s_token -> "s_token"
      | N_selection_statement -> "selection_statement"
      | N_separated_nonempty_list_COMMA_conditional_expression_ -> "clist(conditional_expression)"
      | N_separated_nonempty_list_COMMA_mock_qualifier_ -> "clist(mock_qualifier)"
      | N_separated_nonempty_list_COMMA_objc_avail_item_ -> "clist(objc_avail_item)"
      | N_separated_nonempty_list_COMMA_objc_class_name_ -> "clist(objc_class_name)"
      | N_separated_nonempty_list_COMMA_objc_key_value_ -> "clist(objc_key_value)"
      | N_separated_nonempty_list_COMMA_objc_property_attr_ -> "clist(objc_property_attr)"
      | N_separated_nonempty_list_COMMA_objc_struct_dtor_ -> "clist(objc_struct_dtor)"
      | N_separated_nonempty_list_COMMA_type_id_ -> "clist(type_id)"
      | N_shift_expression -> "shift_expression"
      | N_simple_capture -> "simple_capture"
      | N_simple_requirement -> "simple_requirement"
      | N_simple_template_id -> "simple_template_id"
      | N_simple_template_id_ -> "simple_template_id_"
      | N_simple_type_specifier -> "simple_type_specifier"
      | N_special_token -> "special_token"
      | N_specs_sub -> "specs_sub"
      | N_statement -> "statement"
      | N_statement_seq_opt -> "statement_seq_opt"
      | N_static_assert_declaration -> "static_assert_declaration"
      | N_stmt_macro_arg -> "stmt_macro_arg"
      | N_stmt_macro_call -> "stmt_macro_call"
      | N_stmts_macro_arg -> "stmts_macro_arg"
      | N_stmts_sub -> "stmts_sub"
      | N_storage_class_specifier -> "storage_class_specifier"
      | N_str_ -> "str_"
      | N_string_literal -> "string_literal"
      | N_string_literal_ -> "string_literal_"
      | N_string_literal_list -> "string_literal_list"
      | N_suffix_macro_call -> "suffix_macro_call"
      | N_swift_arg -> "swift_arg"
      | N_templ_param_macro_call -> "templ_param_macro_call"
      | N_template_argument -> "template_argument"
      | N_template_argument_list -> "template_argument_list"
      | N_template_argument_list_opt -> "template_argument_list_opt"
      | N_template_declaration -> "template_declaration"
      | N_template_head -> "template_head"
      | N_template_id -> "template_id"
      | N_template_parameter -> "template_parameter"
      | N_template_parameter_list -> "template_parameter_list"
      | N_throw_expression -> "throw_expression"
      | N_token -> "token"
      | N_token_no_paren -> "token_no_paren"
      | N_token_seq -> "token_seq"
      | N_trailing_return_type -> "trailing_return_type"
      | N_translation_unit -> "translation_unit"
      | N_try_block -> "try_block"
      | N_ty_macro_call -> "ty_macro_call"
      | N_type_constraint -> "type_constraint"
      | N_type_id -> "type_id"
      | N_type_name -> "type_name"
      | N_type_parameter -> "type_parameter"
      | N_type_requirement -> "type_requirement"
      | N_type_specifier -> "type_specifier"
      | N_type_sub -> "type_sub"
      | N_typename_specifier -> "typename_specifier"
      | N_unary_expression -> "unary_expression"
      | N_unary_operator -> "unary_operator"
      | N_unnamed_namespace_definition -> "unnamed_namespace_definition"
      | N_unnamed_namespace_definition_head -> "unnamed_namespace_definition_head"
      | N_unqualified_id -> "unqualified_id"
      | N_using_declaration -> "using_declaration"
      | N_using_enum_declaration -> "using_enum_declaration"
      | N_using_declarator -> "using_declarator"
      | N_using_enum_declarator -> "using_enum_declarator"
      | N_using_declarator_list -> "using_declarator_list"
      | N_virt_specifier -> "virt_specifier"
      | N_virt_specifier_seq -> "virt_specifier_seq"
      | N_yield_expression -> "yield_expression"
(*      | _ -> "???"*)
    in
    let symbol_to_string = function
      | I.T t -> "T_"^(terminal_to_string t)
      | I.N nt -> "N_"^(nonterminal_to_string nt)
    in
    let xsymbol_to_string = function
      | I.X s -> symbol_to_string s
    in

    let lexpos_of_menv _menv =
      match I.get 0 _menv with
      | Some (I.Element (_, _, _, edp)) -> begin
          edp
      end
      | _ -> Lexing.dummy_pos
    in

    let pr_menv head ith () _menv =
      let buf = Buffer.create 0 in
      begin
        match I.get ith _menv with
        | Some (I.Element (stat, _, stp, edp)) -> begin
            let n = I.number stat in
            Buffer.add_string buf (sprintf "[%d] STATE-%d (%s)\n" ith n head);
            List.iter
              (fun (prod, i) ->
                let lhs = I.lhs prod in
                let rhs = I.rhs prod in
                Buffer.add_string buf
                  (sprintf " %s <- %s (%d:%s)\n"
                     (xsymbol_to_string lhs) (Xlist.to_string xsymbol_to_string " " rhs)
                     i (xsymbol_to_string (List.nth rhs (i-1))))
              ) (I.items stat);

            Buffer.add_string buf
              (sprintf " > %s[%s-%s] <\n"
                 (symbol_to_string (I.incoming_symbol stat))
                 (Astloc.lexpos_to_string stp) (Astloc.lexpos_to_string edp));
        end
        | None -> ()
      end;
      Buffer.contents buf
    in
    let _ = pr_menv in

    (*let item_to_string (sn, l, r0, r) =
      sprintf "[%d] %s <- %s (%s)"
        sn (xsymbol_to_string l) (xsymbol_to_string r0) (xsymbol_to_string r)
    in
    let items_to_string items =
      String.concat "\n" (List.map item_to_string items)
    in*)

    let get_items ?(ith=0) _menv =
      match I.get ith _menv with
      | Some (I.Element (stat, _, _, _)) -> I.items stat
      | None -> []
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
            | Some (s, lh, rh, rhx, i0) when
                s == sn && lh == lhs && rhx == rhsi && List.hd rh == rhs0 && i0 = i -> o
            | _ ->
                let x = (sn, lhs, rhs, rhsi, i) in
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

    let rec rollback _menv state_number =
      [%debug_log "%d\n%a" state_number (pr_menv "rollback" 0) _menv];
      match I.top _menv with
      | Some _ -> begin
          if I.current_state_number _menv = state_number then
            _menv
          else
            match I.pop _menv with
            | Some me -> rollback me state_number
            | None -> _menv
      end
      | None -> _menv
    in

    let rec loop ckpt =
      match ckpt with
      | I.InputNeeded _menv -> begin
          let tok = scanner#get_token() in
          tokens_read <- tokens_read + 1;
          let ckpt = I.offer ckpt tok in
          loop ckpt
      end
      | I.Shifting (_menv, menv_, _) -> begin
          begin %debug_block
            [%debug_log "\n%a" (pr_menv "shift" 0) menv_];
            for ith = 1 to 9 do
              match I.get ith menv_ with
              | Some _ -> [%debug_log "\n%a" (pr_menv "shift" ith) menv_]
              | _ -> ()
            done
          end;

          let ctx_start_of_stmt sn =
            [%debug_log "sn=%d" sn];
            menv_backup_obj := Some menv_;
            scanner#ctx_start_of_stmt sn
          in

          let in_params () =
            try
              iter_items ~ith:1 menv_
                (function
                  | _, I.X (I.N N_parameter_declaration_list), _, _, _ -> raise Exit
                  | _, I.X (I.N N_parameter_declaration), _, _, _ -> raise Exit
                  | _, I.X (I.N N_template_head), _, _, _ -> raise Exit
                  | _, I.X (I.N N_template_parameter_list), _, _, _ -> raise Exit
                  | _, I.X (I.N N_parameters_and_qualifiers), _, I.X (I.T T_TY_LPAREN), _ ->
                      raise Exit
                  | _ -> ()
                );
              false
            with
              Exit -> true
          in
          let _proc_shift0 (_, l, rs, r, i) =
            match l, rs, r with
            | I.X (I.N N_class_body_head_macro), _, I.X (I.T T_RPAREN) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                scanner#ctx_mem();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_class_body_end_macro), _, I.X (I.T T_RPAREN) -> begin
                scanner#pop_context();
                scanner#pop_sub_context();
                raise Exit
            end
            | I.X (I.N N_init_head_macro), _, I.X (I.T T_RPAREN) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                scanner#ctx_expr();
                scanner#ctx_ini();
                env#enter_braced_init();
                raise Exit
            end
            | I.X (I.N N_init_end_macro), _, I.X (I.T T_IDENT_IEM) -> begin
                env#exit_braced_init();
                raise Exit
            end
            | I.X (I.N N_init_end_macro), _, I.X (I.T T_RPAREN) -> begin
                scanner#pop_context();
                scanner#pop_sub_context();
                raise Exit
            end
            | I.X (I.N N_pp_base_clause_if_group), _, I.X (I.T T_BASE_COLON) -> begin
                env#enter_base_clause();
                raise Exit
            end
            | I.X (I.N N_pp_class_head_if_group_broken), _, I.X (I.T T_CLASS_LBRACE) -> begin
                env#set_class_brace_opening_info();
                env#set_broken_info();
                raise Exit
            end
            | I.X (I.N N_new_expression), _, I.X (I.T T_NEW) -> begin
                scanner#ctx_new();
                scanner#ctx_ini();
                env#set_new_flag();
                raise Exit
            end
            | I.X (I.N N_concept_definition), _, I.X (I.T T_CONCEPT) -> begin
                env#set_concept_flag();
                raise Exit
            end
            | I.X (I.N N_concept_definition), _, I.X (I.T T_SEMICOLON) -> begin
                env#clear_concept_flag();
                raise Exit
            end
            | I.X (I.N N_new_placement), _, I.X (I.T T_RPAREN) -> begin
                scanner#ctx_new();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_logical_and_expression), _, I.X (I.T T_AMP_AMP) -> begin
                env#set_expr_flag();
                raise Exit
            end
            | I.X (I.N N_type_requirement), _, I.X (I.T T_SEMICOLON) -> begin
                env#exit_typename();
                raise Exit
            end
            | I.X (I.N N_requires_clause), _, I.X (I.T T_REQUIRES) -> begin
                env#set_requires_clause_flag();
                raise Exit
            end
            | I.X (I.N N_requirement_body), _, I.X (I.T T_LBRACE) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                scanner#enter_block();
                raise Exit
            end

            | I.X (I.N N_requirement_body), _, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                iter_items ~ith:5 menv_
                  (function
                    | _, I.X (I.N N_template_head), _, I.X (I.T T_TEMPL_GT), _ -> begin
                        scanner#ctx_top();
                        scanner#ctx_ini();
                        raise Exit
                    end
                    | _ -> ()
                  );
                raise Exit
            end
            | I.X (I.N N_attribute_specifier), _ , I.X (I.T T_ATTR_LBRACKET) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                raise Exit
            end
            | I.X (I.N N_attribute_specifier), _ , I.X (I.T T_RBRACKET) when i = 5 -> begin
                env#clear_attr_flag();
                scanner#pop_context();
                scanner#pop_sub_context();
                raise Exit
            end

            | _ -> ()
          in (* let _proc_shift0 *)

          let _proc_shift1 (_, l, rs, r, i) =
            match l, rs, r with
            | I.X (I.N N_nodeclspec_function_definition), _, I.X (I.T T_SEMICOLON) -> begin
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_macro_arg), _, I.X (I.T T_MOCK_MARKER) -> begin
                env#set_mock_qualifier_flag();
                raise Exit
            end
            | I.X (I.N N_macro_arg), I.X (I.T T_MOCK_MARKER)::_, I.X (I.T T_RPAREN) -> begin
                env#clear_mock_qualifier_flag();
                raise Exit
            end
            (*| I.X (I.N N_template_argument_list), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_in_simple_templ_id();
                raise Exit
            end*)
            | I.X (I.N N_attribute_token), _ , _ -> begin
                env#set_attr_flag();
                raise Exit
            end
            | I.X (I.N N_unqualified_id), _ , I.X (I.T T_IDENT_V) -> begin
                (*iter_items_w ~from_ith:2 ~to_ith:2 menv_
                  (function
                    | sn, I.X (I.N N_unary_expression), _, I.X (I.N N_unary_operator), _ -> begin
                        env#set_expr_flag();
                        raise Exit
                    end
                    | _ -> ()
                  );*)
                iter_items_w ~from_ith:6 ~to_ith:6 menv_
                  (function
                    | _, I.X (I.N N_logical_and_expression), _, _, _ -> begin
                        env#set_expr_flag();
                        raise Exit
                    end
                    | _ -> ()
                  );
                raise Exit
            end
            (*| I.X (I.N N_simple_type_specifier), _ , x when begin
                match x with
                | I.X (I.T T_CHAR) | I.X (I.T T_CHAR8_T) | I.X (I.T T_CHAR16_T)
                | I.X (I.T T_CHAR32_T) | I.X (I.T T_WCHAR_T) | I.X (I.T T_BOOL)
                | I.X (I.T T_SHORT) | I.X (I.T T_INT) | I.X (I.T T_LONG)
                | I.X (I.T T_SIGNED) | I.X (I.T T_UNSIGNED)
                | I.X (I.T T_FLOAT) | I.X (I.T T_DOUBLE) | I.X (I.T T_VOID) -> true
                | I.X (I.T T_IDENT) -> true
                | _ -> false
            end -> begin
              iter_items_w ~from_ith:4 ~to_ith:7 menv_
                (function
                  | sn, I.X (I.N N_unary_expression), xl, _, _ -> begin
                      match xl with
                      | I.X (I.T T_SIZEOF)::I.X (I.T T_TY_LPAREN)::_ -> raise Exit
                      | I.X (I.N N_postfix_expression)::_ -> raise Exit
                      | _ ->
                      if
                        (match scanner#peek_rawtoken() with
                        | TY_TEMPL_GT -> false
                        | GT_GT when env#templ_param_arg_level > 1 -> false
                        | _ -> true) ||
                        match scanner#peek_nth_rawtoken 2 with
                        | PTR_STAR | PTR_AMP | PTR_AMP_AMP -> begin
                            match scanner#peek_nth_rawtoken 3 with
                            | RPAREN -> false
                            | _ -> true
                        end
                        | _ -> true
                      then
                        env#set_expr_flag();
                      raise Exit
                  end
                  | sn, I.X (I.N N_restricted_land_expr), _, _, _ -> begin
                      env#set_expr_flag();
                      raise Exit
                  end
                  | _ -> ()
                );
              raise Exit
            end*)
            | I.X (I.N N__namespace_alias_definition), _, I.X (I.T T_EQ) -> begin
                env#set_ns_alias_flag();
                raise Exit
            end
            | I.X (I.N N_declaration), I.X (I.T T_ASM_SHADER)::_, I.X (I.T T_NEWLINE) -> begin
                env#clear_asm_shader_flag();
                raise Exit
            end
            | I.X (I.N N_dsl_macro_args), _, I.X (I.T T_RPAREN) -> begin
                env#clear_dsl_flag();
                raise Exit
            end
            | I.X (I.N N_pp_base_clause_if_group), _, I.X (I.T T_CLASS_LBRACE) -> begin
                env#set_class_brace_opening_info();
                raise Exit
            end
            | I.X (I.N N_pp_base_clause_elif_group), _, I.X (I.T T_CLASS_LBRACE) -> begin
                env#set_class_brace_opening_info();
                raise Exit
            end
            | I.X (I.N N_pp_base_clause_else_group), _, I.X (I.T T_CLASS_LBRACE) -> begin
                env#set_class_brace_opening_info();
                raise Exit
            end

            | I.X (I.N N_pp_aexpr_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_aexpr_if_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_dtor_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_dtor_if_group_broken), _, I.X (I.T T_MARKER) -> begin
                env#set_broken_func_head_info();
                raise Exit
            end
            | I.X (I.N N_pp_idtor_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                env#set_pp_top_label (L.InitDeclarator "");
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_idtor_elif_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_idtor_else_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_p_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_p_elif_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_p_else_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_p_if_group), _, I.X (I.T T_COMMA) -> begin
                env#set_comma_info();
                raise Exit
            end
            | I.X (I.N N_pp_p_elif_group), _, I.X (I.T T_COMMA) -> begin
                env#set_comma_info();
                raise Exit
            end
            | I.X (I.N N_pp_p_else_group), _, I.X (I.T T_COMMA) -> begin
                env#set_comma_info();
                raise Exit
            end
            | I.X (I.N N_pp_expr_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_expr_elif_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_expr_else_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_enum_if_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_enum_elif_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_enum_else_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_expr_if_group), _, I.X (I.T T_COMMA) when i = 3 -> begin
                begin
                  match scanner#peek_rawtoken() with
                  (*| PP_ELSE _ | PP_ELIF _ | PP_ENDIF _ -> env#set_comma_info()*)
                  | x when Scanner.is_pp_elif_else_endif_like env x -> env#set_comma_info()
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_expr_elif_group), _, I.X (I.T T_COMMA) when i = 3 -> begin
                begin
                  match scanner#peek_rawtoken() with
                  (*| PP_ELSE _ | PP_ELIF _ | PP_ENDIF _ -> env#set_comma_info()*)
                  | x when Scanner.is_pp_elif_else_endif_like env x -> env#set_comma_info()
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_expr_else_group), _, I.X (I.T T_COMMA) when i = 3 -> begin
                begin
                  match scanner#peek_rawtoken() with
                  (*| PP_ELSE _ | PP_ELIF _ | PP_ENDIF _ -> env#set_comma_info()*)
                  | x when Scanner.is_pp_elif_else_endif_like env x -> env#set_comma_info()
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_templ_arg_if_group), _, I.X (I.T T_COMMA) when i = 3 -> begin
                env#set_comma_info();
                raise Exit
            end
            | I.X (I.N N_pp_templ_arg_elif_group), _, I.X (I.T T_COMMA) when i = 3 -> begin
                env#set_comma_info();
                raise Exit
            end
            | I.X (I.N N_pp_templ_arg_else_group), _, I.X (I.T T_COMMA) when i = 3 -> begin
                env#set_comma_info();
                raise Exit
            end
            | I.X (I.N N_old_param_decl), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_end_of_old_param_decl_flag();
                raise Exit
            end
            | I.X (I.N N_base_clause), _, I.X (I.T T_BASE_COLON) -> begin
                env#enter_base_clause();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_trailing_return_type), _, I.X (I.T T_MINUS_GT) -> begin
                env#set_trailing_retty_flag();
                raise Exit
            end
            | I.X (I.N N_literal_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_literal_macro_call), _, I.X (I.T T_SS_LPAREN) -> begin
                scanner#ctx_top();
                scanner#ctx_ini();
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_literal_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                env#set_end_of_literal_macro_call_flag();
                raise Exit
            end
            | I.X (I.N N_id_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                env#clear_end_of_params_flag();
                env#set_end_of_id_macro_call_flag();
                raise Exit
            end
            | I.X (I.N N_requirement_parameter_list), _, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_req_params_flag();
                raise Exit
            end
            | I.X (I.N N_noexcept_specifier), _, I.X (I.T T_LPAREN) -> begin
                env#enter_noexcept();
                raise Exit
            end
            | I.X (I.N N_noexcept_specifier), _, I.X (I.T T_RPAREN) -> begin
                env#exit_noexcept();
                raise Exit
            end
            | I.X (I.N N_alignment_specifier), _, I.X (I.T T_ALIGNAS) -> begin
                env#enter_alignas();
                raise Exit
            end
            | I.X (I.N N_enum_head), _, I.X (I.T T_IDENT) -> begin
                env#enter_enum_head();
                raise Exit
            end
            (*| I.X (I.N N_equality_expression), _, x -> begin
                begin
                  match x with
                  | I.X (I.T T_EQ_EQ) | I.X (I.T T_EXCLAM_EQ) -> begin
                      scanner#ctx_expr();
                      scanner#ctx_ini();
                  end
                  | _ -> ()
                end;
                raise Exit
            end*)
            | I.X (I.N N_fold_expression), _, I.X (I.T T_FOLD_LPAREN) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_fold_expression), _, I.X (I.T T_RPAREN) -> begin
                scanner#pop_context();
                raise Exit
            end
            | I.X (I.N N_unary_operator), _, I.X (I.T T_EXCLAM) -> begin
                env#set_expr_flag();
                raise Exit
            end
            | I.X (I.N N_unary_expression), I.X (I.T T_SIZEOF)::_, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_sizeof_flag();
                raise Exit
            end
            | I.X (I.N N_unary_expression), I.X (I.T T_ALIGNOF)::_, I.X (I.T T_TY_LPAREN) -> begin
                env#enter_alignof();
                raise Exit
            end
            | I.X (I.N N_unary_expression), I.X (I.T T_ALIGNOF)::_, I.X (I.T T_RPAREN) -> begin
                env#exit_alignof();
                raise Exit
            end
            | I.X (I.N N_restricted_unary_expr), I.X (I.T T_ALIGNOF)::_, I.X (I.T T_TY_LPAREN) -> begin
                env#enter_alignof();
                raise Exit
            end
            | I.X (I.N N_restricted_unary_expr), I.X (I.T T_ALIGNOF)::_, I.X (I.T T_RPAREN) -> begin
                env#exit_alignof();
                raise Exit
            end
            | I.X (I.N N_nested_name_specifier), _, I.X (I.T T_COLON_COLON) -> begin
                begin
                  try
                    let to_ith =
                      if env#templ_arg_flag then
                        3
                      else
                        2
                    in
                    iter_items_w ~from_ith:2 ~to_ith menv_
                      (function
                        | _, I.X (I.N N_unary_expression), _, I.X (I.N N_unary_operator), _
                        | _, I.X (I.N N_equality_expression), _, I.X (I.T T_EQ_EQ), _
                        | _, I.X (I.N N_equality_expression), _, I.X (I.T T_EXCLAM_EQ), _
                        | _, I.X (I.N N_relational_expression), _, I.X (I.T T_LT), _
                        | _, I.X (I.N N_relational_expression), _, I.X (I.T T_GT), _
                        | _, I.X (I.N N_relational_expression), _, I.X (I.T T_LT_EQ), _
                        | _, I.X (I.N N_relational_expression), _, I.X (I.T T_GT_EQ), _
                        | _, I.X (I.N N_and_expression), _, I.X (I.T T_AMP), _
                        | _, I.X (I.N N_logical_and_expression), _, I.X (I.T T_AMP_AMP), _
                        | _, I.X (I.N N_exclusive_or_expression), _, I.X (I.T T_HAT), _
                        | _, I.X (I.N N_inclusive_or_expression), _, I.X (I.T T_BAR), _
                        | _, I.X (I.N N_logical_or_expression), _, I.X (I.T T_BAR_BAR), _
                        | _, I.X (I.N N_compare_expression), _, I.X (I.T T_LT_EQ_GT), _
                        | _, I.X (I.N N_shift_expression), _, I.X (I.T T_LT_LT), _
                        | _, I.X (I.N N_shift_expression), _, I.X (I.T T_GT_GT), _
                        | _, I.X (I.N N_additive_expression), _, I.X (I.T T_PLUS), _
                        | _, I.X (I.N N_additive_expression), _, I.X (I.T T_MINUS), _
                        | _, I.X (I.N N_multiplicative_expression), _, I.X (I.T T_STAR), _
                        | _, I.X (I.N N_multiplicative_expression), _, I.X (I.T T_SLASH), _
                        | _, I.X (I.N N_multiplicative_expression), _, I.X (I.T T_PERC), _
                        | _, I.X (I.N N_pm_expression), _, I.X (I.T T_DOT_STAR), _
                        | _, I.X (I.N N_pm_expression), _, I.X (I.T T_MINUS_GT_STAR), _
                        | _, I.X (I.N N_primary_expression), _, I.X (I.T T_LPAREN), _
                          -> begin
                            env#set_value_flag();
                            raise Exit
                          end
                        | _ -> ()
                      )
                  with
                    Exit -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_statement),_ , y when begin
                match y with
                | I.X (I.T T_GNU_ASM) -> true
                | I.X (I.T T_MS_ASM) -> true
                | _ -> false
            end -> begin
              env#enter_asm env#paren_level;
              raise Exit
            end
            | I.X (I.N N_statement), I.X (I.T T_MS_ASM)::_, I.X (I.T T_LBRACE) -> begin
                env#enter_braced_asm();
                raise Exit
            end
            | I.X (I.N N_statement), I.X (I.T T_MS_ASM)::_, I.X (I.T T_RBRACE) -> begin
                env#exit_asm();
                env#exit_braced_asm();
                raise Exit
            end
            | I.X (I.N N_pp_stmt_if_group),
                I.X (I.N N_pp_ifx)::I.X (I.N N_statement_seq_opt)::I.X (I.T T_RBRACE)::_,
                I.X (I.T T_RPAREN) -> begin
                  env#set_brace_paren_closing_info();
                  raise Exit
                end
            | I.X (I.N N_statement), I.X (I.N N_pp_stmt_if_section_broken)::_, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                raise Exit
            end
            | I.X (I.N N_statement), I.X (I.N N_pp_stmt_if_section_broken)::_, I.X (I.T T_MARKER) -> begin
                scanner#ctx_stmt();
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                raise Exit
            end
            | I.X (I.N N_labeled_statement),_ , y when begin
                match y with
                | I.X (I.T T_GNU_ASM) -> true
                | I.X (I.T T_MS_ASM) -> true
                | _ -> false
            end -> begin
              env#enter_asm env#paren_level;
              raise Exit
            end
            | I.X (I.N N__asm_declaration), _, I.X (I.T T_ASM) -> begin
                env#enter_asm env#paren_level;
                raise Exit
            end
            | I.X (I.N N_pp_str_if_group), _, I.X (I.T T_STR_LITERAL) -> begin
                env#set_pp_top_label (L.StringLiteral "");
                raise Exit
            end
            | I.X (I.N N_pp_str_elif_group), _, I.X (I.T T_STR_LITERAL) -> begin
                env#set_pp_top_label (L.StringLiteral "");
                raise Exit
            end
            | I.X (I.N N_pp_str_else_group), _, I.X (I.T T_STR_LITERAL) -> begin
                env#set_pp_top_label (L.StringLiteral "");
                raise Exit
            end
            | I.X (I.N N_pp_str_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                begin
                  match env#pp_top_label with
                  | StringLiteral _ -> env#set_pp_top_label (L.StringLiteral ";");
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_str_elif_group), _, I.X (I.T T_SEMICOLON) -> begin
                begin
                  match env#pp_top_label with
                  | StringLiteral _ -> env#set_pp_top_label (L.StringLiteral ";");
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_str_else_group), _, I.X (I.T T_SEMICOLON) -> begin
                begin
                  match env#pp_top_label with
                  | StringLiteral _ -> env#set_pp_top_label (L.StringLiteral ";");
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_lor_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_pp_top_label (L.LogicalOrExpression ";");
                raise Exit
            end
            | I.X (I.N N_op_macro_call), _ , I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_op_macro_call), _ , I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                raise Exit
            end
            | I.X (I.N N_ty_macro_call), _ , I.X (I.T T_LPAREN) -> begin
                (*scanner#push_context();
                scanner#push_sub_context();*)
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_ty_macro_call), _ , I.X (I.T T_RPAREN) -> begin
                scanner#ctx_end_of_ty_spec();
                env#exit_macro_arg();
                env#set_end_of_type_macro_call_flag();
                (*scanner#pop_context();
                scanner#pop_sub_context();*)
                raise Exit
            end
            | I.X (I.N N_macro_arg_list), _ , I.X (I.T T_COMMA) -> begin
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_declaration), I.X (I.N N_pp_decl_if_section_broken)::_,
                I.X (I.T T_SEMICOLON) when (try List.nth rs 4 = I.X (I.N N_mid_templ_decl) with _ -> false) ->
                  begin
                    env#stack#exit_template();
                  end
            | I.X (I.N N_declaration), I.X (I.T T_GNU_ASM)::_ , I.X (I.T T_GNU_ASM) -> begin
                env#enter_asm env#paren_level;
                raise Exit
            end
            | I.X (I.N N_declaration), x::_ , I.X (I.T T_SEMICOLON) -> begin
                scanner#ctx_top();
                scanner#ctx_ini();
                begin
                  match x with
                  | I.X (I.T T_GNU_ASM) when not env#asm_block_flag -> env#exit_asm()
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_declaration), I.X (I.T T_BEGIN_ETORS)::_, I.X (I.T T_END_ETORS) -> begin
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_declaration), I.X (I.T T_BEGIN_STMTS)::_, I.X (I.T T_BEGIN_STMTS) -> begin
                scanner#ctx_stmt();
                scanner#ctx_ini();
                env#enter_top_stmts env#pp_if_section_level;
                raise Exit
            end
            | I.X (I.N N_declaration), I.X (I.T T_BEGIN_STMTS)::_, I.X (I.T T_END_STMTS) -> begin
                env#exit_top_stmts();
                raise Exit
            end
            | I.X (I.N N_block_head_macro), I.X (I.T T_BLOCK_HEAD_MACRO)::_, I.X (I.T T_BLOCK_HEAD_MACRO) -> begin
                scanner#push_context();
                scanner#ctx_stmt();
                scanner#ctx_ini();
                env#set_decl_stmt_block_flag();
                raise Exit
            end
            | I.X (I.N N_block_head_macro), I.X (I.T T_IDENT_BHM)::_, I.X (I.T T_IDENT_BHM) -> begin
                scanner#push_context();
                raise Exit
            end
            | I.X (I.N N_block_head_macro), I.X (I.T T_IDENT_BHM)::_, I.X (I.T T_RPAREN) -> begin
                scanner#ctx_stmt();
                scanner#ctx_ini();
                env#set_decl_stmt_block_flag();
                raise Exit
            end
            | I.X (I.N N_block_end_macro), I.X (I.T T_BLOCK_END_MACRO)::_, I.X (I.T T_BLOCK_END_MACRO) -> begin
                env#clear_decl_stmt_block_flag();
                scanner#pop_context();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_block_end_macro), I.X (I.T T_IDENT_BEM)::_, I.X (I.T T_RPAREN) -> begin
                env#clear_decl_stmt_block_flag();
                scanner#pop_context();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_macro_arg), I.X (I.T T_BEGIN_STMTS)::_, I.X (I.T T_BEGIN_STMTS) -> begin
                scanner#ctx_stmt();
                scanner#ctx_ini();
                env#enter_stmts();
                raise Exit
            end
            | I.X (I.N N_macro_arg), I.X (I.T T_BEGIN_STMTS)::_, I.X (I.T T_END_STMTS) -> begin
                env#exit_stmts();
                raise Exit
            end
            | I.X (I.N N_asm_block), I.X (I.T T_BEGIN_ASM)::_, I.X (I.T T_BEGIN_ASM) -> begin
                env#enter_asm env#paren_level;
                env#enter_asm_block();
                raise Exit
            end
            | I.X (I.N N_asm_block), I.X (I.T T_BEGIN_ASM)::_, I.X (I.T T_END_ASM) -> begin
                env#exit_asm();
                env#exit_asm_block();
                raise Exit
            end
            | _ -> ()
          in (* let _proc_shift1 *)

          let _proc_shift2 (_, l, rs, r, _) =
            match l, rs, r with
            | I.X (I.N N_additive_expression), _, I.X (I.T _) -> begin
                if env#templ_param_arg_level = 0 then begin
                  scanner#ctx_expr();
                  scanner#ctx_ini();
                end;
                raise Exit
            end
            | I.X (I.N N_elaborated_type_specifier), I.X (I.T T_ELAB_ENUM)::_, I.X (I.T T_IDENT) -> begin
                if scanner#peek_rawtoken() != COLON_COLON then
                  scanner#ctx_end_of_ty_spec()
                else
                  scanner#ctx_ini();
                raise Exit;
            end
            | I.X (I.N N_function_definition), I.X (I.N N_pp_func_head_if_section_broken)::_,
                I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
            end
            | I.X (I.N N_declaration), I.X (I.N N_pp_func_head_if_section_broken)::_,
                I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                scanner#ctx_top();
                scanner#ctx_ini()
            end
            | I.X (I.N N_declaration), I.X (I.N N_decl_specifier_seq)::I.X (I.T T_SECTION_MARKER)::_,
                I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                scanner#ctx_top();
                scanner#ctx_ini()
            end
            | I.X (I.N N_declaration), I.X (I.N N_pp_decl_if_section_broken)::I.X (I.T T_MARKER)::_,
                I.X (I.T T_RBRACE) -> begin
                scanner#ctx_top();
                scanner#ctx_ini()
            end
            | I.X (I.N N_declaration), _, I.X (I.T T_MARKER) -> begin
                scanner#ctx_stmt();
                scanner#ctx_ini()
            end
            | I.X (I.N N_member_declaration), I.X (I.N N_pp_func_head_if_section_broken)::_,
                I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                scanner#ctx_mem();
                scanner#ctx_ini()
            end
            | I.X (I.N N_pp_func_head_if_group_broken), x::xl, I.X (I.T T_LBRACE) -> begin
                begin
                  match x with
                  | I.X (I.N N_pp_ifx_broken) -> begin
                      [%debug_log "@"];
                      env#clear_virtual_func_flag();
                      scanner#enter_block();
                  end
                  | _ -> ()
                end;
                [%debug_log "@"];
                if (match xl with (I.X (I.T T_MARKER))::_ -> true | _ -> false) then begin
                  env#set_broken_info();
                  env#set_func_head_info();
                  raise Exit
                end
                else if
                  match scanner#peek_rawtoken() with
                  (*| PP_ELIF _ | PP_ELSE _ -> true*)
                  | x when Scanner.is_pp_elif_else_like env x -> true
                  | x when Scanner.is_pp_control_line x -> begin
                      let skip_pp_control_line = true in
                      let nth, _ = scanner#peek_rawtoken_up_to ~skip_pp_control_line [T.NEWLINE] in
                      match scanner#peek_nth_rawtoken (nth+1) with
                      | y when Scanner.is_pp_elif_else_like env y -> true
                      | _ -> false
                  end
                  | _ -> try env#pp_if_section_top_info.Pinfo.i_broken with _ -> false
                then begin
                  [%debug_log "@"];
                  begin
                    try
                      let info2 = env#pp_if_section_nth_info 2 in
                      if info2.Pinfo.i_broken then begin
                        if info2.Pinfo.i_pp_elif <> [] || info2.Pinfo.i_pp_else <> None then begin
                          env#pstat#close_brace();
                          if env#in_body_brace_flag then
                            env#close_in_body_brace()
                        end
                      end
                      else begin
                        [%debug_log "@"];
                        scanner#enter_block()
                      end
                    with
                      _ -> [%debug_log "@"]; scanner#enter_block()
                  end;

                  env#set_in_body_brace_flag();
                  scanner#set_body_flag();

                  (*let sn = I.current_state_number menv_ in
                    ctx_start_of_stmt sn;
                    scanner#ctx_stmt();*)

                  [%debug_log "!!! info=%s"
                    (Pinfo.pp_if_section_info_to_string env#pp_if_section_top_info)];

                  env#set_broken_info();
                  env#set_func_head_info();
                  raise Exit
                end
                (*else begin
                  [%debug_log "@"];
                  env#clear_virtual_func_flag();
                  scanner#enter_block();
                end*)
            end
            | I.X (I.N N_pp_func_head_elif_group_broken), xl, I.X (I.T T_LBRACE) -> begin
                begin
                  match xl with
                  | I.X (I.N N_pp_elif)::I.X (I.T T_MARKER)::_ -> begin
                      scanner#enter_block()
                  end
                  | _ -> ()
                end;
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                scanner#ctx_stmt();
                raise Exit
            end
            | I.X (I.N N_pp_func_head_else_group_broken), xl, I.X (I.T T_LBRACE) -> begin
                begin
                  match xl with
                  | I.X (I.N N_pp_else)::I.X (I.T T_MARKER)::_ -> begin
                      scanner#enter_block()
                  end
                  | _ -> ()
                end;
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                scanner#ctx_stmt();
                raise Exit
            end
            | I.X (I.N N_odd_else_stmt), _, I.X (I.T T_RBRACE) -> begin
                if scanner#peek_rawtoken() == ELSE then begin
                  match scanner#peek_nth_rawtoken 2 with
                  | IF | WHILE -> env#stack#exit_block();
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_nonempty_list_odd_else_stmt_), _, I.X (I.T T_RBRACE) -> begin
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                scanner#ctx_stmt();
                raise Exit
            end
            | I.X (I.N N_separated_nonempty_list_COMMA_type_id_), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_end_of_dtor();
                raise Exit
            end
            | I.X (I.N N__using_directive), _, I.X (I.T T_NAMESPACE) -> begin
                env#set_using_ns_flag();
                raise Exit
            end
            | I.X (I.N N_function_specifier), _, I.X (I.T T_VIRTUAL) -> begin
                env#set_virtual_func_flag();
                raise Exit
            end
            | I.X (I.N N_placeholder_type_specifier), _, I.X (I.T T_AUTO) -> begin
                scanner#ctx_end_of_ty_spec();
                raise Exit
            end
            | I.X (I.N N_noptr_declarator), _, I.X (I.T T_TY_LPAREN) -> begin
                env#stack#enter_params();
                if scanner#context == C.MEM_INIT then begin
                  scanner#ctx_top();
                  scanner#ctx_end_of_ty_spec();
                end;
                raise Exit
            end
            | I.X (I.N N_pp_dtor_if_group), _, I.X (I.T T_PS_LPAREN) -> begin
                env#stack#enter_params();
                env#set_old_param_decl_flag();
                raise Exit
            end
            | I.X (I.N N_pp_dtor_elif_group), _, I.X (I.T T_PS_LPAREN) -> begin
                env#stack#enter_params();
                env#set_old_param_decl_flag();
                raise Exit
            end
            | I.X (I.N N_pp_dtor_else_group), _, I.X (I.T T_PS_LPAREN) -> begin
                env#stack#enter_params();
                env#set_old_param_decl_flag();
                raise Exit
            end
            | I.X (I.N N_pp_dtor_if_group), _, I.X (I.T T_RPAREN) -> begin
                env#stack#exit_params();
                raise Exit
            end
            | I.X (I.N N_pp_dtor_elif_group), _, I.X (I.T T_RPAREN) -> begin
                env#stack#exit_params();
                raise Exit
            end
            | I.X (I.N N_pp_dtor_else_group), _, I.X (I.T T_RPAREN) -> begin
                env#stack#exit_params();
                raise Exit
            end

            | I.X (I.N N_noptr_declarator), _, I.X (I.T T_PS_LPAREN) -> begin
                env#stack#enter_params();
                env#set_old_param_decl_flag();
                raise Exit
            end
            | I.X (I.N N_noptr_declarator), x::y::_, I.X (I.T T_RPAREN) when y <> I.X (I.T T_GNU_ASM) -> begin
                env#stack#exit_params();
                if x = I.X (I.T T_TY_LPAREN) then
                  env#set_end_of_noptr_dtor_paren_flag();
                raise Exit
            end
            (*| I.X (I.N N_noptr_declarator), _, I.X (I.T T_LBRACKET) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end*)
            | I.X (I.N N_noptr_declarator), _, I.X (I.T T_RBRACKET) -> begin
                scanner#ctx_end_of_id_expr();
                raise Exit
            end
            | I.X (I.N N_noptr_abstract_declarator), _, I.X (I.T T_TY_LPAREN) -> begin
                env#stack#enter_params();
                raise Exit
            end
            | I.X (I.N N_noptr_abstract_declarator), _, I.X (I.T T_RPAREN) -> begin
                env#stack#exit_params();
                env#set_end_of_noptr_dtor_paren_flag();
                raise Exit
            end
            (*| I.X (I.N N_noptr_abstract_declarator), _, I.X (I.T T_LBRACKET) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end*)
            | I.X (I.N N_parameters_and_qualifiers), _, I.X (I.T T_TY_LPAREN) -> begin
                env#stack#enter_params();
                scanner#ctx_ini();
                env#set_function_name();
                raise Exit
            end
            | I.X (I.N N_parameters_and_qualifiers), I.X (I.T T_TY_LPAREN)::_::_, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_params_flag();
                env#stack#exit_params();
                env#clear_ty_param_key_flag();
                if
                  env#in_body_brace_flag &&
                  scanner#context != NEW &&
                  not (scanner#context == MEM && env#stack#at_class)
                then
                  scanner#ctx_stmt()
                else if scanner#context == CLASS then
                  ()
                else if scanner#context != MEM then
                  if env#stack#in_class then
                    scanner#ctx_mem()
                  else if scanner#context != NEW then
                    scanner#ctx_top();
                raise Exit
            end

            | I.X (I.N N_macro_arg), I.X (I.T T_TY_LPAREN)::x::_, I.X (I.T T_RPAREN) -> begin
                begin
                  match x with
                  | I.X (I.N N_params_list) -> env#stack#exit_params()
                  | _ -> ()
                end;
                raise Exit
            end

            | I.X (I.N N_handler), _, I.X (I.T T_TY_LPAREN) -> begin
                env#stack#enter_params();
                scanner#ctx_stmt();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_handler), _, I.X (I.T T_RPAREN) -> begin
                env#stack#exit_params();
                env#set_end_of_handler_head_flag();
                raise Exit
            end
            | I.X (I.N N_primary_expression), _, I.X (I.T T_RPAREN) -> begin
                env#set_expr_flag();
                raise Exit
            end
            | I.X (I.N N_lambda_introducer), _, I.X (I.T T_LAM_MACRO) -> begin
                scanner#push_context();
                raise Exit
            end
            | I.X (I.N N_lambda_introducer), _, I.X (I.T T_LAM_LBRACKET) -> begin
                scanner#push_context();
                env#enter_lambda_intro();
                raise Exit
            end
            | I.X (I.N N_lambda_introducer), _, I.X (I.T T_RBRACKET) -> begin
                scanner#ctx_end_of_lam_intro();
                env#exit_lambda_intro();
                raise Exit
            end
            | I.X (I.N N__static_assert_declaration), _, I.X (I.T T_STATIC_ASSERT) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                scanner#ctx_expr();
                scanner#ctx_in_expr();
                raise Exit
            end
            | I.X (I.N N__static_assert_declaration), _, I.X (I.T T_RPAREN) -> begin
                scanner#pop_context();
                scanner#pop_sub_context();
                env#clear_str_flag();
                raise Exit
            end
            | I.X (I.N N__static_assert_declaration), _, I.X (I.T T_COMMA) -> begin
                env#set_str_flag();
                raise Exit
            end
            | I.X (I.N N_conversion_function_id), _, I.X (I.T T_OPERATOR) -> begin
                begin
                  match scanner#peek_rawtoken() with
                  | IDENT _ | CONST | COLON_COLON | HEAD_COLON_COLON -> env#set_conv_func_id_flag();
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_type_parameter), _, x -> begin
                begin
                  match x with
                  | I.X (I.T T_CLASS) -> begin
                      if in_params() then
                        env#set_ty_param_key_flag()
                  end
                  | I.X (I.T T_TYPENAME) -> begin
                      if in_params() then
                        env#set_ty_param_key_flag()
                  end
                  | I.X (I.T T_EQ) -> begin
                      env#set_ty_param_rhs_flag()
                  end
                  | _ -> ()
                end;
                if env#templ_param_arg_level > 0 then
                  env#enter_ty_param();
                raise Exit
            end
            (*| I.X (I.N N_type_parameter), I.X (I.T T_TYPENAME), I.X (I.T T_IDENT) -> begin
                env#exit_typename();
                raise Exit
            end
            | I.X (I.N N_type_parameter), _, I.X (I.T T_CLASS) -> begin
                if in_params() then
                  env#set_ty_param_key_flag();
                raise Exit
            end
            | I.X (I.N N_type_parameter), _, I.X (I.T T_TYPENAME) -> begin
                if in_params() then
                  env#set_ty_param_key_flag();
                env#enter_typename();
                raise Exit
            end*)
            | I.X (I.N N_typename_specifier), _, I.X (I.T T_TYPENAME) -> begin
                if in_params() then
                  env#set_ty_param_key_flag();
                env#enter_typename();
                raise Exit
            end
            (*| I.X (I.N N_typename_specifier), _, I.X (I.T T_IDENT) -> begin
                begin
                  match scanner#peek_rawtoken() with
                  | TEMPL_LT | COLON_COLON -> ()
                  | _ -> env#exit_typename()
                end;
                raise Exit
            end*)
            | I.X (I.N N_block_declaration), _, I.X (I.T T_SEMICOLON) -> begin
                if env#stack#in_class then
                  scanner#ctx_mem()
                else
                  scanner#ctx_top();
                scanner#ctx_ini();
                begin
                  match PB.token_to_rawtoken scanner#current_token with
                  | SEMICOLON true ->
                      iter_items ~ith:2 menv_
                        (fun item ->
                          match item with
                          | _, I.X (I.N N_pp_decl_if_group), _, _, _ -> begin
                              begin
                                match scanner#peek_rawtoken() with
                                (*| PP_ELSE _ | PP_ELIF _ | PP_ENDIF _ -> env#set_semicolon_info()*)
                                | x when Scanner.is_pp_elif_else_endif_like env x ->
                                    env#set_semicolon_info()
                                | _ -> ()
                              end;
                              raise Exit
                          end
                          | _, I.X (I.N N_pp_decl_elif_group), _, _, _ -> begin
                              begin
                                match scanner#peek_rawtoken() with
                                (*| PP_ELSE _ | PP_ELIF _ | PP_ENDIF _ -> env#set_semicolon_info()*)
                                | x when Scanner.is_pp_elif_else_endif_like env x ->
                                    env#set_semicolon_info()
                                | _ -> ()
                              end;
                              raise Exit
                          end
                          | _, I.X (I.N N_pp_decl_else_group), _, _, _ -> begin
                              begin
                                match scanner#peek_rawtoken() with
                                (*| PP_ELSE _ | PP_ELIF _ | PP_ENDIF _ -> env#set_semicolon_info()*)
                                | x when Scanner.is_pp_elif_else_endif_like env x ->
                                    env#set_semicolon_info()
                                | _ -> ()
                              end;
                              raise Exit
                          end
                          | _ -> ()
                        )
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_enumerator_list), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_enum();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_enumerator_definition), _, I.X (I.T T_EQ) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_enumerator), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_enumerator), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                scanner#ctx_enum();
                scanner#ctx_ini();
                raise Exit
           end
            | I.X (I.N N_constant_expression), _, _ -> begin
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_class_head), I.X (I.T T_IDENT_CHM)::_, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_class_head), I.X (I.T T_IDENT_CHM)::_, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                scanner#ctx_class();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_class_head), _, I.X (I.T T_CLASS_HEAD_MACRO) -> begin
                scanner#ctx_class();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_class_name), _, I.X (I.T T_IDENT) -> begin
                env#set_class_name_flag();
                raise Exit
            end
            | I.X (I.N N_class_name), _, I.X (I.T T_TEMPL_GT) -> begin
                env#set_class_name_flag();
                raise Exit
            end
            | I.X (I.N N_class_key), _, I.X (I.T T_CLASS) -> begin
                if in_params() then
                  env#set_ty_param_key_flag()
                else if
                  not env#cast_key_flag &&
                  not env#sizeof_ty_flag &&
                  not env#macro_arg_flag
                then begin
                  scanner#ctx_class();
                  scanner#ctx_ini();
                end;
                raise Exit
            end
            | I.X (I.N N_class_key), _, I.X (I.T T_UNION) -> begin
                if in_params() then
                  env#set_ty_param_key_flag()
                else if
                  not env#cast_key_flag &&
                  not env#sizeof_ty_flag &&
                  not env#macro_arg_flag
                then begin
                  scanner#ctx_class();
                  scanner#ctx_ini();
                end;
                raise Exit
            end
            | I.X (I.N N_class_key), _, I.X (I.T T_STRUCT) -> begin
                if in_params() then
                  env#set_ty_param_key_flag()
                else if
                  not env#cast_key_flag &&
                  not env#sizeof_ty_flag &&
                  not env#macro_arg_flag
                then begin
                  scanner#ctx_class();
                  scanner#ctx_ini();
                end;
                raise Exit
            end
            | I.X (I.N N_class_specifier), _, I.X (I.T T_CLASS_LBRACE) -> begin
                scanner#ctx_mem();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_class_specifier), _, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_class();
                env#reset_access_spec();
                env#set_end_of_class_spec_flag();
                if scanner#context == MEM then begin
                  scanner#ctx_top();
                  begin
                    match scanner#peek_rawtoken() with
                    | IDENT _ -> scanner#ctx_end_of_ty_spec()
                    | _ -> ()
                  end
                end;
                raise Exit
            end
            | I.X (I.N N_enum_specifier), _, I.X (I.T T_LBRACE) -> begin
                env#exit_enum_head();
                scanner#ctx_enum();
                raise Exit
            end
            | I.X (I.N N_enum_specifier), _, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_enum();
                scanner#ctx_top();
                env#set_end_of_enum_spec_flag();
                begin
                  match scanner#peek_rawtoken() with
                  | IDENT _ -> scanner#ctx_end_of_ty_spec()
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_labeled_statement), _, I.X (I.T T_SEMICOLON) -> begin
                scanner#ctx_stmt();
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                if not env#asm_block_flag then
                  env#exit_asm();
                raise Exit
            end
            | I.X (I.N N_labeled_statement), _::I.X (I.N N_pp_stmt_if_section_broken)::_, I.X (I.T T_MARKER) ->
                begin
                  scanner#ctx_stmt();
                  let sn = I.current_state_number menv_ in
                  ctx_start_of_stmt sn;
                  raise Exit
                end
            | I.X (I.N N_label), _, I.X (I.T T_CASE) -> begin
                scanner#ctx_in_case_label();
                raise Exit
            end
            | I.X (I.N N_label), _, I.X (I.T T_COLON) -> begin
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                env#set_end_of_label_flag();
                raise Exit
            end
            | I.X (I.N N_braced_init_list), _, I.X (I.T T_INI_LBRACE) -> begin
                env#enter_braced_init();
                if scanner#context <> C.CLASS then begin
                  scanner#ctx_expr();
                  scanner#ctx_ini();
                end;
                raise Exit
            end
            | I.X (I.N N_braced_init_list), _, I.X (I.T T_RBRACE) -> begin
                env#exit_braced_init();
                raise Exit
            end
            | I.X (I.N N__initializer_list), _, I.X (I.T T_COMMA) -> begin
                iter_items ~ith:2 menv_
                  (fun item ->
                    match item with
                    | _, I.X (I.N N_pp_stmt_if_group_broken), _, _, _ -> begin
                        begin
                          match scanner#peek_rawtoken() with
                          (*| PP_ELSE _ | PP_ELIF _ -> env#set_comma_info()*)
                          | x when Scanner.is_pp_elif_else_like env x -> env#set_comma_info()
                          | _ -> ()
                        end;
                        raise Exit
                    end
                    | _ -> ()
                  );
                raise Exit
            end
            | I.X (I.N N_template_head), _, I.X (I.T T_TEMPL_LT) -> begin
                env#enter_templ_head env#templ_param_arg_level;
                raise Exit
            end
            | I.X (I.N N_template_head), _, I.X (I.T T_TEMPL_GT) -> begin
                if env#stack#in_class then
                  scanner#ctx_mem()
                else
                  scanner#ctx_top();
                scanner#ctx_ini();
                (*env#exit_templ_head();*)
                env#set_end_of_templ_head_flag();
                raise Exit
            end
            (*| I.X (I.N N_function_body), I.X (I.T T_LBRACE)::_, I.X (I.T T_LBRACE) -> begin
                raise Exit
            end*)
            | I.X (I.N N_function_body), _, I.X (I.T T_SEMICOLON) -> begin
                scanner#ctx_mem();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_function_body), I.X (I.T T_IDENT_BM)::_, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_function_body), I.X (I.T T_IDENT_BM)::_, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                if env#stack#in_class then
                  scanner#ctx_mem()
                else
                  scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_init_declarator_list), _, I.X (I.T T_COMMA) -> begin
                if
                  try
                    iter_items ~ith:2 menv_
                      (function
                        | _, I.X (I.N N_function_definition), _, _, _ -> raise Exit
                        | _, I.X (I.N N_declaration), _, _, _ -> raise Exit
                        | _ -> ()
                      );
                    true
                  with
                    Exit -> false
                then
                  scanner#ctx_stmt();

                scanner#ctx_end_of_ty_spec();
                env#set_dtor_flag();
                raise Exit
            end
            | I.X (I.N N_decl_macro_call_), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                env#change_paren_kind PK_MACRO;
                raise Exit
            end
            | I.X (I.N N_decl_macro_call_), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                env#clear_end_of_params_flag();
                begin
                  match scanner#context with
                  | EXPR -> scanner#ctx_top(); scanner#ctx_ini()
                  | _ -> scanner#ctx_ini()
                end;
                raise Exit
            end
            | I.X (I.N N_decl_OR_stmt_macro_call), _, I.X (I.T T_LPAREN) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_decl_OR_stmt_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                env#clear_end_of_params_flag();
                scanner#pop_context();
                scanner#pop_sub_context();
                iter_items ~ith:5 menv_
                  (fun item ->
                    match item with
                    | sn, I.X (I.N N_compound_statement), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _ -> ()
                  );
                raise Exit
            end
            | I.X (I.N N_lambda_declarator), _, I.X (I.T T_TY_LPAREN) -> begin
                env#stack#enter_params();
                env#set_lambda_dtor_flag();
                raise Exit
            end
            | I.X (I.N N_lambda_declarator), _, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_params_flag();
                env#stack#exit_params();
                raise Exit
            end
            | I.X (I.N N_id_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_alias_declaration), _, I.X (I.T T_SEMICOLON) -> begin
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_member_declaration), _, I.X (I.T T_SEMICOLON) -> begin
                scanner#ctx_mem();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_member_declarator_list), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_end_of_ty_spec();
                env#set_dtor_flag();
                raise Exit
            end
            | I.X (I.N N_shift_expression), _, I.X (I.T T_LT_LT) -> begin
                scanner#ctx_expr();
                raise Exit
            end
            | I.X (I.N N_mem_initializer_list), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_mem_init();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_mem_initializer), _, I.X (I.T T_LPAREN) -> begin
                scanner#ctx_expr();
                raise Exit
            end
            | I.X (I.N N_mem_initializer), _, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_mem_initializer_flag();
                match scanner#peek_rawtoken() with
                | PP_IF | PP_IFDEF | PP_IFNDEF -> begin
                    scanner#ctx_mem_init();
                    scanner#ctx_ini();
                    raise Exit
                end
                | _ -> ()
            end
            | I.X (I.N N_ctor_initializer), _, I.X (I.T T_COLON) -> begin
                scanner#ctx_mem_init();
                scanner#ctx_ini();
                env#enter_ctor_init();
                raise Exit
            end
            | I.X (I.N N_pp_ctor_init_if_group), _, I.X (I.T T_COLON) -> begin
                scanner#ctx_mem_init();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_ctor_init_elif_group), _, I.X (I.T T_COLON) -> begin
                scanner#ctx_mem_init();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_ctor_init_else_group), _, I.X (I.T T_COLON) -> begin
                scanner#ctx_mem_init();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_initializer_), _, I.X (I.T T_LPAREN) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_brace_or_equal_initializer), _, I.X (I.T T_EQ) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                begin
                  match scanner#peek_rawtoken() with
                  | DELETE -> ()
                  | _ -> env#set_eq_init_flag()
                end;
                raise Exit
            end
            | I.X (I.N N_parameter_declaration), _, I.X (I.T T_EQ) -> begin
                scanner#ctx_expr ~force:true ();
                scanner#ctx_ini();
                env#set_init_flag();
                raise Exit
            end
            | I.X (I.N N_parameter_declaration_list), _, I.X (I.T T_COMMA) -> begin
                if env#in_body_brace_flag then
                  scanner#ctx_stmt()
                else
                  if scanner#context != MEM then
                    scanner#ctx_top();
                scanner#ctx_ini();
                env#set_param_head_flag();
                raise Exit
            end
            | I.X (I.N N_template_parameter_list), _, I.X (I.T T_COMMA) -> begin
                if scanner#context != MEM then
                  scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_linkage_specification), _, I.X (I.T T_LBRACE) -> begin
                env#set_linkage_spec_flag();
                raise Exit
            end
            | I.X (I.N N_linkage_specification), _, I.X (I.T T_RBRACE) -> begin
                env#clear_linkage_spec_flag();
                raise Exit
            end
            | I.X (I.N N__lambda_expression), _, I.X (I.T T_TEMPL_GT) -> begin
                env#set_end_of_lambda_templ_flag();
                raise Exit
            end
            | I.X (I.N N_compound_statement), _, I.X (I.T T_LBRACE) -> begin
                [%debug_log "@"];
                env#clear_virtual_func_flag();
                let no_tweak = env#ctor_init_flag in
                scanner#enter_block ~no_tweak ();
                begin
                  try
                    iter_items ~ith:1 menv_
                      (function
                        | _, I.X (I.N N_function_body), _, _, _ -> begin
                            env#set_body_head_flag();
                            env#set_in_body_brace_flag();
                            (*scanner#set_body_flag();*)
                            raise Exit
                        end
                        | _, I.X (I.N N_function_definition), _, _, _ -> begin
                            env#set_body_head_flag();
                            env#set_in_body_brace_flag();
                            scanner#set_body_flag();
                            token_seq#set_func_body_flag();
                            token_seq#add_token (T.IDENT_V "<func>");
                            token_seq#add_token T.LBRACE;
                            raise Exit
                        end
                        | _, I.X (I.N N_declaration), _, _, _ -> begin
                            env#set_body_head_flag();
                            env#set_in_body_brace_flag();
                            (*scanner#set_body_flag();*)
                            raise Exit
                        end
                        | _, I.X (I.N N_lambda_expression), _, _, _ -> begin
                            env#set_body_head_flag();
                            env#set_in_body_brace_flag();
                            scanner#set_body_flag();
                            env#reset_dtor_node();
                            scanner#reset_body_name();
                            raise Exit
                        end
                        | _, I.X (I.N N_block_literal_expression), _, _, _ -> begin
                            env#set_body_head_flag();
                            env#set_in_body_brace_flag();
                            scanner#set_body_flag();
                            env#reset_dtor_node();
                            scanner#reset_body_name();
                            raise Exit
                        end
                        (*| _, I.X (I.N N_decl_macro_call_), _, _, _ -> begin
                            env#set_body_head_flag();
                            env#set_in_body_brace_flag();
                            raise Exit
                        end*)
                        | _ -> ()
                      )
                  with
                    Exit -> ()
                end;
                begin
                  match scanner#peek_rawtoken() with
                  | PP_ENDIF _ -> ()
                  | _ ->
                      let sn = I.current_state_number menv_ in
                      ctx_start_of_stmt sn
                end;
                raise Exit
            end
            | I.X (I.N N_selection_statement), _, I.X (I.T T_ELSE) -> begin
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                scanner#ctx_stmt();
                raise Exit
            end
            | I.X (I.N N_compound_statement), _, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                if
                  try
                    match (env#stack#peek_nth 2)#scope with
                    | Pinfo.Name.Scope.Block _ -> begin
                        match (env#stack#peek_nth 1)#scope with
                        | Pinfo.Name.Scope.Class _ -> false
                        | _ -> true
                    end
                    | _ -> false
                  with
                    _ -> false
                then begin
                  try
                    iter_items ~ith:1 menv_
                      (function
                        | _, I.X (I.N N_compound_statement), _, _, _ -> begin
                            let sn = I.current_state_number menv_ in
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _ -> ()
                      )
                  with
                    Exit -> ()
                end;
                begin
                  try
                    iter_items ~ith:3 menv_
                      (function
                        | _, I.X (I.N N_selection_statement), _, _, _ -> begin
                            let sn = I.current_state_number menv_ in
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _, I.X (I.N N_iteration_statement), _, _, _ -> begin
                            let sn = I.current_state_number menv_ in
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _, I.X (I.N N_iteration_macro), _, _, _ -> begin
                            let sn = I.current_state_number menv_ in
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _, I.X (I.N N_function_body), _, _, _ -> begin
                            if env#stack#block_level = 0 then begin
                              scanner#ctx_reset();
                              env#clear_in_body_brace_flag();
                            end;
                            raise Exit
                        end
                        | _, I.X (I.N N_function_definition), _, _, _ -> begin
                            scanner#ctx_reset();
                            env#clear_in_body_brace_flag();
                            token_seq#add_token T.EOF;
                            token_seq#clear_func_body_flag();
                            raise Exit
                        end
                        | _, I.X (I.N N_declaration), _, _, _ -> begin
                            if not env#top_stmts_flag then begin
                              scanner#ctx_reset();
                              env#clear_in_body_brace_flag();
                            end;
                            raise Exit
                        end
                        | _, I.X (I.N N_decl_macro_call_), _, _, _ -> begin
                            scanner#ctx_reset();
                            raise Exit
                        end
                        | _, I.X (I.N N_member_declaration), _, _, _ -> begin
                            scanner#ctx_mem();
                            raise Exit
                        end
                        | _, I.X (I.N N_member_declarator), _, _, _ -> begin
                            scanner#ctx_mem();
                            raise Exit
                        end
                        | _ -> ()
                      )
                  with
                    Exit -> ()
                end;
                begin
                  try
                    iter_items ~ith:4 menv_
                      (function
                        | _, I.X (I.N N_member_declarator), _, _, _ -> begin
                            begin
                              try
                                match (env#stack#top)#scope with
                                | Pinfo.Name.Scope.Class _ -> scanner#ctx_mem();
                                | _ -> ()
                              with _ -> ()
                            end;
                            raise Exit
                        end
                        | _ -> ()
                      )
                  with
                    Exit -> ()
                end;
                raise Exit
            end
            | _ -> ()

          in (* let _proc_shift2 *)

          let _proc_shift3 (_, l, rs, r, _) =
            match l, rs, r with
            | I.X (I.N N_iteration_statement), I.X (I.T T_FOR)::_, I.X (I.T T_COLON) -> begin
                scanner#ctx_expr();
                env#set_for_range_init_flag();
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_FOR)::_, I.X (I.T T_LPAREN) -> begin
                env#stack#enter_params();
                env#set_for_flag();
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_FOR)::_, I.X (I.T T_RPAREN) -> begin
                env#stack#exit_params();
                env#clear_for_flag();
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_DO)::_, I.X (I.T T_LPAREN) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_DO)::_, I.X (I.T T_DO) -> begin
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_DO)::_, I.X (I.T T_RPAREN) -> begin
                begin
                  match scanner#peek_rawtoken() with
                  | EOF -> begin
                      let _, _, ep = scanner#current_token in
                      scanner#prepend_token (T.SEMICOLON false, ep, ep)
                  end
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_DO)::_, I.X (I.T T_SEMICOLON) -> begin
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_WHILE)::_, I.X (I.T T_LPAREN) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                env#set_condition_flag();
                raise Exit
            end
            | I.X (I.N N_iteration_statement), I.X (I.T T_WHILE)::_, I.X (I.T T_RPAREN) -> begin
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                env#clear_condition_flag();
                raise Exit
            end
            | I.X (I.N N_jump_statement), I.X (I.T T_RETURN)::_, I.X (I.T T_RETURN) -> begin
                scanner#ctx_expr();
                raise Exit
            end
            | I.X (I.N N_jump_statement), _, I.X (I.T T_SEMICOLON) -> begin
                begin
                  match scanner#peek_rawtoken() with
                  | IDENT _ ->
                      let sn = I.current_state_number menv_ in
                      ctx_start_of_stmt sn;
                  | _ -> begin
                      scanner#ctx_stmt();
                      scanner#ctx_ini();
                      begin
                      try
                        iter_items ~ith:3 menv_
                          (function
                            | _, I.X (I.N N_selection_statement), _, _, _ -> begin
                                let sn = I.current_state_number menv_ in
                                ctx_start_of_stmt sn;
                                raise Exit
                            end
                            | _ -> ()
                          )
                      with
                        Exit -> ()
                      end
                  end
                end;
                raise Exit
            end
            | I.X (I.N N_selection_statement), x::_, I.X (I.T T_LPAREN) -> begin
                begin
                  match x with
                  | I.X (I.T T_IF) -> scanner#ctx_expr(); env#set_condition_flag()
                  | I.X (I.T T_SWITCH) -> scanner#ctx_expr(); env#set_condition_flag()
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_selection_statement), x::_, I.X (I.T T_RPAREN) -> begin
                begin
                  match x with
                  | I.X (I.T T_IF) -> begin
                      let sn = I.current_state_number menv_ in
                      ctx_start_of_stmt sn;
                      scanner#ctx_stmt();
                      env#set_end_of_if_head_flag();
                      env#clear_condition_flag()
                  end
                  | I.X (I.T T_SWITCH) -> begin
                      let sn = I.current_state_number menv_ in
                      ctx_start_of_stmt sn;
                      scanner#ctx_stmt();
                      env#clear_condition_flag()
                  end
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_new_initializer), _, I.X (I.T T_LPAREN) -> begin
                scanner#ctx_expr();
                raise Exit
            end
            | I.X (I.N N_cast_expression), _, I.X (I.T T_TY_LPAREN) -> begin
                env#set_cast_head_flag();
                raise Exit
            end
            | I.X (I.N N_cast_expression), _, I.X (I.T T_RPAREN) -> begin
                scanner#ctx_expr();
                env#set_end_of_cast_type_flag();
                env#clear_cast_head_flag();
                raise Exit
            end
            | I.X (I.N N_postfix_expression), x::_, y -> begin
                begin
                  match x, y with
                  | I.X (I.N N_cast_key), I.X (I.T T_LPAREN) -> env#clear_cast_key_flag()
                  | I.X (I.N N_cast_key), I.X (I.T T_TEMPL_LT) -> env#enter_templ_arg false
                  | I.X (I.N N_cast_key), I.X (I.T T_TEMPL_GT) -> env#exit_templ_arg()
                  | I.X (I.N N_postfix_expression), I.X (I.T T_RPAREN) -> env#set_expr_flag()

                  | I.X (I.T T_TY_LPAREN), I.X (I.T T_TY_LPAREN) when begin
                      not env#sizeof_ty_flag &&
                      match scanner#prev_rawtoken2 with
                      | SIZEOF -> false
                      | _ -> true
                  end -> env#set_cast_head_flag()

                  | I.X (I.T T_TY_LPAREN), I.X (I.T T_RPAREN) -> begin
                      scanner#ctx_expr();
                      if env#cast_head_flag then begin
                        env#set_end_of_cast_type_flag();
                        env#clear_cast_head_flag()
                      end;
                  end
                  | _ -> ()
                end;
                scanner#ctx_expr();
                raise Exit
            end
            | I.X (I.N N_restricted_postfix_expr), x::_, y -> begin
                begin
                  match x, y with
                  | I.X (I.N N_cast_key), I.X (I.T T_LPAREN) -> env#clear_cast_key_flag(); scanner#ctx_ini()
                  | I.X (I.N N_cast_key), I.X (I.T T_TEMPL_LT) -> env#enter_templ_arg false
                  | I.X (I.N N_cast_key), I.X (I.T T_TEMPL_GT) -> env#exit_templ_arg()
                  | I.X (I.N N_restricted_postfix_expr), y -> begin
                      match y with
                      | I.X (I.T T_DOT)
                      | I.X (I.T T_MINUS_GT) -> env#set_mem_acc_flag()
                      | _ -> ()
                  end
                  | _ -> ()
                end;
                (*DEPRECATED!scanner#ctx_expr();*)
                raise Exit
            end
            (*| I.X (I.N N_restricted_eq_expr), _, I.X (I.T T_EQ_EQ) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end*)
            | I.X (I.N N_multiplicative_expression), _, _ -> begin
                scanner#ctx_expr();
                raise Exit
            end
            | I.X (I.N N_statement), x::_, y when begin
                match y with
                | I.X (I.T T_SEMICOLON) -> begin
                    if not env#asm_block_flag then
                      env#exit_asm();
                    true
                end
                | I.X (I.T T_STMT_MACRO) -> true
                | _ -> false
            end -> begin
                scanner#ctx_end_of_stmt();
                scanner#ctx_stmt();
                scanner#clear_keep_flag();
                scanner#clear_alternative_tokens();
                let flag = ref true in
                begin
                  try
                    begin
                      match I.get 1 menv_ with
                      | None -> begin
                          let sn = I.current_state_number menv_ in
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _ -> ()
                    end;

                    iter_items ~ith:1 menv_
                      (fun item ->
                        flag := false;
                        match item with
                        | sn, I.X (I.N N_compound_statement), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_statement_seq_opt), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _ -> ()
                      );
                    iter_items_w ~from_ith:2 ~to_ith:6 menv_
                      (fun item ->
                        flag := false;
                        match item with
                        | sn, I.X (I.N N_pp_stmt_if_group_broken), _, _, _
                        | sn, I.X (I.N N_pp_stmt_elif_group_broken), _, _, _
                        | sn, I.X (I.N N_pp_stmt_else_group_broken), _, _, _ when begin
                            match x with
                            | I.X (I.N N_decl_OR_expr) -> true
                            | _ -> false
                        end -> begin
                          ctx_start_of_stmt sn;
                          raise Exit
                        end
                        | sn, I.X (I.N N_compound_statement), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_selection_statement), _, I.X (I.T T_ELSE), _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_pp_stmt_if_group), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_pp_stmt_elif_group), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_pp_stmt_else_group), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_pp_stmt_if_section_closing), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _, I.X (I.N N_iteration_statement), x::_, y, _ -> begin
                            match x, y with
                            | I.X (I.T T_FOR), I.X (I.T T_RPAREN) -> begin
                                iter_items_w ~from_ith:9 ~to_ith:9 menv_
                                  (function
                                    | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                                        ctx_start_of_stmt sn;
                                        raise Exit
                                    end
                                    | sn, I.X (I.N N_compound_statement), _, _, _ -> begin
                                        ctx_start_of_stmt sn;
                                        raise Exit
                                    end
                                    | _ -> ()
                                  )
                            end
                            | _ -> ()
                        end
                        | _, I.X (I.N N_selection_statement), x::_, y, _ -> begin
                            match x, y with
                            | I.X (I.T T_IF), I.X (I.T T_RPAREN) -> begin
                                iter_items_w ~from_ith:6 ~to_ith:7 menv_
                                  (function
                                    | sn, I.X (I.N N_compound_statement), _, _, _ -> begin
                                        ctx_start_of_stmt sn;
                                        raise Exit
                                    end
                                    | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                                        ctx_start_of_stmt sn;
                                        raise Exit
                                    end
                                    | _ -> ()
                                  )
                            end
                            | _ -> ()
                        end
                        | _ -> ()
                      )
                  with
                    Exit -> ()
                end;
                if mode = M_STMTS && !flag then begin
                  let sn = I.current_state_number menv_ in
                  ctx_start_of_stmt sn
                end;
                raise Exit
            end
            | I.X (I.N N_statement), _, I.X (I.T T_END_ASM) -> begin
                env#exit_asm();
                scanner#ctx_end_of_stmt();
                scanner#ctx_stmt();
                let flag = ref true in
                begin
                  try
                    iter_items ~ith:4 menv_
                      (fun item ->
                        flag := false;
                        match item with
                        | sn, I.X (I.N N_compound_statement), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_pp_stmt_if_group), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | sn, I.X (I.N N_pp_stmt_if_section_closing), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _, I.X (I.N N_iteration_statement), x::_, y, _ -> begin
                            match x, y with
                            | I.X (I.T T_FOR), I.X (I.T T_RPAREN) -> begin
                                iter_items_w ~from_ith:9 ~to_ith:9 menv_
                                  (function
                                    | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                                        ctx_start_of_stmt sn;
                                        raise Exit
                                    end
                                    | _ -> ()
                                  )
                            end
                            | _ -> ()
                        end
                        | _, I.X (I.N N_selection_statement), x::_, y, _ -> begin
                            match x, y with
                            | I.X (I.T T_IF), I.X (I.T T_RPAREN) -> begin
                                iter_items_w ~from_ith:6 ~to_ith:6 menv_
                                  (function
                                    | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                                        ctx_start_of_stmt sn;
                                        raise Exit
                                    end
                                    | _ -> ()
                                  )
                            end
                            | _ -> ()
                        end
                        | _ -> ()
                      )
                  with
                    Exit -> ()
                end;
                if mode = M_STMTS && !flag then begin
                  let sn = I.current_state_number menv_ in
                  ctx_start_of_stmt sn
                end;
                raise Exit
            end
            | I.X (I.N N_stmt_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_stmt_macro_call), _, I.X (I.T T_SS_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_stmt_macro_call), _, I.X (I.T T_RPAREN) -> begin
                scanner#ctx_end_of_stmt();
                scanner#clear_keep_flag();
                env#exit_macro_arg();
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                raise Exit
            end
            | I.X (I.N N_expr_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_expr_macro_call), _, I.X (I.T T_SS_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_expr_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                iter_items ~ith:4 menv_
                  (function
                    | _, I.X (I.N N_selection_statement), (I.X (I.T T_IF))::_, _, _ -> begin
                        let sn = I.current_state_number menv_ in
                        ctx_start_of_stmt sn;
                        scanner#ctx_stmt();
                        raise Exit
                    end
                    | _ -> ()
                  );
                raise Exit
            end
            | I.X (I.N N_templ_param_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_templ_param_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                raise Exit
            end
            | I.X (I.N N_attr_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_attr_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                env#set_end_of_attr_macro_call_flag();
                raise Exit
            end

            | _ -> ()
          in (* let _proc_shift3 *)

          let _proc_shift4 (_, l, rs, r, i) =
            match l, rs, r with
            | I.X (I.N N_gnu_asm_attr), _, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_attr_macro_call_flag();
                raise Exit
            end
            | I.X (I.N N_pp_control_line), rhs, I.X (I.T T_NEWLINE) -> begin
                iter_items_w ~from_ith:2 ~to_ith:7 menv_
                  (function
                    | sn, I.X (I.N N_compound_statement), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | sn, I.X (I.N N__statement_seq), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | sn, I.X (I.N N_pp_stmt_if_group), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _ -> ()
                  );
                if
                  match scanner#sub_context with
                  | START_OF_STMT sn0 -> begin
                      try
                        match scanner#top_sub_context with
                        | START_OF_STMT sn1 -> sn1 = sn0
                        | _ -> true
                      with
                        _ -> true
                  end
                  | _ -> true
                then begin
                  match rhs with
                  | I.X (I.T T_PP_DEFINE)::_ -> begin
                      scanner#pop_context();
                      scanner#pop_sub_context()
                  end;
                  | I.X (I.N N_macro_fun_head)::_ -> begin
                      [%debug_log "!!"];
                      scanner#pop_context();
                      scanner#pop_sub_context()
                  end;
                  | I.X (I.N N__pp_define)::_ -> begin
                      scanner#pop_context();
                      scanner#pop_sub_context()
                  end
                  | _ -> ()
                end;
                (*scanner#ctx_ini();*)
                raise Exit
            end
            | I.X (I.N N_macro_fun_head), I.X (I.T T_PP_DEFINE)::_, I.X (I.T T_PP_LPAREN) -> begin
                env#set_pp_params_flag();
                (*scanner#push_context();
                scanner#push_sub_context();*)
                raise Exit
            end
            | I.X (I.N N_pp_ifx_e), _, x -> begin
                begin
                  match x with
                  | I.X (I.T T_PP_IF_E) | I.X (I.T T_PP_IFDEF_E) | I.X (I.T T_PP_IFNDEF_E) -> begin
                      iter_items ~ith:1 menv_
                        (fun item ->
                          match item with
                          | _, I.X (I.N N_asm_block), _, I.X (I.T T_BEGIN_ASM), _ -> begin
                              env#set_begin_asm_info();
                              raise Exit
                          end
                          | _ -> ()
                        )
                  end
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_control_line), I.X (I.N N_macro_fun_head)::_, I.X (I.T T_RPAREN) -> begin
                env#clear_pp_params_flag();
                raise Exit
            end
            | I.X (I.N N_pp_control_line), I.X (I.T T_IDENT_PGM)::_, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_pp_control_line), I.X (I.T T_IDENT_PGM)::_, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                raise Exit
            end
            | I.X (I.N N_pp_ifx_broken), _, I.X (I.T T_NEWLINE) -> begin
                begin
                  match scanner#peek_rawtoken() with
                  | MARKER -> begin
                      try
                        let info = env#pp_if_section_top_info in
                        [%debug_log "info=%s" (Pinfo.pp_if_section_info_to_string info)];
                        scanner#sync_ctx_with_info info
                      with
                        _ -> ()
                  end
                  | _ -> ()
                end;
                raise Exit
            end
            | I.X (I.N N_pp_ifx_attr), _, x -> begin
                begin
                  match x with
                  | I.X (I.T T_PP_IF_ATTR)
                  | I.X (I.T T_PP_IFDEF_ATTR)
                  | I.X (I.T T_PP_IFNDEF_ATTR) -> begin
                      scanner#push_context();
                      scanner#push_sub_context();
                      raise Exit
                  end
                  | I.X (I.T T_NEWLINE) -> begin
                      scanner#pop_context();
                      scanner#pop_sub_context();
                      raise Exit
                  end
                  | _ -> ()
                end
            end
            | I.X (I.N N_pp_ifx_closing), _, I.X (I.T T_NEWLINE) -> begin
                scanner#pp_restore_context();
                raise Exit
            end
            | I.X (I.N N_pp_ifx_d), _, I.X (I.T T_NEWLINE) -> begin
                scanner#pp_restore_context();
                env#enter_pp_ifx_d();
                raise Exit
            end
            | I.X (I.N N_pp_ifx), _, I.X (I.T T_NEWLINE) -> begin
                scanner#ctx_ini();
                scanner#pp_restore_context();
                let sn = I.current_state_number menv_ in
                iter_items_w ~from_ith:3 ~to_ith:4 menv_
                  (function
                    | _, I.X (I.N N_compound_statement), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _, I.X (I.N N__statement_seq), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _, I.X (I.N N_selection_statement), x::_, I.X (I.T T_RPAREN), _ -> begin
                        scanner#ctx_stmt();
                        ctx_start_of_stmt sn;
                        begin
                          match x with
                          | I.X (I.T T_IF) -> env#set_end_of_if_head_flag()
                          | _ -> ()
                        end;
                        raise Exit
                    end
                    | _, I.X (I.N N_selection_statement), _, I.X (I.T T_ELSE), _ -> begin
                        scanner#ctx_stmt();
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _ -> ()
                  );
                if not env#stack#at_enum then
                  iter_items ~ith:5 menv_
                    (function
                      | _, I.X (I.N N_compound_statement), _, _, _ -> begin
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _, I.X (I.N N__statement_seq), _, _, _ -> begin
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _ -> ()
                    );
                iter_items ~ith:2 menv_
                  (function
                    | _, I.X (I.N N_pp_func_body_if_section), _, _, _ -> begin
                        env#set_start_of_func_body_flag();
                        raise Exit
                    end
                    | _ -> ()
                  )
            end
            | I.X (I.N N_pp_elif), _, I.X (I.T T_NEWLINE) -> begin
                env#exit_pp_group();
                env#enter_pp_group();
                env#clear_end_of_params_flag();
                scanner#pp_restore_context();
                if env#get_broken_info() then begin
                  let sn = I.current_state_number menv_ in
                  iter_items_w ~from_ith:3 ~to_ith:5 menv_
                    (function
                      | _, I.X (I.N N_compound_statement), _, _, _ -> begin
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _, I.X (I.N N__statement_seq), _, _, _ -> begin
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _, I.X (I.N N_selection_statement), x::_, I.X (I.T T_RPAREN), _ -> begin
                          scanner#ctx_stmt();
                          ctx_start_of_stmt sn;
                          begin
                            match x with
                            | I.X (I.T T_IF) -> env#set_end_of_if_head_flag()
                            | _ -> ()
                          end;
                          raise Exit
                      end
                      | _, I.X (I.N N_selection_statement), _, I.X (I.T T_ELSE), _ -> begin
                          scanner#ctx_stmt();
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _ -> ()
                    )
                end;
                iter_items ~ith:2 menv_
                  (function
                    | _, I.X (I.N N_pp_func_body_if_section), _, _, _ -> begin
                        env#set_start_of_func_body_flag();
                        raise Exit
                    end
                    | _ -> ()
                  );
                raise Exit
            end
            | I.X (I.N N_pp_else), _, I.X (I.T T_NEWLINE) -> begin
                env#exit_pp_group();
                env#enter_pp_group();
                env#clear_end_of_params_flag();
                scanner#pp_restore_context();
                if env#get_broken_info() then begin
                  let sn = I.current_state_number menv_ in
                  iter_items_w ~from_ith:3 ~to_ith:4 menv_
                    (function
                      | _, I.X (I.N N_compound_statement), _, _, _ -> begin
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _, I.X (I.N N__statement_seq), _, _, _ -> begin
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _, I.X (I.N N_selection_statement), x::_, I.X (I.T T_RPAREN), _ -> begin
                          scanner#ctx_stmt();
                          ctx_start_of_stmt sn;
                          begin
                            match x with
                            | I.X (I.T T_IF) -> env#set_end_of_if_head_flag()
                            | _ -> ()
                          end;
                          raise Exit
                      end
                      | _, I.X (I.N N_selection_statement), _, I.X (I.T T_ELSE), _ -> begin
                          scanner#ctx_stmt();
                          ctx_start_of_stmt sn;
                          raise Exit
                      end
                      | _ -> ()
                    )
                end;
                iter_items ~ith:2 menv_
                  (function
                    | _, I.X (I.N N_pp_decl_spec_if_section), _, _, _ -> begin
                        scanner#pp_restore_context();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_edef_if_section), _, _, _ -> begin
                        scanner#pp_restore_context();
                        raise Exit
                    end
                    | _, I.X (I.N N__pp_func_head_if_section), _, _, _ -> begin
                        scanner#pp_restore_context();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_func_body_if_section), _, _, _ -> begin
                        env#set_start_of_func_body_flag();
                        raise Exit
                    end
                    | _ -> ()
                  );
                let sn = I.current_state_number menv_ in
                iter_items_w ~from_ith:4 ~to_ith:6 menv_
                  (function
                    | _, I.X (I.N N_compound_statement), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _, I.X (I.N N__statement_seq), _, _, _ -> begin
                        if scanner#context != EXPR then
                          ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _ -> ()
                  )
            end
            | I.X (I.N N_pp_endif), _, I.X (I.T T_NEWLINE) -> begin
                env#exit_pp_ifx_d();
                iter_items_w ~from_ith:2 ~to_ith:3 menv_
                  (function
                    | sn, I.X (I.N N_pp_stmt_if_section_closing), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_a_if_section), _, _, _ -> begin
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_edef_if_section), _, _, _ -> begin
                        scanner#ctx_enum();
                        scanner#ctx_ini();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_decl_if_section_broken), _, _, _ -> begin
                        if scanner#peek_rawtoken() == LBRACE then
                          env#set_start_of_func_body_flag()
                        else
                          env#set_end_of_broken_decl_section_flag();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_mdecl_if_section_broken), _, _, _ -> begin
                        if scanner#peek_rawtoken() == LBRACE then
                          env#set_start_of_func_body_flag();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_dtor_if_section), _, _, _ -> begin
                        if scanner#peek_rawtoken() == LBRACE then begin
                          iter_items_w ~from_ith:5 ~to_ith:6 menv_
                            (function
                              | _, I.X (I.N N_function_definition), _, _, _ -> begin
                                  env#set_start_of_func_body_flag();
                                  raise Exit
                              end
                              | _ -> ()
                            );
                        end;
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_minit_if_section), _, _, _ -> begin
                        scanner#ctx_mem_init();
                        scanner#ctx_ini();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_ctor_init_if_section), _, _, _ -> begin
                        scanner#ctx_mem_init();
                        scanner#ctx_ini();
                        raise Exit
                    end
                    | _, I.X (I.N N__pp_func_head_if_section), _, _, _ -> begin
                        env#set_start_of_func_body_flag();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_spec_if_section), _, _, _ -> begin
                        env#set_start_of_func_body_flag();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_func_body_if_section), _, _, _ -> begin
                        begin
                          try
                            match (env#stack#top)#scope with
                            | Pinfo.Name.Scope.Class _ -> scanner#ctx_mem();
                            | _ -> scanner#ctx_top();
                          with _ -> scanner#ctx_top();
                        end;
                        scanner#ctx_ini();
                        raise Exit
                    end
                    (*| sn, I.X (I.N N_pp_args_if_section_closing), _, _, _ -> begin
                        ctx_start_of_stmt sn;
                        raise Exit
                    end*)
                    | _, I.X (I.N N_pp_enum_head_if_section), _, _, _ -> begin
                        scanner#ctx_enum();
                        scanner#ctx_ini();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_str_if_section), _, _, _ -> begin
                        env#set_end_of_str_section_flag();
                        raise Exit
                    end
                    | _, I.X (I.N N_pp_base_clause_if_section), _, _, _ -> begin
                        if env#get_broken_info() then
                          env#exit_base_clause();
                        raise Exit
                    end
                    | _ -> ()
                  );
                begin
                  match scanner#prev_rawtoken3 with
                  | COMMA_BROKEN | EQ -> ()
                  | _ ->
                      let sn = I.current_state_number menv_ in
                      iter_items_w ~from_ith:4 ~to_ith:5 menv_
                        (function
                          | _, I.X (I.N N_compound_statement), _, _, _ -> begin
                              ctx_start_of_stmt sn;
                              raise Exit
                          end
                          | _, I.X (I.N N__statement_seq), _, _, _ -> begin
                              ctx_start_of_stmt sn;
                              raise Exit
                          end
                          | _ -> ()
                        )
                end;
                raise Exit
            end
            | I.X (I.N N_init_statement), _, I.X (I.T T_SEMICOLON) -> begin
                scanner#ctx_end_of_stmt();
                scanner#clear_keep_flag();
                scanner#clear_alternative_tokens();
                scanner#ctx_expr();
                raise Exit
            end
            | I.X (I.N N_macro_arg), I.X (I.T T_TEMPL_LT)::_, I.X (I.T T_TEMPL_LT) -> begin
                env#enter_templ_arg false;
                raise Exit
            end
            | I.X (I.N N_macro_arg), I.X (I.T T_TEMPL_LT)::_, I.X (I.T T_TEMPL_GT) -> begin
                env#exit_templ_arg();
                raise Exit
            end

            | I.X (I.N N_simple_template_id), _, I.X (I.T T_TEMPL_LT) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                let is_ty =
                  List.length (get_items _menv) > 1 &&
                  (*DEPRECATED!scanner#sub_context == END_OF_TY_SPEC ||*)
                  begin
                    try
                      iter_items_w ~from_ith:1 ~to_ith:2 menv_
                        (function
                          | _, I.X (I.N N_typename_specifier), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_new_expression), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N__type_specifier_seq), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_parameter_declaration), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_trailing_return_type), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_postfix_expression), I.X (I.N N_cast_key)::_, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_type_parameter), _, I.X (I.T T_EQ), _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_template_parameter_list), _, I.X (I.T T_COMMA), _ -> begin
                              raise Found
                          end
                          | _ -> ()
                        );
                      iter_items_w ~from_ith:3 ~to_ith:3 menv_
                        (function
                          | _, I.X (I.N N_decl_specifier_seq), _, _, _ -> begin
                              if env#typedef_flag then
                                raise Found
                          end
                          | _, I.X (I.N N_parameter_declaration), _, _, _ -> begin
                              if env#const_flag then
                                raise Found
                          end
                          | _, I.X (I.N N__type_specifier_seq), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_type_parameter), _, I.X (I.T T_EQ), _ -> begin
                              raise Found
                          end
                          | _ -> ()
                        );
                      iter_items_w ~from_ith:6 ~to_ith:6 menv_
                        (function
                          | _, I.X (I.N N_type_parameter), _, I.X (I.T T_EQ), _ -> begin
                              raise Found
                          end
                          | _ -> ()
                        );
                      false
                    with
                      Found -> true
                  end
                in
                [%debug_log "is_ty=%B" is_ty];
                env#enter_templ_arg is_ty;
                scanner#ctx_in_simple_templ_id();
                raise Exit
            end
            | I.X (I.N N_simple_template_id_), _, I.X (I.T T_TEMPL_LT) -> begin
                scanner#push_context();
                scanner#push_sub_context();
                let is_ty =
                  List.length (get_items _menv) = 1 ||
                  (*DEPRECATED!scanner#sub_context == END_OF_TY_SPEC ||*)
                  begin
                    env#pstat#was_at_type_paren ||
                    try
                      iter_items_w ~from_ith:1 ~to_ith:2 menv_
                        (function
                          | _, I.X (I.N N_typename_specifier), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_new_expression), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N__type_specifier_seq), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_parameter_declaration), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_trailing_return_type), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_postfix_expression), I.X (I.N N_cast_key)::_, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_type_parameter), _, I.X (I.T T_EQ), _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_template_parameter_list), _, I.X (I.T T_COMMA), _ -> begin
                              raise Found
                          end
                          | _ -> ()
                        );
                      iter_items_w ~from_ith:3 ~to_ith:3 menv_
                        (function
                          | _, I.X (I.N N_decl_specifier_seq), _, _, _ -> begin
                              if env#typedef_flag then
                                raise Found
                          end
                          | _, I.X (I.N N_parameter_declaration), _, _, _ -> begin
                              if env#const_flag then
                                raise Found
                          end
                          | _, I.X (I.N N__type_specifier_seq), _, _, _ -> begin
                              raise Found
                          end
                          | _, I.X (I.N N_type_parameter), _, I.X (I.T T_EQ), _ -> begin
                              raise Found
                          end
                          | _ -> ()
                        );
                      iter_items_w ~from_ith:6 ~to_ith:6 menv_
                        (function
                          | _, I.X (I.N N_type_parameter), _, I.X (I.T T_EQ), _ -> begin
                              raise Found
                          end
                          | _ -> ()
                        );
                      false
                    with
                      Found -> true
                  end
                in
                [%debug_log "is_ty=%B" is_ty];
                env#enter_templ_arg is_ty;
                scanner#ctx_in_simple_templ_id();
                raise Exit
            end
            | I.X (I.N N_simple_template_id), _, I.X (I.T T_TEMPL_GT) -> begin
                scanner#pop_context();
                scanner#pop_sub_context();
                env#exit_templ_arg();
                iter_items_w ~from_ith:8 ~to_ith:8 menv_
                  (function
                    | _, I.X (I.N N_restricted_unary_expr), _, _, _ -> begin
                        env#set_expr_flag();
                        raise Exit
                    end
                    | _ -> ()
                  );
                raise Exit
            end
            | I.X (I.N N_simple_template_id_), _, I.X (I.T T_TY_TEMPL_GT) -> begin
                scanner#pop_context();
                scanner#pop_sub_context();
                env#exit_templ_arg();
                raise Exit
            end
            | I.X (I.N N_assignment_operator), _, _ -> begin
                scanner#ctx_expr();
                env#set_rhs_flag();
                raise Exit
            end
            (*| I.X (I.N N_pp_a_if_group), _, I.X (I.T T_LT_LT) -> begin
                scanner#ctx_expr();
                raise Exit
            end*)
            | I.X (I.N N_decltype_specifier), _, I.X (I.T T_DECLTYPE) -> begin
                if
                  scanner#peek_rawtoken() != TY_LPAREN ||
                  scanner#peek_nth_rawtoken 2 != AUTO
                then begin
                  scanner#push_context();
                  scanner#ctx_expr();
                  env#enter_decltype();
                end;
                raise Exit
            end
            | I.X (I.N N_decltype_specifier), _, I.X (I.T T_RPAREN) -> begin
                scanner#pop_context();
                scanner#ctx_end_of_ty_spec();
                env#exit_decltype();
                env#set_end_of_decltype_flag();
                raise Exit
            end
            | I.X (I.N N_decl_spec_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_decl_spec_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_decl_spec_macro_call_flag();
                env#exit_macro_arg();
                raise Exit
            end
            | I.X (I.N N_mem_init_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_mem_init_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                if scanner#peek_rawtoken() == LBRACE then
                  scanner#ctx_mem()
                else
                  scanner#ctx_mem_init();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_suffix_macro_call), _, I.X (I.T T_LPAREN) -> begin
                env#enter_macro_arg();
                raise Exit
            end
            | I.X (I.N N_suffix_macro_call), _, I.X (I.T T_RPAREN) -> begin
                env#exit_macro_arg();
                raise Exit
            end
            | I.X (I.N N_pp_edef_if_group), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_enum();
                raise Exit
            end
            | I.X (I.N N_pp_edef_elif_group), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_enum();
                raise Exit
            end
            | I.X (I.N N_pp_edef_else_group), _, I.X (I.T T_COMMA) -> begin
                scanner#ctx_enum();
                raise Exit
            end

            | I.X (I.N N_pp_stmt_if_group_close_open), _, I.X (I.T T_RBRACE) -> begin
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_stmt_elif_group_close_open), _, I.X (I.T T_RBRACE) -> begin
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_stmt_else_group_close_open), _, I.X (I.T T_RBRACE) -> begin
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end

            | I.X (I.N N_pp_ifstmt_if_group_closing), _, I.X (I.T T_RPAREN) -> begin
                env#set_paren_closing_info();
                raise Exit
            end
            | I.X (I.N N_pp_ifstmt_if_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end

            | I.X (I.N N_pp_args_if_group_closing), _, I.X (I.T T_RPAREN) -> begin
                env#set_paren_closing_info();
                raise Exit
            end
            | I.X (I.N N_pp_args_if_group_closing), _, I.X (I.T T_COMMA) -> begin
                env#set_comma_info();
                raise Exit
            end
            | I.X (I.N N_pp_args_if_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            (*| I.X (I.N N_pp_args_elif_group_closing), rhs, I.X (I.T T_RPAREN) -> begin
                if env#pp_if_section_top_info.Pinfo.i_paren_level <> 1 then begin
                  env#pstat#open_paren_normal();
                end;
                raise Exit
            end
            | I.X (I.N N_pp_args_else_group_closing), rhs, I.X (I.T T_RPAREN) -> begin
                if env#pp_if_section_top_info.Pinfo.i_paren_level <> 1 then begin
                  env#pstat#open_paren_normal();
                end;
                raise Exit
            end*)
            (*| I.X (I.N N_pp_enum_if_group_closing), rhs, I.X (I.T T_RBRACE) -> begin
            end*)

            (*| I.X (I.N N_pp_stmt_if_group_closing), rhs, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                raise Exit
            end
            | I.X (I.N N_pp_stmt_elif_group_closing), rhs, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                raise Exit
            end
            | I.X (I.N N_pp_stmt_else_group_closing), rhs, I.X (I.T T_RBRACE) -> begin
                env#stack#exit_block();
                raise Exit
            end*)

            | I.X (I.N N_pp_init_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_init_elif_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_init_else_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end

            | I.X (I.N N_pp_init_if_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_init_elif_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_init_else_group_closing), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end

            | I.X (I.N N_pp_cond_tl_if_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_cond_tl_elif_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end
            | I.X (I.N N_pp_cond_tl_else_group), _, I.X (I.T T_SEMICOLON) -> begin
                env#set_semicolon_info();
                raise Exit
            end

            | I.X (I.N N_pp_decl_if_group_broken), rhs, I.X (I.T T_LBRACE) -> begin
                if List.nth rhs (i-2) = I.X (I.T T_EQ) then begin
                  env#enter_braced_init();
                  raise Exit
                end else if
                  List.nth rhs 1 = I.X (I.T T_IDENT_V) && begin
                    match scanner#peek_rawtoken() with
                    (*| PP_ELIF _ | PP_ELSE _ -> true*)
                    | x when Scanner.is_pp_elif_else_like env x -> true
                    | _ -> false
                  end
                then begin
                  scanner#enter_block();
                  [%debug_log "!!! info=%s"
                    (Pinfo.pp_if_section_info_to_string env#pp_if_section_top_info)];
                  env#set_broken_info();
                  raise Exit
                end
            end
            | I.X (I.N N_pp_stmt_if_group_broken), _, I.X (I.T T_LBRACE) -> begin
                match scanner#peek_rawtoken() with
                (*| PP_ELIF _ | PP_ELSE _ -> begin*)
                | x when Scanner.is_pp_elif_else_like env x -> begin
                    scanner#enter_block();
                    [%debug_log "!!! info=%s"
                      (Pinfo.pp_if_section_info_to_string env#pp_if_section_top_info)];
                    env#set_broken_info();
                    raise Exit
                end
                | _ -> ()
            end
            | I.X (I.N N_odd_if_stmt_open), _, I.X (I.T T_LBRACE) -> begin
                match scanner#peek_rawtoken() with
                (*| PP_ELIF _ | PP_ELSE _ -> begin*)
                | x when Scanner.is_pp_elif_else_like env x -> begin
                    scanner#enter_block();
                    [%debug_log "!!! info=%s"
                      (Pinfo.pp_if_section_info_to_string env#pp_if_section_top_info)];
                    iter_items_w ~from_ith:7 ~to_ith:7 menv_
                      (function
                        | _, I.X (I.N N_pp_stmt_if_group), _, _, _ -> ()
                        | _ -> env#set_broken_info();
                      );
                    raise Exit
                end
                | _ -> begin
                    begin
                      iter_items_w ~from_ith:5 ~to_ith:6 menv_
                        (function
                          | _, I.X (I.N N_odd_else_stmt), _, I.X (I.T T_ELSE), _ -> begin
                              scanner#enter_block();
                              raise Exit
                          end
                          | _ -> ()
                        )
                    end;
                    iter_items_w ~from_ith:7 ~to_ith:8 menv_
                      (function
                        | sn, I.X (I.N N_pp_stmt_if_group), _, _, _ -> begin
                            ctx_start_of_stmt sn;
                            raise Exit
                        end
                        | _ -> ()
                      )
                end
            end
            | I.X (I.N N_pp_stmt_if_group_broken), _, I.X (I.T T_COMMA_BROKEN) -> begin
                match scanner#peek_rawtoken() with
                (*| PP_ELIF _ | PP_ELSE _ -> begin*)
                | x when Scanner.is_pp_elif_else_like env x -> begin
                    [%debug_log "!!! info=%s"
                      (Pinfo.pp_if_section_info_to_string env#pp_if_section_top_info)];
                    env#set_broken_info();
                    raise Exit
                end
                | _ -> ()
            end
            | I.X (I.N N_pp_class_head_if_group_broken), _, I.X (I.T T_CLASS_LBRACE) -> begin
                match scanner#peek_rawtoken() with
                (*| PP_ELIF _ | PP_ELSE _ -> begin*)
                | x when Scanner.is_pp_elif_else_like env x -> begin
                    [%debug_log "!!! info=%s"
                      (Pinfo.pp_if_section_info_to_string env#pp_if_section_top_info)];
                    env#set_broken_info();
                    raise Exit
                end
                | _ -> ()
            end
            | I.X (I.N N_pp_minit_if_group), _, I.X (I.T T_LBRACE) -> begin
                env#set_brace_opening_info();
                raise Exit
            end
            | I.X (I.N N_pp_minit_elif_group), _, I.X (I.T T_LBRACE) -> begin
                env#set_brace_opening_info();
                raise Exit
            end
            | I.X (I.N N_pp_minit_else_group), _, I.X (I.T T_LBRACE) -> begin
                env#set_brace_opening_info();
                raise Exit
            end

            | I.X (I.N N_pp_minit_if_group), _, I.X (I.T T_RBRACE) -> begin
                env#clear_brace_opening_info();
                raise Exit
            end
            | I.X (I.N N_pp_minit_elif_group), _, I.X (I.T T_RBRACE) -> begin
                env#clear_brace_opening_info();
                raise Exit
            end
            | I.X (I.N N_pp_minit_else_group), _, I.X (I.T T_RBRACE) -> begin
                env#clear_brace_opening_info();
                raise Exit
            end

            | I.X (I.N N_conditional_expression), _, I.X (I.T T_QUEST) -> begin
                match scanner#peek_rawtoken() with
                | IDENT _ -> begin
                    match scanner#peek_nth_rawtoken 2 with
                    | COLON_COLON ->
                        env#set_expr_flag();
                        raise Exit
                    | _ -> ()
                end
                | _ -> ()
            end
            (*| I.X (I.N N_conditional_expression), _, I.X (I.T T_QUEST) -> begin
                scanner#ctx_expr();
                scanner#ctx_ini();
                raise Exit
            end*)
            | I.X (I.N N_conditional_expression), _, I.X (I.T T_COLON) -> begin
                match scanner#peek_rawtoken() with
                | IDENT _ -> begin
                    match scanner#peek_nth_rawtoken 2 with
                    | COLON_COLON ->
                        env#set_expr_flag();
                        raise Exit
                    | _ -> ()
                end
                | _ -> ()
            end
            | I.X (I.N N_explicit_instantiation), _, I.X (I.T T_TEMPLATE) -> begin
                env#set_templ_flag();
                raise Exit
            end
            (*| I.X (I.N N_pp_decl_elif_group), _, I.X (I.T T_LBRACE) -> begin
                env#pstat#close_brace();
                raise Exit
            end
            | I.X (I.N N_pp_decl_else_group), _, I.X (I.T T_LBRACE) -> begin
                env#pstat#close_brace();
                raise Exit
            end*)
            (*| I.X (I.N N_simple_type_specifier), _, x -> begin
                begin
                  match x with
                  | I.X (I.T T_CHAR) | I.X (I.T T_CHAR8_T) | I.X (I.T T_CHAR16_T)
                  | I.X (I.T T_CHAR32_T) | I.X (I.T T_WCHAR_T) | I.X (I.T T_BOOL)
                  | I.X (I.T T_SHORT) | I.X (I.T T_INT) | I.X (I.T T_LONG)
                  | I.X (I.T T_SIGNED) | I.X (I.T T_UNSIGNED)
                  | I.X (I.T T_FLOAT) | I.X (I.T T_DOUBLE) | I.X (I.T T_VOID) -> scanner#ctx_end_of_ty_spec()
                  | _ -> ()
                end;
                raise Exit
            end*)
            | _ -> ()
          in (* let _proc_shift4 *)

          let proc_shift x =
            _proc_shift0 x;
            _proc_shift1 x;
            _proc_shift2 x;
            _proc_shift3 x;
            _proc_shift4 x
          in

          let proc_shift_objc (_, l, rs, r, _) =
            match l, rs, r with
            | I.X (I.N N_objc_protocol_ref_list), I.X (I.T T_LT)::_, I.X (I.T T_LT) -> begin
                env#set_objc_protocol_ref_flag();
                raise Exit
            end
            | I.X (I.N N_objc_protocol_ref_list), I.X (I.T T_LT)::_, I.X (I.T T_GT) -> begin
                env#clear_objc_protocol_ref_flag();
                env#set_end_of_objc_protocol_ref_list_flag();
                raise Exit
            end
            | I.X (I.N N_pp_objc_protocol_ref_list_if_section), _, I.X (I.T T_LT) -> begin
                env#set_objc_protocol_ref_flag();
                scanner#ctx_top();
                scanner#ctx_ini();
                raise Exit
            end
            | I.X (I.N N_pp_objc_protocol_ref_list_if_section), _, I.X (I.T T_GT) -> begin
                env#clear_objc_protocol_ref_flag();
                raise Exit
            end
            | I.X (I.N N_objc_class_decl_list), _, I.X (I.T T_OBJC_CLASS) -> begin
                env#set_objc_class_flag();
                raise Exit
            end
            | I.X (I.N N_objc_class_decl_list), _, I.X (I.T T_SEMICOLON) -> begin
                env#clear_objc_class_flag();
                raise Exit
            end
            | I.X (I.N N_objc_class_interface), _, I.X (I.T T_OBJC_INTERFACE) -> begin
                env#set_objc_class_interface_flag();
                raise Exit
            end
            | I.X (I.N N_objc_class_interface), _, I.X (I.T T_OBJC_END) -> begin
                env#clear_objc_class_interface_flag();
                raise Exit
            end
            | I.X (I.N N_objc_category_interface), _, I.X (I.T T_OBJC_INTERFACE) -> begin
                env#set_objc_class_interface_flag();
                raise Exit
            end
            | I.X (I.N N_objc_category_interface), _, I.X (I.T T_RPAREN) -> begin
                env#set_objc_cat_flag();
                raise Exit
            end
            | I.X (I.N N_objc_category_interface), _, I.X (I.T T_OBJC_END) -> begin
                env#clear_objc_class_interface_flag();
                raise Exit
            end
            | I.X (I.N N_objc_protocol_decl), _, I.X (I.T T_OBJC_PROTOCOL) -> begin
                env#set_objc_protocol_decl_flag();
                raise Exit
            end
            | I.X (I.N N_objc_protocol_decl), _, I.X (I.T T_OBJC_END) -> begin
                env#clear_objc_protocol_decl_flag();
                raise Exit
            end
            | I.X (I.N N_objc_protocol_decl_list), _, I.X (I.T T_SEMICOLON) -> begin
                env#clear_objc_protocol_decl_flag();
                raise Exit
            end
            | I.X (I.N N_objc_message_expr), _, I.X (I.T T_OBJC_LBRACKET) -> begin
                if scanner#peek_rawtoken() != RBRACKET then
                  env#enter_objc_message_expr();
                raise Exit
            end
            | I.X (I.N N_objc_message_expr), _, I.X (I.T T_RBRACKET) -> begin
                env#exit_objc_message_expr();
                raise Exit
            end
            | I.X (I.N N_statement), _, I.X (I.T T_OBJC_AUTORELEASEPOOL) -> begin
                env#set_objc_block_flag();
                raise Exit
            end
            | I.X (I.N N_statement), _, I.X (I.T T_OBJC_TRY) -> begin
                env#set_objc_block_flag();
                raise Exit
            end
            | I.X (I.N N_statement), _, I.X (I.T T_OBJC_FINALLY) -> begin
                env#set_objc_block_flag();
                raise Exit
            end
            | I.X (I.N N_statement), _, I.X (I.N N_compound_statement) -> begin
                env#clear_objc_block_flag();
                raise Exit
            end
            | I.X (I.N N_objc_property_attrs_decl), _, I.X (I.T T_RPAREN) -> begin
                scanner#ctx_top();
                scanner#ctx_ini();
                env#set_end_of_objc_property_attrs_decl_flag();
                raise Exit
            end
            | I.X (I.N N_objc_method_decl), _, x when begin
                match x with
                | I.X (I.T T_OBJC_PLUS) | I.X (I.T T_OBJC_MINUS) -> true
                | _ -> false
            end -> begin
                env#set_objc_meth_decl_flag();
                raise Exit
            end
            | I.X (I.N N_objc_method_selector), _, I.X (I.T T_ELLIPSIS) -> begin
                env#set_end_of_objc_meth_sel_flag();
                raise Exit
            end
            | I.X (I.N N_objc_method_type), _, I.X (I.T T_RPAREN) -> begin
                env#set_end_of_objc_meth_type_flag();
                raise Exit
            end
            | I.X (I.N N_objc_catch_clause), _, I.X (I.T T_RPAREN) -> begin
                let sn = I.current_state_number menv_ in
                ctx_start_of_stmt sn;
                raise Exit
            end
            | I.X (I.N N_objc_selector), _, I.X (I.T T_IDENT_V) -> begin
                env#set_objc_sel_flag();
                env#set_objc_meth_sel_flag();
                raise Exit
            end
            | I.X (I.N N_objc_selector), _, I.X (I.T T_IDENT) -> begin
                env#set_objc_sel_flag();
                env#set_objc_meth_sel_flag();
                raise Exit
            end
            | I.X (I.N N_objc_keyword_dtor), _, I.X (I.T T_IDENT_V) -> begin
                env#set_objc_sel_flag();
                env#set_objc_meth_sel_flag();
                raise Exit
            end
            | I.X (I.N N_objc_keyword_dtor), _, I.X (I.T T_IDENT) -> begin
                env#set_objc_sel_flag();
                env#set_objc_meth_sel_flag();
                raise Exit
            end
            | I.X (I.N N_objc_superclass), _, I.X (I.T T_COLON) -> begin
                env#set_objc_superclass_flag();
                raise Exit
            end
            | _ -> ()
          in

          begin
            try
              iter_items menv_ proc_shift;
              iter_items menv_ proc_shift_objc
            with
              Exit -> ()
          end;
          let ckpt = I.resume ckpt in
          loop ckpt
      end
      | I.AboutToReduce (_menv, prod) -> begin
          [%debug_log "\n%a" (pr_menv "reduce" 0) _menv];
          begin
            let lhs = I.lhs prod in
            let rhs = I.rhs prod in
            (*let rhsi_opt =
              match I.get 0 _menv with
              | Some (I.Element (stat, _, _, _)) -> Some (I.incoming_symbol stat)
              | _ -> None
            in*)
            [%debug_log "%s <- %s\n"
              (xsymbol_to_string lhs) (Xlist.to_string xsymbol_to_string " " rhs)];
            match lhs with
            | I.X (I.N N_requires_clause)        -> env#clear_requires_clause_flag()
            | I.X (I.N N_declarator)             -> scanner#ctx_end_of_dtor(); env#clear_class_name_flag()
            | I.X (I.N N_id_expression)          -> scanner#ctx_end_of_id_expr()
            | I.X (I.N N_new_expression)         -> env#clear_new_flag()
            | I.X (I.N N_type_specifier)         -> if not env#alignas_flag then scanner#ctx_end_of_ty_spec()
            (*| I.X (I.N N_defining_type_specifier) -> scanner#ctx_end_of_ty_spec()*)
            | I.X (I.N N_declaration_seq)        -> scanner#ctx_reset()
            | I.X (I.N N_member_declaration)     -> scanner#ctx_mem(); scanner#ctx_ini()
            | I.X (I.N N_conversion_function_id) -> env#clear_conv_func_id_flag()
            | I.X (I.N N_function_definition)    -> begin
                env#clear_in_body_brace_flag();
                env#clear_end_of_params_flag();
                env#clear_function_name()
            end
            | I.X (I.N N_declaration)            -> env#clear_in_body_brace_flag()
            | I.X (I.N N_template_declaration)   -> env#stack#exit_template()
            | I.X (I.N N__using_directive)       -> env#clear_using_ns_flag()
            | I.X (I.N N__asm_declaration)       -> env#exit_asm()
            (*| I.X (I.N N_enum_head)              -> env#exit_enum_head()*)
            | I.X (I.N N__lambda_expression)     -> env#clear_end_of_lambda_templ_flag()
            | I.X (I.N N_lambda_expression)      -> scanner#pop_context()
            | I.X (I.N N_lambda_declarator)      -> env#clear_lambda_dtor_flag();
            | I.X (I.N N_alignment_specifier)    -> env#exit_alignas()
            | I.X (I.N N_trailing_return_type)   -> env#clear_trailing_retty_flag()
            | I.X (I.N N_base_clause)            -> env#exit_base_clause()
            | I.X (I.N N_decl_spec_macro_call)   -> env#clear_end_of_decl_spec_macro_call_flag()
            | I.X (I.N N_ctor_initializer)       -> env#exit_ctor_init()
            (*| I.X (I.N N_statement)              -> env#clear_cast_key_flag()*)
            | I.X (I.N N_statement)              ->
                env#stack#set_popped_frame_scope_from_params_to_top()

            | I.X (I.N N_macro_arg) when
                try (List.nth rhs 0) = I.X (I.N N_cast_key) with _ -> false
                  -> env#clear_cast_key_flag()

            (*| I.X (I.N N_noptr_declarator) when
                try (List.nth rhs 1) = I.X (I.T T_PS_LPAREN) with _ -> false
                  -> env#clear_old_param_decl_flag()*)

            | I.X (I.N N_pp_dtor_if_group) -> begin
                env#clear_old_param_decl_flag();
                if env#pp_if_section_level > 0 && Xlist.last rhs = I.X (I.N N_function_body) then
                  env#set_semicolon_info()
            end
            | I.X (I.N N_pp_dtor_elif_group)     -> begin
                env#clear_old_param_decl_flag();
                if env#pp_if_section_level > 0 && Xlist.last rhs = I.X (I.N N_function_body) then
                  env#set_semicolon_info()
            end
            | I.X (I.N N_pp_dtor_else_group)     -> begin
                env#clear_old_param_decl_flag();
                if env#pp_if_section_level > 0 && Xlist.last rhs = I.X (I.N N_function_body) then
                  env#set_semicolon_info()
            end
            | I.X (I.N N_pp_minit_if_section)    -> begin
                scanner#ctx_mem_init();
                scanner#ctx_ini()
            end
            | I.X (I.N N_pp_decl_if_group_broken) -> begin
                if env#stack#in_class then
                  scanner#ctx_mem()
                else
                  scanner#ctx_top();
                scanner#ctx_ini()
            end
            | I.X (I.N N_pp_decl_elif_group_broken) -> begin
                if env#stack#in_class then
                  scanner#ctx_mem()
                else
                  scanner#ctx_top();
                scanner#ctx_ini()
            end
            | I.X (I.N N_pp_func_head_if_group_broken) -> begin
                if env#stack#in_class then
                  scanner#ctx_mem()
                else
                  scanner#ctx_top();
                scanner#ctx_ini()
            end
            | I.X (I.N N_pp_func_head_elif_group_broken) when begin
                let rt, _, _ = scanner#current_token in
                match rt with
                | PP_ENDIF _ -> false
                | _ -> true
            end -> begin
                if env#stack#in_class then
                  scanner#ctx_mem()
                else
                  scanner#ctx_top();
                scanner#ctx_ini()
            end
            | I.X (I.N N__pp_func_head_if_group) -> begin
                env#set_func_head_info()
            end
            (*| I.X (I.N N_macro_arg) when begin
                match rhs_list with
                | (I.X (I.T T_IDENT_V))::_ -> true
                | _::(I.X (I.T T_IDENT_V))::_ -> true
                | _ -> false
            end -> begin
              env#stack#exit_scope()
            end*)
            | I.X (I.N N_elaborated_type_specifier) -> begin
                if scanner#context = C.CLASS then
                  scanner#ctx_top();
            end
            | I.X (I.N N_typename_specifier) -> env#exit_typename()
            (*| I.X (I.N N_typename_specifier) -> begin
                iter_items _menv
                  (fun (_, l, r0, r) ->
                    match l, r0, r with
                    | I.X (I.N N_typename_specifier), _, I.X (I.N N_simple_template_id) ->
                        env#exit_typename()
                    | _ -> ()
                  )
            end
            | I.X (I.N N_type_parameter) -> begin
                iter_items _menv
                  (fun (_, l, r0, r) ->
                    match l, r0, r with
                    | I.X (I.N N_typename_specifier), _, I.X (I.T T_TYPENAME) ->
                        env#exit_typename()
                    | I.X (I.N N_type_parameter), I.X (I.T T_TYPENAME), I.X (I.T T_ELLIPSIS) ->
                        env#exit_typename()
                    | _ -> ()
                  )
            end*)
            | I.X (I.N N_type_parameter) -> begin
                env#exit_ty_param();
                env#clear_ty_param_rhs_flag();
                iter_items _menv
                  (fun (_, l, rs, r, _) ->
                    match l, rs, r with
                    | I.X (I.N N_type_parameter), I.X (I.T T_TYPENAME)::_, _ ->
                        env#exit_typename()
                    | _ -> ()
                  )
            end
            | I.X (I.N N_pp_ifstmt_if_group_closing) -> begin
                match List.rev rhs with
                | (I.X (I.N N_pp_ifstmt_if_section_closing))::_ -> env#set_paren_closing_info()
                | _ -> ()
            end
            | I.X (I.N N_pp_func_body_if_group) -> begin
                match List.rev rhs with
                | (I.X (I.N N_odd_decl))::_ -> env#set_pp_func_body_odd_flag()
                | _ -> ()
            end
            | I.X (I.N N_pp_func_body_if_section) -> env#clear_pp_func_body_odd_flag()
            | I.X (I.N N_brace_or_equal_initializer) -> begin
                env#clear_init_flag();
                env#clear_eq_init_flag();
            end
            | I.X (I.N N_initializer_clause) -> env#clear_init_flag()
            | I.X (I.N N_objc_method_selector) -> begin
                env#clear_end_of_objc_meth_sel_flag();
                env#clear_objc_meth_sel_flag();
            end
            | I.X (I.N N_objc_selector) -> env#clear_objc_sel_flag()
            | I.X (I.N N_objc_keyword_dtor) -> env#clear_objc_sel_flag()
            | I.X (I.N N_objc_method_decl) -> begin
                env#clear_objc_sel_flag();
                env#clear_end_of_objc_meth_sel_flag();
                env#clear_objc_meth_decl_flag()
            end
            | I.X (I.N N_pp_str_if_section) -> env#clear_end_of_str_section_flag()
            | I.X (I.N N_objc_method_type) -> env#clear_end_of_objc_meth_type_flag()
            | I.X (I.N N_objc_property_attrs_decl) -> env#clear_end_of_objc_property_attrs_decl_flag()
            | I.X (I.N N_objc_interface_decl) -> scanner#ctx_ini()
            | I.X (I.N N_objc_superclass) -> env#clear_objc_superclass_flag()
            | I.X (I.N N_objc_protocol_ref_list) -> env#clear_end_of_objc_protocol_ref_list_flag();
            | I.X (I.N N_attribute_argument_clause) -> env#clear_attr_flag()
            | I.X (I.N N_gnu_attribute) -> env#clear_attr_flag()
            | I.X (I.N N_restricted_postfix_expr) -> env#clear_mem_acc_flag()
            | I.X (I.N N_class_name) -> env#clear_class_name_flag()
            | I.X (I.N N_requirement_parameter_list) -> env#clear_end_of_req_params_flag()
            | I.X (I.N N_braced_init_list) when
                Xlist.last rhs = I.X (I.N N_pp_init_if_section_closing)
              -> env#exit_braced_init()

            | I.X (I.N N_pp_expr_if_section_broken)
            | I.X (I.N N_pp_expr_if_section_broken2)
            | I.X (I.N N_pp_stmt_if_section_broken)
            | I.X (I.N N_pp_decl_if_section_broken)
            | I.X (I.N N_pp_mdecl_if_section_broken)
            | I.X (I.N N_pp_class_head_if_section_broken)
            | I.X (I.N N_pp_dtor_if_section_broken)
            | I.X (I.N N_pp_func_head_if_section_broken)
            | I.X (I.N N_pp_handler_if_section_broken)
            | I.X (I.N N_pp_lambda_head_if_section_broken)
            | I.X (I.N N_pp_minit_if_section_broken)
            | I.X (I.N N_pp_aexpr_if_section_closing)
            | I.X (I.N N_pp_args_if_section_closing)
            | I.X (I.N N_pp_enum_if_section_closing)
            | I.X (I.N N_pp_ifstmt_if_section_closing)
            | I.X (I.N N_pp_init_if_section_closing)
            | I.X (I.N N_pp_stmt_if_section_closing)
            | I.X (I.N N_pp_args_if_section_close_open)
            | I.X (I.N N_pp_stmt_if_section_close_open)
              when scanner#dump_stats_flag
              -> scanner#incr_count "broken pp-branch"

            | _ -> ()
          end;
          let ckpt = I.resume ckpt in
          loop ckpt
      end
      | I.HandlingError _menv -> begin
          [%debug_log "!!! Syntax error"];
          if scanner#keep_flag then begin
            scanner#stop_replay_queue();
            scanner#restore_context();
            scanner#restore_state();
            if dump_tokens_flag then begin
              token_seq#clear_sub();
              (*token_seq#clear_macro()*)
            end;
            let menv =
              match !menv_backup_obj with
              | Some x -> rollback x scanner#state_number
              | None -> assert false
            in
            let ckpt = I.input_needed menv in
            loop ckpt
          end
          else if scanner#has_alternative_tokens then begin
            scanner#setup_replay();
            scanner#restore_context();
            scanner#restore_state();
            if dump_tokens_flag then begin
              token_seq#clear_sub();
              (*token_seq#clear_macro()*)
            end;
            let menv =
              match !menv_backup_obj with
              | Some x -> rollback x scanner#state_number
              | None -> assert false
            in
            let ckpt = I.input_needed menv in
            loop ckpt
          end
          else begin
            raise (Failed_to_parse (lexpos_of_menv _menv))
          end
      end
      | I.Accepted v -> begin
          (*fprintf stderr "Accepted.\n";*)
          begin
            match mode with
            | M_DECLS_SUB s | M_MEM_DECLS_SUB s | M_STMTS_SUB s | M_EXPR_SUB s
            | M_INIT_SUB s | M_TYPE_SUB s | M_SPECS_SUB s | M_DTORS_SUB s | M_ETORS_SUB s
            | M_OBJC_DECLS_SUB s when env#verbose_flag ->
                printf "  macro parsed: %s\n" s
            | _ when env#verbose_flag -> printf "PARSED: %s\n" (Common.relpath env#current_filename)
            | _ -> ()
          end;
          if token_hist_flag then
            scanner#show_token_hist();
          v
      end
      | I.Rejected -> assert false
    in (* let rec loop *)
    let do_parse () =
      let ini_pos =
        { Lexing.pos_fname = env#current_filename;
          Lexing.pos_lnum  = 1;
          Lexing.pos_bol   = 0;
          Lexing.pos_cnum  = 0
        }
      in
      let ini_ckpt =
        match mode with
        | M_NORMAL -> P.Incremental.main ini_pos
        | M_STMTS -> begin
            scanner#ctx_stmt();
            scanner#ctx_ini();
            P.Incremental.stmts_sub ini_pos
        end
        | _ -> assert false
      in
      let root = loop ini_ckpt in

      if parse_macro_defs_flag then begin

        let queue_tokens params feed =
          let prev_rawtok = ref T.EOF in
          let prev_rawtok2 = ref T.EOF in
          let prev_rawtok3 = ref T.EOF in
          let prev_rawtok4 = ref T.EOF in
          let rawtok2_opt_opt = ref None in
          let conv_tbl = Hashtbl.create 0 in

          let conv_token params (tok : token) (tok2_opt : token option) =
            let proc s rt =
              Hashtbl.replace conv_tbl s rt;
              rt
            in
            let get_rawtok2_opt () =
              match !rawtok2_opt_opt with
              | Some x -> x
              | None -> begin
                  match tok2_opt with
                  | Some tok2 -> begin
                      match tok2 with
                      | rt2, _, _ -> begin
                          let rt_opt = Some rt2 in
                          rawtok2_opt_opt := Some rt_opt;
                          rt_opt
                      end
                  end
                  | None -> begin
                      rawtok2_opt_opt := None;
                      None
                  end
              end
            in
            let conv_rt mk_default_rt s =
              try
                Hashtbl.find conv_tbl s
              with
                Not_found -> begin
                  match !prev_rawtok with
                  | OPERATOR when begin
                      match get_rawtok2_opt() with
                      | Some (PTR_STAR|PTR_AMP|PTR_AMP_AMP) -> false
                      | _ -> true
                  end -> [%debug_log "@"]; proc s (T.OP_MACRO s)
                  | RPAREN -> begin
                      match !prev_rawtok2 with
                      | IDENT _ -> begin
                          match !prev_rawtok3 with
                          | PTR_STAR | PTR_AMP | PTR_AMP_AMP -> begin
                              let _s = String.lowercase_ascii s in
                              match !prev_rawtok4 with
                              | TY_LPAREN when
                                  _s <> "op" && _s <> "__op"(*begin
                                  match get_rawtok2_opt() with
                                  | Some (IDENT _) -> false
                                  | _ -> true
                              end*) -> [%debug_log "@"]; proc s (T.PARAMS_MACRO s)
                              | _ -> mk_default_rt s
                          end
                          | _ -> mk_default_rt s
                      end
                      | TY_LPAREN -> begin
                          match !prev_rawtok3 with
                          | IDENT _ -> begin
                              match !prev_rawtok4 with
                              | DOT | MINUS_GT -> [%debug_log "@"]; proc s (T.OP_MACRO s)
                              | _ -> mk_default_rt s
                          end
                          | _ -> mk_default_rt s
                      end
                      | _ -> mk_default_rt s
                  end
                  | IDENT _ when begin
                      match !prev_rawtok2 with
                      | NEW -> true
                      | _ -> false
                  end -> [%debug_log "@"]; proc s (T.NEW_INIT_MACRO s)
                  | IDENT _ when begin
                      match get_rawtok2_opt() with
                      | Some DOT when begin
                          match !prev_rawtok2 with
                          | MS_ASM _ -> true
                          | _ -> false
                      end -> false
                      | Some DOT -> true
                      | _ -> false
                  end -> [%debug_log "@"]; proc s (T.ARGS_MACRO s)
                  | _ -> mk_default_rt s
                end
            in
            let rawtok =
              match tok with
              | rt, _, _ -> begin
                  let rt =
                    match rt with
                    | CONST | CLASS | RETURN | TYPENAME | TEMPLATE -> begin
                        let s = Token.rawtoken_to_repr rt in
                        if List.mem s params then
                          conv_rt (fun x -> T.IDENT x) s
                        else
                          rt
                    end
                    | IDENT s when List.mem s params -> conv_rt (fun _ -> rt) s
                    | _ -> rt
                  in
                  prev_rawtok4 := !prev_rawtok3;
                  prev_rawtok3 := !prev_rawtok2;
                  prev_rawtok2 := !prev_rawtok;
                  prev_rawtok := rt;
                  rt
              end
            in
            let _, sp, ep = tok in
            rawtok, sp, ep
          in
          let rec doit = function
            | h::(h2::_ as t) -> begin
                feed (conv_token params h (Some h2));
                doit t
            end
            | h::[] -> feed (conv_token params h None)
            | [] -> ()
          in
          doit
        in (* let queue_tokens *)
        env#iter_pending_macro
          (fun name (pnd, macro_kind, tok_list_obj) ->
            [%debug_log "pending_macro (%s): %s"
              (match macro_kind with
              | ObjectLike -> "object-like"
              | FunctionLike _ -> "function-like"
              | MK_DUMMY -> "DUMMY"
              ) name];

            if macro_kind == MK_DUMMY then begin
              if env#dump_tokens_flag then
                token_seq#reg_dummy_macro name
            end
            else

            let params =
              match macro_kind with
              | FunctionLike {L.fm_params=il;_} -> il
              | ObjectLike -> []
              | _ -> assert false
            in
            let setup_macro_node nd =
              let mnd =
                let lab =
                  match macro_kind with
                  | ObjectLike -> L.ObjectLikeMacro
                  | FunctionLike _ -> L.FunctionLikeMacro macro_kind
                  | _ -> assert false
                in
                let children =
                  match nd#label with
                  | L.STMTS -> begin
                      match nd#children with
                      | [_] -> nd#children
                      | _ -> [nd]
                  end
                  | _ -> [nd]
                in
                new Ast.node ~lloc:(nd#lloc) ~children lab
              in
              pnd#set_children [mnd]
            in

            let tok_list = (Obj.obj tok_list_obj : token list) in

            let q0 = new Xqueue.c in
            let _ = queue_tokens params q0#add tok_list in
            let setup_scanner () =
              env#stack#reset();
              let frm = new Pinfo.Name.stack_frame Pinfo.Name.Scope.Top in
              env#stack#push frm;
              env#set_top_frame frm;
              scanner#reset();
              scanner#set_macro_body_parsing_flag();
              scanner#clear_check_top_stmts_flag();
              List.iter (fun i -> env#register_macro_obj (Ast.mk_macro_id i) Ast.dummy_node) params;
              let has_pp_flag = ref false in
              if
                Scanner.is_params_body_macro name ||
                Scanner.is_params_body_macro_ident name
              then begin
                match q0#peek with
                | TY_LPAREN, s, _ -> scanner#queue_token (DUMMY_DTOR, s, s)
                | _ -> ()
              end;
              let last_lexpos = ref Lexing.dummy_pos in
              q0#iter
                (fun ((rt, _, ep) as t) ->
                  last_lexpos := ep;
                  begin
                    match rt with
                    | PP_ERROR | PP_INCLUDE
                      -> has_pp_flag := true
                    | _ -> ()
                  end;
                  scanner#queue_token t);
              [%debug_log "has_pp_flag=%B" !has_pp_flag];
              if !has_pp_flag then
                scanner#queue_token (NEWLINE, !last_lexpos, !last_lexpos);
              scanner#queue_token (EOF, !last_lexpos, !last_lexpos);
              !last_lexpos
            in
            let enter_macro =
              if dump_tokens_flag then
                fun name mode ->
                  token_seq#clear_sub();
                  token_seq#enter_macro name mode
              else
                fun _ _ -> ()
            in
            let exit_macro =
              if dump_tokens_flag then
                fun () -> token_seq#exit_macro()
              else
                fun () -> ()
            in
            try
              [%debug_log "parsing %s with decls_sub" name];
              mode <- M_DECLS_SUB name;
              scanner#set_mode mode;
              let _ = setup_scanner() in
              scanner#ctx_top();
              scanner#ctx_ini();
              enter_macro name mode;
              let ckpt = P.Incremental.decls_sub ini_pos in
              let nd = loop ckpt in
              exit_macro();
              setup_macro_node nd
            with
              Failed_to_parse _ ->
                try
                  (*match tok_list with
                  | ((PUBLIC | PROTECTED | PRIVATE), _, _)::_ -> begin*)
                      [%debug_log "parsing %s with mem_decls_sub" name];
                      mode <- M_MEM_DECLS_SUB name;
                      scanner#set_mode mode;
                      let _ = setup_scanner() in
                      scanner#ctx_mem();
                      scanner#ctx_ini();
                      enter_macro name mode;
                      let ckpt = P.Incremental.mem_decls_sub ini_pos in
                      let nd = loop ckpt in
                      exit_macro();
                      setup_macro_node nd
                  (*end
                  | _ -> raise (Failed_to_parse pos)*)
                with
                  Failed_to_parse _ ->
                try
                  [%debug_log "parsing %s with stmts_sub" name];
                  mode <- M_STMTS_SUB name;
                  scanner#set_mode mode;
                  let last_lexpos = setup_scanner() in
                  scanner#prepend_token (SEMICOLON false, last_lexpos, last_lexpos);
                  scanner#ctx_stmt();
                  scanner#ctx_ini();
                  enter_macro name mode;
                  let ckpt = P.Incremental.stmts_sub ini_pos in
                  let nd = loop ckpt in
                  exit_macro();
                  setup_macro_node nd
                with
                  Failed_to_parse pos ->

                    try
                      [%debug_log "parsing %s with expr_sub" name];
                      mode <- M_EXPR_SUB name;
                      scanner#set_mode mode;
                      let _ = setup_scanner() in
                      scanner#ctx_expr();
                      scanner#ctx_ini();
                      enter_macro name mode;
                      let ckpt = P.Incremental.expr_sub ini_pos in
                      let nd = loop ckpt in
                      exit_macro();
                      setup_macro_node nd
                    with
                      Failed_to_parse _ ->

                    try
                      [%debug_log "parsing %s with init_sub" name];
                      mode <- M_INIT_SUB name;
                      scanner#set_mode mode;
                      let _ = setup_scanner() in
                      scanner#ctx_mem_init();
                      scanner#ctx_ini();
                      enter_macro name mode;
                      let ckpt = P.Incremental.init_sub ini_pos in
                      let nd = loop ckpt in
                      exit_macro();
                      setup_macro_node nd
                    with
                      Failed_to_parse _ ->
                        try
                          [%debug_log "parsing %s with type_sub" name];
                          mode <- M_TYPE_SUB name;
                          scanner#set_mode mode;
                          let _ = setup_scanner() in
                          scanner#ctx_top();
                          scanner#ctx_ini();
                          enter_macro name mode;
                          let ckpt = P.Incremental.type_sub ini_pos in
                          let nd = loop ckpt in
                          exit_macro();
                          setup_macro_node nd
                        with
                          Failed_to_parse _ ->
                            try
                              [%debug_log "parsing %s with specs_sub" name];
                              mode <- M_SPECS_SUB name;
                              scanner#set_mode mode;
                              let _ = setup_scanner() in
                              scanner#ctx_top();
                              scanner#ctx_ini();
                              enter_macro name mode;
                              (*scanner#ctx_end_of_dtor();*)
                              let ckpt = P.Incremental.specs_sub ini_pos in
                              let nd = loop ckpt in
                              exit_macro();
                              setup_macro_node nd
                            with
                              Failed_to_parse _ ->
                                try
                                  [%debug_log "parsing %s with dtors_sub" name];
                                  mode <- M_DTORS_SUB name;
                                  scanner#set_mode mode;
                                  let _ = setup_scanner() in
                                  scanner#ctx_mem_init();
                                  scanner#ctx_ini();
                                  enter_macro name mode;
                                  (*scanner#ctx_end_of_dtor();*)
                                  let ckpt = P.Incremental.dtors_sub ini_pos in
                                  let nd = loop ckpt in
                                  exit_macro();
                                  setup_macro_node nd
                                with
                                  Failed_to_parse _ ->
                                    try
                                      [%debug_log "parsing %s with etors_sub" name];
                                      mode <- M_ETORS_SUB name;
                                      scanner#set_mode mode;
                                      let _ = setup_scanner() in
                                      scanner#ctx_enum();
                                      scanner#ctx_ini();
                                      enter_macro name mode;
                                      let ckpt = P.Incremental.etors_sub ini_pos in
                                      let nd = loop ckpt in
                                      exit_macro();
                                      setup_macro_node nd
                                    with
                                      Failed_to_parse _ ->
                                        try
                                          [%debug_log "parsing %s with objc_decls_sub" name];
                                          mode <- M_OBJC_DECLS_SUB name;
                                          scanner#set_mode mode;
                                          let _ = setup_scanner() in
                                          scanner#ctx_mem();
                                          scanner#ctx_ini();
                                          env#set_objc_class_interface_flag();
                                          enter_macro name mode;
                                          let ckpt = P.Incremental.objc_decls_sub ini_pos in
                                          let nd = loop ckpt in
                                          exit_macro();
                                          setup_macro_node nd
                                        with
                                        | Failed_to_parse _ when dump_tokens_flag -> ()
                                        | Failed_to_parse _ -> begin
                                            [%debug_log "all attempts failed for %s" name];
                                            Xprint.warning "all attempts failed for %s" name;
                                            raise (Failed_to_parse pos)
                                        end
          )
      end;
      new Ast.c root
    in (* let do_parse *)

    let get_line src ln =
      if ln <= 0 then
        ""
      else begin
        let ic = src#get_channel in
        let count = ref 0 in
        let res = ref "" in
        try
          while true do
            incr count;
            let line = ic#input_line() in
            if !count >= ln then begin
              res := line;
              raise Exit
            end
          done;
          ""
        with
        | End_of_file | Exit ->
            ic#close();
            !res
      end
    in

    _parse <- fun () ->
      try
        let ast = do_parse() in
        if dump_tokens_flag then
          token_seq#dump (env#current_source#file#fullpath^".tkns");
        if dump_stats_flag then
          scanner#dump_stats();
        ast
      with
        Failed_to_parse pos ->
          let src = env#current_source in
          let ln = pos.Lexing.pos_lnum in
          let line = ref "" in
          let l0 = get_line src (ln-1) in
          if l0 <> "" then
            line := "   "^l0;
          let l1 = get_line src ln in
          if l1 <> "" then
            line := !line^"\n=> "^l1;
          let l2 = get_line src (ln+1) in
          if l2 <> "" then
            line := !line^"\n   "^l2;
          let mes =
            sprintf "failed to parse \"%s\" (%s)\n%s"
              (Common.relpath env#current_filename)
              (Astloc.lexpos_to_string pos)
              !line
          in
          raise (PB.Parse_error("", mes))

end (* Lib.parser_c *)
]
