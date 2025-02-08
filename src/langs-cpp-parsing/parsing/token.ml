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
module Position = Langs_common.Position

open Tokens_
open Printf

module PB = Parserlib_base

type t = T.token PB.token


let rawtoken_to_string = function
  | PMODE m              -> "PMODE:"^(Parser_aux.parsing_mode_to_string m)
  | EOF                  -> "EOF"
  | NEWLINE              -> "NEWLINE"
  (*| STMT_MARKER          -> "STMT_MARKER"*)
  | BRACE_PAREN_MARKER   -> "BRACE_PAREN_MARKER"
  | SUFFIX_MARKER        -> "SUFFIX_MARKER"
  | STR_MARKER           -> "STR_MARKER"
  | COND_MARKER          -> "COND_MARKER"
  | LAM_MARKER           -> "LAM_MARKER"
  | SECTION_MARKER       -> "SECTION_MARKER"
  | PP_MARKER            -> "PP_MARKER"
  | MOCK_MARKER          -> "MOCK_MARKER"
  | MARKER               -> "MARKER"
  | DUMMY_STMT           -> "DUMMY_STMT"
  | DUMMY_EXPR           -> "DUMMY_EXPR"
  | DUMMY_OP             -> "DUMMY_OP"
  | DUMMY_BODY           -> "DUMMY_BODY"
  | DUMMY_DTOR           -> "DUMMY_DTOR"
  | DUMMY_TYPE           -> "DUMMY_TYPE"
  | BRACE_LEVEL(lv, b)   -> sprintf "BRACE_LEVEL(%d,%B)" lv b
  | BEGIN_STMTS          -> "BEGIN_STMTS"
  | END_STMTS            -> "END_STMTS"
  | BEGIN_ETORS          -> "BEGIN_ETORS"
  | END_ETORS            -> "END_ETORS"
  | BEGIN_QPROP          -> "BEGIN_QPROP"
  | END_QPROP            -> "END_QPROP"
  | ASM_SHADER           -> "ASM_SHADER"

  | GT_7 b                -> sprintf "GT_7:%B" !b
  | CONFLICT_MARKER(b, s) -> sprintf "CONFLICT_MARKER:%B:%s" !b s

  | STR_MACRO s          -> sprintf "STR_MACRO:%s" s
  | INT_MACRO s          -> sprintf "INT_MACRO:%s" s
  | DECL_MACRO s         -> sprintf "DECL_MACRO:%s" s
  | PRAGMA_MACRO s       -> sprintf "PRAGMA_MACRO:%s" s
  | STMT_MACRO s         -> sprintf "STMT_MACRO:%s" s
  | VIRT_SPEC_MACRO s    -> sprintf "VIRT_SPEC_MACRO:%s" s
  | OP_MACRO s           -> sprintf "OP_MACRO:%s" s
  | PARAM_DECL_MACRO s   -> sprintf "PARAM_DECL_MACRO:%s" s
  | PARAMS_MACRO s       -> sprintf "PARAMS_MACRO:%s" s
  | PARAMS_BODY_MACRO s  -> sprintf "PARAMS_BODY_MACRO:%s" s
  | ARG_MACRO s          -> sprintf "ARG_MACRO:%s" s
  | ARGS_MACRO s         -> sprintf "ARGS_MACRO:%s" s
  | NEW_INIT_MACRO s     -> sprintf "NEW_INIT_MACRO:%s" s
  | ATTR_MACRO s         -> sprintf "ATTR_MACRO:%s" s
  | ACC_SPEC_MACRO s     -> sprintf "ACC_SPEC_MACRO:%s" s
  | DECL_SPEC_MACRO s    -> sprintf "DECL_SPEC_MACRO:%s" s
  | CC_MACRO s           -> sprintf "CC_MACRO:%s" s
  | LAM_MACRO s          -> sprintf "LAM_MACRO:%s" s
  | CV_MACRO s           -> sprintf "CV_MACRO:%s" s
  | REF_MACRO s          -> sprintf "REF_MACRO:%s" s
  | NOEXCEPT_MACRO s     -> sprintf "NOEXCEPT_MACRO:%s" s
  | NS_MACRO s           -> sprintf "NS_MACRO:%s" s
  | EMPTY_MACRO s        -> sprintf "EMPTY_MACRO:%s" s
  | DELIM_MACRO s        -> sprintf "DELIM_MACRO:%s" s
  | BLOCK_HEAD_MACRO s   -> sprintf "BLOCK_HEAD_MACRO:%s" s
  | BLOCK_END_MACRO s    -> sprintf "BLOCK_END_MACRO:%s" s
  | TYPE_MACRO s         -> sprintf "TYPE_MACRO:%s" s
  | BASE_MACRO s         -> sprintf "BASE_MACRO:%s" s
  | BASE_SPEC_MACRO s    -> sprintf "BASE_SPEC_MACRO:%s" s
  | SUFFIX_MACRO s       -> sprintf "SUFFIX_MACRO:%s" s
  | PTR_MACRO s          -> sprintf "PTR_MACRO:%s" s
  | BODY_MACRO s         -> sprintf "BODY_MACRO:%s" s
  | DTOR_MACRO s         -> sprintf "DTOR_MACRO:%s" s
  | PTR_DTOR_MACRO s     -> sprintf "PTR_DTOR_MACRO:%s" s
  | CLASS_HEAD_MACRO s   -> sprintf "CLASS_HEAD_MACRO:%s" s
  | FUNC_HEAD_MACRO s    -> sprintf "FUNC_HEAD_MACRO:%s" s
  | CAST_HEAD_MACRO s    -> sprintf "CAST_HEAD_MACRO:%s" s
  | OBJC_PROTOCOL_REF_LIST_MACRO s -> sprintf "OBJC_PROTOCOL_REF_LIST_MACRO:%s" s
  | OBJC_SEL_MACRO s     -> sprintf "OBJC_SEL_MACRO:%s" s
  | CLASS_BODY_HEAD_MACRO s -> sprintf "CLASS_BODY_HEAD_MACRO:%s" s
  | CLASS_BODY_END_MACRO s  -> sprintf "CLASS_BODY_END_MACRO:%s" s

  | IDENT s               -> sprintf "IDENT:%s" s
  | IDENT_ s              -> sprintf "IDENT_:%s" s
  | IDENT_V s             -> sprintf "IDENT_V:%s" s
  | IDENT_B s             -> sprintf "IDENT_B:%s" s
  | IDENT_C s             -> sprintf "IDENT_C:%s" s
  | IDENT_E s             -> sprintf "IDENT_E:%s" s
  | IDENT_BM s            -> sprintf "IDENT_BM:%s" s
  | IDENT_DM s            -> sprintf "IDENT_DM:%s" s
  | IDENT_EM s            -> sprintf "IDENT_EM:%s" s
  | IDENT_SM s            -> sprintf "IDENT_SM:%s" s
  | IDENT_TM s            -> sprintf "IDENT_TM:%s" s
  | IDENT_IM s            -> sprintf "IDENT_IM:%s" s
  | IDENT_PM s            -> sprintf "IDENT_PM:%s" s
  | IDENT_PBM s           -> sprintf "IDENT_PBM:%s" s
  | IDENT_PGM s           -> sprintf "IDENT_PGM:%s" s
  | IDENT_CM s            -> sprintf "IDENT_CM:%s" s
  | IDENT_LM s            -> sprintf "IDENT_LM:%s" s
  | IDENT_LPAREN s        -> sprintf "IDENT_LPAREN:%s" s
  | IDENT_AM s            -> sprintf "IDENT_AM:%s" s
  | IDENT_OM s            -> sprintf "IDENT_OM:%s" s
  | IDENT_TPM s           -> sprintf "IDENT_TPM:%s" s
  | IDENT_NSM s           -> sprintf "IDENT_NSM:%s" s
  | IDENT_DSM s           -> sprintf "IDENT_DSM:%s" s
  | IDENT_BHM s           -> sprintf "IDENT_BHM:%s" s
  | IDENT_BIM s           -> sprintf "IDENT_BIM:%s" s
  | IDENT_BEM s           -> sprintf "IDENT_BEM:%s" s
  | IDENT_BFM s           -> sprintf "IDENT_BFM:%s" s
  | IDENT_BSM s           -> sprintf "IDENT_BSM:%s" s
  | IDENT_CHM s           -> sprintf "IDENT_CHM:%s" s
  | IDENT_CTM s           -> sprintf "IDENT_CTM:%s" s
  | IDENT_AGM s           -> sprintf "IDENT_AGM:%s" s
  | IDENT_AGSM s          -> sprintf "IDENT_AGSM:%s" s
  | IDENT_LOM s           -> sprintf "IDENT_LOM:%s" s
  | IDENT_PDM s           -> sprintf "IDENT_PDM:%s" s
  | IDENT_VM s            -> sprintf "IDENT_VM:%s" s
  | IDENT_SXM s           -> sprintf "IDENT_SXM:%s" s
  | IDENT_DSL s           -> sprintf "IDENT_DSL:%s" s
  | IDENT_DLM s           -> sprintf "IDENT_DLM:%s" s
  | IDENT_CBHM s          -> sprintf "IDENT_CBHM:%s" s
  | IDENT_CBEM s          -> sprintf "IDENT_CBEM:%s" s
  | IDENT_IHM s           -> sprintf "IDENT_IHM:%s" s
  | IDENT_IEM s           -> sprintf "IDENT_IEM:%s" s

  | AT                    -> "AT"
  | BS                    -> "BS"
  | DQ                    -> "DQ"
  | TEMPL_LT              -> "TEMPL_LT"
  | TEMPL_LT_             -> "TEMPL_LT_"
  | TEMPL_GT              -> "TEMPL_GT"
  | TY_TEMPL_GT           -> "TY_TEMPL_GT"
  | TY_TEMPL_GT_          -> "TY_TEMPL_GT_"
  | LAM_LBRACKET          -> "LAM_LBRACKET"
  | ATTR_LBRACKET         -> "ATTR_LBRACKET"
  | MS_ATTR_LBRACKET      -> "MS_ATTR_LBRACKET"
  | INI_LBRACE            -> "INI_LBRACE"
  | CLASS_LBRACE          -> "CLASS_LBRACE"
  | FOLD_LPAREN           -> "FOLD_LPAREN"
  | TY_LPAREN             -> "TY_LPAREN"
  | TY_LPAREN_            -> "TY_LPAREN_"
  | PP_LPAREN             -> "PP_LPAREN"
  | SS_LPAREN             -> "SS_LPAREN"
  | PS_LPAREN             -> "PS_LPAREN"
  | S_LPAREN              -> "S_LPAREN"
  | S_RPAREN              -> "S_RPAREN"
  | ELLIPSIS_             -> "ELLIPSIS_"
  | PTR_STAR              -> "PTR_STAR"
  | PTR_AMP               -> "PTR_AMP"
  | PTR_AMP_AMP           -> "PTR_AMP_AMP"
  | PTR_HAT               -> "PTR_HAT"
  | TY_HAT                -> "TY_HAT"
  | TY_TILDE              -> "TY_TILDE"
  | HEAD_COLON_COLON      -> "HEAD_COLON_COLON"
  | BASE_COLON            -> "BASE_COLON"
  | PURE_ZERO             -> "PURE_ZERO"
  | SUB_REQUIRES          -> "SUB_REQUIRES"
  | ELAB_ENUM             -> "ELAB_ENUM"
  | ELAB_CLASS            -> "ELAB_CLASS"
  | EXTERN_X s            -> "EXTERN_X:"^s
  | ODD_ELSE              -> "ODD_ELSE"
  | ODD_FOR               -> "ODD_FOR"
  | ODD_LBRACE            -> "ODD_LBRACE"
  | ODD_RBRACE            -> "ODD_RBRACE"
  | PP_IF_ATTR            -> "PP_IF_ATTR"
  | PP_IFDEF_ATTR         -> "PP_IFDEF_ATTR"
  | PP_IFNDEF_ATTR        -> "PP_IFNDEF_ATTR"
  | PP_IF_COND            -> "PP_IF_COND"
  | PP_IFDEF_COND         -> "PP_IFDEF_COND"
  | PP_IFNDEF_COND        -> "PP_IFNDEF_COND"
  | PP_IF_COND_           -> "PP_IF_COND_"
  | PP_IFDEF_COND_        -> "PP_IFDEF_COND_"
  | PP_IFNDEF_COND_       -> "PP_IFNDEF_COND_"
  | PP_IF_D               -> "PP_IF_D"
  | PP_IFDEF_D            -> "PP_IFDEF_D"
  | PP_IFNDEF_D           -> "PP_IFNDEF_D"
  | PP_IF_E               -> "PP_IF_E"
  | PP_IFDEF_E            -> "PP_IFDEF_E"
  | PP_IFNDEF_E           -> "PP_IFNDEF_E"
  | PP_IF_EH              -> "PP_IF_EH"
  | PP_IFDEF_EH           -> "PP_IFDEF_EH"
  | PP_IFNDEF_EH          -> "PP_IFNDEF_EH"
  | PP_IF_I               -> "PP_IF_I"
  | PP_IFDEF_I            -> "PP_IFDEF_I"
  | PP_IFNDEF_I           -> "PP_IFNDEF_I"
  | PP_IF_A               -> "PP_IF_A"
  | PP_IFDEF_A            -> "PP_IFDEF_A"
  | PP_IFNDEF_A           -> "PP_IFNDEF_A"
  | PP_IF_B               -> "PP_IF_B"
  | PP_IFDEF_B            -> "PP_IFDEF_B"
  | PP_IFNDEF_B           -> "PP_IFNDEF_B"
  | PP_IF_BROKEN          -> "PP_IF_BROKEN"
  | PP_IFDEF_BROKEN       -> "PP_IFDEF_BROKEN"
  | PP_IFNDEF_BROKEN      -> "PP_IFNDEF_BROKEN"
  | PP_IF_X               -> "PP_IF_X"
  | PP_IFDEF_X            -> "PP_IFDEF_X"
  | PP_IFNDEF_X           -> "PP_IFNDEF_X"
  | PP_IF_C               -> "PP_IF_C"
  | PP_IFDEF_C            -> "PP_IFDEF_C"
  | PP_IFNDEF_C           -> "PP_IFNDEF_C"
  | PP_IF_CB              -> "PP_IF_CB"
  | PP_IFDEF_CB           -> "PP_IFDEF_CB"
  | PP_IFNDEF_CB          -> "PP_IFNDEF_CB"
  | PP_IF_H               -> "PP_IF_H"
  | PP_IFDEF_H            -> "PP_IFDEF_H"
  | PP_IFNDEF_H           -> "PP_IFNDEF_H"
  | PP_IF_O               -> "PP_IF_O"
  | PP_IFDEF_O            -> "PP_IFDEF_O"
  | PP_IFNDEF_O           -> "PP_IFNDEF_O"
  | PP_IF_P               -> "PP_IF_P"
  | PP_IFDEF_P            -> "PP_IFDEF_P"
  | PP_IFNDEF_P           -> "PP_IFNDEF_P"
  | PP_IF_S               -> "PP_IF_S"
  | PP_IFDEF_S            -> "PP_IFDEF_S"
  | PP_IFNDEF_S           -> "PP_IFNDEF_S"
  | PP_IF_SHIFT           -> "PP_IF_SHIFT"
  | PP_IFDEF_SHIFT        -> "PP_IFDEF_SHIFT"
  | PP_IFNDEF_SHIFT       -> "PP_IFNDEF_SHIFT"
  | PP_IF_CLOSING         -> "PP_IF_CLOSING"
  | PP_IFDEF_CLOSING      -> "PP_IFDEF_CLOSING"
  | PP_IFNDEF_CLOSING     -> "PP_IFNDEF_CLOSING"
  | PP_IF_CLOSE_OPEN      -> "PP_IF_CLOSE_OPEN"
  | PP_IFDEF_CLOSE_OPEN   -> "PP_IFDEF_CLOSE_OPEN"
  | PP_IFNDEF_CLOSE_OPEN  -> "PP_IFNDEF_CLOSE_OPEN"
  | BAR_BAR_BROKEN i      -> "BAR_BAR_BROKEN:"^i
  | AMP_AMP_BROKEN i      -> "AMP_AMP_BROKEN:"^i
  | COMMA_BROKEN          -> "COMMA_BROKEN"
  | COMMA_BROKEN2         -> "COMMA_BROKEN2"
  | PP_ODD_ENDIF x        -> "PP_ODD_ENDIF:"^x
  | PP_ODD_IF             -> "PP_ODD_IF"
  | PP_ODD_IFDEF          -> "PP_ODD_IFDEF"
  | PP_ODD_IFNDEF         -> "PP_ODD_IFNDEF"
  | PP_ODD_ELIF x         -> "PP_ODD_ELIF:"^x
  | PP_ODD_ELSE x         -> "PP_ODD_ELSE:"^x
  | PP_STRINGIZED s       -> sprintf "PP_STRINGIZED:%s" s

  | INT_LITERAL s         -> sprintf "INT_LITERAL:%s" s
  | CHAR_LITERAL s        -> sprintf "CHAR_LITERAL:%s" s
  | FLOAT_LITERAL s       -> sprintf "FLOAT_LITERAL:%s" s
  | STR_LITERAL s         -> sprintf "STR_LITERAL:%s" (String.escaped s)
  | BOOL_LITERAL s        -> sprintf "BOOL_LITERAL:%s" s
  | USER_INT_LITERAL s    -> sprintf "USER_INT_LITERAL:%s" s
  | USER_FLOAT_LITERAL s  -> sprintf "USER_FLOAT_LITERAL:%s" s
  | USER_STR_LITERAL s    -> sprintf "USER_STR_LITERAL:%s" s
  | USER_CHAR_LITERAL s   -> sprintf "USER_CHAR_LITERAL:%s" s

  | ALIGNAS               -> "ALIGNAS"
  | ALIGNOF               -> "ALIGNOF"
  | ASM                   -> "ASM"
  | AUTO                  -> "AUTO"
  | BOOL                  -> "BOOL"
  | BREAK                 -> "BREAK"
  | CASE                  -> "CASE"
  | CATCH                 -> "CATCH"
  | CHAR                  -> "CHAR"
  | CHAR8_T               -> "CHAR8_T"
  | CHAR16_T              -> "CHAR16_T"
  | CHAR32_T              -> "CHAR32_T"
  | CLASS                 -> "CLASS"
  | CONCEPT               -> "CONCEPT"
  | CONST                 -> "CONST"
  | CONSTEVAL             -> "CONSTEVAL"
  | CONSTEXPR             -> "CONSTEXPR"
  | CONSTINIT             -> "CONSTINIT"
  | CONST_CAST            -> "CONST_CAST"
  | CONTINUE              -> "CONTINUE"
  | DECLTYPE              -> "DECLTYPE"
  | DEFAULT               -> "DEFAULT"
  | DELETE                -> "DELETE"
  | DOUBLE                -> "DOUBLE"
  | DO                    -> "DO"
  | DYNAMIC_CAST          -> "DYNAMIC_CAST"
  | ELSE                  -> "ELSE"
  | ENUM                  -> "ENUM"
  | EXPLICIT              -> "EXPLICIT"
  | EXPORT                -> "EXPORT"
  | EXTERN                -> "EXTERN"
  | FALSE                 -> "FALSE"
  | FLOAT                 -> "FLOAT"
  | FOR                   -> "FOR"
  | FRIEND                -> "FRIEND"
  | GOTO                  -> "GOTO"
  | IF                    -> "IF"
  | INLINE                -> "INLINE"
  | INT                   -> "INT"
  | LONG                  -> "LONG"
  | MUTABLE               -> "MUTABLE"
  | NAMESPACE             -> "NAMESPACE"
  | NEW                   -> "NEW"
  | NOEXCEPT              -> "NOEXCEPT"
  | NULLPTR               -> "NULLPTR"
  | OPERATOR              -> "OPERATOR"
  | PRIVATE               -> "PRIVATE"
  | PROTECTED             -> "PROTECTED"
  | PUBLIC                -> "PUBLIC"
  | REGISTER              -> "REGISTER"
  | REINTERPRET_CAST      -> "REINTERPRET_CAST"
  | REQUIRES              -> "REQUIRES"
  | RESTRICT s            -> "RESTRICT:"^s
  | RETURN                -> "RETURN"
  | SHORT                 -> "SHORT"
  | SIGNED                -> "SIGNED"
  | SIZEOF                -> "SIZEOF"
  | STATIC                -> "STATIC"
  | STATIC_ASSERT         -> "STATIC_ASSERT"
  | STATIC_CAST           -> "STATIC_CAST"
  | STRUCT                -> "STRUCT"
  | SWITCH                -> "SWITCH"
  | TEMPLATE              -> "TEMPLATE"
  | THIS                  -> "THIS"
  | THREAD_LOCAL          -> "THREAD_LOCAL"
  | THROW                 -> "THROW"
  | THROW_                -> "THROW_"
  | TRUE                  -> "TRUE"
  | TRY                   -> "TRY"
  | TYPEDEF               -> "TYPEDEF"
  | TYPEID                -> "TYPEID"
  | TYPENAME              -> "TYPENAME"
  | UNION                 -> "UNION"
  | UNSIGNED              -> "UNSIGNED"
  | USING                 -> "USING"
  | VIRTUAL               -> "VIRTUAL"
  | VOID                  -> "VOID"
  | VOLATILE              -> "VOLATILE"
  | WCHAR_T               -> "WCHAR_T"
  | WHILE                 -> "WHILE"

  | IN                    -> "IN"

  | DEFINED               -> "DEFINED"
  | HAS_INCLUDE           -> "HAS_INCLUDE"
  | HAS_CPP_ATTRIBUTE     -> "HAS_CPP_ATTRIBUTE"

  | BEGIN_ASM             -> "BEGIN_ASM"
  | END_ASM               -> "END_ASM"
  | MS_ASM s              -> "MS_ASM:"^s
  | MS_PRAGMA s           -> "MS_PRAGMA:"^s
  | MS_CDECL s            -> "MS_CDECL:"^s
  | MS_STDCALL s          -> "MS_STDCALL:"^s
  | MS_REF                -> "MS_REF"
  | MS_PROPERTY           -> "MS_PROPERTY"
  | MS_SEALED             -> "MS_SEALED"

  | GNU_ASM s             -> "GNU_ASM:"^s
  | GNU_ATTR s            -> "GNU_ATTR:"^s

  | LBRACE                -> "LBRACE"
  | RBRACE                -> "RBRACE"
  | LBRACKET              -> "LBRACKET"
  | RBRACKET              -> "RBRACKET"
  | SHARP                 -> "SHARP"
  | SHARP_SHARP           -> "SHARP_SHARP"
  | LPAREN                -> "LPAREN"
  | RPAREN                -> "RPAREN"
  | LT_COLON              -> "LT_COLON"
  | COLON_GT              -> "COLON_GT"
  | LT_PERC               -> "LT_PERC"
  | PERC_GT               -> "PERC_GT"
  | PERC_COLON            -> "PERC_COLON"
  | PERC_COLON_PERC_COLON -> "PERC_COLON_PERC_COLON"
  | SEMICOLON b           -> sprintf "SEMICOLON:%B" b
  | SEMICOLON_            -> "SEMICOLON_"
  | COLON                 -> "COLON"
  | ELLIPSIS              -> "ELLIPSIS"
  | QUEST                 -> "QUEST"
  | COLON_COLON           -> "COLON_COLON"
  | DOT                   -> "DOT"
  | DOT_STAR              -> "DOT_STAR"
  | MINUS_GT              -> "MINUS_GT"
  | MINUS_GT_STAR         -> "MINUS_GT_STAR"
  | TILDE s               -> "TILDE:"^s
  | EXCLAM s              -> "EXCLAM:"^s
  | PLUS                  -> "PLUS"
  | MINUS                 -> "MINUS"
  | STAR                  -> "STAR"
  | SLASH                 -> "SLASH"
  | PERC                  -> "PERC"
  | HAT s                 -> "HAT:"^s
  | AMP s                 -> "AMP:"^s
  | BAR s                 -> "BAR:"^s
  | EQ                    -> "EQ"
  | PLUS_EQ               -> "PLUS_EQ"
  | MINUS_EQ              -> "MINUS_EQ"
  | STAR_EQ               -> "STAR_EQ"
  | SLASH_EQ              -> "SLASH_EQ"
  | PERC_EQ               -> "PERC_EQ"
  | HAT_EQ s              -> "HAT_EQ:"^s
  | AMP_EQ s              -> "AMP_EQ:"^s
  | BAR_EQ s              -> "BAR_EQ:"^s
  | EQ_EQ                 -> "EQ_EQ"
  | EQ_EQ_EQ              -> "EQ_EQ_EQ"
  | EXCLAM_EQ s           -> "EXCLAM_EQ:"^s
  | LT                    -> "LT"
  | GT                    -> "GT"
  | LT_EQ                 -> "LT_EQ"
  | GT_EQ                 -> "GT_EQ"
  | LT_EQ_GT              -> "LT_EQ_GT"
  | AMP_AMP s             -> "AMP_AMP:"^s
  | BAR_BAR s             -> "BAR_BAR:"^s
  | LT_LT                 -> "LT_LT"
  | CUDA_LT_LT_LT         -> "CUDA_LT_LT_LT" (* CUDA C *)
  | CUDA_GT_GT_GT         -> "CUDA_GT_GT_GT" (* CUDA C *)
  | GT_GT_GT              -> "GT_GT_GT"
  | GT_GT                 -> "GT_GT"
  | LT_LT_EQ              -> "LT_LT_EQ"
  | GT_GT_EQ              -> "GT_GT_EQ"
  | PLUS_PLUS             -> "PLUS_PLUS"
  | MINUS_MINUS           -> "MINUS_MINUS"
  | COMMA                 -> "COMMA"
  | AND                   -> "AND"
  | OR                    -> "OR"
  | XOR                   -> "XOR"
  | NOT                   -> "NOT"
  | BITAND                -> "BITAND"
  | BITOR                 -> "BITOR"
  | COMPL                 -> "COMPL"
  | AND_EQ                -> "AND_EQ"
  | OR_EQ                 -> "OR_EQ"
  | XOR_EQ                -> "XOR_EQ"
  | NOT_EQ                -> "NOT_EQ"

  | PP_INCLUDE            -> "PP_INCLUDE"
  | PP_DEFINE             -> "PP_DEFINE"
  | PP_UNDEF              -> "PP_UNDEF"
  | PP_LINE               -> "PP_LINE"
  | PP_ERROR              -> "PP_ERROR"
  | PP_PRAGMA             -> "PP_PRAGMA"
  | PP_                   -> "PP_"
  | PP_IF                 -> "PP_IF"
  | PP_IFDEF              -> "PP_IFDEF"
  | PP_IFNDEF             -> "PP_IFNDEF"
  | PP_ELIF x             -> "PP_ELIF:"^(!x)
  | PP_ELSE x             -> "PP_ELSE:"^(!x)
  | PP_ENDIF x            -> "PP_ENDIF:"^(!x)
  | PP_ENDIF_             -> "PP_ENDIF_"

  | PP_IMPORT             -> "PP_IMPORT"

  | PP_UNKNOWN s          -> sprintf "PP_UNKNOWN:%s" s

  | AUDIT    -> "AUDIT"
  | AXIOM    -> "AXIOM"
  | FINAL    -> "FINAL"
  | OVERRIDE -> "OVERRIDE"
  | IMPORT   -> "IMPORT"

  | EXPECTS  -> "EXPECTS"
  | ENSURES  -> "ENSURES"
  | ASSERT   -> "ASSERT"

  | CO_AWAIT  -> "CO_AWAIT"
  | CO_RETURN -> "CO_RETURN"
  | CO_YIELD  -> "CO_YIELD"

  | BS_IDENT s -> "BS_IDENT:"^s

  | DOXYGEN_CMD s -> "DOXYGEN_CMD:"^s
  | DOXYGEN_LINE s -> "DOXYGEN_LINE:"^s

  | VAX_GLOBALDEF -> "VAX_GLOBALDEF"

  | OBJC_AUTORELEASEPOOL -> "OBJC_AUTORELEASEPOOL"
  | OBJC_AVAILABLE    -> "OBJC_ABAILABLE"
  | OBJC_CATCH        -> "OBJC_CATCH"
  | OBJC_CLASS        -> "OBJC_CLASS"
  | OBJC_DEFS         -> "OBJC_DEFS"
  | OBJC_DYNAMIC      -> "OBJC_DYNAMIC"
  | OBJC_ENCODE       -> "OBJC_ENCODE"
  | OBJC_END          -> "OBJC_END"
  | OBJC_FINALLY      -> "OBJC_FINALLY"
  | OBJC_INTERFACE    -> "OBJC_INTERFACE"
  | OBJC_LBRACKET     -> "OBJC_LBRACKET"
  | OBJC_MINUS        -> "OBJC_MINUS"
  | OBJC_OPTIONAL     -> "OBJC_OPTIONAL"
  | OBJC_PACKAGE      -> "OBJC_PACKAGE"
  | OBJC_PLUS         -> "OBJC_PLUS"
  | OBJC_PRIVATE      -> "OBJC_PRIVATE"
  | OBJC_PROPERTY     -> "OBJC_PROPERTY"
  | OBJC_PROTECTED    -> "OBJC_PROTECTED"
  | OBJC_PROTOCOL     -> "OBJC_PROTOCOL"
  | OBJC_PUBLIC       -> "OBJC_PUBLIC"
  | OBJC_REQUIRED     -> "OBJC_REQUIRED"
  | OBJC_SELECTOR     -> "OBJC_SELECTOR"
  | OBJC_SYNCHRONIZED -> "OBJC_SYNCHRONIZED"
  | OBJC_SYNTHESIZE   -> "OBJC_SYNTHESIZE"
  | OBJC_THROW        -> "OBJC_THROW"
  | OBJC_TRY          -> "OBJC_TRY"
  | OBJC_UNKNOWN s    -> "OBJC_UNKNOWN:"^s

(*  | _ -> "<not yet>"*)

let to_string (tok, st, ed) =
  let loc = Ast.Loc.of_lexposs st ed in
  Printf.sprintf "%s[%s]" (rawtoken_to_string tok) (Ast.Loc.to_string ~short:true loc)

let rawtoken_to_repr = function
  | PMODE _              -> ""
  | EOF                  -> ""
  | NEWLINE              -> "\n"
  (*| STMT_MARKER          -> ""*)
  | BRACE_PAREN_MARKER   -> ""
  | STR_MARKER           -> ""
  | SUFFIX_MARKER        -> ""
  | COND_MARKER          -> ""
  | LAM_MARKER           -> ""
  | SECTION_MARKER       -> ""
  | PP_MARKER            -> ""
  | MOCK_MARKER          -> ""
  | MARKER               -> ""
  | DUMMY_STMT           -> ""
  | DUMMY_EXPR           -> ""
  | DUMMY_OP             -> ""
  | DUMMY_BODY           -> ""
  | DUMMY_DTOR           -> ""
  | DUMMY_TYPE           -> ""
  | BRACE_LEVEL _        -> ""
  | BEGIN_STMTS          -> ""
  | END_STMTS            -> ""
  | BEGIN_ETORS          -> ""
  | END_ETORS            -> ""
  | BEGIN_QPROP          -> ""
  | END_QPROP            -> ""
  | ASM_SHADER           -> ""

  | GT_7 _                -> ">>>>>>>"
  | CONFLICT_MARKER(_, s) -> s

  | STR_MACRO s          -> s
  | INT_MACRO s          -> s
  | DECL_MACRO s         -> s
  | PRAGMA_MACRO s       -> s
  | STMT_MACRO s         -> s
  | VIRT_SPEC_MACRO s    -> s
  | OP_MACRO s           -> s
  | PARAM_DECL_MACRO s   -> s
  | PARAMS_MACRO s       -> s
  | PARAMS_BODY_MACRO s  -> s
  | ARG_MACRO s          -> s
  | ARGS_MACRO s         -> s
  | NEW_INIT_MACRO s     -> s
  | ATTR_MACRO s         -> s
  | ACC_SPEC_MACRO s     -> s
  | DECL_SPEC_MACRO s    -> s
  | CC_MACRO s           -> s
  | LAM_MACRO s          -> s
  | CV_MACRO s           -> s
  | REF_MACRO s           -> s
  | NOEXCEPT_MACRO s     -> s
  | NS_MACRO s           -> s
  | EMPTY_MACRO s        -> s
  | DELIM_MACRO s        -> s
  | BLOCK_HEAD_MACRO s   -> s
  | BLOCK_END_MACRO s    -> s
  | TYPE_MACRO s         -> s
  | BASE_MACRO s         -> s
  | BASE_SPEC_MACRO s    -> s
  | SUFFIX_MACRO s       -> s
  | PTR_MACRO s          -> s
  | BODY_MACRO s         -> s
  | DTOR_MACRO s         -> s
  | PTR_DTOR_MACRO s     -> s
  | CLASS_HEAD_MACRO s   -> s
  | FUNC_HEAD_MACRO s    -> s
  | CAST_HEAD_MACRO s    -> s
  | OBJC_PROTOCOL_REF_LIST_MACRO s -> s
  | OBJC_SEL_MACRO s      -> s
  | CLASS_BODY_HEAD_MACRO s -> s
  | CLASS_BODY_END_MACRO s -> s
  | IDENT s               -> s
  | IDENT_ s              -> s
  | IDENT_V s             -> s
  | IDENT_B s             -> s
  | IDENT_C s             -> s
  | IDENT_E s             -> s
  | IDENT_BM s            -> s
  | IDENT_DM s            -> s
  | IDENT_EM s            -> s
  | IDENT_SM s            -> s
  | IDENT_TM s            -> s
  | IDENT_IM s            -> s
  | IDENT_PM s            -> s
  | IDENT_PBM s           -> s
  | IDENT_PGM s           -> s
  | IDENT_CM s            -> s
  | IDENT_LM s            -> s
  | IDENT_LPAREN s        -> s
  | IDENT_AM s            -> s
  | IDENT_OM s            -> s
  | IDENT_TPM s           -> s
  | IDENT_NSM s           -> s
  | IDENT_DSM s           -> s
  | IDENT_BHM s           -> s
  | IDENT_BIM s           -> s
  | IDENT_BEM s           -> s
  | IDENT_BFM s           -> s
  | IDENT_BSM s           -> s
  | IDENT_CHM s           -> s
  | IDENT_CTM s           -> s
  | IDENT_AGM s           -> s
  | IDENT_AGSM s          -> s
  | IDENT_LOM s           -> s
  | IDENT_PDM s           -> s
  | IDENT_VM s            -> s
  | IDENT_SXM s           -> s
  | IDENT_DSL s           -> s
  | IDENT_DLM s           -> s
  | IDENT_CBHM s          -> s
  | IDENT_CBEM s          -> s
  | IDENT_IHM s           -> s
  | IDENT_IEM s           -> s

  | AT                    -> "@"
  | BS                    -> "\\"
  | DQ                    -> "\""
  | TEMPL_LT              -> "<"
  | TEMPL_LT_             -> "<"
  | TEMPL_GT              -> ">"
  | TY_TEMPL_GT           -> ">"
  | TY_TEMPL_GT_          -> ">"
  | LAM_LBRACKET          -> "["
  | ATTR_LBRACKET         -> "["
  | MS_ATTR_LBRACKET      -> "["
  | INI_LBRACE            -> "{"
  | CLASS_LBRACE          -> "{"
  | FOLD_LPAREN           -> "("
  | TY_LPAREN             -> "("
  | TY_LPAREN_            -> "("
  | PP_LPAREN             -> "("
  | SS_LPAREN             -> "("
  | PS_LPAREN             -> "("
  | S_LPAREN              -> "("
  | S_RPAREN              -> ")"
  | ELLIPSIS_             -> "..."
  | PTR_STAR              -> "*"
  | PTR_AMP               -> "&"
  | PTR_AMP_AMP           -> "&&"
  | PTR_HAT               -> "^"
  | TY_HAT                -> "^"
  | TY_TILDE              -> "~"
  | HEAD_COLON_COLON      -> "::"
  | BASE_COLON            -> ":"
  | PURE_ZERO             -> "=0"
  | SUB_REQUIRES          -> "requires"
  | ELAB_ENUM             -> "enum"
  | ELAB_CLASS            -> "class"
  | EXTERN_X s            -> sprintf "extern %s" s
  | ODD_ELSE              -> "else"
  | ODD_FOR               -> "for"
  | ODD_LBRACE            -> "{"
  | ODD_RBRACE            -> "}"
  | PP_IF_ATTR            -> "#if"
  | PP_IFDEF_ATTR         -> "#ifdef"
  | PP_IFNDEF_ATTR        -> "#ifndef"
  | PP_IF_COND            -> "#if"
  | PP_IFDEF_COND         -> "#ifdef"
  | PP_IFNDEF_COND        -> "#ifndef"
  | PP_IF_COND_           -> "#if"
  | PP_IFDEF_COND_        -> "#ifdef"
  | PP_IFNDEF_COND_       -> "#ifndef"
  | PP_IF_D               -> "#if"
  | PP_IFDEF_D            -> "#ifdef"
  | PP_IFNDEF_D           -> "#ifndef"
  | PP_IF_E               -> "#if"
  | PP_IFDEF_E            -> "#ifdef"
  | PP_IFNDEF_E           -> "#ifndef"
  | PP_IF_EH              -> "#if"
  | PP_IFDEF_EH           -> "#ifdef"
  | PP_IFNDEF_EH          -> "#ifndef"
  | PP_IF_I               -> "#if"
  | PP_IFDEF_I            -> "#ifdef"
  | PP_IFNDEF_I           -> "#ifndef"
  | PP_IF_A               -> "#if"
  | PP_IFDEF_A            -> "#ifdef"
  | PP_IFNDEF_A           -> "#ifndef"
  | PP_IF_B               -> "#if"
  | PP_IFDEF_B            -> "#ifdef"
  | PP_IFNDEF_B           -> "#ifndef"
  | PP_IF_BROKEN          -> "#if"
  | PP_IFDEF_BROKEN       -> "#ifdef"
  | PP_IFNDEF_BROKEN      -> "#ifndef"
  | PP_IF_X               -> "#if"
  | PP_IFDEF_X            -> "#ifdef"
  | PP_IFNDEF_X           -> "#ifndef"
  | PP_IF_C               -> "#if"
  | PP_IFDEF_C            -> "#ifdef"
  | PP_IFNDEF_C           -> "#ifndef"
  | PP_IF_CB              -> "#if"
  | PP_IFDEF_CB           -> "#ifdef"
  | PP_IFNDEF_CB          -> "#ifndef"
  | PP_IF_H               -> "#if"
  | PP_IFDEF_H            -> "#ifdef"
  | PP_IFNDEF_H           -> "#ifndef"
  | PP_IF_O               -> "#if"
  | PP_IFDEF_O            -> "#ifdef"
  | PP_IFNDEF_O           -> "#ifndef"
  | PP_IF_P               -> "#if"
  | PP_IFDEF_P            -> "#ifdef"
  | PP_IFNDEF_P           -> "#ifndef"
  | PP_IF_S               -> "#if"
  | PP_IFDEF_S            -> "#ifdef"
  | PP_IFNDEF_S           -> "#ifndef"
  | PP_IF_SHIFT           -> "#if"
  | PP_IFDEF_SHIFT        -> "#ifdef"
  | PP_IFNDEF_SHIFT       -> "#ifndef"
  | PP_IF_CLOSING         -> "#if"
  | PP_IFDEF_CLOSING      -> "#ifdef"
  | PP_IFNDEF_CLOSING     -> "#ifndef"
  | PP_IF_CLOSE_OPEN      -> "#if"
  | PP_IFDEF_CLOSE_OPEN   -> "#ifdef"
  | PP_IFNDEF_CLOSE_OPEN  -> "#ifndef"
  | BAR_BAR_BROKEN i      -> i
  | AMP_AMP_BROKEN i      -> i
  | COMMA_BROKEN          -> ","
  | COMMA_BROKEN2         -> ","
  | PP_ODD_ENDIF _        -> "#endif"
  | PP_ODD_IF             -> "#if"
  | PP_ODD_IFDEF          -> "#ifdef"
  | PP_ODD_IFNDEF         -> "#ifndef"
  | PP_ODD_ELIF _         -> "#elif"
  | PP_ODD_ELSE _         -> "#else"
  | PP_STRINGIZED s       -> sprintf "#%s" s

  | INT_LITERAL s         -> s
  | CHAR_LITERAL s        -> s
  | FLOAT_LITERAL s       -> s
  | STR_LITERAL s         -> s
  | BOOL_LITERAL s        -> s
  | USER_INT_LITERAL s    -> s
  | USER_FLOAT_LITERAL s  -> s
  | USER_STR_LITERAL s    -> s
  | USER_CHAR_LITERAL s   -> s

  | ALIGNAS               -> "alignas"
  | ALIGNOF               -> "alignof"
  | ASM                   -> "asm"
  | AUTO                  -> "auto"
  | BOOL                  -> "bool"
  | BREAK                 -> "break"
  | CASE                  -> "case"
  | CATCH                 -> "catch"
  | CHAR                  -> "char"
  | CHAR8_T               -> "char8_t"
  | CHAR16_T              -> "char16_t"
  | CHAR32_T              -> "char32_t"
  | CLASS                 -> "class"
  | CONCEPT               -> "concept"
  | CONST                 -> "const"
  | CONSTEVAL             -> "consteval"
  | CONSTEXPR             -> "constexpr"
  | CONSTINIT             -> "constinit"
  | CONST_CAST            -> "const_cast"
  | CONTINUE              -> "continue"
  | DECLTYPE              -> "decltype"
  | DEFAULT               -> "default"
  | DELETE                -> "delete"
  | DOUBLE                -> "double"
  | DO                    -> "do"
  | DYNAMIC_CAST          -> "dynamic_cast"
  | ELSE                  -> "else"
  | ENUM                  -> "enum"
  | EXPLICIT              -> "explicit"
  | EXPORT                -> "export"
  | EXTERN                -> "extern"
  | FALSE                 -> "false"
  | FLOAT                 -> "float"
  | FOR                   -> "for"
  | FRIEND                -> "friend"
  | GOTO                  -> "goto"
  | IF                    -> "if"
  | INLINE                -> "inline"
  | INT                   -> "int"
  | LONG                  -> "long"
  | MUTABLE               -> "mutable"
  | NAMESPACE             -> "namespace"
  | NEW                   -> "new"
  | NOEXCEPT              -> "noexcept"
  | NULLPTR               -> "nullptr"
  | OPERATOR              -> "operator"
  | PRIVATE               -> "private"
  | PROTECTED             -> "protected"
  | PUBLIC                -> "public"
  | REGISTER              -> "register"
  | REINTERPRET_CAST      -> "reinterpret_cast"
  | REQUIRES              -> "requires"
  | RESTRICT s            -> s
  | RETURN                -> "return"
  | SHORT                 -> "short"
  | SIGNED                -> "signed"
  | SIZEOF                -> "sizeof"
  | STATIC                -> "static"
  | STATIC_ASSERT         -> "static_assert"
  | STATIC_CAST           -> "static_cast"
  | STRUCT                -> "struct"
  | SWITCH                -> "switch"
  | TEMPLATE              -> "template"
  | THIS                  -> "this"
  | THREAD_LOCAL          -> "thread_local"
  | THROW                 -> "throw"
  | THROW_                -> "throw"
  | TRUE                  -> "true"
  | TRY                   -> "try"
  | TYPEDEF               -> "typedef"
  | TYPEID                -> "typeid"
  | TYPENAME              -> "typename"
  | UNION                 -> "union"
  | UNSIGNED              -> "unsigned"
  | USING                 -> "using"
  | VIRTUAL               -> "virtual"
  | VOID                  -> "void"
  | VOLATILE              -> "volatile"
  | WCHAR_T               -> "wchar_t"
  | WHILE                 -> "while"

  | IN                    -> "in"

  | DEFINED               -> "defined"
  | HAS_INCLUDE           -> "__has_include"
  | HAS_CPP_ATTRIBUTE     -> "__has_cpp_attribute"


  | BEGIN_ASM             -> "<begin-asm>"
  | END_ASM               -> "<end-asm>"
  | MS_ASM s              -> s
  | MS_PRAGMA s           -> "MS_PRAGMA:"^s
  | MS_CDECL s            -> s
  | MS_STDCALL s          -> s
  | MS_REF                -> "ref"
  | MS_PROPERTY           -> "property"
  | MS_SEALED             -> "sealed"

  | GNU_ASM s             -> s
  | GNU_ATTR s            -> s

  | LBRACE                -> "{"
  | RBRACE                -> "}"
  | LBRACKET              -> "["
  | RBRACKET              -> "]"
  | SHARP                 -> "#"
  | SHARP_SHARP           -> "##"
  | LPAREN                -> "("
  | RPAREN                -> ")"
  | LT_COLON              -> "<:"
  | COLON_GT              -> ":>"
  | LT_PERC               -> "<%"
  | PERC_GT               -> "%>"
  | PERC_COLON            -> "%:"
  | PERC_COLON_PERC_COLON -> "%:%:"
  | SEMICOLON false       -> ""
  | SEMICOLON true        -> ";"
  | SEMICOLON_            -> ";"
  | COLON                 -> ":"
  | ELLIPSIS              -> "..."
  | QUEST                 -> "?"
  | COLON_COLON           -> "::"
  | DOT                   -> "."
  | DOT_STAR              -> ".*"
  | MINUS_GT              -> "->"
  | MINUS_GT_STAR         -> "->*"
  | TILDE s               -> s
  | EXCLAM s              -> s
  | PLUS                  -> "+"
  | MINUS                 -> "-"
  | STAR                  -> "*"
  | SLASH                 -> "/"
  | PERC                  -> "%"
  | HAT s                 -> s
  | AMP s                 -> s
  | BAR s                 -> s
  | EQ                    -> "="
  | PLUS_EQ               -> "+="
  | MINUS_EQ              -> "-="
  | STAR_EQ               -> "*="
  | SLASH_EQ              -> "/="
  | PERC_EQ               -> "%="
  | HAT_EQ s              -> s
  | AMP_EQ s              -> s
  | BAR_EQ s              -> s
  | EQ_EQ                 -> "=="
  | EQ_EQ_EQ              -> "==="
  | EXCLAM_EQ s           -> s
  | LT                    -> "<"
  | GT                    -> ">"
  | LT_EQ                 -> "<="
  | GT_EQ                 -> ">="
  | LT_EQ_GT              -> "<=>"
  | AMP_AMP s             -> s
  | BAR_BAR s             -> s
  | LT_LT                 -> "<<"
  | CUDA_LT_LT_LT         -> "<<<"
  | CUDA_GT_GT_GT         -> ">>>"
  | GT_GT_GT              -> ">>>"
  | GT_GT                 -> ">>"
  | LT_LT_EQ              -> "<<="
  | GT_GT_EQ              -> ">>="
  | PLUS_PLUS             -> "++"
  | MINUS_MINUS           -> "--"
  | COMMA                 -> ","
  | AND                   -> "and"
  | OR                    -> "or"
  | XOR                   -> "xor"
  | NOT                   -> "not"
  | BITAND                -> "bitand"
  | BITOR                 -> "bitor"
  | COMPL                 -> "compl"
  | AND_EQ                -> "and_eq"
  | OR_EQ                 -> "or_eq"
  | XOR_EQ                -> "xor_eq"
  | NOT_EQ                -> "not_eq"

  | PP_INCLUDE            -> "#include"
  | PP_DEFINE             -> "#define"
  | PP_UNDEF              -> "#undef"
  | PP_LINE               -> "#line"
  | PP_ERROR              -> "#error"
  | PP_PRAGMA             -> "#pragma"
  | PP_                   -> "#"
  | PP_IF                 -> "#if"
  | PP_IFDEF              -> "#ifdef"
  | PP_IFNDEF             -> "#ifndef"
  | PP_ELIF _             -> "#elif"
  | PP_ELSE _             -> "#else"
  | PP_ENDIF _            -> "#endif"
  | PP_ENDIF_             -> "#endif"

  | PP_IMPORT             -> "#import"

  | PP_UNKNOWN s          -> sprintf "#%s" s

  | AUDIT    -> "audit"
  | AXIOM    -> "axiom"
  | FINAL    -> "final"
  | OVERRIDE -> "override"
  | IMPORT   -> "import"

  | EXPECTS  -> "expects"
  | ENSURES  -> "ensures"
  | ASSERT   -> "assert"

  | CO_AWAIT  -> "co_await"
  | CO_RETURN -> "co_return"
  | CO_YIELD  -> "co_yield"

  | BS_IDENT s -> s

  | DOXYGEN_CMD s -> s
  | DOXYGEN_LINE s -> s

  | VAX_GLOBALDEF -> "globaldef"

  | OBJC_AUTORELEASEPOOL -> "@autoreleasepool"
  | OBJC_AVAILABLE    -> "@available"
  | OBJC_CATCH        -> "@catch"
  | OBJC_CLASS        -> "@class"
  | OBJC_DEFS         -> "@defs"
  | OBJC_DYNAMIC      -> "@dynamic"
  | OBJC_ENCODE       -> "@encode"
  | OBJC_END          -> "@end"
  | OBJC_FINALLY      -> "@finally"
  | OBJC_INTERFACE    -> "@interface"
  | OBJC_LBRACKET     -> "["
  | OBJC_MINUS        -> "-"
  | OBJC_OPTIONAL     -> "@optional"
  | OBJC_PACKAGE      -> "@package"
  | OBJC_PLUS         -> "+"
  | OBJC_PRIVATE      -> "@private"
  | OBJC_PROPERTY     -> "@property"
  | OBJC_PROTECTED    -> "@protected"
  | OBJC_PROTOCOL     -> "@protocol"
  | OBJC_PUBLIC       -> "@public"
  | OBJC_REQUIRED     -> "@required"
  | OBJC_SELECTOR     -> "@selector"
  | OBJC_SYNCHRONIZED -> "@synchronized"
  | OBJC_SYNTHESIZE   -> "@synthesize"
  | OBJC_THROW        -> "@throw"
  | OBJC_TRY          -> "@try"
  | OBJC_UNKNOWN s    -> s


let to_repr (rt, _, _) = rawtoken_to_repr rt

let pat_last_alpha_numeric = Str.regexp ".*[a-zA-Z0-9'\"]$"
let pat_first_alpha_numeric = Str.regexp "^[a-zA-Z0-9'\"].*"
let seq_to_repr tl =
  let sz = ref 0 in
  let sl = List.map (fun x -> let s = to_repr x in sz := !sz + String.length s; s) tl in
  let buf = Buffer.create !sz in
  let sa = Array.of_list sl in
  Array.iteri
    (fun i x ->
      Buffer.add_string buf x;
      if
        Str.string_match pat_last_alpha_numeric x 0 &&
        try Str.string_match pat_first_alpha_numeric sa.(i+1) 0 with _ -> false
      then
        Buffer.add_string buf " "
    ) sa;
  Buffer.contents buf
