(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>

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
(* token.ml *)

open Tokens_

module PB = Langs_common.Parserlib_base
module Position = Langs_common.Position

type t = T.token PB.token

let rawtoken_to_string = function
  | STMT _       -> "STMT"
  | BLOCK_STMT _ -> "BLOCK_STMT"
  | ERROR_STMT s -> "ERROR_STMT:" ^ s
  | ERROR_MOD s  -> "ERROR_MOD:" ^ s
  | ERROR s      -> "ERROR:" ^ s
  | MARKER s     -> "MARKER:" ^ s
  | GT_7         -> "GT_7"
  | EOP          -> "EOP"

  | EXPORTS _    -> "EXPORTS"
  | MODULE _     -> "MODULE"
  | NON_SEALED _ -> "NON_SEALED"
  | OPEN _       -> "OPEN"
  | OPENS _      -> "OPENS"
  | PERMITS _    -> "PERMITS"
  | PROVIDES _   -> "PROVIDES"
  | RECORD _     -> "RECORD"
  | REQUIRES _   -> "REQUIRES"
  | SEALED _     -> "SEALED"
  | TO _         -> "TO"
  | TRANSITIVE _ -> "TRANSITIVE"
  | USES _       -> "USES"
  | VAR _        -> "VAR"
  | WITH_ _      -> "WITH_"
  | YIELD _      -> "YIELD"

  | IDENTIFIER(_, s)         -> "IDENTIFIER:" ^ s
  | INTEGER_LITERAL i        -> "INTEGER_LITERAL:" ^ i
  | FLOATING_POINT_LITERAL f -> "FLOATING_POINT_LITERAL:" ^ f
  | CHARACTER_LITERAL c      -> "CHARACTER_LITERAL:" ^ c
  | STRING_LITERAL s         -> "STRING_LITERAL:" ^ s
  | TEXT_BLOCK s             -> "TEXT_BLOCK:" ^ s
  | TRUE                     -> "TRUE"
  | FALSE                    -> "FALSE"
  | NULL                     -> "NULL"

  | LPAREN _  -> "LPAREN"
  | LPAREN__LAMBDA _ -> "LPAREN__LAMBDA"
  | RPAREN _  -> "RPAREN"
  | LBRACE    -> "LBRACE"
  | RBRACE    -> "RBRACE"
  | LBRACKET  -> "LBRACKET"
  | RBRACKET  -> "RBRACKET"
  | SEMICOLON -> "SEMICOLON"
  | COMMA     -> "COMMA"
  | DOT       -> "DOT"
  | ELLIPSIS  -> "ELLIPSIS"
  | COLON_COLON -> "COLON_COLON"
  | AT _      -> "AT"
  | AT__INTERFACE _      -> "AT__INTERFACE"

  | EQ          -> "EQ"
  | GT          -> "GT"
  | LT _        -> "LT"
  | EXCLAM      -> "EXCLAM"
  | TILDE       -> "TILDE"
  | QUESTION    -> "QUESTION"
  | COLON       -> "COLON"
  | EQ_EQ       -> "EQ_EQ"
  | LT_EQ       -> "LT_EQ"
  | GT_EQ       -> "GT_EQ"
  | EXCLAM_EQ   -> "EXCLAM_EQ"
  | AND_AND     -> "AND_AND"
  | OR_OR       -> "OR_OR"
  | PLUS_PLUS   -> "PLUS_PLUS"
  | MINUS_MINUS -> "MINUS_MINUS"
  | PLUS        -> "PLUS"
  | MINUS       -> "MINUS"
  | STAR        -> "STAR"
  | SLASH       -> "SLASH"
  | AND         -> "AND"
  | OR          -> "OR"
  | HAT         -> "HAT"
  | PERCENT     -> "PERCENT"
  | LT_LT       -> "LT_LT"
  | GT_GT       -> "GT_GT"
  | GT_GT_GT    -> "GT_GT_GT"
  | PLUS_EQ     -> "PLUS_EQ"
  | MINUS_EQ    -> "MINUS_EQ"
  | MINUS_GT    -> "MINUS_GT"
  | MINUS_GT__CASE -> "MINUS_GT__CASE"
  | STAR_EQ     -> "STAR_EQ"
  | SLASH_EQ    -> "SLASH_EQ"
  | AND_EQ      -> "AND_EQ"
  | OR_EQ       -> "OR_EQ"
  | HAT_EQ      -> "HAT_EQ"
  | PERCENT_EQ  -> "PERCENT_EQ"
  | LT_LT_EQ    -> "LT_LT_EQ"
  | GT_GT_EQ    -> "GT_GT_EQ"
  | GT_GT_GT_EQ -> "GT_GT_GT_EQ"

  (* keywords *)
  | ABSTRACT _     -> "ABSTRACT"
  | ASSERT _       -> "ASSERT"
  | BOOLEAN _      -> "BOOLEAN"
  | BREAK _        -> "BREAK"
  | BYTE _         -> "BYTE"
  | CASE _         -> "CASE"
  | CATCH _        -> "CATCH"
  | CHAR _         -> "CHAR"
  | CLASS _        -> "CLASS"
  | CONST _        -> "CONST"
  | CONTINUE _     -> "CONTINUE"
  | DEFAULT _      -> "DEFAULT"
  | DEFAULT__COLON _ -> "DEFAULT__COLON"
  | DO _           -> "DO"
  | DOUBLE _       -> "DOUBLE"
  | ELSE _         -> "ELSE"
  | ENUM _         -> "ENUM"
  | EXTENDS _      -> "EXTENDS"
  | FINAL _        -> "FINAL"
  | FINALLY _      -> "FINALLY"
  | FLOAT _        -> "FLOAT"
  | FOR _          -> "FOR"
  | GOTO _         -> "GOTO"
  | IF _           -> "IF"
  | IMPLEMENTS _   -> "IMPLEMENTS"
  | IMPORT _       -> "IMPORT"
  | INSTANCEOF _   -> "INSTANCEOF"
  | INT _          -> "INT"
  | INTERFACE _    -> "INTERFACE"
  | LONG _         -> "LONG"
  | NATIVE _       -> "NATIVE"
  | NEW _          -> "NEW"
  | PACKAGE _      -> "PACKAGE"
  | PRIVATE _      -> "PRIVATE"
  | PROTECTED _    -> "PROTECTED"
  | PUBLIC _       -> "PUBLIC"
  | RETURN _       -> "RETURN"
  | SHORT _        -> "SHORT"
  | STATIC _       -> "STATIC"
  | STRICTFP _     -> "STRICTFP"
  | SUPER _        -> "SUPER"
  | SWITCH _       -> "SWITCH"
  | SYNCHRONIZED _ -> "SYNCHRONIZED"
  | THIS _         -> "THIS"
  | THROW _        -> "THROW"
  | THROWS _       -> "THROWS"
  | TRANSIENT _    -> "TRANSIENT"
  | TRY _          -> "TRY"
  | VOLATILE _     -> "VOLATILE"
  | VOID _         -> "VOID"
  | WHILE _        -> "WHILE"

  | EOF -> "EOF"

  | ASPECT _       -> "ASPECT"
  | POINTCUT _     -> "POINTCUT"
  | WITHIN _       -> "WITHIN"
  | DECLARE _      -> "DECLARE"
  | DOT_DOT        -> "DOT_DOT"

let rawtoken_to_orig = function
  | STMT _       -> "<stmt>"
  | BLOCK_STMT _ -> "<block-stmt>"
  | ERROR_STMT s -> s
  | ERROR_MOD s  -> s
  | ERROR s      -> s
  | MARKER s     -> s
  | GT_7         -> ">>>>>>>"
  | EOP          -> ""

  | EXPORTS _    -> "exports"
  | MODULE _     -> "module"
  | NON_SEALED _ -> "non-sealed"
  | OPEN _       -> "open"
  | OPENS _      -> "opens"
  | PERMITS _    -> "permits"
  | PROVIDES _   -> "provides"
  | RECORD _     -> "record"
  | REQUIRES _   -> "requires"
  | SEALED _     -> "sealed"
  | TO _         -> "to"
  | TRANSITIVE _ -> "transitive"
  | USES _       -> "uses"
  | VAR _        -> "var"
  | WITH_ _      -> "with"
  | YIELD _      -> "yield"

  | IDENTIFIER(_, s)         -> s
  | INTEGER_LITERAL i        -> i
  | FLOATING_POINT_LITERAL f -> f
  | CHARACTER_LITERAL c      -> c
  | STRING_LITERAL s         -> s
  | TEXT_BLOCK s             -> s
  | TRUE                     -> "true"
  | FALSE                    -> "false"
  | NULL                     -> "null"

  | LPAREN _  -> "("
  | LPAREN__LAMBDA _ -> "("
  | RPAREN _  -> ")"
  | LBRACE    -> "{"
  | RBRACE    -> "}"
  | LBRACKET  -> "["
  | RBRACKET  -> "]"
  | SEMICOLON -> ";"
  | COMMA     -> ","
  | DOT       -> "."
  | ELLIPSIS  -> "..."
  | COLON_COLON -> "::"
  | AT _      -> "@"
  | AT__INTERFACE _ -> "@"

  | EQ          -> "="
  | GT          -> ">"
  | LT _        -> "<"
  | EXCLAM      -> "!"
  | TILDE       -> "~"
  | QUESTION    -> "?"
  | COLON       -> ":"
  | EQ_EQ       -> "=="
  | LT_EQ       -> "<="
  | GT_EQ       -> ">="
  | EXCLAM_EQ   -> "!="
  | AND_AND     -> "&&"
  | OR_OR       -> "||"
  | PLUS_PLUS   -> "++"
  | MINUS_MINUS -> "--"
  | PLUS        -> "+"
  | MINUS       -> "-"
  | STAR        -> "*"
  | SLASH       -> "/"
  | AND         -> "&"
  | OR          -> "|"
  | HAT         -> "^"
  | PERCENT     -> "%"
  | LT_LT       -> "<<"
  | GT_GT       -> ">>"
  | GT_GT_GT    -> ">>>"
  | PLUS_EQ     -> "+="
  | MINUS_EQ    -> "-="
  | MINUS_GT    -> "->"
  | MINUS_GT__CASE -> "->"
  | STAR_EQ     -> "*="
  | SLASH_EQ    -> "/="
  | AND_EQ      -> "&="
  | OR_EQ       -> "|="
  | HAT_EQ      -> "^="
  | PERCENT_EQ  -> "%="
  | LT_LT_EQ    -> "<<="
  | GT_GT_EQ    -> ">>="
  | GT_GT_GT_EQ -> ">>>="

  (* keywords *)
  | ABSTRACT _       -> "abstract"
  | ASSERT _         -> "assert"
  | BOOLEAN _        -> "boolean"
  | BREAK _          -> "break"
  | BYTE _           -> "byte"
  | CASE _           -> "case"
  | CATCH _          -> "catch"
  | CHAR _           -> "char"
  | CLASS _          -> "class"
  | CONST _          -> "const"
  | CONTINUE _       -> "continue"
  | DEFAULT _        -> "default"
  | DEFAULT__COLON _ -> "default"
  | DO _             -> "do"
  | DOUBLE _         -> "double"
  | ELSE _           -> "else"
  | ENUM _           -> "enum"
  | EXTENDS _        -> "extends"
  | FINAL _          -> "final"
  | FINALLY _        -> "finally"
  | FLOAT _          -> "float"
  | FOR _            -> "for"
  | GOTO _           -> "goto"
  | IF _             -> "if"
  | IMPLEMENTS _     -> "implements"
  | IMPORT _         -> "import"
  | INSTANCEOF _     -> "instanceof"
  | INT _            -> "int"
  | INTERFACE _      -> "interface"
  | LONG _           -> "long"
  | NATIVE _         -> "native"
  | NEW _            -> "new"
  | PACKAGE _        -> "package"
  | PRIVATE _        -> "private"
  | PROTECTED _      -> "protected"
  | PUBLIC _         -> "public"
  | RETURN _         -> "return"
  | SHORT _          -> "short"
  | STATIC _         -> "static"
  | STRICTFP _       -> "strictfp"
  | SUPER _          -> "super"
  | SWITCH _         -> "switch"
  | SYNCHRONIZED _   -> "synchronized"
  | THIS _           -> "this"
  | THROW _          -> "throw"
  | THROWS _         -> "throws"
  | TRANSIENT _      -> "transient"
  | TRY _            -> "try"
  | VOLATILE _       -> "volatile"
  | VOID _           -> "void"
  | WHILE _          -> "while"

  | EOF -> ""

  | ASPECT _         -> "aspect"
  | POINTCUT _       -> "pointcut"
  | WITHIN _         -> "within"
  | DECLARE _        -> "declare"
  | DOT_DOT          -> ".."



let to_string (tok, st, ed) =
  let loc = Ast.Loc.of_lexposs st ed in
  Printf.sprintf "%s[%s]" (rawtoken_to_string tok) (Ast.Loc.to_string ~short:true loc)


let to_rawtoken = PB.token_to_rawtoken
let to_lexposs  = PB.token_to_lexposs
let decompose   = PB.decompose_token
let create      = PB.make_token

let to_orig t = rawtoken_to_orig (to_rawtoken t)
