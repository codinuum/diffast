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
(* token.ml *)

module Parserlib_base = Langs_common.Parserlib_base
module Position = Langs_common.Position

open Printf

open Tokens_

module PB = Parserlib_base

type t = T.token PB.token

let get_rawtoken (rt, _, _) = rt

let rawtoken_to_string = function
  | AND      -> "AND"
  | AS       -> "AS"
  | ASSERT   -> "ASSERT"
  | BREAK    -> "BREAK"
  | CASE     -> "CASE"
  | CLASS    -> "CLASS"
  | CONTINUE -> "CONTINUE"
  | DEF      -> "DEF"
  | ELIF     -> "ELIF"
  | ELSE     -> "ELSE"
  | EXCEPT   -> "EXCEPT"
  | EXEC     -> "EXEC"
  | FALSE    -> "FALSE"
  | FINALLY  -> "FINALLY"
  | FOR      -> "FOR"
  | FROM     -> "FROM"
  | GLOBAL   -> "GLOBAL"
  | IF       -> "IF"
  | IMPORT   -> "IMPORT"
  | IN       -> "IN"
  | IS       -> "IS"
  | LAMBDA   -> "LAMBDA"
  | MATCH    -> "MATCH"
  | NONE     -> "NONE"
  | NOT      -> "NOT"
  | OR       -> "OR"
  | PASS     -> "PASS"
  | PRINT    -> "PRINT"
  | RAISE    -> "RAISE"
  | RETURN   -> "RETURN"
  | TRUE     -> "TRUE"
  | TRY      -> "TRY"
  | WHILE    -> "WHILE"
  | WITHx    -> "WITH"
  | YIELD    -> "YIELD"
  | NONLOCAL -> "NONLOCAL"
  | DEL      -> "DEL"
  | AWAIT    -> "AWAIT"
  | ASYNC    -> "ASYNC"

  | NAMEx s -> sprintf "NAME(%s)" s

  | INDENT    -> "INDENT"
  | DEDENT    -> "DEDENT"
  | NEWLINE n -> sprintf "NEWLINE(%d)" n

  | INTEGER s     -> sprintf "INTEGER(%s)" s
  | LONGINTEGER s -> sprintf "LONGINTEGER(%s)" s
  | FLOATNUMBER s -> sprintf "FLOATNUMBER(%s)" s
  | IMAGNUMBER s  -> sprintf "IMAGNUMBER(%s)" s
  | SHORTSTRING s -> sprintf "SHORTSTRING(%s)" s

  | LONGSTRING_BEGIN_S s -> sprintf "LONGSTRING_BEGIN_S(%s)" s
  | LONGSTRING_BEGIN_D s -> sprintf "LONGSTRING_BEGIN_D(%s)" s
  | LONGSTRING_REST s    -> sprintf "LONGSTRING_REST(%s)" s

  | EQ_EQ     -> "EQ_EQ"
  | LT_EQ     -> "LT_EQ"
  | GT_EQ     -> "GT_EQ"
  | EXCLAM_EQ -> "EXCLAM_EQ"
  | LT_GT     -> "LT_GT"

  | STAR_STAR   -> "STAR_STAR"
  | SLASH_SLASH -> "SLASH_SLASH"
  | LT_LT       -> "LT_LT"
  | GT_GT       -> "GT_GT"

  | PLUS_EQ        -> "PLUS_EQ"
  | MINUS_EQ       -> "MINUS_EQ"
  | STAR_EQ        -> "STAR_EQ"
  | SLASH_EQ       -> "SLASH_EQ"
  | SLASH_SLASH_EQ -> "SLASH_SLASH_EQ"
  | PERCENT_EQ     -> "PERCENT_EQ"
  | AMP_EQ         -> "AMP_EQ"
  | PIPE_EQ        -> "PIPE_EQ"
  | HAT_EQ         -> "HAT_EQ"
  | GT_GT_EQ       -> "GT_GT_EQ"
  | LT_LT_EQ       -> "LT_LT_EQ"
  | STAR_STAR_EQ   -> "STAR_STAR_EQ"

  | MINUS_GT -> "MINUS_GT"

  | COLON_EQ -> "COLON_EQ"

  | PLUS    -> "PLUS"
  | MINUS   -> "MINUS"
  | STAR    -> "STAR"
  | SLASH   -> "SLASH"
  | PERCENT -> "PERCENT"
  | AMP     -> "AMP"
  | PIPE    -> "PIPE"
  | HAT     -> "HAT"
  | TILDE   -> "TILDE"
  | GT      -> "GT"
  | LT      -> "LT"

  | LPAREN    -> "LPAREN"
  | RPAREN    -> "RPAREN"
  | LBRACE    -> "LBRACE"
  | RBRACE    -> "RBRACE"
  | LBRACKET  -> "LBRACKET"
  | RBRACKET  -> "RBRACKET"
  | AT        -> "AT"
  | COMMA     -> "COMMA"
  | COLON     -> "COLON"
  | DOT       -> "DOT"
  | BACKQUOTE -> "BACKQUOTE"
  | EQ        -> "EQ"
  | SEMICOLON -> "SEMICOLON"
  | ELLIPSIS  -> "ELLIPSIS"
  | UNDERSCORE -> "UNDERSCORE"

  | EOF -> "EOF"

  | ERROR s -> sprintf "ERROR(%s)" s
  | MARKER s -> sprintf "MARKER(%s)" s



let rawtoken_to_orig = function
  | AND      -> "and"
  | AS       -> "as"
  | ASSERT   -> "assert"
  | BREAK    -> "break"
  | CASE     -> "case"
  | CLASS    -> "class"
  | CONTINUE -> "continue"
  | DEF      -> "def"
  | ELIF     -> "elif"
  | ELSE     -> "else"
  | EXCEPT   -> "except"
  | EXEC     -> "exec"
  | FALSE    -> "False"
  | FINALLY  -> "finally"
  | FOR      -> "for"
  | FROM     -> "from"
  | GLOBAL   -> "global"
  | IF       -> "if"
  | IMPORT   -> "import"
  | IN       -> "in"
  | IS       -> "is"
  | LAMBDA   -> "lambda"
  | MATCH    -> "match"
  | NONE     -> "None"
  | NOT      -> "not"
  | OR       -> "or"
  | PASS     -> "pass"
  | PRINT    -> "print"
  | RAISE    -> "raise"
  | RETURN   -> "return"
  | TRUE     -> "True"
  | TRY      -> "try"
  | WHILE    -> "while"
  | WITHx    -> "with"
  | YIELD    -> "yield"
  | NONLOCAL -> "nonlocal"
  | DEL      -> "del"
  | AWAIT    -> "await"
  | ASYNC    -> "async"


  | NAMEx s -> s

  | INDENT    -> "INDENT"
  | DEDENT    -> "DEDENT"
  | NEWLINE n -> sprintf "NEWLINE(%d)" n

  | INTEGER s     -> s
  | LONGINTEGER s -> s
  | FLOATNUMBER s -> s
  | IMAGNUMBER s  -> s
  | SHORTSTRING s -> s

  | LONGSTRING_BEGIN_S s -> s
  | LONGSTRING_BEGIN_D s -> s
  | LONGSTRING_REST s    -> s

  | EQ_EQ     -> "=="
  | LT_EQ     -> "<="
  | GT_EQ     -> ">="
  | EXCLAM_EQ -> "!="
  | LT_GT     -> "<>"

  | STAR_STAR   -> "**"
  | SLASH_SLASH -> "//"
  | LT_LT       -> "<<"
  | GT_GT       -> ">>"

  | PLUS_EQ        -> "+="
  | MINUS_EQ       -> "-="
  | STAR_EQ        -> "*="
  | SLASH_EQ       -> "/="
  | SLASH_SLASH_EQ -> "//="
  | PERCENT_EQ     -> "%="
  | AMP_EQ         -> "&="
  | PIPE_EQ        -> "|="
  | HAT_EQ         -> "^="
  | GT_GT_EQ       -> ">>="
  | LT_LT_EQ       -> "<<="
  | STAR_STAR_EQ   -> "**="

  | MINUS_GT -> "->"

  | COLON_EQ -> ":="

  | PLUS    -> "+"
  | MINUS   -> "-"
  | STAR    -> "*"
  | SLASH   -> "/"
  | PERCENT -> "%"
  | AMP     -> "&"
  | PIPE    -> "|"
  | HAT     -> "^"
  | TILDE   -> "~"
  | GT      -> ">"
  | LT      -> "<"

  | LPAREN    -> "("
  | RPAREN    -> ")"
  | LBRACE    -> "{"
  | RBRACE    -> "}"
  | LBRACKET  -> "["
  | RBRACKET  -> "]"
  | AT        -> "@"
  | COMMA     -> ","
  | COLON     -> ":"
  | DOT       -> "."
  | BACKQUOTE -> "`"
  | EQ        -> "="
  | SEMICOLON -> ";"
  | ELLIPSIS  -> "..."
  | UNDERSCORE -> "_"

  | EOF -> "EOF"

  | ERROR s -> sprintf "ERROR(%s)" s
  | MARKER s -> s


let to_string (tok, st, ed) =
  let loc = Ast.Loc.of_lexposs st ed in
  sprintf "%s[%s]" (rawtoken_to_string tok) (Ast.Loc.to_string loc)


let to_rawtoken = PB.token_to_rawtoken
let to_lexposs  = PB.token_to_lexposs
let decompose   = PB.decompose_token
let create      = PB.make_token

let to_orig t = rawtoken_to_orig (to_rawtoken t)
