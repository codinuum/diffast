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
(*
 * A parser for the Python programming language (for v2.7 and v3)
 * based on Python-2.7.3/Grammar/Grammar and https://github.com/python/cpython/Grammar/Grammar
 * parser.mly
 *
 *)

%{
(*open Printf*)
(*open Common*)
open Ast

(*open Parser_aux*)
module A = Parser_aux.F (Stat)
open A
(*open Stat*)

let mklexpos i =
    { Lexing.pos_fname = "";
      Lexing.pos_lnum = 0;
      Lexing.pos_bol = 0;
      Lexing.pos_cnum = i
    }

%}

%parameter <Stat : Parser_aux.STATE_T>

%token EOF

%token <string> NAMEx
%token <string> INTEGER
%token <string> LONGINTEGER
%token <string> FLOATNUMBER
%token <string> IMAGNUMBER
%token <string> SHORTSTRING

%token <string> LONGSTRING_BEGIN_S
%token <string> LONGSTRING_BEGIN_D
%token <string> LONGSTRING_REST

%token <int> NEWLINE
%token INDENT DEDENT

(* Operators *)
%token PLUS MINUS STAR STAR_STAR SLASH SLASH_SLASH PERCENT
%token LT_LT GT_GT AMP PIPE HAT TILDE
%token GT LT EQ_EQ LT_EQ GT_EQ EXCLAM_EQ LT_GT

(* Delimiters *)
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE AT
%token COMMA COLON DOT BACKQUOTE EQ SEMICOLON ELLIPSIS
%token PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ SLASH_SLASH_EQ PERCENT_EQ
%token AMP_EQ PIPE_EQ HAT_EQ LT_LT_EQ GT_GT_EQ STAR_STAR_EQ

(* Keywords *)
%token AND AS ASSERT BREAK CLASS CONTINUE DEF DEL
%token ELIF ELSE EXCEPT EXEC
%token FALSE FINALLY FOR FROM GLOBAL
%token IF IMPORT IN IS LAMBDA NONE NOT OR
%token PASS PRINT RAISE RETURN TRUE TRY
%token WHILE WITHx YIELD

(* Python3 *)
%token COLON_EQ MINUS_GT UNDERSCORE
%token AWAIT ASYNC NONLOCAL
%token MATCH CASE

(* Error handling *)
%token <string> ERROR MARKER

%start main

%type <Ast.fileinput> main


%%
(********** Rules **********)

%inline
olist(X):
| l=separated_nonempty_list(PIPE, X) { l }
;

main:
| f=file_input EOF { Fileinput(get_loc (mklexpos 0) $endpos, f) }
|              EOF { Fileinput(get_loc $startpos $endpos, []) }
;

file_input:
| f=file_input_ { List.rev f }
;
file_input_:
|                      NEWLINE { [] }
|               s=stmt         { [s] }
| f=file_input_        NEWLINE { f }
| f=file_input_ s=stmt         { s :: f }
;

decorator:
| AT d=dotted_name NEWLINE { get_loc $startpos $endpos(d), d, emptyarglist() }
| AT d=dotted_name lp=LPAREN rp=RPAREN NEWLINE
    { 
      ignore lp;
      ignore rp;
      get_loc $startpos $endpos(rp), d, (get_loc $startpos(lp) $endpos(rp), [])
    }
| AT d=dotted_name LPAREN a=arglist rp=RPAREN NEWLINE
    { 
      ignore rp;
      get_loc $startpos $endpos(rp), d, a
    }
;

decorators:
| d=decorator               { [d] }
| d=decorator dl=decorators { d :: dl }
;

decorated:
| d=decorators c=classdef
    { 
      match c with
      | Sclassdef(_, n, t, s) -> Sclassdef(d, n, t, s)
      | _ -> assert false
    }
| d=decorators f=funcdef
    { 
      match f with
      | Sfuncdef(_, n, p, a, s) -> Sfuncdef(d, n, p, a, s)
      | _ -> assert false
    }
| d=decorators a=async_funcdef
    { 
      match a with
      | Sasync_funcdef(_, n, p, a, s) -> Sasync_funcdef(d, n, p, a, s)
      | _ -> assert false
    }

async_funcdef:
| ASYNC DEF n=name p=parameters             COLON s=suite { Sasync_funcdef([], n, p, None, s) }
| ASYNC DEF n=name p=parameters r=ret_annot COLON s=suite { Sasync_funcdef([], n, p, Some r, s) }
;
funcdef:
| DEF n=name p=parameters             COLON s=suite { Sfuncdef([], n, p, None, s) }
| DEF n=name p=parameters r=ret_annot COLON s=suite { Sfuncdef([], n, p, Some r, s) }
;
ret_annot:
| MINUS_GT t=test { t }
;
name:
| n=NAMEx { get_loc $startpos $endpos, n }
;

parameters:
| LPAREN                 RPAREN { emptytypedargslist ~loc:(get_loc $startpos $endpos) () }
| LPAREN t=typedargslist RPAREN { chg_loc t (get_loc $startpos $endpos) }
;

typedargslist:
| v=typedargs_ COMMA? { get_loc $startpos $endpos, (List.rev v) }
;
typedargs_:
|                     t=typedarg { [t] }
| tl=typedargs_ COMMA t=typedarg { t :: tl }
;
typedarg:
| t=tfpdef           { VAarg (t, None) }
| t=tfpdef EQ e=test { VAarg (t, Some e) }
| STAR                     { VAargs(get_loc $startpos $endpos, None, None) }
| STAR n=name              { VAargs(get_loc $startpos $endpos, Some n, None) }
| STAR n=name COLON t=test { VAargs(get_loc $startpos $endpos, Some n, Some t) }
| STAR_STAR n=name              { VAkwargs(get_loc $startpos $endpos, n, None) }
| STAR_STAR n=name COLON t=test { VAkwargs(get_loc $startpos $endpos, n, Some t) }
| SLASH { VAsep (get_loc $startpos $endpos) }
;

varargslist:
| v=varargs_ COMMA? { get_loc $startpos $endpos, (List.rev v) }
;
varargs_:
|                   v=vararg { [v] }
| vl=varargs_ COMMA v=vararg { v :: vl }
;
vararg:
| f=fpdef           { VAarg (f, None) }
| f=fpdef EQ t=test { VAarg (f, Some t) }
| STAR              { VAargs(get_loc $startpos $endpos, None, None) }
| STAR n=name       { VAargs(get_loc $startpos $endpos, Some n, None) }
| STAR_STAR n=name  { VAkwargs(get_loc $startpos $endpos, n, None) }
;

tfpdef:
| f=fpdef { f }
| n=name COLON t=test { Ftyped(get_loc $startpos $endpos, n, t) }
;

fpdef:
| n=name                 { Fname n }
| LPAREN f=fplist RPAREN { Flist(get_loc $startpos $endpos, f) }
;

fplist:
| f=fpdefs       { List.rev f }
| f=fpdefs COMMA { List.rev f }
;
fpdefs:
|                 f=fpdef { [f] }
| fl=fpdefs COMMA f=fpdef { f :: fl }
;

stmt:
| s=simple_stmt   { s }
| c=compound_stmt { c }
| ERROR    { mkerrstmt $startpos $endpos }
| m=MARKER { mkmarkerstmt $startpos $endpos m }
;

simple_stmt:
| s=simple_stmt_ NEWLINE { s }
;
simple_stmt_:
| s=small_stmts           { mkstmt $startpos $endpos (Ssimple (List.rev s)) }
| s=small_stmts SEMICOLON { mkstmt $startpos $endpos (Ssimple (List.rev s)) }
;
small_stmts:
|                          s=small_stmt { [s] }
| sl=small_stmts SEMICOLON s=small_stmt { s :: sl }
; 

small_stmt:
| s=small_stmt_ { mksstmt $startpos $endpos s }
;
small_stmt_:
| e=expr_stmt     { e }
| p=print_stmt    { p }
| d=del_stmt      { d }
| p=pass_stmt     { p }
| f=flow_stmt     { f }
| i=import_stmt   { i }
| g=global_stmt   { g }
| n=nonlocal_stmt { n }
| e=exec_stmt     { e }
| a=assert_stmt   { a }
;

annot:
| COLON t=test { get_loc $startpos $endpos, t }
;
annassign:
| a=annot                             { a, None }
| a=annot EQ y=testlist_or_yield_expr { a, Some y }
;

expr_stmt:
| t=testlist_star_expr { SSexpr t.list }
| t=testlist_star_expr a=annassign { SSannassign(t.list, fst a, snd a) }
| t=testlist_star_expr a=augassign y=testlist_or_yield_expr { SSaugassign(t.list, a, y) }
| t=testlist_star_expr e=eq_testlists
    { 
      match e with
      | last :: a -> SSassign(t :: (List.rev a), last)
      | _ ->
          parse_error $startpos $endpos "syntax error";
          SSerror
    }
;

eq_testlists:
|                 EQ t=testlist_or_yield_expr { [t] }
| el=eq_testlists EQ t=testlist_or_yield_expr { t :: el }
;

testlist_or_yield_expr:
| t=testlist_star_expr { t }
| y=yield_expr { y }
;

augassign:
| PLUS_EQ        { AaddEq }
| MINUS_EQ       { AsubEq }
| STAR_EQ        { AmulEq }
| SLASH_EQ       { AdivEq }
| PERCENT_EQ     { AmodEq }
| AMP_EQ         { AandEq }
| PIPE_EQ        { AorEq }
| HAT_EQ         { AxorEq }
| LT_LT_EQ       { AshiftLEq }
| GT_GT_EQ       { AshiftREq }
| STAR_STAR_EQ   { ApowEq }
| SLASH_SLASH_EQ { AfdivEq }
;

print_stmt:
| PRINT                { SSprint [] }
| PRINT       t=testlist { SSprint t.list }
| PRINT GT_GT t=testlist
    { 
      match t.list with
      | h :: t -> SSprintchevron(h, t)
      | _ ->
          parse_error $startpos $endpos "syntax error";
          SSerror
    }
;

del_stmt:
| DEL e=exprlist { SSdel e }
;

pass_stmt:
| PASS { SSpass }
;

flow_stmt:
| b=break_stmt    { b }
| c=continue_stmt { c }
| r=return_stmt   { r }
| r=raise_stmt    { r }
| y=yield_stmt    { y }
;

break_stmt:
| BREAK { SSbreak }
;

continue_stmt:
| CONTINUE { SScontinue }
;

return_stmt:
| RETURN                      { SSreturn [] }
| RETURN t=testlist_star_expr { SSreturn t.list }
;

yield_stmt:
| y=yield_expr { SSyield y.list }
;

raise_stmt:
| RAISE                                     { SSraise }
| RAISE t=test                              { SSraise1 t }
| RAISE t0=test COMMA t1=test               { SSraise2(t0, t1) }
| RAISE t0=test COMMA t1=test COMMA t2=test { SSraise3(t0, t1, t2) }
| RAISE t0=test FROM t1=test                { SSraisefrom(t0, t1) }
;

import_stmt:
| i=import_name { i }
| i=import_from { i }
;

import_name:
| IMPORT d=dotted_as_names { SSimport d }
;

import_from:
| FROM d=dotted_name IMPORT i=imports 
    {
     (*begin
       match d, i with
         [_, "__future__"], [(_, "with_statement"), None] ->
           env#enable_with_stmt
       | _ -> ()
     end;*)
     SSfrom(None, Some d, i)
   }
| FROM d=dot_or_ellipsis_seq n=dotted_name IMPORT i=imports { SSfrom(Some d, Some n, i) }
| FROM d=dot_or_ellipsis_seq               IMPORT i=imports { SSfrom(Some d, None, i) }
;

%inline
dot_or_ellipsis:
| DOT      { 1 }
| ELLIPSIS { 3 }
;
dot_or_ellipsis_seq:
| d=dot_or_ellipsis+ { get_loc $startpos $endpos, (List.fold_left (fun s x -> s + x) 0 d) }
;

imports:
| STAR { [] }
| LPAREN i=import_as_names_list RPAREN { i }
| i=import_as_names_list { i }
;
import_as_names_list:
| i=import_as_names       { List.rev i }
| i=import_as_names COMMA { List.rev i }
;

import_as_name:
| n=name             { n, None }
| n0=name AS n1=name { n0, Some n1 }
;

dotted_as_name:
| d=dotted_name { d, None }
| d=dotted_name n0=name n1=name
    { 
      if (snd n0) = "as" then
        d, Some n1
      else begin
        parse_error $startpos $endpos "syntax error";
        d, Some n1
      end
    }
| d=dotted_name AS n=name   { d, Some n }
;

import_as_names:
|                          i=import_as_name { [i] }
| il=import_as_names COMMA i=import_as_name { i :: il }
;

dotted_as_names:
| d=dotted_as_name                          { [d] }
| d=dotted_as_name COMMA dl=dotted_as_names { d :: dl }
;

dotted_name_:
| n0=name DOT n1=name    { [n0; n1] }
| n=name DOT nl=dotted_name_ { n :: nl }
;
dotted_name:
| n=name          { [n] }
| nl=dotted_name_ { nl }
;

global_stmt:
| GLOBAL n=names { SSglobal n }
;

nonlocal_stmt:
| NONLOCAL n=names { SSnonlocal n }
;

names:
| n=name                { [n] }
| n=name COMMA nl=names { n :: nl }
;

exec_stmt: 
| EXEC e=expr                          { SSexec e }
| EXEC e=expr IN t=test                { SSexec2(e, t) }
| EXEC e=expr IN t0=test COMMA t1=test { SSexec3(e, t0, t1) }
;

assert_stmt:
| ASSERT t=test                { SSassert t }
| ASSERT t0=test COMMA t1=test { SSassert2(t0, t1) }
;

compound_stmt:
| c=compound_stmt_ { mkstmt $startpos $endpos c }
;
compound_stmt_:
| i=if_stmt       { i }
| w=while_stmt    { w }
| f=for_stmt      { f }
| t=try_stmt      { t }
| w=with_stmt     { w }
| a=async_funcdef { a }
| f=funcdef       { f }
| c=classdef      { c }
| d=decorated     { d }
| a=async_stmt    { a }
| m=match_stmt    { m }
;

match_stmt:
| MATCH s=subject_expr COLON NEWLINE INDENT cl=case_block+ DEDENT { Smatch(s, cl) }
;

subject_expr:
| s=star_expr COMMA                      { SEstar(get_loc $startpos $endpos, s, [] ) }
| s=star_expr COMMA sl=star_exprs COMMA? { SEstar(get_loc $startpos $endpos, s, sl) }
| n=namedexpr_test { SEnamed(get_loc $startpos $endpos, n) }
;

%inline
star_exprs:
| sl=_star_exprs { List.rev sl }
;
_star_exprs:
|                      s=star_expr { [s] }
| sl=_star_exprs COMMA s=star_expr { s :: sl }
;

case_block:
| CASE p=patterns g_opt=guard? COLON s=suite { get_loc $startpos $endpos, p, g_opt, s }
;

guard:
| IF n=namedexpr_test { get_loc $startpos $endpos, n }
;

patterns:
| o=open_sequence_pattern { o }
| p=pattern { p }
;

pattern:
| a=as_pattern { a }
| o=or_pattern { o }
;

as_pattern:
| o=or_pattern AS p=pattern_capture_target { PAas(get_loc $startpos $endpos, o, p) }
;

pattern_capture_target:
| n=name { PAcapture n }
;

or_pattern:
| pl=olist(closed_pattern) { PAor(get_loc $startpos $endpos, pl) }
;

closed_pattern:
| l=literal_pattern { PAliteral l }
| c=capture_pattern { c }
| w=wildcard_pattern { w }
| v=value_pattern { v }
| g=group_pattern { g }
| s=sequence_pattern { s }
| m=mapping_pattern { m }
| c=class_pattern { c }
;

number:
| i=INTEGER     { Linteger i }
| l=LONGINTEGER { Llonginteger l }
| f=FLOATNUMBER { Lfloatnumber f }
| i=IMAGNUMBER  { Limagnumber i }
;

signed_number:
|       n=number { LEsigned(get_loc $startpos $endpos, n) }
| MINUS n=number { LEsignedMinus(get_loc $startpos $endpos, n) }
;

complex_number:
| s=signed_number PLUS i=IMAGNUMBER { LEcmplxPlus(get_loc $startpos $endpos, s, i) }
| s=signed_number MINUS i=IMAGNUMBER { LEcmplxMinus(get_loc $startpos $endpos, s, i) }
;

literal_expr:
| s=signed_number { s }
| c=complex_number { c }
| s=strings { LEstrings(get_loc $startpos $endpos, s) }
| NONE { LEnone(get_loc $startpos $endpos) }
| TRUE { LEtrue(get_loc $startpos $endpos) }
| FALSE { LEfalse(get_loc $startpos $endpos) }
;

%inline
literal_pattern:
| l=literal_expr { l }
;

%inline
capture_pattern:
| p=pattern_capture_target { p }
;

wildcard_pattern:
| UNDERSCORE { PAwildcard(get_loc $startpos $endpos) }
;

value_pattern:
| a=attr { PAvalue(get_loc $startpos $endpos, a) }
;

%inline
attr:
| d=dotted_name_ { d }
;

%inline
name_or_attr:
| d=dotted_name { d }
;

group_pattern:
| LPAREN p=pattern RPAREN { PAgroup(get_loc $startpos $endpos, p) }
;

sequence_pattern:
| LBRACKET m_opt=maybe_sequence_pattern? RBRACKET { PAseqB(get_loc $startpos $endpos, m_opt) }
| LPAREN o_opt=open_sequence_pattern? RPAREN { PAseqP(get_loc $startpos $endpos, o_opt) }
;

open_sequence_pattern:
| m=maybe_star_pattern COMMA m_opt=maybe_sequence_pattern? { PAseqOpen(get_loc $startpos $endpos, m, m_opt) }
;

%inline
maybe_star_patterns:
| ml=_maybe_star_patterns { List.rev ml }
;
_maybe_star_patterns:
|                               m=maybe_star_pattern { [m] }
| ml=_maybe_star_patterns COMMA m=maybe_star_pattern { m :: ml }
;

maybe_sequence_pattern:
| ml=maybe_star_patterns COMMA? { PAseqMaybe(get_loc $startpos $endpos, ml) }
;

maybe_star_pattern:
| s=star_pattern { s }
| p=pattern { p }
;

star_pattern:
| STAR p=pattern_capture_target { PAstar(get_loc $startpos $endpos, p) }
| STAR w=wildcard_pattern { PAstar(get_loc $startpos $endpos, w) }
;

mapping_pattern:
| LBRACE                                                    RBRACE { PAmap(get_loc $startpos $endpos, [], None) }
| LBRACE                       d=double_star_pattern COMMA? RBRACE { PAmap(get_loc $startpos $endpos, [], Some d) }
| LBRACE i=items_pattern COMMA d=double_star_pattern COMMA? RBRACE { PAmap(get_loc $startpos $endpos, i, Some d) }
| LBRACE i=items_pattern                             COMMA? RBRACE { PAmap(get_loc $startpos $endpos, i, None) }
;

%inline
items_pattern:
| kl=_items_pattern { List.rev kl }
;
_items_pattern:
|                   COMMA k=key_value_pattern { [k] }
| kl=_items_pattern COMMA k=key_value_pattern { k :: kl }
;

key_value_pattern:
| l=literal_expr COLON p=pattern
    { 
      let k = Kliteral(get_loc $startpos $endpos(l), l) in
      PAkeyValue(get_loc $startpos $endpos, k, p)
    }
| a=attr COLON p=pattern
    { 
      let k = Kattr(get_loc $startpos $endpos(a), a) in
      PAkeyValue(get_loc $startpos $endpos, k, p)
    }
;

double_star_pattern:
| STAR_STAR p=pattern_capture_target { PAdblStar(get_loc $startpos $endpos, p) }
;

class_pattern:
| n=name_or_attr LPAREN                                                 RPAREN
    { PAclass(get_loc $startpos $endpos, n, [], []) }
| n=name_or_attr LPAREN p=positional_patterns                          COMMA? RPAREN
    { PAclass(get_loc $startpos $endpos, n, p, []) }
| n=name_or_attr LPAREN                             k=keyword_patterns COMMA? RPAREN
    { PAclass(get_loc $startpos $endpos, n, [], k) }
| n=name_or_attr LPAREN p=positional_patterns COMMA k=keyword_patterns COMMA? RPAREN
    { PAclass(get_loc $startpos $endpos, n, p, k) }
;

%inline
positional_patterns:
| pl=_positional_patterns { List.rev pl }
;
_positional_patterns:
|                         COMMA p=pattern { [p] }
| pl=_positional_patterns COMMA p=pattern { p :: pl }
;

%inline
keyword_patterns:
| kl=_keyword_patterns { List.rev kl }
;
_keyword_patterns:
|                      COMMA k=keyword_pattern { [k] }
| kl=_keyword_patterns COMMA k=keyword_pattern { k :: kl }
;

keyword_pattern:
| n=name EQ p=pattern { PAkeyword(get_loc $startpos $endpos, n, p) }
;


async_stmt:
| ASYNC w=with_stmt { Sasync (mkstmt $startpos(w) $endpos(w) w) }
| ASYNC f=for_stmt  { Sasync (mkstmt $startpos(f) $endpos(f) f) }
;

if_stmt:
| IF t=test COLON s=suite               { Sif(t, s, [], None) }
| IF t=test COLON s=suite i=elifs       { Sif(t, s, i, None) }
| IF t=test COLON s=suite         e=els { Sif(t, s, [], Some e) }
| IF t=test COLON s=suite i=elifs e=els { Sif(t, s, i, Some e) }
;
elifs:
| e=elif          { [e] }
| e=elif el=elifs { e :: el } 
;
elif:
| ELIF t=test COLON s=suite { get_loc $startpos $endpos, t, s }
;
els:
| ELSE COLON s=suite { get_loc $startpos $endpos, s }
;

while_stmt:
| WHILE t=namedexpr_test COLON s=suite       { Swhile(t, s, None) }
| WHILE t=namedexpr_test COLON s=suite e=els { Swhile(t, s, Some e) }
;

for_stmt:
| FOR el=exprlist IN t=testlist COLON s=suite       { Sfor(el, t.list, s, None) }
| FOR el=exprlist IN t=testlist COLON s=suite e=els { Sfor(el, t.list, s, Some e) }
;

try_stmt:
| t=try_except                 { let _t, _e = t in Stry(_t, _e, None, None) }
| t=try_except e=els           { let _t, _e = t in Stry(_t, _e, Some e, None) }
| t=try_except       f=finally { let _t, _e = t in Stry(_t, _e, None, Some f) }
| t=try_except e=els f=finally { let _t, _e = t in Stry(_t, _e, Some e, Some f) }
| TRY COLON s=suite f=finally  { Stryfin(s, f) }
;
try_except:
| TRY COLON s=suite e=except_clause_suites { s, e }
;
finally:
| FINALLY COLON s=suite { get_loc $startpos $endpos, s }
;
except_clause_suites:
| e=except_clause COLON s=suite                         { [e, s] }
| e=except_clause COLON s=suite el=except_clause_suites { (e, s) :: el }
;

with_stmt:
| WITHx w=with_item_list COLON s=suite { Swith(List.rev w, s) }
;

with_item:
| t=test           { t, None }
| t=test AS e=expr { t, Some e }
;

with_item_list:
|                         w=with_item { [w] }
| wl=with_item_list COMMA w=with_item { w :: wl }
;

except_clause:
| EXCEPT                       { EX(get_loc $startpos $endpos) }
| EXCEPT t=test                { EX1(get_loc $startpos $endpos, t) }
| EXCEPT t0=test COMMA t1=test { EX2(get_loc $startpos $endpos, t0, t1) }
| EXCEPT t0=test AS    t1=test { EX2(get_loc $startpos $endpos, t0, t1) }
;

suite:
| s=simple_stmt { get_loc $startpos $endpos, [s] }
| NEWLINE INDENT s=stmts DEDENT { get_loc $startpos $endpos, s }
| NEWLINE INDENT         DEDENT { get_loc $startpos $endpos, [] } (* empty suite *)
;
stmts:
| s=stmt          { [s] }
| s=stmt sl=stmts { s :: sl }
;

old_test:
| o=or_test { o }
| o=old_lambdef { mkexpr $startpos $endpos o }
;

old_lambdef:
| LAMBDA               COLON o=old_test { Elambda(emptyvarargslist(), o) }
| LAMBDA v=varargslist COLON o=old_test { Elambda(v, o) }
;

namedexpr_test:
| t=test { t }
| t0=test COLON_EQ t1=test { mkexpr $startpos $endpos (Enamed(t0, t1)) }
| t0=test EQ       t1=test { mkexpr $startpos $endpos (Enamed(t0, t1)) } (* for print *)
;

test:
| o=or_test { o }
| o0=or_test IF o1=or_test ELSE t=test { mkexpr $startpos $endpos (Econd(o0, o1, t)) }
| l=lambdef { mkexpr $startpos $endpos l }
(*| ERROR { mkerrexpr $startpos $endpos }*)
;

or_test:
|              a=and_test { a }
| o=or_test OR a=and_test { mkexpr $startpos $endpos (Ebop(o, Bor, a)) }
;

and_test:
|                n=not_test { n }
| a=and_test AND n=not_test { mkexpr $startpos $endpos (Ebop(a, Band, n)) }
;

not_test:
| c=comparison { c }
| NOT n=not_test { mkexpr $startpos $endpos (Euop(Unot, n)) }
;

comparison:
| e=expr { e }
| c=comparison o=comp_op e=expr { mkexpr $startpos $endpos (Ebop(c, o, e)) }
;

comp_op:
| LT        { Blt }
| GT        { Bgt }
| EQ_EQ     { Beq }
| GT_EQ     { Bge }
| LT_EQ     { Ble }
| LT_GT     { Bneq }
| EXCLAM_EQ { Bneq }
| IN        { Bin }
| NOT IN    { BnotIn }
| IS        { Bis }
| IS NOT    { BisNot }
;

star_expr:
| STAR e=expr { mkexpr $startpos $endpos (Estar e) }
;

expr:
| x=xor_expr             { x }
| x=xor_expr PIPE e=expr { mkexpr $startpos $endpos (Ebop(x, BbitOr, e)) }
;

xor_expr:
|                a=and_expr { a }
| x=xor_expr HAT a=and_expr { mkexpr $startpos $endpos (Ebop(x, BbitXor, a)) }
;

and_expr:
|                s=shift_expr { s }
| a=and_expr AMP s=shift_expr { mkexpr $startpos $endpos (Ebop(a, BbitAnd, s)) }
;

shift_expr:
|                    a=arith_expr { a }
| s=shift_expr LT_LT a=arith_expr { mkexpr $startpos $endpos (Ebop(s, BshiftL, a)) }
| s=shift_expr GT_GT a=arith_expr { mkexpr $startpos $endpos (Ebop(s, BshiftR, a)) }
;

arith_expr:
|                    t=term { t }
| a=arith_expr PLUS  t=term { mkexpr $startpos $endpos (Ebop(a, Badd, t)) }
| a=arith_expr MINUS t=term { mkexpr $startpos $endpos (Ebop(a, Bsub, t)) }
;

term:
|              f=factor { f }
| t=term m=mop f=factor { mkexpr $startpos $endpos (Ebop(t, m, f)) }
;
mop:
| STAR        { Bmul }
| SLASH       { Bdiv }
| PERCENT     { Bmod }
| SLASH_SLASH { Bfdiv }
;

factor:
| PLUS  f=factor { mkexpr $startpos $endpos (Euop(Upositive, f)) }
| MINUS f=factor { mkexpr $startpos $endpos (Euop(Unegative, f)) }
| TILDE f=factor { mkexpr $startpos $endpos (Euop(Ucomplement, f)) }
| p=power { p }
;

power:
| p=primary                    { mkexpr $startpos $endpos (Eprimary p) }
| p=primary STAR_STAR f=factor { mkexpr $startpos $endpos (Epower(p, f)) }
;
primary:
|       p=_primary { p }
| AWAIT p=_primary { mkprim $startpos $endpos (Pawait p) }
;
_primary:
| a=atom { mkprim $startpos $endpos a }
| p=_primary t=trailer
    { 
      let p_ = 
        match t with
        | TRattrref n    -> Pattrref(p, n)
        | TRsubscript el -> Psubscript(p, el)
        | TRslice sil    -> Pslice(p, sil)
        | TRcall al      -> Pcall(p, al)
      in
      mkprim $startpos $endpos p_
    }
;

atom:
| LPAREN                    RPAREN { Ptuple [] }
| LPAREN y=yield_expr       RPAREN { Pyield y.list }
| LPAREN t=testlist_comp    RPAREN
    { 
      match t with
      | Pexpr _ -> Pparen (mkprimexpr $startpos(t) $endpos(t) t)
      | _ -> t
    }
| LBRACKET                  RBRACKET { Plistnull }
| LBRACKET tc=testlist_comp RBRACKET
    { 
      match tc with
      | Pparen t | Pexpr t -> Plist [t]
      | Ptuple l -> Plist l
      | PcompT(x, y) -> PcompL(x, y)
      | _ -> assert false
    }
| LBRACE                  RBRACE { Pdictnull }
| LBRACE d=dictorsetmaker RBRACE { Pdictorset d }
| BACKQUOTE t=testlist1 BACKQUOTE { Pstrconv t }
| n=name { Pname n }
| l=literal { Pliteral l }
| ELLIPSIS { Pellipsis }
;
literal:
| i=INTEGER     { Linteger i }
| l=LONGINTEGER { Llonginteger l }
| f=FLOATNUMBER { Lfloatnumber f }
| i=IMAGNUMBER  { Limagnumber i }
| s=strings     { Lstring s }
| NONE  { Lnone }
| TRUE  { Ltrue }
| FALSE { Lfalse }
;
strings:
| s=stringliteral            { [s] }
| s=stringliteral sl=strings { s :: sl }
;
stringliteral:
| s=SHORTSTRING                            { PSshort(get_loc $startpos $endpos, s) }
| l0=LONGSTRING_BEGIN_S l1=LONGSTRING_REST { PSlong(get_loc $startpos $endpos, l0 ^ l1) }
| l0=LONGSTRING_BEGIN_D l1=LONGSTRING_REST { PSlong(get_loc $startpos $endpos, l0 ^ l1) }
;

testlist_comp:
| t=test_ c=comp_for { PcompT(t, c) }
| t=testlist_
    { 
      if t.yield then
        Pyield t.list
      else
        if t.comma then
          Ptuple t.list
        else
          match t.list with
          | [t0] -> Pexpr t0
          | _ -> Ptuple t.list
    }
;
%inline
test_:
| n=namedexpr_test { n }
| s=star_expr { s }
;

lambdef:
| LAMBDA               COLON t=test { Elambda(emptyvarargslist(), t) }
| LAMBDA v=varargslist COLON t=test { Elambda(v, t) }
;

trailer:
| LPAREN           RPAREN { TRcall (emptyarglist ~loc:(get_loc $startpos $endpos) ()) }
| LPAREN a=arglist RPAREN { TRcall (chg_loc a (get_loc $startpos $endpos)) }
| LBRACKET                 RBRACKET { TRsubscript [] }
| LBRACKET s=subscriptlist RBRACKET
    { 
      if (List.for_all (function SIexpr _ -> true | _ -> false) s) then
        TRsubscript
          (List.map
             (function
               | SIexpr e -> e
               | _ ->
                   parse_error $startpos $endpos "syntax error";
                   mkerrexpr $startpos $endpos
             ) s
          )
      else TRslice s
    }
| DOT n=name { TRattrref n }
;

subscriptlist:
| s=subscripts COMMA? { List.rev s }
;
subscripts:
|                     s=subscript { [s] }
| sl=subscripts COMMA s=subscript { s :: sl }
;

subscript:
(*| DOT DOT DOT { SIellipsis(get_loc $startpos $endpos) }*)
(*| ELLIPSIS { SIellipsis(get_loc $startpos $endpos) }*)
| t=test { SIexpr t }

|         COLON         { SI2(get_loc $startpos $endpos, None, None) }
| t=test  COLON         { SI2(get_loc $startpos $endpos, Some t, None) }
|         COLON t=test  { SI2(get_loc $startpos $endpos, None, Some t) }
| t0=test COLON t1=test { SI2(get_loc $startpos $endpos, Some t0, Some t1) }

|         COLON         s=sliceop { SI3(get_loc $startpos $endpos, None, None, s) }
| t=test  COLON         s=sliceop { SI3(get_loc $startpos $endpos, Some t, None, s) }
|         COLON t=test  s=sliceop { SI3(get_loc $startpos $endpos, None, Some t, s) }
| t0=test COLON t1=test s=sliceop { SI3(get_loc $startpos $endpos, Some t0, Some t1, s) }
;

sliceop:
| COLON        { None }
| COLON t=test { Some t }
;

exprlist:
| e=_exprs COMMA? { List.rev e }
;
_exprs:
|                 e=expr_ { [e] }
| el=_exprs COMMA e=expr_ { e :: el }
;
%inline
expr_:
| e=expr { e }
| s=star_expr { s }
;

testlist:
| t=testlist1       { mktestlist t }
| t=testlist1 COMMA { mktestlist ~comma:true t }
;
testlist_star_expr:
| t=testlist1_star_expr       { mktestlist t }
| t=testlist1_star_expr COMMA { mktestlist ~comma:true t }
;
testlist_:
| t=testlist1_       { mktestlist t }
| t=testlist1_ COMMA { mktestlist ~comma:true t }
;

dictorsetmaker:
| d=dictelem c=comp_for { DSMdictC(d, c) }
| d=dictelems           { DSMdict(List.rev d) }
| d=dictelems COMMA     { DSMdict(List.rev d) }
| t=test_ c=comp_for { DSMsetC(t, c) }
| t=testlist1_star_expr       { DSMset t }
| t=testlist1_star_expr COMMA { DSMset t }
;
dictelems:
|                    d=dictelem { [d] }
| dl=dictelems COMMA d=dictelem { d :: dl }
;
dictelem:
| t0=test COLON t1=test { mkde $startpos $endpos (DEkeyValue(t0, t1)) }
| STAR_STAR e=expr  { mkde $startpos $endpos (DEstarStar e) }
;

%inline
test_star_expr:
| t=test { t }
| s=star_expr { s }
;

classdef:
| CLASS n=name                               COLON s=suite { Sclassdef([], n, emptyarglist(), s) }
| CLASS n=name lp=LPAREN           rp=RPAREN COLON s=suite
    { 
      ignore lp;
      ignore rp;
      Sclassdef([], n, (get_loc $startpos(lp) $endpos(rp), []), s)
    }
| CLASS n=name lp=LPAREN a=arglist rp=RPAREN COLON s=suite
    { 
      ignore lp;
      ignore rp;
      let _, l = a in
      let loc = get_loc $startpos(lp) $endpos(rp) in
      Sclassdef([], n, (loc, l), s)
    }
;

arglist:
| al=arg_comma_list a=argument       { get_loc $symbolstartpos $endpos, al @ [a] }
| al=arg_comma_list a=argument COMMA { get_loc $symbolstartpos $endpos, al @ [a] }
;
%inline arg_comma_list:
| (* *)             { [] }
| a=arg_comma_list_ { a }
;
arg_comma_list_:
|                    a=argument COMMA { [a] }
| al=arg_comma_list_ a=argument COMMA { al @ [a] }

argument:
| t=test                   { Aarg(get_loc $startpos $endpos, t, None) }
| t0=test EQ       t1=test { Aarg(get_loc $startpos $endpos, t0, Some t1) }
| t=test c=comp_for        { Acomp(get_loc $startpos $endpos, t, c) }
| t0=test COLON_EQ t1=test { Aassign(get_loc $startpos $endpos, t0, t1) }
| STAR t=test              { Aargs(get_loc $startpos $endpos, t) }
| STAR_STAR t=test         { Akwargs(get_loc $startpos $endpos, t) }
;

comp_iter:
| c=comp_for { Cfor c }
| c=comp_if  { Cif c }
;

comp_for:
|       s=sync_comp_for { get_loc $startpos $endpos, s, false }
| ASYNC s=sync_comp_for { get_loc $startpos $endpos, s, true }
;
sync_comp_for:
| FOR e=exprlist IN o=or_test             { e, o, None }
| FOR e=exprlist IN o=or_test c=comp_iter { e, o, Some c }
;

comp_if:
| IF o=old_test             { get_loc $startpos $endpos, o, None }
| IF o=old_test c=comp_iter { get_loc $startpos $endpos, o, Some c }
;

testlist1:
|                    t=test { [t] }
| tl=testlist1 COMMA t=test { tl @ [t] }
;

testlist1_star_expr:
|                              t=test_star_expr { [t] }
| tl=testlist1_star_expr COMMA t=test_star_expr { tl @ [t] }
;

testlist1_:
|                     t=test_ { [t] }
| tl=testlist1_ COMMA t=test_ { tl @ [t] }
;

yield_expr:
| YIELD                      { mktestlist ~yield:true [] }
| YIELD t=testlist_star_expr { t.yield<-true; t }
| YIELD FROM t=test          { mktestlist ~yield:true [mkexpr $startpos $endpos (Efrom t)] }
;


%%
