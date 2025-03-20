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
 * A parser for the Java Language (based on the JLS 3rd ed.) 
 * 
 * parser.mly
 *
 *)

%{
module Xoption = Diffast_misc.Xoption
module P = Printer
open Printf
open Ast

open Parser_aux
module A = Parser_aux.F (Stat)
open A
open Stat
%}

%parameter <Stat : Parser_aux.STATE_T>

%token EOF

(* Literals *)
%token <Ast.Loc.t * string> IDENTIFIER
%token <string> INTEGER_LITERAL
%token <string> FLOATING_POINT_LITERAL
%token <string> CHARACTER_LITERAL
%token <string> STRING_LITERAL
%token <string> TEXT_BLOCK
%token TRUE FALSE NULL

(* Separators *)
%token <Ast.Loc.t> AT AT__INTERFACE LPAREN RPAREN LPAREN__LAMBDA
%token LBRACE RBRACE LBRACKET RBRACKET SEMICOLON COMMA DOT 
%token ELLIPSIS COLON_COLON

(* Operators *)
%token <Ast.Loc.t> LT
%token EQ GT EXCLAM TILDE QUESTION COLON
%token EQ_EQ LT_EQ GT_EQ EXCLAM_EQ AND_AND OR_OR PLUS_PLUS MINUS_MINUS
%token PLUS MINUS STAR SLASH AND OR HAT PERCENT LT_LT GT_GT GT_GT_GT
%token PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ AND_EQ OR_EQ HAT_EQ PERCENT_EQ 
%token LT_LT_EQ GT_GT_EQ GT_GT_GT_EQ MINUS_GT MINUS_GT__CASE

(* Keywords *)
%token <Ast.Loc.t> ABSTRACT ASSERT BOOLEAN BREAK BYTE 
%token <Ast.Loc.t> CASE CATCH CHAR CLASS CONST CONTINUE
%token <Ast.Loc.t> DEFAULT DEFAULT__COLON DO DOUBLE ELSE ENUM EXTENDS
%token <Ast.Loc.t> FINAL FINALLY FLOAT FOR GOTO
%token <Ast.Loc.t> IF IMPLEMENTS IMPORT INSTANCEOF INT INTERFACE LONG 
%token <Ast.Loc.t> NATIVE NEW PACKAGE PRIVATE PROTECTED PUBLIC RETURN
%token <Ast.Loc.t> SHORT STATIC STRICTFP SUPER SWITCH SYNCHRONIZED
%token <Ast.Loc.t> THIS THROW THROWS TRANSIENT TRY VOLATILE VOID WHILE

(* Contextual Keywords *)
%token <Ast.Loc.t> EXPORTS MODULE NON_SEALED OPEN OPENS PERMITS PROVIDES RECORD REQUIRES
%token <Ast.Loc.t> SEALED TO TRANSITIVE USES VAR WITH_ YIELD

(* AspectJ *)
%token <Ast.Loc.t> ASPECT POINTCUT WITHIN DECLARE
%token DOT_DOT

(* *)
%token <Ast.statement> STMT
%token <Ast.block_statement> BLOCK_STMT
%token <string> MARKER ERROR ERROR_STMT ERROR_MOD
%token GT_7
%token EOP

%start main
%start partial_assert_statement
%start partial_block_statement

%type <Ast.compilation_unit> main
%type <Ast.statement> partial_assert_statement
%type <Ast.block_statement> partial_block_statement


(* to avoid warnings *)
%start reserved
%type <unit> reserved

%%
(********** Rules **********)


%inline
clist(X):
| l=separated_nonempty_list(COMMA, X) { l }
;

%inline
clist0(X):
| l_opt=ioption(separated_nonempty_list(COMMA, X)) { Xoption.list_opt_to_list l_opt }
;

reserved:
| GOTO  { }
| CONST { }

| GT_7 { }

| VAR { }
;

partial_block_statement:
| p=block_statement EOP { p }
;

partial_assert_statement:
| p=assert_statement EOP { p }
;


main:
| c=compilation_unit EOF { end_scope(); c }
;

literal:
| i=INTEGER_LITERAL        { env#incr_nintegers(); Linteger i }
| f=FLOATING_POINT_LITERAL { env#incr_nfloats(); LfloatingPoint f }
| TRUE                     { Ltrue }
| FALSE                    { Lfalse }
| c=CHARACTER_LITERAL      { Lcharacter(String.sub c 1 ((String.length c) - 2)) }
| s=STRING_LITERAL         { env#incr_nstrings(); Lstring(String.sub s 1 ((String.length s) - 2)) }
| s=TEXT_BLOCK
    { 
      check_JLS_level 15
        (fun () ->
          env#incr_nstrings();
          LtextBlock(String.sub s 3 ((String.length s) - 6))
        )
        (fun () -> parse_error $startpos $endpos "text-block is available since JLS15")
    }
| NULL                     { Lnull }
;

unann_type:
| p=unann_primitive_type { p }
| r=unann_reference_type { r }
;

unann_primitive_type:
| n=numeric_type { n }
| BOOLEAN        { mktype $startpos $endpos (Tprimitive([], PTboolean)) }
;

%inline
primitive_type:
|               u=unann_primitive_type { u }
| a=annotations u=unann_primitive_type 
    { 
      check_JLS_level 8
        (fun () ->
          let loc = get_loc $startpos $endpos in
          add_ann loc a u
        )
        (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
    }
;

numeric_type:
| i=integral_type       { mktype $startpos $endpos (Tprimitive([], i)) }
| f=floating_point_type { mktype $startpos $endpos (Tprimitive([], f)) }
;

integral_type:
| BYTE  { PTbyte }
| SHORT { PTshort }
| INT   { PTint }
| LONG  { PTlong }
| CHAR  { PTchar }
;

floating_point_type:
| FLOAT  { PTfloat }
| DOUBLE { PTdouble }
;


unann_reference_type:
| c=unann_class_or_interface_type { c }
| a=unann_array_type              { a }
;

%inline
reference_type:
|               u=unann_reference_type { u }
| a=annotations u=unann_reference_type 
    { 
      check_JLS_level 8
        (fun () ->
          let loc = get_loc $startpos $endpos in
          add_ann loc a u
        )
        (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
    }
;

%inline
class_or_interface_type:
|               u=unann_class_or_interface_type { u }
| a=annotations u=unann_class_or_interface_type 
    { 
      check_JLS_level 8
        (fun () ->
          let loc = get_loc $startpos $endpos in
          add_ann loc a u
        )
        (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
    }
;

%inline
class_or_interface_type_spec:
|               u=unann_class_or_interface_type_spec { u }
| a=annotations u=unann_class_or_interface_type_spec 
    { 
      check_JLS_level 8
        (fun () ->
          let head, a0, n0 = u in
          head, a @ a0, n0
        )
        (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
    }
;


unann_class_or_interface_type_spec:
| n=name 
    {
     let rr =
       try
         mkresolved (get_type_fqn n)
       with
       | _ -> env#resolve n
     in
     set_attribute_PT_T rr n;
     if env#in_method then begin
       try
         register_qname_as_typename_at_class ~outer:1 n
       with
         Not_found -> ()
     end
     else
       register_qname_as_typename n;
     [], [], n 
   }

| c=unann_class_or_interface_type_spec ts=type_arguments DOT a=annotations0 n=name
    { 
      let thunk () =
        let head, a0, n0 = c in
        head @ [TSapply(a0, n0, ts)], a, n
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }
;

unann_class_or_interface_type:
| c=unann_class_or_interface_type_spec 
    { 
      let head, a, n = c in
      mktype $startpos $endpos (TclassOrInterface(head @ [TSname(a, n)])) 
    }

| c=unann_class_or_interface_type_spec ts=type_arguments
    { 
      let head, a, n = c in
      mktype $startpos $endpos (TclassOrInterface(head @ [TSapply(a, n, ts)])) 
    }
;

%inline
unann_class_type:
| c=unann_class_or_interface_type { c }
;

%inline
class_type:
| c=class_or_interface_type { c }
;

%inline
interface_type:
| c=class_or_interface_type { c }
;

unann_array_type:
| n=name d=ann_dims 
    { 
      set_attribute_PT_T (env#resolve n) n;
      register_qname_as_typename n;
      mktype $startpos $endpos (Tarray(name_to_ty [] n, d))
    }

| p=unann_primitive_type d=ann_dims { mktype $startpos $endpos (Tarray(p, d)) }

| c=unann_class_or_interface_type_spec ts=type_arguments DOT a=annotations0 n=name d=ann_dims 
    { 
      let thunk () =
        let head, a0, n0 = c in
        let ty =
          _mktype (Loc.merge (get_loc $startpos $endpos) n.n_loc)
            (TclassOrInterface(head @ [TSapply(a0, n0, ts); TSname(a, n)]))
        in
        mktype $startpos $endpos (Tarray(ty, d))
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }

| c=unann_class_or_interface_type_spec ts=type_arguments d=ann_dims 
    { 
      let head, a, n = c in
      let ty =
        _mktype (Loc.merge (get_loc $startpos $endpos) ts.tas_loc)
          (TclassOrInterface(head @ [TSapply(a, n, ts)]))
      in
      mktype $startpos $endpos (Tarray(ty, d))
    }
;


%inline
type_arguments_opt:
| ts_opt=ioption(type_arguments) { ts_opt }
;

type_arguments:
| LT GT { mktyargs $startpos $endpos [] }
| LT tas=type_argument_list_1 { mktyargs $startpos $endpos tas }
;

%inline
wildcard_head:
| a=annotations0 QUESTION
    { 
      let thunk () = a, $endpos in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }
;

wildcard:
| alo=wildcard_head                            { let al, _ = alo in al, None }
| alo=wildcard_head e=EXTENDS r=reference_type
    { 
      let _ = e in
      let al, _ = alo in
      al, Some(mkwb $startpos(e) $endpos (WBextends r))
    }
| alo=wildcard_head s=SUPER   r=reference_type
    { 
      let _ = s in
      let al, _ = alo in
      al, Some(mkwb $startpos(s) $endpos (WBsuper r))
    }
;
wildcard_1:
| alo=wildcard_head GT                           { let al, o = alo in (al, None), o }
| alo=wildcard_head e=EXTENDS r=reference_type_1
    { 
      let _ = e in
      let ep = Loc.to_end_lexpos r.Ast.ty_loc in
      let al, _ = alo in
      (al, Some(mkwb $startpos(e) ep (WBextends r))), ep
    }
| alo=wildcard_head s=SUPER   r=reference_type_1
    { 
      let _ = s in
      let ep = Loc.to_end_lexpos r.Ast.ty_loc in
      let al, _ = alo in
      (al, Some(mkwb $startpos(s) ep (WBsuper r))), ep
    }
;
wildcard_2:
| alo=wildcard_head GT_GT                        { let al, o = alo in (al, None), o }
| alo=wildcard_head e=EXTENDS r=reference_type_2
    { 
      let _ = e in
      let ep = Loc.to_end_lexpos r.Ast.ty_loc in
      let al, _ = alo in
      (al, Some(mkwb $startpos(e) ep (WBextends r))), ep
    }
| alo=wildcard_head s=SUPER   r=reference_type_2
    { 
      let _ = s in
      let ep = Loc.to_end_lexpos r.Ast.ty_loc in
      let al, _ = alo in
      (al, Some(mkwb $startpos(s) ep (WBsuper r))), ep
    }
;
wildcard_3:
| alo=wildcard_head GT_GT_GT                     { let al, o = alo in (al, None), o }
| alo=wildcard_head e=EXTENDS r=reference_type_3
    { 
      let _ = e in
      let ep = Loc.to_end_lexpos r.Ast.ty_loc in
      let al, _ = alo in
      (al, Some(mkwb $startpos(e) ep (WBextends r))), ep
    }
| alo=wildcard_head s=SUPER   r=reference_type_3
    { 
      let _ = s in
      let ep = Loc.to_end_lexpos r.Ast.ty_loc in
      let al, _ = alo in
      (al, Some(mkwb $startpos(s) ep (WBsuper r))), ep
    }
;

reference_type_1:
| r=reference_type GT { r }
| c=class_or_interface_type_spec lt=LT tas=type_argument_list_2 
    {
      let head, a, n = c in
      let ed_pos = Loc.decr_lexpos $endpos in
      let _ = lt in
      let tyargs = mktyargs $startpos(lt) ed_pos tas in
      mktype $startpos ed_pos (TclassOrInterface(head @ [TSapply(a, n, tyargs)]))
    }
;
reference_type_2:
| r=reference_type GT_GT { r }
| c=class_or_interface_type_spec lt=LT tas=type_argument_list_3 
    {  
      let head, a, n = c in
      let ed_pos = Loc.decr_n_lexpos 2 $endpos in
      let _ = lt in
      let tyargs = mktyargs $startpos(lt) ed_pos tas in
      mktype $startpos ed_pos (TclassOrInterface(head @ [TSapply(a, n, tyargs)]))
    }
;
reference_type_3:
| r=reference_type GT_GT_GT { r }
;

type_argument_list:
|                            t=type_argument { [t] }
| l=type_argument_list COMMA t=type_argument { l @ [t] }
;
type_argument_list_1:
|                            t=type_argument_1 { [t] }
| l=type_argument_list COMMA t=type_argument_1 { l @ [t] }
;
type_argument_list_2:
|                            t=type_argument_2 { [t] }
| l=type_argument_list COMMA t=type_argument_2 { l @ [t] }
;
type_argument_list_3:
|                            t=type_argument_3 { [t] }
| l=type_argument_list COMMA t=type_argument_3 { l @ [t] }
;

type_argument:
| r=reference_type { mktyarg $startpos $endpos (TAreferenceType r) }
| aw=wildcard      { mktyarg $symbolstartpos $endpos (TAwildcard aw) }
;
type_argument_1:
| r=reference_type_1 { _mktyarg r.ty_loc (TAreferenceType r) }
| awo=wildcard_1     { let aw, o = awo in mktyarg $symbolstartpos o (TAwildcard aw) }
;
type_argument_2:
| r=reference_type_2 { _mktyarg r.ty_loc (TAreferenceType r) }
| awo=wildcard_2     { let aw, o = awo in mktyarg $symbolstartpos o (TAwildcard aw) }
;
type_argument_3:
| r=reference_type_3 { _mktyarg r.ty_loc (TAreferenceType r) }
| awo=wildcard_3     { let aw, o = awo in mktyarg $symbolstartpos o (TAwildcard aw) }
;


name:
| s=simple_name    { mkname $startpos $endpos (Nsimple(ref NAunknown, s)) }
| q=qualified_name { q }
;

simple_name:
| i=identifier { let _, id = i in id }
;

%inline
qualified_name:
| n=name DOT i=identifier
    { 
      let _, id = i in
      mkname $startpos $endpos (Nqualified(ref NAunknown, n, [], id))
    }
| n=name DOT a=annotations i=identifier
    { 
      check_JLS_level 10
        (fun () ->
          let _, id = i in
          mkname $startpos $endpos (Nqualified(ref NAunknown, n, a, id))
        )
        (fun () -> parse_error $startpos(a) $endpos(a) "dot annotation is available since JLS10")
    }
(*| s=ERROR DOT i=identifier
    { 
      let n = mkerrname $startpos $endpos(s) s in
      let _, id = i in
      mkname $startpos $endpos (Nqualified(ref NAunknown, n, [], id))
    }*)
;


identifier:
| i=IDENTIFIER { i }
;


(***** *****)

compilation_unit:
| u=ordinary_compilation_unit { u }
| u=modular_compilation_unit { u }
;

%inline
ordinary_compilation_unit:
| { mkcu None [] [] }
| dl=declarations
    { 
      let il, tl = partition_declarations dl in
      mkcu None il tl
    }
| p=package_declaration dl=declarations
    { 
      let il, tl = partition_declarations dl in
      mkcu (Some p) il tl
    }
;

declaration:
| i=import_declaration { D_import i }
| t=type_declaration { D_type t }
;

declarations:
|                 d=declaration { [d] }
| dl=declarations d=declaration { dl@[d] }
;

%inline
modular_compilation_unit:
|                  m=module_declaration { mkmcu [] m }
| dl=declarations  m=module_declaration
    { 
      let il, tl = partition_declarations dl in
      begin
        match tl with
        | t::_ -> begin
            if env#keep_going_flag then
              Common.warning_loc t.Ast.td_loc "illegal type declaration(s)"
            else
              parse_error_loc t.Ast.td_loc "illegal type declaration(s)"
        end
        | _ -> ()
      end;
      mkmcu il m
    }
;
module_declaration:
| h=module_declaration_head b=module_body { mkmodule $startpos $endpos h b }
;
module_declaration_head:
| a=annotations0        MODULE n=name
    { 
      check_JLS_level 9
        (fun () -> mkmdh $symbolstartpos $endpos a None n)
        (fun () -> parse_error $startpos $endpos "module-declaration is available since JLS9")
    }
| a=annotations0 o=OPEN MODULE n=name
    { 
      check_JLS_level 9
        (fun () -> mkmdh $symbolstartpos $endpos a (Some o) n)
        (fun () -> parse_error $startpos $endpos "module-declaration is available since JLS9")
    }
;
module_body:
| LBRACE ds=module_directive* RBRACE { mkmb $startpos $endpos ds }
;
module_name:
| n=name { mkmn $startpos $endpos n }
;
module_directive:
| REQUIRES ms=requires_modifier* n=name SEMICOLON
    { 
      check_JLS_level 9
        (fun () -> mkmd $startpos $endpos (MDrequires(ms, n)))
        (fun () -> parse_error $startpos $endpos "requires-directive is available since JLS9")
    }
| EXPORTS n=name SEMICOLON
    { 
      check_JLS_level 9
        (fun () -> mkmd $startpos $endpos (MDexports(n, [])))
        (fun () -> parse_error $startpos $endpos "exports-directive is available since JLS9")
    }
| EXPORTS n=name TO ns=clist(module_name) SEMICOLON
    { 
      check_JLS_level 9
        (fun () -> mkmd $startpos $endpos (MDexports(n, ns)))
        (fun () -> parse_error $startpos $endpos "exports-directive is available since JLS9")
    }
| OPENS n=name SEMICOLON
    { 
      check_JLS_level 9
        (fun () -> mkmd $startpos $endpos (MDopens(n, [])))
        (fun () -> parse_error $startpos $endpos "opens-directive is available since JLS9")
    }
| OPENS n=name TO ns=clist(module_name) SEMICOLON
    { 
      check_JLS_level 9
        (fun () -> mkmd $startpos $endpos (MDopens(n, ns)))
        (fun () -> parse_error $startpos $endpos "opens-directive is available since JLS9")
    }
| USES n=name SEMICOLON
    { 
      check_JLS_level 9
        (fun () -> mkmd $startpos $endpos (MDuses n))
        (fun () -> parse_error $startpos $endpos "uses-directive is available since JLS9")
    }
| PROVIDES n=name WITH_ ns=clist(module_name) SEMICOLON
    { 
      check_JLS_level 9
        (fun () -> mkmd $startpos $endpos (MDprovides(n, ns)))
        (fun () -> parse_error $startpos $endpos "provides-directive is available since JLS9")
    }
;
requires_modifier:
| TRANSITIVE
    { 
      check_JLS_level 9
        (fun () -> mkmod $startpos $endpos Mtransitive)
        (fun () -> parse_error $startpos $endpos "transitive-modifier is available since JLS9")
    }
| STATIC { mkmod $startpos $endpos Mstatic }
;

package_declaration:
| p=_package_declaration { p }
| n=name p=_package_declaration
    { 
      let s = P.name_to_simple_string n in
      if env#keep_going_flag then begin
        parse_warning $startpos(n) $endpos(n) "syntax error: %s" s;
        p
      end
      else
        parse_error $startpos(n) $endpos(n) (sprintf "syntax error: %s" s)
    }
;

%inline
_package_declaration:
| a=annotations0 p=PACKAGE n=name SEMICOLON
    { 
      let pname = P.name_to_simple_string n in
      env#set_current_package_name pname;

      if not env#no_implicit_name_resolution_flag then begin
        let d = env#current_source#file#dirname in
        env#classtbl#add_package ~dir:(env#current_source#tree#get_entry d) pname
      end;

      set_attribute_P_P n;
      let loc =
        match a with
        | [] -> Loc.merge p (get_loc $startpos $endpos)
        | _ -> get_loc $startpos $endpos
      in
      mkpkgdecl loc a n 
    }
;

import_declaration: 
| s=single_type_import_declaration           { s }
| t=type_import_on_demand_declaration        { t }
| s=static_single_type_import_declaration    { s }
| s=static_type_import_on_demand_declaration { s }
(*| s=MARKER { mkerrimpdecl $startpos $endpos s }*)
(*| s=ERROR  { mkerrimpdecl $startpos $endpos s }*)
;

single_type_import_declaration:
| IMPORT n=name SEMICOLON 
    { 
      begin
        try
          let fqn =
            try
              env#resolve_qualified_type_name n
            with _ ->
              P.name_to_simple_string n
          in
          register_identifier_as_typename fqn (rightmost_identifier n);
          set_attribute_PT_T (mkresolved fqn) n;
          register_qname_as_typename n;
        with
          _ ->
            ()(*let sn = P.name_to_simple_string n in
            parse_warning $startpos $endpos "failed to resolve %s" sn*)
      end;
      mkimpdecl $startpos $endpos (IDsingle n)
    }
;

static_single_type_import_declaration:
| IMPORT STATIC n=name DOT i=identifier SEMICOLON
    { 
      let fqn_opt = ref None in
      begin
        try
          let fqn =
            try
              env#resolve_qualified_type_name n
            with
              _ -> P.name_to_simple_string n
          in
          fqn_opt := Some fqn;
          register_identifier_as_typename fqn (rightmost_identifier n);
          set_attribute_PT_T (mkresolved fqn) n;
          register_qname_as_typename n;
        with
          _ ->
            ()(*let sn = P.name_to_simple_string n in
            parse_warning $startpos $endpos "failed to resolve %s" sn*)
      end;
      let _, id = i in
      let sfqn =
        match !fqn_opt with
        | Some x -> x^"."^id
        | _ -> id
      in
      register_identifier_as_static_member sfqn id;
      mkimpdecl $startpos $endpos (IDsingleStatic(n, id)) 
    }
;

type_import_on_demand_declaration:
| IMPORT n=name DOT STAR SEMICOLON 
    { 
      begin
        try
          ignore (env#resolve_qualified_type_name n)
        with
          _ ->
            let sn = P.name_to_simple_string n in
            (*parse_warning $startpos $endpos "failed to resolve %s" sn;*)
            try
              if env#no_implicit_name_resolution_flag then
                raise Not_found;
              let p =
                Filename.concat env#classtbl#get_source_dir#path (Common.pkg_to_path sn)
              in
              env#classtbl#add_package ~dir:(env#current_source#tree#get_entry p) sn
            with
              _ -> env#classtbl#add_api_package sn
      end;
      set_attribute_PT_PT n;
      mkimpdecl $startpos $endpos (IDtypeOnDemand n)
    }
;

static_type_import_on_demand_declaration:
| IMPORT STATIC n=name DOT STAR SEMICOLON 
    { 
      begin
        try
          let fqn =
            try
              env#resolve_qualified_type_name n
            with
              _ -> P.name_to_simple_string n
          in
          register_identifier_as_typename fqn (rightmost_identifier n);
          set_attribute_PT_T (mkresolved fqn) n;
          register_qname_as_typename n;
        with
          _ ->
            ()(*let sn = P.name_to_simple_string n in
            parse_warning $startpos $endpos "failed to resolve %s" sn*)
      end;
      mkimpdecl $startpos $endpos (IDstaticOnDemand n)
    }
;

type_declaration: 
| c=class_declaration     { mktd $startpos $endpos (TDclass c) }
| e=enum_declaration      { mktd $startpos $endpos (TDclass e) }
| r=record_declaration    { mktd $startpos $endpos (TDclass r) } (* JLS16 *)
| i=interface_declaration { mktd $startpos $endpos (TDinterface i) }
| SEMICOLON               { mktd $startpos $endpos TDempty }
| a=aspect_declaration    { mktd $startpos $endpos (TDclass a) }
| m=method_declaration (* orphan method *)
    { 
      if env#keep_going_flag then begin
        let pos_to_str { Lexing.pos_lnum = l;
                         Lexing.pos_bol = b;
                         Lexing.pos_cnum = c;
                         _
                       }
            = Printf.sprintf "%dL,%dC" l (c - b)
        in
        let warn x = parse_warning $startpos $endpos x in
        warn "orphan method declaration";
        let err_opt =
          match env#last_td_end_opt with
          | Some (p, s) -> begin
              warn "last type declaration end: %s (%s)" s (pos_to_str p);
              env#clear_last_td_end;
              Some (mkerrtd p p s)
          end
          | None -> None
        in
        mktd $startpos $endpos (TDorphan(err_opt, m))
      end
      else
        parse_error $startpos $endpos "orphan method declaration"
    }
| m=MARKER { mkerrtd $startpos $endpos m }
| e=ERROR { mkerrtd $startpos $endpos e }
;

%inline
modifiers_opt:
| o=ioption(modifiers) { o }
;

modifiers:
| l=nonempty_list(annotation_or_modifier) { mkmods $startpos $endpos l }
;

%inline
annotation_or_modifier:
| a=annotation     { annot_to_mod a }
| m=adhoc_modifier { mkmod $startpos $endpos m }
| s=ERROR_MOD { mkerrmod $startpos $endpos s }
;

adhoc_modifier:
| PUBLIC       { Mpublic }
| PROTECTED    { Mprotected }
| PRIVATE      { Mprivate }
| STATIC       { Mstatic }
| ABSTRACT     { Mabstract }
| FINAL        { Mfinal }
| NATIVE       { Mnative }
| SYNCHRONIZED { Msynchronized }
| TRANSIENT    { Mtransient }
| VOLATILE     { Mvolatile }
| STRICTFP     { Mstrictfp }
| DEFAULT      { Mdefault }
| SEALED
    { 
      check_JLS_level 17
        (fun () -> Msealed)
        (fun () -> parse_error $startpos $endpos "sealed-modifier is available since JLS17")
    }
| NON_SEALED
    { 
      check_JLS_level 17
        (fun () -> Mnon_sealed)
        (fun () -> parse_error $startpos $endpos "sealed-modifier is available since JLS17")
    }
;

%inline
annotations0:
| (* *)         { [] }
| a=annotations { a }
;

annotations:
| l=nonempty_list(annotation) { l }
(*|               a=annotation { [a] }
| l=annotations a=annotation { l @ [a] }*)
;

annotation:
| AT a=annotation_body { mkannot $startpos $endpos a }
;

annotation_body:
| n=normal_annotation_body         { n }
| m=marker_annotation_body         { m }
| s=single_element_annotation_body { s }
;

normal_annotation_body:
| n=name LPAREN e=element_value_pairs0 RPAREN { Anormal(n, e) }
;

marker_annotation_body:
| n=name { Amarker n }
;

single_element_annotation_body:
| n=name LPAREN e=element_value RPAREN { AsingleElement(n, e) }
;

%inline
element_value_pairs0:
| l=clist0(element_value_pair) { l }
;

element_value_pair:
| i=identifier EQ e=element_value { let _, id = i in mkevp $startpos $endpos (id, e) }
;

element_value:
| a=annotation                      { mkev $startpos $endpos (EVannotation a) }
| e=element_value_array_initializer { mkev $startpos $endpos (EVarrayInit e) }
| c=conditional_expression          { mkev $startpos $endpos (EVconditional c) }
;

element_value_array_initializer:
| LBRACE COMMA                   RBRACE { [] }
| LBRACE e=element_values0       RBRACE { e }
| LBRACE e=element_values0_comma RBRACE { e }
;

%inline
element_values0:
| l=clist0(element_value) { l }
;

%inline
element_values0_comma:
| l=nonempty_list(element_value_comma) { l }
;

%inline
element_value_comma:
| e=element_value COMMA { e }
;

record_declaration_head0:
| m_opt=modifiers_opt RECORD i=identifier
    { 
      let _, id = i in
      let fqn = mkfqn_cls id in
      register_identifier_as_class fqn id;
      begin_scope ~kind:(FKclass(id, ref false)) ();
      m_opt, i
    }
;
record_declaration_head1:
| rh=record_declaration_head0 ts_opt=type_parameters_opt { rh, ts_opt }
;
record_header:
| LPAREN                            RPAREN { [] }
(*| LPAREN rl=clist(record_component) RPAREN { rl }*)
| LPAREN rl=clist(formal_parameter) RPAREN { rl }
;
(*record_component:
| ms=annotations0 t=unann_type                       i=identifier { }
| ms=annotations0 t=unann_type              ELLIPSIS i=identifier { }
| ms=annotations0 t=unann_type a=annotation ELLIPSIS i=identifier { }
;*)
record_declaration_head:
| rh1=record_declaration_head1 h=record_header i_opt=interfaces_opt
    { 
      let rh0, ts_opt = rh1 in
      end_typeparameter_scope ts_opt;
      let ms_opt, (id_loc, id) = rh0 in
      (*begin (* ??? *)
        match ms_opt with
        | Some ms when has_user_defined_annotation ms -> env#set_has_super()
        | _ -> ()
      end;*)
      mkrh $startpos $endpos ms_opt id id_loc ts_opt h i_opt
    }
;
record_declaration:
| rh=record_declaration_head b=record_body
    { 
      check_JLS_level 16
        (fun () -> mkcd $startpos $endpos (CDrecord(rh, b)))
        (fun () -> parse_error $startpos $endpos "record-declaration is available since JLS16")
    }
;

record_body:
| LBRACE c=record_body_declarations0 RBRACE { end_scope(); mkrb $startpos $endpos c }
;

%inline
record_body_declarations0:
| l=list(record_body_declaration) { l }
;

record_body_declaration:
| c=class_body_declaration { mkrbd $startpos $endpos (RBDclass_body_decl c) }
| c=compact_constructor_declaration { mkrbd $startpos $endpos (RBDcompact_ctor_decl c) }
;

compact_constructor_declaration:
| m_opt=modifiers_opt i=identifier cb=constructor_body
    { 
      let _, id = i in
      mkccnd $symbolstartpos $endpos m_opt id cb
    }
;

class_declaration_head0:
| m_opt=modifiers_opt CLASS i=identifier 
    { 
      let _, id = i in
      let fqn = mkfqn_cls id in
      register_identifier_as_class fqn id;
      begin_scope ~kind:(FKclass(id, ref false)) ();
      m_opt, i
    }
;
class_declaration_head1:
| ch=class_declaration_head0 ts_opt=type_parameters_opt { ch, ts_opt }
;
class_declaration_head:
| ch1=class_declaration_head1 s_opt=super_opt i_opt=interfaces_opt p_opt=permits_opt
    { 
      let ch0, ts_opt = ch1 in
      end_typeparameter_scope ts_opt;
      let ms_opt, (id_loc, id) = ch0 in
      (*begin (* ??? *)
        match ms_opt with
        | Some ms when has_user_defined_annotation ms -> env#set_has_super()
        | _ -> ()
      end;*)
      mkch $startpos $endpos ms_opt id id_loc ts_opt s_opt i_opt p_opt
    }
;
class_declaration:
| ch=class_declaration_head b=class_body
    { 
      mkcd $startpos $endpos (CDclass(ch, b))
    }
;

super_ext:
| EXTENDS ct=class_type { env#set_has_super(); mkexc $startpos $endpos ct }
;

%inline
super_opt:
| o=ioption(super_ext) { o }
;

interfaces:
| IMPLEMENTS i=interface_type_list { mkim $startpos $endpos i }
| IMPLEMENTS i=interface_type_list IMPLEMENTS i_=interface_type_list
    { 
      if env#keep_going_flag then begin
        parse_warning $startpos $endpos "odd implements specification";
        mkim $startpos $endpos (ty_list_union i i_)
      end
      else
        parse_error $startpos $endpos "odd implements specification"
    }
;

%inline
interfaces_opt:
| o=ioption(interfaces) { o }
;

%inline
interface_type_list:
| l=clist(interface_type) { l }
;

permits:
| PERMITS tl=type_name_list
    { 
      check_JLS_level 17
        (fun () -> mkpm $startpos $endpos tl)
        (fun () -> parse_error $startpos $endpos "class-permits is available since JLS17")
    }
;

%inline
permits_opt:
| p=ioption(permits) { p }
;

%inline
type_name_list:
| l=clist(name) { l }
;

class_body: 
| LBRACE c=class_body_declarations0 r=RBRACE
    { 
      ignore r;
      end_scope();
      env#set_last_td_end $endpos(r) "}";
      mkcb $startpos $endpos c
    }
;

%inline
class_body_opt:
| o=ioption(class_body) { o }
;

%inline
class_body_declarations0:
| l=list(class_body_declaration) { l }
;

class_body_declaration:
| c=class_member_declaration { c }
| s=static_initializer       { s }
| i=instance_initializer     { i }
| c=constructor_declaration  { mkcbd $startpos $endpos (CBDconstructor c) }
(*| error                      { mkerrcbd $startpos $endpos "" }*)
| s=ERROR                    { mkerrcbd $startpos $endpos s }
;

class_member_declaration:
| f=field_declaration     { mkcbd $startpos $endpos (CBDfield f) }
| m=method_declaration    { m }
| c=class_declaration     { mkcbd $startpos $endpos (CBDclass c) }
| e=enum_declaration      { mkcbd $startpos $endpos (CBDclass e) }
| r=record_declaration    { mkcbd $startpos $endpos (CBDclass r) } (* JLS16 *)
| i=interface_declaration { mkcbd $startpos $endpos (CBDinterface i) }
| SEMICOLON               { mkcbd $startpos $endpos CBDempty }
| s=MARKER                { mkerrcbd $startpos $endpos s }
| a=aspect_declaration    { mkcbd $startpos $endpos (CBDclass a) }
;

enum_declaration_head0:
| m_opt=modifiers_opt ENUM i=IDENTIFIER
    { 
      let _, id = i in
      check_JLS_level 3
        (fun () ->
          register_identifier_as_class (mkfqn_cls id) id;
          begin_scope ~kind:(FKclass(id, ref false)) ();
          m_opt, i
        )
        (fun () -> parse_error $symbolstartpos $endpos "'enum' declaration is available since JLS3")
    }
;
enum_declaration_head:
| eh0=enum_declaration_head0 i_opt=interfaces_opt
    { 
      let ms, (id_loc, id) = eh0 in
      mkch $startpos $endpos ms id id_loc None None i_opt None
    }
;
enum_declaration:
| eh=enum_declaration_head b_opt=enum_body
    { 
      mkcd $startpos $endpos (CDenum(eh, b_opt))
    }
;

enum_body:
| LBRACE                  comma_opt b=enum_body_declarations0 RBRACE
    { end_scope(); mkeb $startpos $endpos [] b }
| LBRACE e=enum_constants comma_opt b=enum_body_declarations0 RBRACE
    { end_scope(); mkeb $startpos $endpos e b } 
;

%inline
comma_opt:
| ioption(COMMA) {}
;


enum_constants:
|                         e=enum_constant { [e] }
| es=enum_constants COMMA e=enum_constant { es @ [e] }
;

enum_constant_head:
| a=annotations0 i=identifier e=enum_arguments_opt          
    { 
      let loc0, id = i in
      register_identifier_as_enumconst (mkfqn id) id;
      let loc =
        match a with
        | [] -> Loc.merge loc0 (get_loc $startpos $endpos)
        | _ -> get_loc $startpos $endpos
      in
      begin_scope();
      (loc, a, id, e)
    }
;

enum_constant:
| x=enum_constant_head
    { 
      let loc, a, id, e = x in
      end_scope();
      mkec loc a id e None
    }
| x=enum_constant_head c=class_body
    { 
      let loc, a, id, e = x in
      mkec loc a id e (Some c)
    }
;

%inline 
enum_arguments_opt:
| (* *)                          { None }
| LPAREN a=argument_list0 RPAREN { Some(mkargs $startpos $endpos a) }
;

enum_body_declarations0:
| (* *)                                { [] }
| s=SEMICOLON c=class_body_declarations0
    { 
      ignore s;
      (mkcbd $startpos $endpos(s) CBDempty) :: c
    }
;

field_declaration:
| m_opt=modifiers_opt t=unann_type v=variable_declarators SEMICOLON 
    { 
      let loc, is_static =
        match m_opt with
        | None -> Loc.merge t.ty_loc (get_loc $symbolstartpos $endpos), false
        | Some ms -> get_loc $symbolstartpos $endpos, has_static ms
      in
      List.iter 
        (fun vd ->
          let (_, id), _ = vd.vd_variable_declarator_id in
          register_identifier_as_field ~is_static id t;
          (*env#register_identifier ~qualify:true id IAfield;*)
          vd.vd_is_local := false;
        ) v;
      Ast.proc_type (register_qname_as_typename ~skip:1) t;
      mkfd loc m_opt t v
    }
;

aspect_declaration_head0:
| m_opt=modifiers_opt ASPECT i=identifier 
    { 
      let _, id = i in
      register_identifier_as_class (mkfqn_cls id) id;
      begin_scope ~kind:(FKclass(id, ref false)) ();
      m_opt, i
    }
;
aspect_declaration_head:
| ah0=aspect_declaration_head0 s_opt=super_opt i_opt=interfaces_opt
    { 
      let ms, (id_loc, id) = ah0 in
      mkch $startpos $endpos ms id id_loc None s_opt i_opt None
    }
;
aspect_declaration:
| ah=aspect_declaration_head b=aspect_body
    { 
      mkcd $startpos $endpos (CDaspect(ah, b))
    }
;
aspect_body:
| LBRACE                             RBRACE { end_scope(); mkabd $startpos $endpos [] }
| LBRACE al=aspect_body_declarations RBRACE { end_scope(); mkabd $startpos $endpos al }
;
aspect_body_declarations:
|                             a=aspect_body_declaration { [a] }
| al=aspect_body_declarations a=aspect_body_declaration { al@[a] }
;
aspect_body_declaration:
| c=class_body_declaration { c }
| p=pointcut_declaration  { mkcbd $startpos $endpos (CBDpointcut p) }
| d=declare_declaration { mkcbd $startpos $endpos (CBDdeclare d) }
;
declare_declaration:
| DECLARE k=identifier COLON c=classname_pattern_expr s=super_ext SEMICOLON
    { 
      let _, kwd = k in 
      mkdd $startpos $endpos (DDparents(kwd, c, Some s, None))
    }
| DECLARE k=identifier COLON c=classname_pattern_expr i=interfaces SEMICOLON
    { 
      let _, kwd = k in
      mkdd $startpos $endpos (DDparents(kwd, c, None, Some i))
    }
| DECLARE k=identifier COLON p=pointcut_expr COLON s=primary SEMICOLON
    { 
      let _, kwd = k in
      mkdd $startpos $endpos (DDmessage(kwd, p, s))
    }
| DECLARE k=identifier COLON p=pointcut_expr SEMICOLON
    { 
      let _, kwd = k in
      mkdd $startpos $endpos (DDsoft(kwd, p))
    }
| DECLARE k=identifier COLON cl=classname_pattern_expr_list SEMICOLON
    { 
      let _, kwd = k in
      mkdd $startpos $endpos (DDprecedence(kwd, cl))
    }
;
classname_pattern_expr_list:
|                                      c=classname_pattern_expr { [c] }
| cl=classname_pattern_expr_list COMMA c=classname_pattern_expr { cl@[c] }
;
pointcut_declaration:
| m_opt=modifiers_opt POINTCUT i=identifier lp=LPAREN f=formal_parameter_list0 rp=RPAREN SEMICOLON
    { 
      let _, id = i in
      mkpcd $symbolstartpos $endpos m_opt id (Loc.merge lp rp) f None
    }
| m_opt=modifiers_opt POINTCUT i=identifier lp=LPAREN f=formal_parameter_list0 rp=RPAREN COLON p=pointcut_expr SEMICOLON
    { 
      let _, id = i in
      mkpcd $symbolstartpos $endpos m_opt id (Loc.merge lp rp) f (Some p)
   }
;
pointcut_expr:
|                         o=or_pointcut_expr { o }
| p=pointcut_expr AND_AND o=or_pointcut_expr { mkpe $startpos $endpos (PEand(p, o)) }
;
or_pointcut_expr:
|                          u=unary_pointcut_expr { u }
| o=or_pointcut_expr OR_OR u=unary_pointcut_expr { mkpe $startpos $endpos (PEor(o, u)) }
;
unary_pointcut_expr:
| p=basic_pointcut_expr { p }
| EXCLAM u=unary_pointcut_expr { mkpe $startpos $endpos (PEnot u) }
;
basic_pointcut_expr:
| LPAREN p=pointcut_expr RPAREN { mkpe $startpos $endpos (PEparen p) }
| WITHIN LPAREN c=classname_pattern_expr RPAREN { mkpe $startpos $endpos (PEwithin c) }
;
classname_pattern_expr:
|                                a=and_classname_pattern_expr { a }
| c=classname_pattern_expr OR_OR a=and_classname_pattern_expr { mkcpe $startpos $endpos (CPEor(c, a)) }
;
and_classname_pattern_expr:
|                                      u=unary_classname_pattern_expr { u }
| a=and_classname_pattern_expr AND_AND u=unary_classname_pattern_expr { mkcpe $startpos $endpos (CPEand(a, u)) }
;
unary_classname_pattern_expr:
| b=basic_classname_pattern_expr { b }
| EXCLAM u=unary_classname_pattern_expr { mkcpe $startpos $endpos (CPEnot u) }
;
basic_classname_pattern_expr:
| n=name_pattern { mkcpe $startpos $endpos (CPEname n) }
| n=name_pattern PLUS { mkcpe $startpos $endpos (CPEnamePlus n) }
| LPAREN c=classname_pattern_expr RPAREN { mkcpe $startpos $endpos (CPEparen c) }
;
name_pattern:
|                        s=simple_name_pattern { s }
| n=name_pattern DOT     s=simple_name_pattern { n^"."^s }
| n=name_pattern DOT_DOT s=simple_name_pattern { n^".."^s }
;
simple_name_pattern:
| STAR         { "*" }
| i=identifier { let _, id = i in id }
;

%inline
variable_declarators:
| l=clist(variable_declarator) { l }
;

variable_declarator: 
| v=variable_declarator_id                            { mkvd $startpos $endpos v None }
| v=variable_declarator_id EQ vi=variable_initializer { mkvd $startpos $endpos v (Some vi) }
(*| v=variable_declarator_id EQ s=ERROR
    { 
      let vi = mkerrvi $startpos(s) $endpos s in
      mkvd $startpos $endpos v (Some vi)
    }*)
;

variable_declarator_id: 
| i=identifier { i, [] }
| v=variable_declarator_id a=annotations0 LBRACKET RBRACKET
    { 
      let thunk () =
        let d = mkad $startpos(a) $endpos a in
        let i, dl = v in
        i, (dl@[d])
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
        (fun () -> parse_error $startpos $endpos(a) "dims annotation is available since JLS8")
      else
        thunk()
    }
;

variable_initializer: 
(*| e=expression        { mkvi $startpos $endpos (VIexpression e) }*)
| e=expr_or_err        { mkvi $startpos $endpos (VIexpression e) }
| a=array_initializer { a }
;

method_declaration:
| mh=method_header b=method_body 
    { 
      end_typeparameter_scope mh.mh_type_parameters;
      (*if mh_is_generic mh then end_scope();*)
      mkcbd $startpos $endpos (CBDmethod(mh, b)) 
    }
;

void:
| VOID { mktype $startpos $endpos (Tvoid) }
;

method_header:
| m_opt=modifiers_opt tv=type_or_void md=method_declarator t_opt=throws_opt
    { 
      let (id, params_loc, params), dim = md in
      let loc =
        match m_opt with
        | None -> Loc.merge tv.ty_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      Ast.proc_type (register_qname_as_typename ~skip:1) tv;
      let _ =
        match m_opt with
        | Some ms when has_static ms -> env#set_is_static()
        | _ -> ()
      in
      mkmh loc m_opt None [] tv id params_loc params dim t_opt
    }
| m_opt=modifiers_opt ts=type_parameters al=annotations0 tv=type_or_void
    md=method_declarator t_opt=throws_opt
    { 
      let (id, params_loc, params), dim = md in
      let loc =
        match m_opt with
        | None -> Loc.merge ts.tps_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      Ast.proc_type (register_qname_as_typename ~skip:1) tv;
      let _ =
        match m_opt with
        | Some ms when has_static ms -> env#set_is_static()
        | _ -> ()
      in
      mkmh loc m_opt (Some ts) al tv id params_loc params dim t_opt
    }
;

%inline
type_or_void:
| j=unann_type { j }
| v=void       { v }
;


method_declarator_head: 
| i=identifier lp=LPAREN 
    { 
      let _, id = i in
      register_identifier_as_method id; 
      begin_scope ~kind:(FKmethod(id, ref false)) ();
      i, lp
    }
;

method_declarator:
| m=method_declarator_head f=formal_parameter_list0 rp=RPAREN 
       { 
         let id, lparen_loc = m in
         let params_loc = Loc.merge lparen_loc rp in
         (id, params_loc, f), []
       }
| m=method_declarator_head i=identifier rp=RPAREN 
       { 
         if env#keep_going_flag then begin
           parse_warning $startpos(rp) $endpos(rp) "identifier expected";
           let id, lparen_loc = m in
           let params_loc = Loc.merge lparen_loc rp in
           let t =
             mktype $startpos(i) $endpos(i)
               (TclassOrInterface([TSname([], mkname $startpos(i) $endpos(i)
                                            (Nsimple(ref NAunknown, (snd i))))]))
           in
           let f = [mkfp (fst i) None t ((Loc.dummy, "_"), []) false] in
           (id, params_loc, f), []
         end
         else
           parse_error $startpos(rp) $endpos(rp) "identifier expected"
       }
| m=method_declarator a=annotations0 LBRACKET RBRACKET
    { 
      let thunk () =
        let d = mkad $startpos(a) $endpos a in
        let md, dl = m in
        md, (dl@[d])
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
        (fun () -> parse_error $startpos $endpos(a) "dims annotation is available since JLS8")
      else
        thunk()
    }
;

%inline
receiver_parameter:
| a=variable_modifiers_opt t=unann_type THIS
    { 
      let loc =
        match a with
        | None -> Loc.merge t.ty_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      mkfp ~receiver:(Some "") loc a t ((Loc.dummy, ""), []) false
    }
| a=variable_modifiers_opt t=unann_type i=identifier DOT THIS
    { 
      let loc =
        match a with
        | None -> Loc.merge t.ty_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      let receiver = Some (let _, id = i in id) in
      mkfp ~receiver loc a t ((Loc.dummy, ""), []) false
    }
;

%inline
formal_parameter_list0:
| l=clist0(formal_parameter)
    { 
      (* TODO: check receiver-paramter and last-formal-parameter *)
      l
    }
;

formal_parameter:
| v=variable_modifiers_opt t=unann_type d=variable_declarator_id 
    { 
      let loc = 
        match v with
        | None -> Loc.merge t.ty_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      let (_, id), _ = d in
      register_identifier_as_parameter id t;
      Ast.proc_type (register_qname_as_typename ~skip:2) t;
      let rec chk_vararg = function
        | [] -> false
        | [d] -> d.Ast.ad_ellipsis
        | d::dl ->
            if d.Ast.ad_ellipsis && dl <> [] then
              let st, ed = Loc.to_lexposs d.Ast.ad_loc in
              parse_error st ed "ellipsis in annotations"
            else
              chk_vararg dl
      in
      let varargs = chk_vararg (get_annot_dims_from_type t) in
      mkfp loc v t d varargs
    }
(*| v=variable_modifiers_opt t=unann_type ELLIPSIS d=variable_declarator_id
    { 
      let loc = 
        match v with
        | None -> Loc.merge t.ty_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      let (_, id), _ = d in
      register_identifier_as_parameter id t;
      Ast.proc_type (register_qname_as_typename ~skip:2) t;
      mkfp loc v t d true 
    }*)
| r=receiver_parameter
    { 
      check_JLS_level 8
        (fun () -> r)
        (fun () -> parse_error $startpos $endpos "receiver parameter is available since JLS8")
    }
;

%inline
variable_modifiers_opt:
| (* *)                { None }
| v=variable_modifiers { Some (mkmods $startpos $endpos v) }
;

%inline
variable_modifiers:
| l=nonempty_list(variable_modifier) { l }
;

variable_modifier:
| FINAL        { mkmod $startpos $endpos Mfinal }
| a=annotation { mkmod $startpos $endpos (Mannotation a) }
;

%inline 
throws_opt:
| o=ioption(throws) { o }
;

throws:
| THROWS c=class_type_list { mkth $startpos $endpos c }
| THROWS c=class_type_list THROWS c_=class_type_list
    { 
      if env#keep_going_flag then begin
        parse_warning $startpos $endpos "odd throws specification";
        mkth $startpos $endpos (ty_list_union c c_)
      end
      else
        parse_error $startpos $endpos "odd throws specification"
    }
;

%inline
class_type_list:
| l=clist(class_type) { l }
;

method_body:
| b=block   { end_scope(); Some b }
| SEMICOLON { end_scope(); None }
;

static_initializer:
| STATIC b=block { mkcbd $startpos $endpos (CBDstaticInitializer b) }
;

instance_initializer:
| b=block { mkcbd $startpos $endpos (CBDinstanceInitializer b) }
;

constructor_declaration:
| m_opt=modifiers_opt ts_opt=type_parameters_opt c=constructor_declarator t_opt=throws_opt cb=constructor_body
    { 
      end_typeparameter_scope ts_opt;
      let cloc, sn, params_loc, params = c in
      let loc = 
        match m_opt with
        | None -> begin
            match ts_opt with
            | Some ts -> Loc.merge ts.tps_loc (get_loc $symbolstartpos $endpos)
            | None ->  Loc.merge cloc (get_loc $symbolstartpos $endpos)
        end
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      mkcnd loc m_opt ts_opt sn params_loc params t_opt cb
    }
;

constructor_declarator_head:
| s=simple_name lp=LPAREN 
    { 
      register_identifier_as_constructor s; 
      begin_scope(); 
      s, lp 
    }
;

constructor_declarator:
| c=constructor_declarator_head f=formal_parameter_list0 rp=RPAREN 
    { 
      let n, lparen_loc = c in
      let params_loc = Loc.merge lparen_loc rp in
      get_loc $startpos $endpos, n, params_loc, f 
    }
;

constructor_body:
| LBRACE e_opt=ioption(explicit_constructor_invocation) b=loption(block_statements) RBRACE 
    { 
      end_scope(); 
      mkcnb $startpos $endpos e_opt b 
    }
;

this:
| THIS { get_loc $startpos $endpos }
;

super:
| SUPER { get_loc $startpos $endpos }
;

explicit_constructor_invocation:
| this a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIthis(None, a)) }

| t=type_arguments this a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIthis(Some t, a)) }

| super a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIsuper(None, a)) }

| t=type_arguments super a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIsuper(Some t, a)) }

| p=primary DOT super a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIprimary(p, None, a)) }

| p=primary DOT t=type_arguments super a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIprimary(p, Some t, a)) }

| n=name DOT super a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIname(n, None, a)) }

| n=name DOT t=type_arguments super a=arguments SEMICOLON 
    { mkeci $startpos $endpos (ECIname(n, Some t, a)) }
;

%inline
arguments:
| lp=LPAREN a=argument_list0 rp=RPAREN { _mkargs (Loc.merge lp rp) a }
;

interface_declaration:
| n=normal_interface_declaration { n }
| a=annotation_type_declaration  { a }
;

normal_interface_declaration_head0:
| m_opt=modifiers_opt INTERFACE i=identifier 
    { 
      let _, id = i in
      register_identifier_as_interface (mkfqn_cls id) id; 
      begin_scope ~kind:(FKclass(id, ref false)) ();
      m_opt, id
    }
;
normal_interface_declaration_head1:
| h0=normal_interface_declaration_head0 ts_opt=type_parameters_opt { h0, ts_opt }
;
normal_interface_declaration_head:
| h1=normal_interface_declaration_head1 e_opt=extends_interfaces_opt p_opt=permits_opt
    { 
      let h0, ts_opt = h1 in
      end_typeparameter_scope ts_opt;
      let ms, id = h0 in
      mkifh $startpos $endpos ms id ts_opt e_opt p_opt
    }
;
normal_interface_declaration:
| h=normal_interface_declaration_head b=interface_body
    { 
      mkifd $startpos $endpos (IFDnormal(h, b))
    }
;

annotation_type_declaration_head:
| m_opt=modifiers_opt AT__INTERFACE INTERFACE i=identifier
    { 
      let _, id = i in
      register_identifier_as_interface (mkfqn_cls id) id;
      begin_scope ~kind:(FKclass(id, ref false)) ();
      mkifh $startpos $endpos m_opt id None None None
    }
;

annotation_type_declaration:
| h=annotation_type_declaration_head b=annotation_type_body
    { 
      mkifd $startpos $endpos (IFDannotation(h, b))
    }
;

annotation_type_body:
| LBRACE a=annotation_type_member_declarations0 RBRACE { end_scope(); mkatb $startpos $endpos a }
;

%inline
annotation_type_member_declarations0:
| l=list(annotation_type_member_declaration) { l }
;

annotation_type_member_declaration:
| c=constant_declaration { mkatmd $startpos $endpos (ATMDconstant c) }
| m_opt=modifiers_opt j=unann_type i=identifier LPAREN RPAREN a=ann_dims0 d=default_value_opt SEMICOLON 
    { 
      let loc = 
        match m_opt with
        | None -> Loc.merge j.ty_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      let _, id = i in
      _mkatmd loc (ATMDelement(m_opt, j, id, a, d))
    }
| c=class_declaration     { _mkatmd c.cd_loc (ATMDclass c)  }
| e=enum_declaration      { _mkatmd e.cd_loc (ATMDclass e) }
| i=interface_declaration { _mkatmd i.ifd_loc (ATMDinterface i) }
| SEMICOLON               { mkatmd $startpos $endpos ATMDempty }
;

default_value_opt:
| d_opt=ioption(default_value) { d_opt }
;

default_value:
| DEFAULT e=element_value { e }
;

%inline
ann_dims0:
| (* *)      { [] }
| a=ann_dims { a }
;

ann_dims:
| l=nonempty_list(ann_dim) { l }
(*|            a=ann_dim { [a] }
| d=ann_dims a=ann_dim { d @ [a] }*)
;

ann_dim:
| a=annotations0 LBRACKET RBRACKET
    { 
      let thunk () = mkad $symbolstartpos $endpos a in
      if List.length a > 0 then
        check_JLS_level 8 thunk
        (fun () -> parse_error $startpos $endpos(a) "dims annotation is available since JLS8")
      else
        thunk()
    }
| a=annotations0 ELLIPSIS
    { 
      let thunk () = mkad ~ellipsis:true $symbolstartpos $endpos a in
      if List.length a > 0 then
        check_JLS_level 8 thunk
        (fun () -> parse_error $startpos $endpos(a) "ellipsis annotation is available since JLS8")
      else
        thunk()
    }
;

extends_interfaces_opt:
| (* *)                { None }
| e=extends_interfaces { Some(mkexi $startpos $endpos e) }
;

%inline
extends_interfaces:
| EXTENDS l=clist(interface_type) { env#set_has_super(); l }
;

interface_body:
| LBRACE i=interface_member_declarations0 RBRACE { end_scope(); mkib $startpos $endpos i }
;

%inline
interface_member_declarations0:
| l=list(interface_member_declaration) { l }
;

interface_member_declaration:
| c=constant_declaration         { _mkimd c.fd_loc (IMDconstant c) }
| a=interface_method_declaration { _mkimd a.amd_loc (IMDinterfaceMethod a) }
| c=class_declaration            { _mkimd c.cd_loc (IMDclass c) }
| e=enum_declaration             { _mkimd e.cd_loc (IMDclass e) }
| i=interface_declaration        { _mkimd i.ifd_loc (IMDinterface i) }
| SEMICOLON                      { mkimd $startpos $endpos IMDempty }
;

%inline
constant_declaration:
| f=field_declaration { f }
;

interface_method_declaration:
| mh=method_header b=method_body
    { 
      if mh_is_generic mh then end_scope();
      let ms = get_modifiers_from_mh mh in
      List.iter
        (fun m ->
          match m.m_desc with
          | Mdefault | Mstatic -> begin
              check_JLS_level 8
                (fun () -> ())
                (fun () ->
                  parse_error $startpos (Loc.to_end_lexpos m.Ast.m_loc)
                    "static or default interface method is available since JLS8")
          end
          | _ -> ()
        ) ms;
      List.iter
        (fun m ->
          match m.m_desc with
          | Mprivate -> begin
              check_JLS_level 9
                (fun () -> ())
                (fun () ->
                  parse_error $startpos (Loc.to_end_lexpos m.Ast.m_loc)
                    "private interface method is available since JLS9")
          end
          | _ -> ()
        ) ms;
      let loc = Loc.merge mh.mh_loc (get_loc $startpos $endpos) in
      mkimed loc mh b
    }
;

array_initializer:
| LBRACE                         ioption(COMMA) RBRACE { mkvi $startpos $endpos (VIarray []) }
| LBRACE v=variable_initializers ioption(COMMA) RBRACE
    { mkvi $startpos $endpos (VIarray (List.rev v)) }
;

variable_initializers:
|                                v=variable_initializer { [v] }
| vs=variable_initializers COMMA v=variable_initializer { v::vs }
;

block: 
| LBRACE b=block_statements0 RBRACE { mkb $startpos $endpos b }
;

%inline
block_statements0: 
| (* *)              { [] }
| b=block_statements { b }
;

%inline
block_statements: 
| l=nonempty_list(block_statement) { l }
;

block_statement: 
| l=local_variable_declaration_statement { l }
| c=class_declaration                    { mkbs $startpos $endpos (BSclass c) }
| s=statement                            { mkbs $startpos $endpos (BSstatement s) }
| e=enum_declaration                     { mkbs $startpos $endpos (BSclass e) }
(*| error                                  { mkerrbs $symbolstartpos $endpos "" }*)
| s=ERROR                                { mkerrbs $startpos $endpos s }
| s=MARKER                               { mkerrbs $startpos $endpos s }
| s=BLOCK_STMT                           { s }
;

local_variable_declaration_statement:
| l=local_variable_declaration SEMICOLON { mkbs $startpos $endpos (BSlocal l) }
;

local_variable_declaration:
| m_opt=modifiers_opt t=unann_type v=variable_declarators 
    { 
       List.iter
       (fun vd ->
         let (_, id), _ = vd.vd_variable_declarator_id in
         register_identifier_as_variable id t;
         vd.vd_is_local := true;
       ) v;
      mklvd $symbolstartpos $endpos m_opt t v
    }
;

statement:
| s=statement_without_trailing_substatement { s }
| l=labeled_statement                       { l }
| i=if_then_statement                       { i }
| i=if_then_else_statement                  { i }
| w=while_statement                         { w }
| f=for_statement                           { f }
| e=enhanced_for_statement                  { e }
;

statement_no_short_if:
| s=statement_without_trailing_substatement { s }
| l=labeled_statement_no_short_if           { l }
| i=if_then_else_statement_no_short_if      { i }
| w=while_statement_no_short_if             { w }
| f=for_statement_no_short_if               { f }
| e=enhanced_for_statement_no_short_if      { e }
;

statement_without_trailing_substatement:
| b=block                  { mkstmt $startpos $endpos (Sblock b) }
| e=empty_statement        { e }
| e=expression_statement   { e }
| s=switch_statement       { s }
| d=do_statement           { d }
| b=break_statement        { b }
| c=continue_statement     { c }
| r=return_statement       { r }
| s=synchronized_statement { s }
| t=throw_statement        { t }
| t=try_statement          { t }
| y=yield_statement        { y }
| a=assert_statement       { a }
| s=STMT                   { s }
| s=ERROR_STMT             { mkerrstmt $startpos $endpos s }
;

empty_statement:
| SEMICOLON { mkstmt $startpos $endpos Sempty }
;

labeled_statement_head:
| i=identifier COLON 
    { 
      let _, id = i in
      register_identifier_as_label id; 
      begin_scope(); 
      id
    }
;

labeled_statement:
| l=labeled_statement_head s=statement { end_scope(); mkstmt $startpos $endpos (Slabeled(l, s)) }
;

labeled_statement_no_short_if:
| l=labeled_statement_head s=statement_no_short_if 
    { end_scope(); mkstmt $startpos $endpos (Slabeled(l, s)) }
;

expression_statement:
| s=statement_expression SEMICOLON { mkstmt $startpos $endpos (Sexpression s) }
(*| error                SEMICOLON { mkerrstmt $startpos $endpos } *)
;

statement_expression:
| a=assignment                         { mkstmtexpr $startpos $endpos (SEassignment a) }
| p=pre_increment_expression           { mkstmtexpr $startpos $endpos (SEpreIncrement p) }
| p=pre_decrement_expression           { mkstmtexpr $startpos $endpos (SEpreDecrement p) }
| p=post_increment_expression          { mkstmtexpr $startpos $endpos (SEpostIncrement p) }
| p=post_decrement_expression          { mkstmtexpr $startpos $endpos (SEpostDecrement p) }
| m=method_invocation                  { mkstmtexpr $startpos $endpos (SEmethodInvocation m) }
| c=class_instance_creation_expression { mkstmtexpr $startpos $endpos (SEclassInstanceCreation c) }
;

if_then_statement:
| IF LPAREN e=expr_or_err RPAREN s=statement { mkstmt $startpos $endpos (SifThen(e, s)) }
;

if_then_else_statement:
| IF LPAREN e=expr_or_err RPAREN s0=statement_no_short_if x=ELSE s1=statement
    { 
      let _ = x in
      let esp = $startpos(x) in
      let eep = $endpos(x) in
      mkstmt ~esp ~eep $startpos $endpos (SifThenElse(e, s0, s1))
    }
;

if_then_else_statement_no_short_if:
| IF LPAREN e=expr_or_err RPAREN s0=statement_no_short_if x=ELSE s1=statement_no_short_if
    { 
      let _ = x in
      let esp = $startpos(x) in
      let eep = $endpos(x) in
      mkstmt ~esp ~eep $startpos $endpos (SifThenElse(e, s0, s1))
    }
(*
| IF LPAREN e=expression RPAREN er=error                 ELSE s=statement_no_short_if 
    { 
      let err = mkerrstmt $startpos(er) $endpos(er) in
      let _ = er in
      mkstmt $startpos $endpos (SifThenElse(e, err, s))
    }
*)
;

switch_statement:
| SWITCH LPAREN e=expr_or_err RPAREN s=switch_block { mkstmt $startpos $endpos (Sswitch(e, s)) }
;

switch_block:
| LBRACE                                                 RBRACE { mksb $startpos $endpos [] [] }
| LBRACE                                 s=switch_labels RBRACE { mksb $startpos $endpos [(s, [])] [] }
| LBRACE g=switch_block_statement_groups                 RBRACE { mksb $startpos $endpos (List.rev g) [] }
| LBRACE g=switch_block_statement_groups s=switch_labels RBRACE { mksb $startpos $endpos (List.rev ((s, [])::g)) [] }
| LBRACE r=switch_rules RBRACE { mksb $startpos $endpos [] (List.rev r) } (* JLS14 *)
;

switch_rules:
|                 r=switch_rule { [r] }
| rs=switch_rules r=switch_rule { r :: rs }
;

switch_rule_label:
| CASE cl=clist(constant_expression) MINUS_GT__CASE
    { 
      check_JLS_level 14
        (fun () -> mksrl $startpos $endpos (SLconstant cl))
        (fun () -> parse_error $startpos $endpos "switch-rule is available since JLS14")
    }
| DEFAULT MINUS_GT
    { 
      check_JLS_level 14
        (fun () -> mksrl $startpos $endpos SLdefault)
        (fun () -> parse_error $startpos $endpos "switch-rule is available since JLS14")
    }
;

switch_rule:
| s=switch_rule_label e=expression SEMICOLON { s, mksrb $startpos(e) $endpos (SRBexpr e) }
| s=switch_rule_label b=block { s, mksrb $startpos(b) $endpos (SRBblock b)  }
| s=switch_rule_label t=throw_statement { s, mksrb $startpos(t) $endpos (SRBthrow t) }
;

switch_block_statement_groups:
|                                  s=switch_block_statement_group { [s] }
| ss=switch_block_statement_groups s=switch_block_statement_group { s :: ss }
;

switch_block_statement_group: 
| s=switch_labels b=block_statements { s, b }
;

%inline
switch_labels:
| l=nonempty_list(switch_label) { l }
;

switch_label: 
| CASE cl=clist(constant_expression) COLON
    { 
      let thunk () = mksl $startpos $endpos (SLconstant cl) in
      if List.length cl > 1 then begin
        check_JLS_level 14 thunk
          (fun () -> parse_error $startpos $endpos "multi-switch-label is available since JLS14")
      end
      else
        thunk()
    }
| DEFAULT__COLON COLON { mksl $startpos $endpos SLdefault }
;

while_statement:
| WHILE LPAREN e=expr_or_err RPAREN s=statement { mkstmt $startpos $endpos (Swhile(e, s)) }
;  

while_statement_no_short_if:
| WHILE LPAREN e=expr_or_err RPAREN s=statement_no_short_if { mkstmt $startpos $endpos (Swhile(e, s)) }
;

do_statement:
| DO s=statement WHILE LPAREN e=expression RPAREN SEMICOLON { mkstmt $startpos $endpos (Sdo(s, e)) }
(*
| DO er=error    WHILE LPAREN e=expression RPAREN SEMICOLON 
     { 
       let err = mkerrstmt $startpos(er) $endpos(er) in
       let _ = er in
       mkstmt $startpos $endpos (Sdo(err, e))
     }
*)
;

for_statement_head:
| FOR LPAREN { begin_scope() }
;

javatype_vdid:
| j=unann_type d=variable_declarator_id
    { 
      let (_, id), _ = d in
      register_identifier_as_variable id j;
      mkfp (get_loc $startpos $endpos) None j d false
    }
;

enhanced_for_statement:
| for_statement_head j=javatype_vdid COLON e=expr_or_err RPAREN s=statement
    { end_scope(); mkstmt $startpos $endpos (SforEnhanced(j, e, s)) }

| for_statement_head m=modifiers j=javatype_vdid COLON e=expr_or_err RPAREN s=statement
    { end_scope();
      let fp0 = j in
      let fp =
        mkfp (Loc.merge m.Ast.ms_loc fp0.Ast.fp_loc) (Some m)
          fp0.Ast.fp_type fp0.Ast.fp_variable_declarator_id false
      in
      mkstmt $startpos $endpos (SforEnhanced(fp, e, s))
    }
;

enhanced_for_statement_no_short_if:
| for_statement_head j=javatype_vdid COLON e=expr_or_err RPAREN s=statement_no_short_if
    { end_scope(); mkstmt $startpos $endpos (SforEnhanced(j, e, s)) }

| for_statement_head m=modifiers j=javatype_vdid COLON e=expr_or_err RPAREN s=statement_no_short_if
    { end_scope();
      let fp0 = j in
      let fp =
        mkfp (Loc.merge m.Ast.ms_loc fp0.Ast.fp_loc) (Some m)
          fp0.Ast.fp_type fp0.Ast.fp_variable_declarator_id false
      in
      mkstmt $startpos $endpos (SforEnhanced(fp, e, s))
    }
;


for_statement:
| for_statement_head i_opt=for_init_opt SEMICOLON e_opt=expression_opt SEMICOLON u=for_update0 RPAREN s=statement 
    { end_scope(); mkstmt $startpos $endpos (Sfor(i_opt, e_opt, u, s)) }
;

for_statement_no_short_if:
| for_statement_head i_opt=for_init_opt SEMICOLON e_opt=expression_opt SEMICOLON u=for_update0 RPAREN s=statement_no_short_if
    { end_scope(); mkstmt $startpos $endpos (Sfor(i_opt, e_opt, u, s)) }
;

for_init_opt:
| o=ioption(for_init) { o }
;

for_init: 
| s=statement_expression_list   { mkfi $startpos $endpos (FIstatement s)}
| l=local_variable_declaration  { mkfi $startpos $endpos (FIlocal l) }
;

for_update0:
| (* *)        { [] }
| f=for_update { f }
;

for_update:
| s=statement_expression_list { s }
;

%inline
statement_expression_list:
| l=clist(statement_expression) { l }
;

%inline
identifier_opt:
| (* *)        { None }
| i=identifier { let _, id = i in Some id }
;

break_statement:
| BREAK i=identifier_opt SEMICOLON { mkstmt $startpos $endpos (Sbreak i) }
(*| BREAK error SEMICOLON { mkerrstmt $startpos $endpos } *)
;

continue_statement:
| CONTINUE i=identifier_opt SEMICOLON { mkstmt $startpos $endpos (Scontinue i) }
(*| CONTINUE error SEMICOLON { mkerrstmt $startpos $endpos } *)
;

return_statement:
| RETURN e_opt=expression_opt SEMICOLON { mkstmt $startpos $endpos (Sreturn e_opt) }
;

throw_statement:
| THROW e=expr_or_err SEMICOLON { mkstmt $startpos $endpos (Sthrow e) }
;

synchronized_statement:
| SYNCHRONIZED LPAREN e=expr_or_err RPAREN b=block { mkstmt $startpos $endpos (Ssynchronized(e, b)) }
;

try_head:
| TRY { begin_scope() }
;
try_block:
| try_head r_opt=resource_spec_opt b=block { end_scope(); r_opt, b }
;
try_statement:
| tb=try_block c=catches           { let r_opt, b = tb in mkstmt $startpos $endpos (Stry(r_opt, b, Some c, None)) }
| tb=try_block           f=finally { let r_opt, b = tb in mkstmt $startpos $endpos (Stry(r_opt, b, None, Some f)) }
| tb=try_block c=catches f=finally { let r_opt, b = tb in mkstmt $startpos $endpos (Stry(r_opt, b, Some c, Some f)) }
| tb=try_block                     { let r_opt, b = tb in mkstmt $startpos $endpos (Stry(r_opt, b, None, None)) }
;

yield_statement:
| YIELD e=expression SEMICOLON
    { 
      check_JLS_level 14
        (fun () -> mkstmt $startpos $endpos (Syield e))
        (fun () -> parse_error $startpos $endpos "yield-statement is available since JLS14")
    }
;

%inline
resource_spec_opt:
| r_opt=ioption(resource_spec) { r_opt }
;

resource_spec:
| LPAREN rl=resource_list ioption(SEMICOLON) RPAREN
    { 
      check_JLS_level 7
        (fun () -> mkresspec $symbolstartpos $endpos rl)
        (fun () -> parse_error $startpos $endpos "resource-spec is available since JLS7")
    }
;

resource_list:
|                           r=resource { [r] }
| l=resource_list SEMICOLON r=resource { l @ [r] }
;

resource:
| l=local_variable_declaration { mkres $startpos $endpos (RlocalVarDecl l)}
| f=field_access
    { 
      check_JLS_level 9
        (fun () -> mkres $startpos $endpos (RfieldAccess f))
        (fun () -> parse_error $startpos $endpos "variable-access is available since JLS9")
    }
| n=name
    { 
      check_JLS_level 9
        (fun () -> mkres $startpos $endpos (Rname n))
        (fun () -> parse_error $startpos $endpos "variable-access is available since JLS9")
    }
;

%inline
catches:
| l=nonempty_list(catch_clause) { l }
;

catch_clause_header:
| CATCH { begin_scope() }

catch_formal_parameter:
| ms_opt=variable_modifiers_opt tl=catch_type d=variable_declarator_id
    {
      let loc = 
        match ms_opt with
        | None -> Loc.merge (List.hd tl).ty_loc (get_loc $symbolstartpos $endpos)
        | Some _ -> get_loc $symbolstartpos $endpos
      in
      let (_, id), _ = d in
      List.iter (register_identifier_as_parameter id) tl;
      mkcfp loc ms_opt tl d
    }
;

catch_type:
|                 t=unann_class_type { [t] }
| l=catch_type OR t=class_type       { l @ [t] }
;

catch_clause: 
| catch_clause_header LPAREN f=catch_formal_parameter RPAREN b=block 
    { end_scope(); mkcatch $startpos $endpos f b }
;

finally:
| FINALLY b=block { mkfinally $startpos $endpos b }
;


%inline
expr_or_err:
| e=expression { e }
(*| error        { mkerrexpr $startpos $endpos }*)
| s=ERROR { mkerrexpr $startpos $endpos s }
;

%inline
colon__expr:
| COLON e=expr_or_err { e }
;

assert_statement:
| ASSERT b=expression e_opt=ioption(colon__expr) SEMICOLON
    { 
      let lab =
        match e_opt with
        | Some e -> Sassert2(b, e)
        | None   -> Sassert1 b
      in
      check_JLS_level 3
        (fun () -> mkstmt $startpos $endpos lab)
        (fun () -> parse_error $startpos $endpos "assert statement is available since JLS3")
    }
;


primary:
| p=primary_no_new_array  { p }
| a=array_creation_init   { mkprim $startpos $endpos (ParrayCreationExpression a) }
| a=array_creation_noinit { mkprim $startpos $endpos (ParrayCreationExpression a) }
(*| error                 { mkerrprim $startpos $endpos } *)
;

primary_no_new_array:
| l=literal                            { mkprim $startpos $endpos (Pliteral l) }
| this                                 { mkprim $startpos $endpos Pthis }
| LPAREN n=name          RPAREN        { mkprim $startpos $endpos (Pparen(_name_to_expr n.n_loc n)) }
| LPAREN e=expression_nn RPAREN        { mkprim $startpos $endpos (Pparen e) }

(*| LPAREN error           RPAREN        { mkerrprim $startpos $endpos }*)

| c=class_instance_creation_expression { mkprim $startpos $endpos (PclassInstanceCreation c) }
| f=field_access       { mkprim $startpos $endpos (PfieldAccess f) }
| m=method_invocation  { mkprim $startpos $endpos (PmethodInvocation m) }
| a=array_access       { mkprim $startpos $endpos (ParrayAccess a) }
| n=name DOT this      { register_qname_as_typename n; mkprim $startpos $endpos (PqualifiedThis n) }
| n=name DOT CLASS     { register_qname_as_typename n; mkprim $startpos $endpos (PclassLiteral (name_to_ty [] n)) }
| n=name d=ann_dims DOT CLASS 
    { 
      register_qname_as_typename n;
      let ty = _mkty (Loc.merge n.n_loc (Xlist.last d).Ast.ad_loc) (Tarray(name_to_ty [] n, d)) in
      mkprim $startpos $endpos (PclassLiteral ty) 
    }
| p=unann_primitive_type        DOT CLASS { mkprim $startpos $endpos (PclassLiteral p) }

| p=unann_primitive_type d=ann_dims DOT CLASS 
    { 
      let ty = _mkty (Loc.merge p.ty_loc (Xlist.last d).Ast.ad_loc) (Tarray(p, d)) in
      mkprim $startpos $endpos (PclassLiteral ty) 
    }

| void DOT CLASS { mkprim $startpos $endpos PclassLiteralVoid }

| r=method_reference
    { 
      check_JLS_level 8
        (fun () -> mkprim $startpos $endpos (PmethodReference r))
        (fun () -> parse_error $startpos $endpos "method reference is available since JLS8")
    }
;

method_reference:
| n=name COLON_COLON tas_opt=type_arguments_opt i=identifier
    { 
      begin
        try
          env#reclassify_identifier(leftmost_of_name n);
        with
          Not_found -> ()
      end;
      let _, id = i in
      mkmr $startpos $endpos (MRname(n, tas_opt, id))
    }
| p=primary COLON_COLON tas_opt=type_arguments_opt i=identifier
    { 
      let _, id = i in
      mkmr $startpos $endpos (MRprimary(p, tas_opt, id))
    }
| SUPER            COLON_COLON tas_opt=type_arguments_opt i=identifier
    { 
      let _, id = i in
      mkmr $startpos $endpos (MRsuper(tas_opt, id))
    }
| n=name DOT SUPER COLON_COLON tas_opt=type_arguments_opt i=identifier
    { 
      register_qname_as_typename n;
      let _, id = i in
      mkmr $startpos $endpos (MRtypeSuper(n, tas_opt, id))
    }
(*| n=name           COLON_COLON tas_opt=type_arguments_opt NEW
    { 
      register_qname_as_typename n;
      mkmr $startpos $endpos (MRtypeNew(n, tas_opt))
    }*)
| p=unann_primitive_type d=ann_dims0 COLON_COLON tas_opt=type_arguments_opt NEW
    { 
      let ty =
        match d with
        | [] -> p
        | l -> _mkty (Loc.merge p.ty_loc (Xlist.last l).Ast.ad_loc) (Tarray(p, d))
      in
      mkmr $startpos $endpos (MRtypeNew(ty, tas_opt))
    }
| n=name d=ann_dims0 COLON_COLON tas_opt=type_arguments_opt NEW
    { 
      let ty =
        match d with
        | [] -> name_to_ty [] n
        | l -> _mkty (Loc.merge n.n_loc (Xlist.last l).Ast.ad_loc) (Tarray(name_to_ty [] n, d))
      in
      register_qname_as_typename n;
      mkmr $startpos $endpos (MRtypeNew(ty, tas_opt))
    }
;

class_instance_creation_head:
| NEW                  c=class_or_interface_type { begin_scope(); None, c }
| NEW t=type_arguments c=class_or_interface_type { begin_scope(); Some t, c }
;

class_instance_creation_head_qualified:
| p=primary DOT NEW t=type_arguments_opt { begin_scope(); Some p, None, t }
| n=name    DOT NEW t=type_arguments_opt { begin_scope(); None, Some n, t }
;

class_instance_creation_expression: 
| c=class_instance_creation_head a=arguments cb=class_body_opt
    { 
      let tyargs, ty = c in
      begin 
        match cb with
        | None -> end_scope()
        | _ -> ()
      end;
      mkcic $startpos $endpos (CICunqualified(tyargs, ty, a, cb))
    }

| c=class_instance_creation_head_qualified i=identifier 
    t=type_arguments_opt a=arguments cb=class_body_opt
    { 
      let _, id = i in
      let po, no, tyargs = c in
      let _ =
        match t with
        | Some tas when List.length tas.tas_type_arguments = 0 -> begin
            if cb = None then
              check_JLS_level 7
                (fun () -> ())
                (fun () ->
                  parse_error $startpos(t) $endpos(t)
                    "diamond instance creation is available since JLS7")
            else
              check_JLS_level 9
                (fun () -> ())
                (fun () ->
                  parse_error $startpos(t) $endpos(t)
                    "diamond anonymous instance creation is available since JLS9")
        end
        | _ -> ()
      in
      let cic =
        match po, no with
        | Some p, None ->
            CICqualified(p, tyargs, id, t, a, cb)
        | None, Some n ->
            CICnameQualified(n, tyargs, id, t, a, cb)
        | _ -> assert false
      in
      begin 
        match cb with
        | None -> end_scope()
        | _ -> ()
      end;
      mkcic $startpos $endpos cic
    }
;

%inline
argument_list0:
(*| l=clist0(expression) { l }*)
| l=clist0(expr_or_err) { l }
;

array_creation_noinit:
| NEW p=primitive_type          d=dim_exprs             { ACEtype(p, List.rev d, []) }
| NEW c=class_or_interface_type d=dim_exprs             { ACEtype(c, List.rev d, []) }
| NEW p=primitive_type          d=dim_exprs dm=ann_dims { ACEtype(p, List.rev d, dm) }
| NEW c=class_or_interface_type d=dim_exprs dm=ann_dims { ACEtype(c, List.rev d, dm) }
;

array_creation_init:
| NEW p=primitive_type          d=ann_dims a=array_initializer { ACEtypeInit(p, d, [a]) }
| NEW c=class_or_interface_type d=ann_dims a=array_initializer { ACEtypeInit(c, d, [a]) }
;

dim_exprs:
|              d=dim_expr { [d] }
| ds=dim_exprs d=dim_expr { d :: ds }
;

dim_expr:
| LBRACKET e=expression RBRACKET { mkde $startpos $endpos e }
;

(*%inline
dims_opt:
| o=ioption(dims) { o }
;

dims:
|        LBRACKET RBRACKET { 1, get_loc $startpos $endpos }
| d=dims LBRACKET RBRACKET { (fst d) + 1, get_loc $startpos $endpos }
;*)

field_access:
| p=primary DOT           i=identifier 
     { 
       let _, id = i in 
       FAprimary(p, id) 
     }
(*
| e=error   DOT           i=identifier
     {
      let err = mkerrprim $startpos(e) $endpos(e) in
      let _ = e in
      let _, id = i in FAprimary(err, id)
     }
*)
| super     DOT           i=identifier { let _, id = i in FAsuper id }
| n=name    DOT super DOT i=identifier 
     { 
       register_qname_as_typename n;
       let _, id = i in
       set_attribute_PT_T (env#resolve n) n;
       register_qname_as_typename n;
       FAclassSuper(n, id) 
     }
;

method_invocation:
| n=name a=arguments
    { 
      set_name_attribute NAmethod n;
      register_qname_as_method n;
      if is_local_name n then begin
        mkmi $startpos $endpos (MImethodName(n, a))
      end
      else if
        env#partial_name_resolution_flag &&
        (
         Ast.is_simple n ||
         not (is_local_name ~force:true (Ast.leftmost_name n))
        )
      then begin
        mkmi $startpos $endpos (MImethodName(n, a))
      end
      else begin
        try
          let q = get_qualifier n in
          env#set_attribute_A q;
          let id = rightmost_identifier n in
          if
            is_local_name ~force:true q ||
            is_implicit_field_name q ||
            is_field_access q ||
            is_expr_name q
          then begin
            set_name_attribute (NAexpression EKunknown) q;
            register_qname_as_expression q;
            env#reclassify_identifier(leftmost_of_name q);
            mkmi $startpos $endpos (MIprimary(_name_to_prim ~whole:false q.n_loc q, None, id, a))
          end
          else begin
            if
              is_type_name q ||
              (*Ast.is_simple q &&*)
              not (is_static_member q) &&
              (
               env#in_static_method ||
               (env#rely_on_naming_convention_flag && Ast.is_rightmost_id_capitalized q) ||
               (not env#rely_on_naming_convention_flag && (not env#surrounding_class_has_super))
              )
            then begin
              try
                let fqn = get_type_fqn q in
                set_attribute_PT_T (mkresolved fqn) q;
                register_qname_as_typename q;
                mkmi $startpos $endpos (MItypeName(q, None, id, a))
              with
              | Unknown _ ->
                  set_attribute_PT_T (env#resolve q) q;
                  register_qname_as_typename q;
                  mkmi $startpos $endpos (MItypeName(q, None, id, a))
            end
            else begin
              env#reclassify_identifier(leftmost_of_name q);
              mkmi $startpos $endpos (MIprimary(_name_to_prim ~whole:false q.n_loc q, None, id, a))
              (*raise (Unknown "")*)
            end
          end
        with
        | Not_found -> mkmi $startpos $endpos (MImethodName(n, a))
      end
    }

| p=primary DOT i=identifier a=arguments
    { 
      let _, id = i in
      mkmi $startpos $endpos (MIprimary(p, None, id, a)) 
    }

| p=primary DOT t=type_arguments i=identifier a=arguments
    { 
      let _, id = i in
      mkmi $startpos $endpos (MIprimary(p, Some t, id, a)) 
    }

| q=name DOT t=type_arguments i=identifier a=arguments
    { 
      let _, id = i in
      if env#partial_name_resolution_flag then begin
        mkmi $startpos $endpos (MIprimary(_name_to_prim ~whole:false q.n_loc q, Some t, id, a))
      end
      else if
        is_local_name q ||
        is_implicit_field_name q ||
        is_field_access q ||
        is_expr_name q
      then begin
        set_name_attribute (NAexpression EKunknown) q;
        register_qname_as_expression q;
        begin
          try
            env#reclassify_identifier(leftmost_of_name q);
          with
            Not_found -> ()
        end;
        mkmi $startpos $endpos (MIprimary(_name_to_prim ~whole:false q.n_loc q, Some t, id, a))
      end
      else begin
        if is_type_name q then begin
          try
            let fqn = get_type_fqn q in
            set_attribute_PT_T (mkresolved fqn) q;
            register_qname_as_typename q;
            mkmi $startpos $endpos (MItypeName(q, Some t, id, a))
          with
          | Unknown _ ->
              set_attribute_PT_T (env#resolve q) q;
              register_qname_as_typename q;
              mkmi $startpos $endpos (MItypeName(q, Some t, id, a))
        end
        else begin
          begin
            try
              env#reclassify_identifier(leftmost_of_name q);
            with
              Not_found -> ()
          end;
          mkmi $startpos $endpos (MIprimary(_name_to_prim ~whole:false q.n_loc q, Some t, id, a))
        end
      end
    }

| s=super DOT i=identifier a=arguments
    { 
      let _, id = i in
      mkmi $startpos $endpos (MIsuper(s, None, id, a)) 
    }

| s=super DOT t=type_arguments i=identifier a=arguments
    { 
      let _, id = i in
      mkmi $startpos $endpos (MIsuper(s, Some t, id, a)) 
    }

| n=name DOT s=super DOT i=identifier a=arguments
    { 
      let _, id = i in
      set_attribute_PT_T (env#resolve n) n;
      register_qname_as_typename n;
      mkmi $startpos $endpos (MIclassSuper(n.n_loc, s, n, None, id, a)) 
    }

| n=name DOT s=super DOT t=type_arguments i=identifier a=arguments
    { 
      let _, id = i in
      set_attribute_PT_T (env#resolve n) n;
      register_qname_as_typename n;
      mkmi $startpos $endpos (MIclassSuper(n.n_loc, s, n, Some t, id, a)) 
    }
;

array_access:
| n=name LBRACKET e=expression RBRACKET               
    { 
      if is_qualified n then begin
        set_name_attribute (NAexpression EKunknown) n;
        let q = get_qualifier n in
        env#set_attribute_A q
      end;
      register_qname_as_array n;
      if is_local_name n then
        mkaa $startpos $endpos (AAname(n, e))
      else
        mkaa $startpos $endpos (AAprimary(_name_to_prim n.n_loc n, e))
    }
| p=primary_no_new_array LBRACKET e=expression RBRACKET 
     { 
       mkaa $startpos $endpos (AAprimary(p, e)) 
     }
;

postfix_expression:
| p=primary { mkexpr $startpos $endpos (Eprimary p) }
| n=name                      
    { 
      if is_qualified n then begin
        set_name_attribute (NAexpression EKunknown) n;
        let q = get_qualifier n in
        env#set_attribute_A ~force_defer:true q
      end;
      register_qname_as_expression n;
      begin
        try
          env#reclassify_identifier(leftmost_of_name n)
        with
          Not_found -> ()
      end;
      name_to_expr $startpos $endpos n
    }
| p=post_increment_expression { p }
| p=post_decrement_expression { p }
;

post_increment_expression:
| p=postfix_expression PLUS_PLUS { mkexpr $startpos $endpos (Eunary(UOpostIncrement, p)) }
;

post_decrement_expression:
| p=postfix_expression MINUS_MINUS { mkexpr $startpos $endpos (Eunary(UOpostDecrement, p)) }
;

unary_expression:
| p=pre_increment_expression        { p }
| p=pre_decrement_expression        { p }
| PLUS  u=unary_expression          { mkexpr $startpos $endpos (Eunary(UOpositive, u)) }
| MINUS u=unary_expression          { mkexpr $startpos $endpos (Eunary(UOnegative, u)) }
| u=unary_expression_not_plus_minus { u }
;

pre_increment_expression:
| PLUS_PLUS u=unary_expression { mkexpr $startpos $endpos (Eunary(UOpreIncrement, u)) }
;

pre_decrement_expression:
| MINUS_MINUS u=unary_expression { mkexpr $startpos $endpos (Eunary(UOpreDecrement, u)) }
;

unary_expression_not_plus_minus:
| p=postfix_expression      { p }
| TILDE  u=unary_expression { mkexpr $startpos $endpos (Eunary(UOcomplement, u)) }
| EXCLAM u=unary_expression { mkexpr $startpos $endpos (Eunary(UOnot, u)) }
| c=cast_expression         { c }
| s=switch_expression       { s }
;

switch_expression:
| SWITCH LPAREN e=expr_or_err RPAREN s=switch_block
    { 
      check_JLS_level 14
        (fun () -> mkexpr $startpos $endpos (Eswitch(e, s)))
        (fun () -> parse_error $startpos $endpos "switch-expression is available since JLS14")
    }
;

unary_expression_not_plus_minus_or_lambda_expression:
| u=unary_expression_not_plus_minus { u }
| l=lambda_e                        { l }
;

lambda_e:
| p=lambda_parameters MINUS_GT b=lambda_b { mkexpr $startpos $endpos (Elambda(p, b)) }
;
lambda_b:
| e=unary_expression_not_plus_minus { LBexpr e }
| b=block                           { LBblock b }
;

cast_expression:
| LPAREN p=primitive_type d=ann_dims0 RPAREN u=unary_expression 
    { 
      let ty =
        match d with
        | [] -> p
        | l -> _mkty (Loc.merge p.ty_loc (Xlist.last l).Ast.ad_loc) (Tarray(p, d))
      in
      mkexpr $startpos $endpos (Ecast(ty, u)) 
    }
| LPAREN a=annotations0 n=name RPAREN u=unary_expression_not_plus_minus_or_lambda_expression
    { 
      let thunk () =
        set_attribute_PT_T (env#resolve n) n;
        register_qname_as_typename n;
        mkexpr $startpos $endpos (Ecast(name_to_ty a n, u))
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }
| LPAREN a=annotations0 n=name d=ann_dims RPAREN
    u=unary_expression_not_plus_minus_or_lambda_expression
    { 
      let thunk () =
        let ty = _mkty (Loc.merge n.n_loc (Xlist.last d).Ast.ad_loc) (Tarray(name_to_ty a n, d)) in
        set_attribute_PT_T (env#resolve n) n;
        register_qname_as_typename n;
        mkexpr $startpos $endpos (Ecast(ty, u))
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }
| LPAREN a=annotations0 n=name ts=type_arguments d=ann_dims0 RPAREN
    u=unary_expression_not_plus_minus_or_lambda_expression
    { 
      let thunk () =
        let ty = name_to_ty_args (Loc.merge n.n_loc ts.tas_loc) a n ts in
        let ty' =
          match d with
          | [] -> ty
          | l -> _mkty (Loc.merge ty.ty_loc (Xlist.last l).Ast.ad_loc) (Tarray(ty, l))
        in
        set_attribute_PT_T (env#resolve n) n;
        register_qname_as_typename n;
        mkexpr $startpos $endpos (Ecast(ty', u))
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }
| LPAREN a=annotations0 n=name ts0=type_arguments DOT c=class_or_interface_type d=ann_dims0 RPAREN
       u=unary_expression_not_plus_minus_or_lambda_expression
    { 
      let thunk () =
        let tspecs =
          match c.ty_desc with
          | TclassOrInterface ts | Tclass ts | Tinterface ts -> ts
          | _ -> parse_error $startpos $endpos "invalid type"
        in
        let ty =
          _mkty (Loc.merge n.n_loc c.ty_loc)
            (TclassOrInterface((TSapply(a, n, ts0)) :: tspecs))
        in
        let ty' =
          match d with
          | [] -> ty
          | l -> _mkty (Loc.merge ty.ty_loc (Xlist.last l).Ast.ad_loc) (Tarray(ty, l))
        in
        set_attribute_PT_T (env#resolve n) n;
        register_qname_as_typename n;
        mkexpr $startpos $endpos (Ecast(ty', u))
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }
;

multiplicative_expression:
|                                        u=unary_expression { u }
| m=multiplicative_expression op=mult_op u=unary_expression { mkexpr $startpos $endpos (Ebinary(op, m, u)) }
;

%inline
mult_op:
| STAR    { BOmul }
| SLASH   { BOdiv }
| PERCENT { BOmod }
;

additive_expression:
|                             m=multiplicative_expression { m }
| a=additive_expression PLUS  m=multiplicative_expression { mkexpr $startpos $endpos (Ebinary(BOadd, a, m)) }
| a=additive_expression MINUS m=multiplicative_expression { mkexpr $startpos $endpos (Ebinary(BOsub, a, m)) }
;

shift_expression:
|                                a=additive_expression { a }
| s=shift_expression op=shift_op a=additive_expression { mkexpr $startpos $endpos (Ebinary(op, s, a)) }
;

%inline
shift_op:
| LT_LT    { BOshiftL }
| GT_GT    { BOshiftR }
| GT_GT_GT { BOshiftRU }
;

relational_expression:
|                                   s=shift_expression { s }
| r=relational_expression op=rel_op s=shift_expression { mkexpr $startpos $endpos (Ebinary(op, r, s)) }
;

%inline
rel_op:
| LT    { BOlt }
| GT    { BOgt }
| LT_EQ { BOle }
| GT_EQ { BOge }
;

instanceof_expression:
| r=relational_expression                             { r }
| i=instanceof_expression INSTANCEOF r=reference_type { mkexpr $startpos $endpos (Einstanceof(i, r)) }
| s=ERROR INSTANCEOF r=reference_type
    { 
      let e = mkerrexpr $startpos $endpos(s) s in
      mkexpr $startpos $endpos (Einstanceof(e, r))
    }
| i=instanceof_expression INSTANCEOF p=pattern { mkexpr $startpos $endpos (EinstanceofP(i, p)) }
| s=ERROR INSTANCEOF p=pattern
    { 
      let e = mkerrexpr $startpos $endpos(s) s in
      mkexpr $startpos $endpos (EinstanceofP(e, p))
    }
;

pattern:
| t=reference_type v=variable_declarator_id
    { 
      check_JLS_level 14
        (fun () ->
          let vd = mkvd $startpos(v) $endpos v None in
          let (_, id), _ = vd.vd_variable_declarator_id in
          register_identifier_as_variable id t;
          vd.vd_is_local := true;
          mklvd $symbolstartpos $endpos None t [vd]
        )
        (fun () -> parse_error $startpos $endpos "instanceof-pattern is available since JLS16")
    }
| f=FINAL t=reference_type v=variable_declarator_id
    { 
      ignore f;
      check_JLS_level 14
        (fun () ->
          let m = mkmod $startpos $endpos(f) Mfinal in
          let vd = mkvd $startpos(v) $endpos v None in
          let (_, id), _ = vd.vd_variable_declarator_id in
          register_identifier_as_variable id t;
          vd.vd_is_local := true;
          mklvd $startpos $endpos (Some (mkmods $startpos $endpos(f) [m])) t [vd]
        )
        (fun () -> parse_error $startpos $endpos "instanceof-pattern is available since JLS16")
    }
;

equality_expression:
|                                 i=instanceof_expression { i }
| e=equality_expression EQ_EQ     i=instanceof_expression { mkexpr $startpos $endpos (Ebinary(BOeq, e, i)) }
| e=equality_expression EXCLAM_EQ i=instanceof_expression { mkexpr $startpos $endpos (Ebinary(BOneq, e, i)) }
;

and_expression:
|                      e=equality_expression { e }
| a=and_expression AND e=equality_expression { mkexpr $startpos $endpos (Ebinary(BObitAnd, a, e)) }
;

exclusive_or_expression:
|                               a=and_expression { a }
| e=exclusive_or_expression HAT a=and_expression { mkexpr $startpos $endpos (Ebinary(BObitXor, e, a)) }
;

inclusive_or_expression:
|                              e=exclusive_or_expression { e }
| i=inclusive_or_expression OR e=exclusive_or_expression { mkexpr $startpos $endpos (Ebinary(BObitOr, i, e)) }
;

conditional_and_expression:
|                                      i=inclusive_or_expression { i }
| c=conditional_and_expression AND_AND i=inclusive_or_expression { mkexpr $startpos $endpos (Ebinary(BOand, c, i)) }
;

conditional_or_expression:
|                                   a=conditional_and_expression { a }
| c=conditional_or_expression OR_OR a=conditional_and_expression { mkexpr $startpos $endpos (Ebinary(BOor, c, a)) }
;

conditional_expression:
| c=conditional_or_expression { c }
| c=conditional_or_expression QUESTION e=expression COLON ce=conditional_expression { mkexpr $startpos $endpos (Econd(c, e, ce)) }
| c=conditional_or_expression QUESTION e=expression COLON le=lambda_expression { mkexpr $startpos $endpos (Econd(c, e, le)) }
;

assignment_expression:
| c=conditional_expression { c }
| a=assignment             { mkexpr $startpos $endpos (Eassignment a) }
;

assignment: (* set_attribute_A_E name *)
| p=postfix_expression op=assign_op e=expr_or_err { p, mkaop $startpos $endpos op, e }
;

%inline
assign_op:
| EQ          { AOeq }
| STAR_EQ     { AOmulEq }
| SLASH_EQ    { AOdivEq }
| PERCENT_EQ  { AOmodEq }
| PLUS_EQ     { AOaddEq }
| MINUS_EQ    { AOsubEq }
| LT_LT_EQ    { AOshiftLEq }
| GT_GT_EQ    { AOshiftREq }
| GT_GT_GT_EQ { AOshiftRUEq }
| AND_EQ      { AOandEq }
| HAT_EQ      { AOxorEq }
| OR_EQ       { AOorEq }
;

expression_opt:
| o=ioption(expression) { o }
;

expression:
| a=assignment_expression { a }
| l=lambda_expression     { l }
(*| s=ERROR { mkerrexpr $startpos $endpos s }*)
;

lambda_expression:
| p=lambda_parameters MINUS_GT b=lambda_body
    { 
      check_JLS_level 8
        (fun () -> mkexpr $startpos $endpos (Elambda(p, b)))
        (fun () -> parse_error $startpos $endpos "lambda-expression is available since JLS8")
    }
;

lambda_parameters:
| i=identifier
    { 
      let _, id = i in
      env#register_identifier id IAparameter;
      mklp $startpos $endpos (LPident id)
    }
| LPAREN__LAMBDA l=formal_parameter_list0 RPAREN { mklp $startpos $endpos (LPformal l) }
| LPAREN__LAMBDA l=clist(identifier)      RPAREN
    { 
      List.iter
        (fun (_, id) ->
          env#register_identifier id IAparameter
        ) l;
      mklp $startpos $endpos (LPinferred l)
    }
;

lambda_body:
| e=expression { LBexpr e }
| b=block      { LBblock b }
;

%inline
constant_expression:
| e=expression { e }
;

%inline
type_parameters_opt:
| o=ioption(type_parameters) { o }
;

type_parameters:
| LT tps=type_parameter_list_1 { mktyparams $startpos $endpos tps }
;

type_parameter_list:
|                               tp=type_parameter { [tp] }
| tps=type_parameter_list COMMA tp=type_parameter { tps @ [tp] }
;

type_parameter_list_1:
|                               tp=type_parameter_1 { [tp] }
| tps=type_parameter_list COMMA tp=type_parameter_1 { tps @ [tp] }
;

type_variable:
| a=annotations0 i=identifier 
    { 
      let thunk () =
        begin_scope ~kind:FKtypeparameter ();
        let _, id = i in
        register_identifier_as_typeparameter id;
        a, id
      in
      if List.length a > 0 then
        check_JLS_level 8 thunk
          (fun () -> parse_error $startpos $endpos(a) "type annotation is available since JLS8")
      else
        thunk()
    }
;

type_parameter:
| tv=type_variable tb=type_bound_opt { mktyparam $symbolstartpos $endpos tv tb }
;

type_parameter_1:
| tv=type_variable GT              { mktyparam $symbolstartpos $endpos(tv) tv None }
| tv=type_variable tb=type_bound_1 { mktyparam $symbolstartpos (Loc.to_end_lexpos tb.Ast.tb_loc) tv (Some tb) }
;

%inline
type_bound_opt:
| o=ioption(type_bound) { o }
;

type_bound:
| EXTENDS r=reference_type a=additional_bound_list0 { mktb $startpos $endpos r a }
;

type_bound_1:
| EXTENDS r=reference_type_1                           { mktb $startpos (Loc.to_end_lexpos r.Ast.ty_loc) r [] }
| EXTENDS r=reference_type   a=additional_bound_list_1
    { 
      let ed_pos = Loc.to_end_lexpos (Xlist.last a).Ast.ab_loc in
      mktb $startpos ed_pos r a
    }
;

%inline
additional_bound_list0:
| (* *)                   { [] }
| a=additional_bound_list { a }
;

additional_bound_list:
| l=nonempty_list(additional_bound) { l }
;

additional_bound_list_1:
| a=additional_bound_1                           { [a] }
| a=additional_bound   l=additional_bound_list_1 { a :: l }
;

additional_bound:
| AND i=interface_type { mkab $startpos $endpos i }
;

additional_bound_1:
| AND r=reference_type_1 { mkab $startpos (Loc.to_end_lexpos r.Ast.ty_loc) r }
;

postfix_expression_nn:
| p=primary                   { mkexpr $startpos $endpos (Eprimary p) }
| p=post_increment_expression { p }
| p=post_decrement_expression { p }
;

unary_expression_nn:
| p=pre_increment_expression           { p }
| p=pre_decrement_expression           { p }
| PLUS u=unary_expression              { mkexpr $startpos $endpos (Eunary(UOpositive, u)) }
| MINUS u=unary_expression             { mkexpr $startpos $endpos (Eunary(UOnegative, u)) }
| u=unary_expression_not_plus_minus_nn { u }
;

unary_expression_not_plus_minus_nn:
| p=postfix_expression_nn   { p }
| TILDE u=unary_expression  { mkexpr $startpos $endpos (Eunary(UOcomplement, u)) }
| EXCLAM u=unary_expression { mkexpr $startpos $endpos (Eunary(UOnot, u)) }
| c=cast_expression         { c }
| s=switch_expression       { s }
;

multiplicative_expression_nn:
|                                           u=unary_expression_nn { u }
| m=multiplicative_expression_nn op=mult_op u=unary_expression    { mkexpr $startpos $endpos (Ebinary(op, m, u)) }
| n=name                         op=mult_op u=unary_expression    { mkexpr $startpos $endpos (Ebinary(op, _name_to_expr n.n_loc n, u)) }
;

additive_expression_nn:
|                                m=multiplicative_expression_nn { m }
| a=additive_expression_nn PLUS  m=multiplicative_expression    { mkexpr $startpos $endpos (Ebinary(BOadd, a, m)) }
| a=additive_expression_nn MINUS m=multiplicative_expression    { mkexpr $startpos $endpos (Ebinary(BOsub, a, m)) }
| n=name                   PLUS  m=multiplicative_expression    { mkexpr $startpos $endpos (Ebinary(BOadd, _name_to_expr n.n_loc n, m)) }
| n=name                   MINUS m=multiplicative_expression    { mkexpr $startpos $endpos (Ebinary(BOsub, _name_to_expr n.n_loc n, m)) }
;

shift_expression_nn:
|                                   a=additive_expression_nn { a }
| s=shift_expression_nn op=shift_op a=additive_expression    { mkexpr $startpos $endpos (Ebinary(op, s, a)) }
| n=name                op=shift_op a=additive_expression    { mkexpr $startpos $endpos (Ebinary(op, _name_to_expr n.n_loc n, a)) }
;

relational_expression_nn:
|                                      s=shift_expression_nn { s }

| r=shift_expression_nn LT s=shift_expression    { mkexpr $startpos $endpos (Ebinary(BOlt, r, s)) } (* to avoid conflicts *)
| r=shift_expression_nn GT s=shift_expression    { mkexpr $startpos $endpos (Ebinary(BOgt, r, s)) }

| r=relational_expression_nn LT_EQ s=shift_expression    { mkexpr $startpos $endpos (Ebinary(BOle, r, s)) }
| r=relational_expression_nn GT_EQ s=shift_expression    { mkexpr $startpos $endpos (Ebinary(BOge, r, s)) }

| n=name                     op=rel_op s=shift_expression { mkexpr $startpos $endpos (Ebinary(op, _name_to_expr n.n_loc n, s)) }
;

instanceof_expression_nn:
| r=relational_expression_nn { r }
| n=name INSTANCEOF r=reference_type { mkexpr $startpos $endpos (Einstanceof(_name_to_expr n.n_loc n, r)) }
| n=name INSTANCEOF p=pattern        { mkexpr $startpos $endpos (EinstanceofP(_name_to_expr n.n_loc n, p)) }
| i=instanceof_expression_nn INSTANCEOF r=reference_type { mkexpr $startpos $endpos (Einstanceof(i, r)) }
| i=instanceof_expression_nn INSTANCEOF p=pattern        { mkexpr $startpos $endpos (EinstanceofP(i, p)) }
;

equality_expression_nn:
|                                    i=instanceof_expression_nn { i }

| e=equality_expression_nn EQ_EQ     i=instanceof_expression { mkexpr $startpos $endpos (Ebinary(BOeq, e, i)) }
| e=equality_expression_nn EXCLAM_EQ i=instanceof_expression { mkexpr $startpos $endpos (Ebinary(BOneq, e, i)) }

| n=name EQ_EQ     i=instanceof_expression { mkexpr $startpos $endpos (Ebinary(BOeq, _name_to_expr n.n_loc n, i)) }
| n=name EXCLAM_EQ i=instanceof_expression { mkexpr $startpos $endpos (Ebinary(BOneq, _name_to_expr n.n_loc n, i)) }
;

and_expression_nn:
|                         e=equality_expression_nn { e }
| a=and_expression_nn AND e=equality_expression    { mkexpr $startpos $endpos (Ebinary(BObitAnd, a, e)) }
| n=name              AND e=equality_expression    { mkexpr $startpos $endpos (Ebinary(BObitAnd, _name_to_expr n.n_loc n, e)) }
;

exclusive_or_expression_nn:
|                                  a=and_expression_nn { a }
| e=exclusive_or_expression_nn HAT a=and_expression    { mkexpr $startpos $endpos (Ebinary(BObitXor, e, a)) }
| n=name                       HAT a=and_expression    { mkexpr $startpos $endpos (Ebinary(BObitXor, _name_to_expr n.n_loc n, a)) }
;

inclusive_or_expression_nn:
|                                 e=exclusive_or_expression_nn { e }
| i=inclusive_or_expression_nn OR e=exclusive_or_expression    { mkexpr $startpos $endpos (Ebinary(BObitOr, i, e)) }
| n=name                       OR e=exclusive_or_expression    { mkexpr $startpos $endpos (Ebinary(BObitOr, _name_to_expr n.n_loc n, e)) }
;

conditional_and_expression_nn:
|                                         i=inclusive_or_expression_nn { i }
| c=conditional_and_expression_nn AND_AND i=inclusive_or_expression    { mkexpr $startpos $endpos (Ebinary(BOand, c, i)) }
| n=name                          AND_AND i=inclusive_or_expression    { mkexpr $startpos $endpos (Ebinary(BOand, _name_to_expr n.n_loc n, i)) }
;

conditional_or_expression_nn:
|                                      c=conditional_and_expression_nn { c }
| o=conditional_or_expression_nn OR_OR c=conditional_and_expression    { mkexpr $startpos $endpos (Ebinary(BOor, o, c)) }
| n=name                         OR_OR c=conditional_and_expression    { mkexpr $startpos $endpos (Ebinary(BOor, _name_to_expr n.n_loc n, c)) }
;

conditional_expression_nn:
| c=conditional_or_expression_nn { c }
| c=conditional_or_expression_nn QUESTION e=expression COLON ce=conditional_expression { mkexpr $startpos $endpos (Econd(c, e, ce)) }
| c=conditional_or_expression_nn QUESTION e=expression COLON le=lambda_expression      { mkexpr $startpos $endpos (Econd(c, e, le)) }
| n=name                         QUESTION e=expression COLON ce=conditional_expression { mkexpr $startpos $endpos (Econd(_name_to_expr n.n_loc n, e, ce)) }
| n=name                         QUESTION e=expression COLON le=lambda_expression      { mkexpr $startpos $endpos (Econd(_name_to_expr n.n_loc n, e, le)) }
;

assignment_expression_nn:
| c=conditional_expression_nn { c }
| a=assignment { mkexpr $startpos $endpos (Eassignment a) }
;

expression_nn:
| a=assignment_expression_nn { a }
| l=lambda_expression        { l }
;


%%
