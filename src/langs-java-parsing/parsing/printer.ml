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
 * A pretty printer for the Java Language
 *
 * printer.ml
 *
 *)

module Xlist = Diffast_misc.Xlist

open Ast
open Format
(*open Common*)

let indent = 2

let list_to_string to_str sep l = String.concat sep (List.map to_str l)

let pr_option pr = function Some x -> pr x | None -> ()

let pr_string   = print_string
let pr_break    = print_break
let pr_space    = print_space
let pr_newline  = print_newline
let pr_cut      = print_cut
let pr_comma()  = print_string ","; pr_space()
let pr_lparen() = print_string "("
let pr_rparen() = print_string ")"
let pr_semicolon() = print_string ";"
let pr_bor()    = print_string "|"
let pr_colon()  = pr_string ":"

let pad i = pr_string (String.make i ' ')

type block_style = BSshort | BStall

let pr_block_begin = function
  | BStall -> pr_cut(); pr_string "{"; open_vbox indent; pr_cut()
  | BSshort -> pad 1; pr_string "{"; pr_cut(); open_vbox indent; pad indent

let pr_block_end() = close_box(); pr_cut(); pr_string "}"

let pr_block_begin_short() = pr_block_begin BSshort

let pr_block_begin_tall() = pr_block_begin BStall


(* Precedence of each of the operators
 *
 * 15: []  .  (params)  expr++  expr--
 * 14: ++expr  --expr  +expr  -expr  ~  !
 * 13: new  (type)expr
 * 12: *  /  %
 * 11: +  -
 * 10: <<  >>  >>>
 *  9: <  >  >=  <=  instanceof
 *  8: ==  !=
 *  7: &
 *  6: ^
 *  5: |
 *  4: &&
 *  3: ||
 *  2: ?:
 *  1: =  +=  -=  *=  /=  %=  >>=  <<=  >>>=  &=  ^=  |=
 *
 *)

let get_precedence = function
  | "." | "[]" -> 15
  | "::" -> 15 (* ??? *)
  | _ -> 0

let get_precedence_of_statement_expression se =
  match se.se_desc with
  | SEpreIncrement _ | SEpreDecrement _ -> 14
  | SEpostIncrement _ | SEpostDecrement _ -> 15
  | _ -> 0

let get_precedence_of_expression e =
  match e.e_desc with
  | Eunary(op, _) ->
      (match op with
      | UOpostIncrement | UOpostDecrement -> 15
      | UOpreIncrement | UOpreDecrement | UOpositive | UOnegative
      | UOcomplement | UOnot -> 14)
  | Ebinary(op, _, _) ->
      (match op with
      | BOmul | BOdiv | BOmod -> 12
      | BOadd | BOsub -> 11
      | BOshiftL | BOshiftR | BOshiftRU -> 10
      | BOlt | BOgt | BOle | BOge -> 9
      | BOeq | BOneq -> 8
      | BObitAnd -> 7
      | BObitXor -> 6
      | BObitOr -> 5
      | BOand -> 4
      | BOor -> 3)
  | Eprimary({p_desc=Pname _;_}) -> 15
  | Eprimary({p_desc=PclassInstanceCreation _;_})
  | Eprimary({p_desc=ParrayCreationExpression _;_})
  | Ecast _ -> 13
  | Einstanceof _  | EinstanceofP _ -> 9
  | Econd _ -> 2
  | Eassignment _ -> 1
  | _ -> 0

let precedence_of_assignment_operators = 1

let rec pr_list pr_sep pr = function
  | [] -> ()
  | [x] -> pr x;
  | x::xs -> pr x; pr_sep(); pr_list pr_sep pr xs

let pr_hlist pr_sep pr = function
  | [] -> ()
  | l -> open_hbox(); pr_list pr_sep pr l; close_box()

let pr_vlist pr_sep pr = function
  | [] -> ()
  | l -> open_vbox 0; pr_list pr_sep pr l; close_box()

let pr_hovlist pr_sep pr = function
  | [] -> ()
  | l ->
      open_hovbox 0; pr_list (fun () -> pr_sep(); pr_cut()) pr l; close_box()

let pr_loc loc = pr_string (sprintf "{%s}" (Loc.to_string loc))

let pr_id id = pr_string id

let dims_to_short_string dims =
  let res = ref "" in
  for _ = 1 to dims do
    res := !res ^ "["
  done; !res

let name_attribute_to_string = function
  | NApackage       -> "P"
  | NAtype r        -> "T:"^(resolve_result_to_str r)
  | NAexpression EKfacc -> "Ef"
  | NAexpression EKname -> "En"
  | NAexpression EKunknown -> "E"
  | NAmethod        -> "M"
  | NApackageOrType -> "PT"
  | NAstatic r      -> "S:"^(resolve_result_to_str r)
  | NAambiguous r   -> "A:"^(resolve_result_to_str r)
  | NAunknown       -> "U"

let rec name_to_simple_string name =
  match name.n_desc with
  | Nsimple(_, sn) -> sn
  | Nqualified(_, n, al, sn) ->
      sprintf "%s.%s%s" (name_to_simple_string n) (annotations_to_string al) sn
  | Nerror s -> s

and _name_to_string name =
  match name.n_desc with
  | Nsimple(attr, sn) ->
      sprintf "(%s)_{%s}" sn (name_attribute_to_string !attr)

  | Nqualified(attr, n, al, sn) ->
      sprintf "(%s.%s%s)_{%s}" (_name_to_string n) (annotations_to_string al) sn (name_attribute_to_string !attr)

  | Nerror s -> s

and name_to_string ?(show_attr=true) n =
  if show_attr then
    _name_to_string n
  else
    name_to_simple_string n

and pr_name name = pr_string (name_to_string ~show_attr:true name)

and type_to_short_string ?(resolve=true) dims ty =
  let dim_str = dims_to_short_string (List.length dims) in
  let base =
    match ty.ty_desc with
    | Tprimitive(a, p) -> begin
        (annotations_to_string a)^
        match p with
        | PTbyte    -> "B"
        | PTshort   -> "S"
        | PTint     -> "I"
        | PTlong    -> "J"
        | PTchar    -> "C"
        | PTfloat   -> "F"
        | PTdouble  -> "D"
        | PTboolean -> "Z"
    end
    | TclassOrInterface tspecs
    | Tclass tspecs
    | Tinterface tspecs -> type_specs_to_short_string ~resolve tspecs

    | Tarray(ty, dims') -> type_to_short_string ~resolve (dims @ dims') ty

    | Tvoid -> "V"

  in sprintf "%s%s" dim_str base

and type_specs_to_short_string ?(resolve=false) = function
  | [] -> ""
  | [tspec] -> sprintf "L%s;" (type_spec_to_short_string ~resolve tspec)
  | tspec::ts ->
      sprintf "L%s.%s;"
        (type_spec_to_short_string ~resolve tspec)
        (list_to_string type_spec_to_short_string "." ts)

and type_spec_to_short_string ?(resolve=false) tspec =
  let n_to_s =
    if resolve then
      fun n ->
        let lname = name_to_simple_string n in
        let attr = get_name_attribute n in
        let fqn =
          match attr with
          | NAtype r -> resolve_result_to_str r
          | _ -> lname
        in
        fqn
    else
      name_to_simple_string
  in
  match tspec with
  | TSname(_, n)
  | TSapply(_, n, _) -> n_to_s n

and annotations_to_string ?(show_attr=false) ?(sep=" ") = function
  | [] -> ""
  | al -> (Xlist.to_string (annotation_to_string ~show_attr) " " al)^sep

and annotation_to_string ?(show_attr=false) a =
  match a.a_desc with
  | Anormal(name, pairs) ->
      let ps =
        String.concat ","
          (List.map (fun {evp_desc=(id, _);_} -> sprintf "%s=" id) pairs)
      in
      String.concat "" ["@";name_to_string ~show_attr name;"(";ps;")"]

  | Amarker name -> "@"^(name_to_string ~show_attr name)

  | AsingleElement(name, _) -> String.concat "" ["@";name_to_string ~show_attr name;"()"]


and type_arguments_to_short_string tyargs =
  sprintf "<%s>"
    (list_to_string type_argument_to_short_string "," tyargs.tas_type_arguments)

and type_argument_to_short_string ?(resolve=true) ta =
  match ta.ta_desc with
  | TAreferenceType ty -> type_to_short_string ~resolve [] ty
  | TAwildcard wc      -> wildcard_to_short_string wc

and wildcard_bounds_to_short_string ?(resolve=true) wb =
  match wb.wb_desc with
  | WBextends ty -> sprintf "extends %s" (type_to_short_string ~resolve [] ty)
  | WBsuper ty   -> sprintf "super %s" (type_to_short_string ~resolve [] ty)

and wildcard_to_short_string = function
  | al, Some wcb -> sprintf "%s? %s" (annotations_to_string al) (wildcard_bounds_to_short_string wcb)
  | al, None     -> sprintf "%s?" (annotations_to_string al)


let rec dims_to_string dims =
  if dims = 0 then "" else "[]"^(dims_to_string (dims - 1))

let rec annot_dims_to_string dims =
  match dims with
  | [] -> ""
  | ad::rest ->
      (annotations_to_string ~sep:"" ad.ad_annotations)^
      (if ad.ad_ellipsis then "" else "[]")^
      (annot_dims_to_string rest)

let rec type_to_string ?(resolve=false) ?(show_attr=true) ty =
  match ty.ty_desc with
  | Tprimitive(a, p) -> begin
      (annotations_to_string a)^
      match p with
      | PTbyte    -> "byte"
      | PTshort   -> "short"
      | PTint     -> "int"
      | PTlong    -> "long"
      | PTchar    -> "char"
      | PTfloat   -> "float"
      | PTdouble  -> "double"
      | PTboolean -> "boolean"
  end
  | TclassOrInterface tspecs
  | Tclass tspecs
  | Tinterface tspecs
    -> (list_to_string (type_spec_to_string ~resolve ~show_attr) "." tspecs)

  | Tarray(ty, dims)  ->
      (type_to_string ~resolve ~show_attr ty)^(annot_dims_to_string dims)

  | Tvoid -> "void"

and type_spec_to_string ?(resolve=false) ?(show_attr=true) name =
  match name with
  | TSname(al, n) ->
      let sn =
        let lname = name_to_string ~show_attr n in
        if resolve then
          match get_name_attribute n with
          | NAtype r -> resolve_result_to_str r
          | _ -> lname
        else
          lname
      in
      (annotations_to_string ~show_attr al)^sn

  | TSapply(al, n, tyargs) ->
      sprintf "%s%s%s"
        (annotations_to_string ~show_attr al)
        (name_to_string ~show_attr n)
        (type_arguments_to_string ~resolve ~show_attr tyargs)

and type_arguments_to_string ?(resolve=false) ?(show_attr=true) tyargs =
  sprintf "<%s>"
    (list_to_string
       (type_argument_to_string ~resolve ~show_attr) "," tyargs.tas_type_arguments)

and type_argument_to_string ?(resolve=false) ?(show_attr=true) ta =
  match ta.ta_desc with
  | TAreferenceType ty -> type_to_string ~resolve ~show_attr ty
  | TAwildcard wc      -> wildcard_to_string ~resolve ~show_attr wc

and wildcard_bounds_to_string ?(resolve=false) ?(show_attr=true) wb =
  match wb.wb_desc with
  | WBextends ty -> sprintf "extends %s" (type_to_string ~resolve ~show_attr ty)
  | WBsuper ty   -> sprintf "super %s" (type_to_string ~resolve ~show_attr ty)

and wildcard_to_string ?(resolve=false) ?(show_attr=true) = function
  | al, Some wb ->
      sprintf "%s? %s"
        (annotations_to_string ~show_attr al)
        (wildcard_bounds_to_string ~resolve ~show_attr wb)
  | al, None ->
      sprintf "%s?" (annotations_to_string ~show_attr al)


let pr_dims dims = pr_string (dims_to_string dims)

let pr_type ty = pr_string (type_to_string ty)

let pr_types = pr_hovlist pr_comma pr_type

let pr_literal lit =
  pr_string
    (match lit with
    | Linteger s       -> s
    | LfloatingPoint s -> s
    | Ltrue            -> "true"
    | Lfalse           -> "false"
    | Lcharacter s     -> "'"^s^"'"
    | Lstring s        -> "\""^s^"\""
    | LtextBlock s     -> "\"\"\""^s^"\"\"\""
    | Lnull            -> "null")

let pr_unary_operator op =
  pr_string
  (match op with
  | UOpostIncrement -> "++"
  | UOpostDecrement -> "--"
  | UOpreIncrement  -> "++"
  | UOpreDecrement  -> "--"
  | UOpositive      -> "+"
  | UOnegative      -> "-"
  | UOcomplement    -> "~"
  | UOnot           -> "!")

let binary_operator_to_string op =
  match op with
  | BOmul     -> "*"
  | BOdiv     -> "/"
  | BOmod     -> "%"
  | BOadd     -> "+"
  | BOsub     -> "-"
  | BOshiftL  -> "<<"
  | BOshiftR  -> ">>"
  | BOshiftRU -> ">>>"
  | BOeq      -> "=="
  | BOneq     -> "!="
  | BOlt      -> "<"
  | BOgt      -> ">"
  | BOle      -> "<="
  | BOge      -> ">="
  | BObitAnd  -> "&"
  | BObitOr   -> "|"
  | BObitXor  -> "^"
  | BOand     -> "&&"
  | BOor      -> "||"

let pr_binary_operator op =
  pr_string (binary_operator_to_string op)

let pr_assignment_operator ao =
  pr_string
  (match ao.ao_desc with
  | AOeq        -> "="
  | AOmulEq     -> "*="
  | AOdivEq     -> "/="
  | AOmodEq     -> "%="
  | AOaddEq     -> "+="
  | AOsubEq     -> "-="
  | AOshiftLEq  -> "<<="
  | AOshiftREq  -> ">>="
  | AOshiftRUEq -> ">>>="
  | AOandEq     -> "&="
  | AOxorEq     -> "^="
  | AOorEq      -> "|=")

let rec pr_primary prec p =
  match p.p_desc with
  | Pname n           -> pr_name n
  | Pliteral lit      -> pr_literal lit
  | PclassLiteral ty  -> pr_type ty; pr_string ".class"
  | PclassLiteralVoid -> pr_string "void.class"
  | Pthis             -> pr_string "this"
  | PqualifiedThis n  -> pr_name n; pr_string ".this"

  | Pparen e ->
      if (get_precedence_of_expression e) >= prec then
        pr_expression 0 e
      else
        (pr_lparen(); pr_expression 0 e; pr_rparen())

  | PclassInstanceCreation cic   -> pr_class_instance_creation cic
  | PfieldAccess fa              -> pr_string "("; pr_field_access fa; pr_string ")_{FA}";
  | PmethodInvocation mi         -> pr_method_invocation mi
  | ParrayAccess aa              -> pr_array_access aa
  | ParrayCreationExpression ace -> pr_array_creation_expression ace
  | PmethodReference mr          -> pr_method_reference mr

  | Perror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"

and pr_method_reference mr =
  match mr.mr_desc with
  | MRname(n, tas_opt, id) ->
      pr_name n;
      pr_string "::";
      pr_option pr_type_arguments tas_opt;
      pr_id id

  | MRprimary(p, tas_opt, id) ->
      pr_primary (get_precedence "::") p;
      pr_string "::";
      pr_option pr_type_arguments tas_opt;
      pr_id id

  | MRsuper(tas_opt, id) ->
      pr_string "super";
      pr_string "::";
      pr_option pr_type_arguments tas_opt;
      pr_id id

  | MRtypeSuper(n, tas_opt, id) ->
      pr_name n;
      pr_string ".";
      pr_string "super";
      pr_string "::";
      pr_option pr_type_arguments tas_opt;
      pr_id id

  | MRtypeNew(ty, tas_opt) ->
      pr_type ty;
      pr_string "::";
      pr_option pr_type_arguments tas_opt;
      pr_string "new"

and pr_expressions prec pr_sep = pr_hovlist pr_sep (pr_expression prec)

and pr_argument_list args = pr_expressions 0 pr_comma args.as_arguments

and pr_modifier m =
  match m.m_desc with
  | Mpublic       -> pr_string "public"
  | Mprotected    -> pr_string "protected"
  | Mprivate      -> pr_string "private"
  | Mstatic       -> pr_string "static"
  | Mabstract     -> pr_string "abstract"
  | Mfinal        -> pr_string "final"
  | Mnative       -> pr_string "native"
  | Msynchronized -> pr_string "synchronized"
  | Mtransient    -> pr_string "transient"
  | Mvolatile     -> pr_string "volatile"
  | Mstrictfp     -> pr_string "strictfp"
  | Mannotation a -> pr_annotation a
  | Mdefault      -> pr_string "default"
  | Mtransitive   -> pr_string "transitive"
  | Msealed       -> pr_string "sealed"
  | Mnon_sealed   -> pr_string "non-sealed"
  | Merror s      -> pr_string "<ERROR:"; pr_string s; pr_string ">"


and pr_modifiers ms =
  open_hbox(); pr_list pr_space pr_modifier ms.ms_modifiers; close_box()

and pr_annotation a =
  match a.a_desc with
  | Anormal(name, pairs) ->
      pr_string "@";
      pr_name name;
      pr_lparen();
      pr_vlist pr_comma
        (fun {evp_desc=(id, ev);_} ->
          pr_id id; pr_string "="; pr_element_value ev)
        pairs;
      pr_rparen()

  | Amarker name -> pr_string "@"; pr_name name

  | AsingleElement(name, ev) ->
      pr_string "@";
      pr_name name;
      pr_lparen();
      pr_element_value ev;
      pr_rparen()

and pr_element_value ev =
  match ev.ev_desc with
  | EVconditional e -> pr_expression 0 e
  | EVannotation a -> pr_annotation a
  | EVarrayInit evs ->
      pr_string "{";
      pr_list pr_comma pr_element_value evs;
      pr_string "}"

and pr_annotations a = pr_list pr_space pr_annotation a

and pr_class_instance_creation cic =
  match cic.cic_desc with
  | CICunqualified(tyargs_opt, ty, args, body_opt) ->
      open_vbox 0;
      open_box 0;
      pr_string "new ";
      pr_option pr_type_arguments tyargs_opt;
      pr_type ty;
      pr_lparen(); pr_argument_list args; pr_rparen();
      close_box();
      pr_option pr_class_body body_opt;
      close_box()

  | CICqualified(p, tyargs1_opt, id, tyargs2_opt, args, body_opt) ->
      pr_primary (get_precedence ".") p;
      pr_string ".new ";
      pr_option pr_type_arguments tyargs1_opt;
      pr_id id;
      pr_option pr_type_arguments tyargs2_opt;
      pr_lparen(); pr_argument_list args; pr_rparen();
      pr_option pr_class_body body_opt

  | CICnameQualified(n, tyargs1_opt, id, tyargs2_opt, args, body_opt) ->
      pr_name n;
      pr_string ".new ";
      pr_option pr_type_arguments tyargs1_opt;
      pr_id id;
      pr_option pr_type_arguments tyargs2_opt;
      pr_lparen(); pr_argument_list args; pr_rparen();
      pr_option pr_class_body body_opt

and pr_type_argument tyarg =
  pr_string (type_argument_to_string tyarg)


and pr_type_arguments tyargs =
  pr_string "<";
  pr_list pr_comma pr_type_argument tyargs.tas_type_arguments;
  pr_string ">";

and pr_array_creation_expression = function
  | ACEtype(ty, des, dims) ->
      let des = List.map (fun de -> de.de_desc) des in
      pr_string "new "; pr_type ty; pr_string "[";
      pr_expressions 0 (fun () -> pr_string "][") des; pr_string "]";
      pr_annot_dims dims
  | ACEtypeInit(ty, dims, ai) ->
      pr_string "new "; pr_type ty; pr_annot_dims dims;
      pr_string "{"; pr_array_initializer ai; pr_string "}"

and pr_method_invocation mi =
  open_box 0;
  let pr_mi_d = function
    | MImethodName(n, args) ->
        pr_name n; pr_lparen(); pr_argument_list args; pr_string ")";
    | MIprimary(p, tyargs_opt, id, args) ->
        pr_primary (get_precedence ".") p; pr_string ".";
        pr_option pr_type_arguments tyargs_opt;
        pr_id id;
        pr_lparen(); pr_argument_list args; pr_string ")"
    | MItypeName(n, tyargs_opt, id, args) ->
        pr_name n; pr_string ".";
        pr_option pr_type_arguments tyargs_opt;
        pr_id id;
        pr_lparen(); pr_argument_list args; pr_string ")"
    | MIsuper(_, tyargs_opt, id, args) ->
        pr_string "super.";
        pr_option pr_type_arguments tyargs_opt;
        pr_id id;
        pr_lparen(); pr_argument_list args; pr_string ")"
    | MIclassSuper(_, _, n, tyargs_opt, id, args) ->
        pr_name n; pr_string ".super.";
        pr_option pr_type_arguments tyargs_opt;
        pr_id id;
        pr_lparen(); pr_argument_list args; pr_string ")"
  in
  let _ = pr_mi_d mi.mi_desc in
  close_box()

and pr_field_access = function
  | FAprimary(p, id) -> pr_primary (get_precedence ".") p; pr_string "."; pr_id id
  | FAsuper id -> pr_string "super."; pr_id id
  | FAclassSuper(n, id) -> pr_name n; pr_string ".super."; pr_id id
  | FAimplicit n -> pr_string "."; pr_name n

and pr_expression prec expr =
  let prec' = get_precedence_of_expression expr in
  match expr.e_desc with
  | Eprimary p -> pr_primary prec p

  | Eunary(op, e) ->
      (match op with
        UOpostIncrement | UOpostDecrement ->
          pr_expression prec' e; pr_unary_operator op
      | UOpreIncrement | UOpreDecrement | UOpositive | UOnegative
      | UOcomplement | UOnot -> pr_unary_operator op; pr_expression prec' e)

  | Ecast(ty, e) -> pr_lparen(); pr_type ty; pr_rparen(); pr_expression prec' e

  | Ebinary(op, e1, e2) ->
      pr_expression prec' e1; pr_binary_operator op; pr_expression prec' e2

  | Einstanceof(e, ty) ->
      pr_expression prec' e; pr_string " instanceof "; pr_type ty

  | EinstanceofP(e, lvd) ->
      pr_expression prec' e; pr_string " instanceof "; pr_local_variable_declaration lvd

  | Econd(e1, e2, e3) ->
      pr_expression prec' e1; pr_string " ? ";
      pr_expression prec' e2; pr_string " : "; pr_expression prec' e3

  | Eassignment a -> pr_assignment a

  | Elambda(params, body) ->
      pr_lambda_params params;
      pr_string " -> ";
      pr_lambda_body prec' body

  | Eswitch(e, sb) ->
      pr_string "switch ("; pr_expression 0 e; pr_rparen();
      pr_switch_block BSshort sb

  | Eerror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"

and pr_lambda_params params =
  match params.lp_desc with
  | LPident id     -> pr_id id
  | LPformal fps   -> pr_lparen(); pr_formal_parameters fps; pr_rparen()
  | LPinferred ids ->
      pr_lparen(); pr_hovlist pr_comma (fun (_, id) -> pr_id id) ids; pr_rparen()

and pr_lambda_body prec = function
  | LBexpr expr   -> pr_expression prec expr
  | LBblock block -> pr_block_short block


and pr_array_access aa =
  match aa.aa_desc with
  | AAname(n, e) -> pr_name n; pr_string "["; pr_expression 0 e; pr_string "]"
  | AAprimary(p, e) ->
      pr_primary (get_precedence "[]") p;
      pr_string "["; pr_expression 0 e; pr_string "]"

and pr_lhs lhs = pr_expression 0 lhs

and pr_assignment(lhs, aop, e) =
  open_box 0;
  pr_lhs lhs; pad 1;
  pr_assignment_operator aop; pr_space();
  pr_expression precedence_of_assignment_operators e;
  close_box()

and pr_variable_initializer vi =
  match vi.vi_desc with
  | VIexpression e -> pr_expression 0 e
  | VIarray ai -> pr_array_initializer ai
  | VIerror s -> pr_string s

and pr_array_initializer ai = pr_list pr_comma pr_variable_initializer ai

and pr_variable_declarator_id ((_, id), dims) = pr_id id; pr_annot_dims dims

and pr_variable_declarator vd =
  pr_variable_declarator_id vd.vd_variable_declarator_id;
  pr_string " ="; pr_break 1 indent;
  pr_option pr_variable_initializer vd.vd_variable_initializer


and pr_variable_declarators vds =
  pr_list pr_comma pr_variable_declarator vds

and pr_formal_parameter fp =
  pr_option pr_modifiers fp.fp_modifiers;
  pr_type fp.fp_type;
  if fp.fp_variable_arity then pr_string "...";
  pad 1;
  pr_variable_declarator_id fp.fp_variable_declarator_id

and pr_formal_parameters = function
  | [] -> ()
  | fps -> pr_hovlist pr_comma pr_formal_parameter fps

and pr_throws th =
  match th.th_exceptions with
  | [] -> ()
  | tys -> pr_break 1 indent; pr_string "throws "; pr_types tys;

and pr_throws_op = function
  | None -> ()
  | Some throws -> pr_throws throws

and pr_method_header mh =
  open_box 0;
  begin
    match mh.mh_modifiers with None -> () | Some ms -> pr_modifiers ms; pad 1
  end;
  pr_option pr_type_parameters mh.mh_type_parameters;
  pr_annotations mh.mh_annotations;
  pr_type mh.mh_return_type; pad 1; pr_id mh.mh_name;
  pr_lparen(); pr_formal_parameters mh.mh_parameters; pr_rparen();
  pr_annot_dims mh.mh_dims;
  pr_throws_op mh.mh_throws;
  close_box()

and pr_block_statement sty bs =
  match bs.bs_desc with
  | BSlocal lvd -> pr_local_variable_declaration_statement lvd
  | BSclass cd -> pr_class_declaration cd
  | BSstatement s -> pr_statement sty s
  | BSerror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"

and pr_statement_short s = pr_statement BSshort s

and pr_statement sty s =
  match s.s_desc with
  | Sblock b -> pr_block sty b
  | Sempty -> pr_semicolon()
  | Sexpression se -> pr_expression_statement se
  | Sswitch(e, sb) ->
      pr_string "switch ("; pr_expression 0 e; pr_rparen();
      pr_switch_block sty sb
  | Sdo(s, e) ->
      pr_string "do "; pr_statement sty s;
      pr_string "while("; pr_expression 0 e; pr_string ")"
  | Sbreak id_opt -> begin
      match id_opt with
      | None -> pr_string "break;"
      | Some id -> pr_string "break "; pr_id id; pr_semicolon()
  end
  | Scontinue id_opt -> begin
      match id_opt with
      | None -> pr_string "continue;"
      | Some id -> pr_string "continue "; pr_id id; pr_semicolon()
  end
  | Sreturn e_opt -> begin
      match e_opt with
      | None -> pr_string "return;"
      | Some e -> pr_string "return "; pr_expression 0 e; pr_semicolon()
  end
  | Ssynchronized(e, b) ->
      pr_string "synchronized ("; pr_expression 0 e; pr_rparen();
      pr_block sty b
  | Sthrow e -> pr_string "throw "; pr_expression 0 e; pr_semicolon()
  | Stry(rs_opt, b, cs_opt, fin_opt) -> begin
      pr_string "try";
      begin
        match rs_opt with
        | Some rs -> pad 1; pr_resource_spec rs
        | None -> ()
      end;
      pr_block_short b;
      match cs_opt, fin_opt with
      | Some cs, None -> pad 1; pr_catches_short cs
      | None, Some fin -> pad 1; pr_finally_short fin
      | Some cs, Some fin ->
          pad 1; pr_catches_short cs; pad 1;
          pr_finally_short fin
      | _ -> () (* impossible *)
  end
  | Syield e -> pr_string "yield "; pr_expression 0 e; pr_semicolon()
  | Slabeled(id, s) -> pr_id id; pr_string ": "; pr_statement sty s
  | SifThen(e, s) ->
      pr_string "if ("; pr_expression 0 e; pr_rparen(); pr_space(); pr_statement_short s;
  | SifThenElse(e, s1, s2) ->
      pr_string "if ("; pr_expression 0 e; pr_rparen(); pr_space();
      pr_statement_short s1; pr_string " else"; pr_space(); pr_statement_short s2;
  | Swhile(e, s) -> pr_string "while ("; pr_expression 0 e; pr_rparen(); pr_space();
      pr_statement_short s
  | Sfor(fi_op, e_op, ses, s) ->
      let pr_fi_op = function Some fi -> pr_for_init fi | None -> () in
      let pr_e_op = function  Some e -> pr_expression 0 e | None -> () in
      pr_string "for (";
      pr_fi_op fi_op; pr_semicolon();
      pr_e_op e_op; pr_semicolon();
      pr_statement_expression_list ses; pr_rparen(); pr_space();
      pr_statement_short s
  | SforEnhanced(fp, e, s) ->
      pr_string "for (";
      pr_formal_parameter fp;
      pr_colon();
      pr_expression 0 e;
      pr_space();
      pr_rparen(); pr_space();
      pr_statement_short s

  | Sassert1 e -> pr_string "assert "; pr_expression 0 e; pr_semicolon()
  | Sassert2(e1, e2) -> pr_string "assert "; pr_expression 0 e1;
      pr_colon(); pr_expression 0 e2; pr_semicolon()

  | Serror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"

and pr_resource_spec rs =
  pr_lparen();
  begin
    match rs.rs_resources with
    | [] -> ()
    | rl -> pr_hovlist pr_semicolon pr_resource rl
  end;
  pr_rparen()

and pr_resource r =
  match r.r_desc with
  | RlocalVarDecl lvd -> pr_local_variable_declaration lvd
  | RfieldAccess fa -> pr_field_access fa
  | Rname n -> pr_name n

and pr_catch_clause sty c =
  pr_string "catch (";
  pr_catch_formal_parameter c.c_formal_parameter;
  pr_rparen();
  pr_block sty c.c_block

and pr_catch_formal_parameter cfp =
  pr_option pr_modifiers cfp.cfp_modifiers;
  pr_hovlist pr_bor pr_type cfp.cfp_type_list;
  pad 1;
  pr_variable_declarator_id cfp.cfp_variable_declarator_id

and pr_finally sty f =
  pr_string "finally";
  pr_block sty f.f_block

and pr_finally_short f = pr_finally BSshort f

and pr_catches_short cs = pr_catches BSshort cs

and pr_catches sty cs = pr_list pr_space (pr_catch_clause sty) cs

and pr_switch_label sl =
  match sl.sl_desc with
  | SLconstant el -> pr_string "case "; pr_list pr_comma (pr_expression 0) el; pr_colon()
  | SLdefault -> pr_string "default:"

and pr_switch_block sty sb =
  pr_block_begin_short();
  pr_list pr_space (pr_switch_block_stmt_grp sty) sb.sb_switch_block_stmt_grps;
  pr_list pr_space (pr_switch_rule sty) sb.sb_switch_rules;
  pr_block_end()

and pr_switch_block_stmt_grp sty (sls, bss) =
  open_box 0;
  pr_list pr_newline pr_switch_label sls;
  pr_break 1 indent;
  open_vbox 0;
  pr_list pr_space (pr_block_statement sty) bss;
  close_box();
  close_box()

and pr_switch_rule_label srl =
  match srl.srl_desc with
  | SLconstant el -> pr_string "case "; pr_list pr_comma (pr_expression 0) el; pr_string " ->"
  | SLdefault -> pr_string "default ->"

and pr_switch_rule_body sty srb =
  match srb.srb_desc with
  | SRBexpr e -> pr_expression 0 e; pr_semicolon()
  | SRBblock b -> pr_block sty b
  | SRBthrow t -> pr_statement sty t

and pr_switch_rule sty (srl, srb) =
  pr_switch_rule_label srl;
  pr_break 1 indent;
  open_vbox 0;
  pr_switch_rule_body sty srb;
  close_box()

and pr_local_variable_declaration_statement lvd =
  pr_local_variable_declaration lvd; pr_semicolon()

and pr_local_variable_declaration lvd =
  open_box 0;
  pr_option pr_modifiers lvd.lvd_modifiers;
  pr_type lvd.lvd_type;
  pad 1;
  pr_variable_declarators lvd.lvd_variable_declarators;
  close_box()

and pr_for_init fi =
  match fi.fi_desc with
  | FIstatement ses -> pr_statement_expression_list ses
  | FIlocal lvd -> pr_local_variable_declaration lvd

and pr_expression_statement se =
  pr_statement_expression se; pr_semicolon()

and pr_statement_expression_list ses =
  pr_list pr_comma pr_statement_expression ses

and pr_statement_expression se =
  match se.se_desc with
  | SEassignment a -> pr_assignment a
  | SEpreIncrement e ->
      pr_expression (get_precedence_of_statement_expression se) e
  | SEpreDecrement e ->
      pr_expression (get_precedence_of_statement_expression se) e
  | SEpostIncrement e ->
      pr_expression (get_precedence_of_statement_expression se) e
  | SEpostDecrement e ->
      pr_expression (get_precedence_of_statement_expression se) e
  | SEmethodInvocation mi -> pr_method_invocation mi
  | SEclassInstanceCreation cic -> pr_class_instance_creation cic

  | SEerror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"

and pr_block_statements sty bss =
  pr_list pr_space (pr_block_statement sty) bss

and pr_block_statements_tall bss = pr_block_statements BStall bss
and pr_block_short b = pr_block BSshort b
and pr_block_tall b = pr_block BStall b

and pr_block sty b =
  match b.b_block_statements with
  | [] -> pr_string " {}"
  | bss ->
      pr_block_begin sty; pr_block_statements_tall bss; pr_block_end()

and pr_method_declaration mh body_opt =
  pr_method_header mh;
  pr_option pr_block_short body_opt

and pr_field_declaration fd =
  open_box 0;
  begin
    match fd.fd_modifiers with
    | None -> () | Some ms -> pr_modifiers ms; pr_space()
  end;
  pr_type fd.fd_type; pr_space();
  pr_variable_declarators fd.fd_variable_declarators; pr_semicolon();
  close_box()

and pr_interface_method_declaration amd =
  pr_method_header amd.amd_method_header;
  pr_option pr_block_short amd.amd_body

and pr_class_body_declaration cbd =
  match cbd.cbd_desc with
  | CBDfield fd -> pr_field_declaration fd
  | CBDmethod(mh, b) -> pr_method_declaration mh b
  | CBDclass cd -> pr_class_declaration cd
  | CBDinterface id -> pr_interface_declaration id
  | CBDstaticInitializer b -> pr_string "static "; pr_block_tall b
  | CBDinstanceInitializer b -> pr_block_tall b
  | CBDconstructor cd -> pr_constructor_declaration cd
  | CBDempty -> pr_semicolon()
  | CBDerror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"
  | CBDpointcut p -> pr_pointcut_declaration p
  | CBDdeclare d -> pr_declare_declaration d

and pr_record_body_declaration rbd =
  match rbd.rbd_desc with
  | RBDclass_body_decl c -> pr_class_body_declaration c
  | RBDcompact_ctor_decl c -> pr_compact_ctor_decl c

and pr_compact_ctor_decl ccnd =
  open_box 0;
  begin
    match ccnd.ccnd_modifiers with None -> () | Some ms -> pr_modifiers ms; pad 1
  end;
  pr_id ccnd.ccnd_name;
  close_box();
  pr_constructor_body ccnd.ccnd_body


and pr_declare_declaration dd =
  match dd.dd_desc with
  | DDparents(kwd, c, x_opt, i_opt) ->
      pr_string "declare "; pr_string kwd; pr_colon(); pr_classname_pattern_expr c;
      pr_option pr_extends_class x_opt;
      pr_option pr_implements i_opt;
      pr_semicolon()
  | DDmessage(kwd, p, s) ->
      pr_string "declare "; pr_string kwd; pr_colon(); pr_pointcut_expr p; pr_colon(); pr_primary 0 s; pr_semicolon()
  | DDsoft(kwd, p) ->
      pr_string "declare "; pr_string kwd; pr_colon(); pr_pointcut_expr p; pr_semicolon()
  | DDprecedence(kwd, cl) ->
      pr_string "declare "; pr_string kwd; pr_colon(); pr_classname_pattern_expr_list cl; pr_semicolon()

and pr_classname_pattern_expr_list cl = pr_list pr_comma pr_classname_pattern_expr cl

and pr_pointcut_declaration pcd =
  open_box 0;
  begin
    match pcd.pcd_modifiers with None -> () | Some ms -> pr_modifiers ms; pad 1
  end;
  pr_string "pointcut ";
  pr_id pcd.pcd_name;
  pr_lparen(); pr_formal_parameters pcd.pcd_parameters; pr_rparen();
  begin
    match pcd.pcd_pointcut_expr with
    | None -> ()
    | Some pe -> pr_colon(); pr_pointcut_expr pe
  end;
  pr_semicolon();
  close_box()

and pr_pointcut_expr pe =
  match pe.pe_desc with
  | PEand(pe0, pe1) -> pr_pointcut_expr pe0; pr_string " && "; pr_pointcut_expr pe1
  | PEor(pe0, pe1) -> pr_pointcut_expr pe0; pr_string " || "; pr_pointcut_expr pe1
  | PEnot pe0 -> pr_string "!"; pr_pointcut_expr pe0
  | PEparen pe0 -> pr_lparen(); pr_pointcut_expr pe0; pr_rparen()
  | PEwithin cpe -> pr_string "within"; pr_lparen(); pr_classname_pattern_expr cpe; pr_rparen()

and pr_classname_pattern_expr cpe =
  match cpe.cpe_desc with
  | CPEand(cpe0, cpe1) -> pr_classname_pattern_expr cpe0; pr_string " && "; pr_classname_pattern_expr cpe1
  | CPEor(cpe0, cpe1) -> pr_classname_pattern_expr cpe0; pr_string " || "; pr_classname_pattern_expr cpe1
  | CPEnot cpe0 -> pr_string "!"; pr_classname_pattern_expr cpe0
  | CPEparen cpe0 -> pr_lparen(); pr_classname_pattern_expr cpe0; pr_rparen()
  | CPEname n -> pr_string n
  | CPEnamePlus n -> pr_string n; pr_string "+"

and pr_interface_member_declaration imd =
  match imd.imd_desc with
  | IMDconstant fd -> pr_field_declaration fd
  | IMDinterfaceMethod amd -> pr_interface_method_declaration amd
  | IMDclass cd -> pr_class_declaration cd
  | IMDinterface id -> pr_interface_declaration id
  | IMDempty -> pr_semicolon()

and pr_interface_body ib =
  match ib.ib_member_declarations with
  | [] -> pr_string " {}"
  | ib ->
      pr_block_begin_tall();
      pr_list pr_space pr_interface_member_declaration ib;
      pr_block_end()

and pr_interface_declaration_head kind ifh =
  open_vbox 0;
  open_box 0;
  begin
    match ifh.ifh_modifiers with None -> () | Some ms -> pr_modifiers ms; pr_space()
  end;
  pr_string (kind^" "); pr_id ifh.ifh_identifier;
  pr_option pr_type_parameters ifh.ifh_type_parameters;
  pr_option pr_extends_interfaces ifh.ifh_extends_interfaces;
  pr_option pr_permits ifh.ifh_permits;
  close_box()

and pr_interface_declaration ifd =
  match ifd.ifd_desc with
  | IFDnormal(ih, body) ->
      pr_interface_declaration_head "interface" ih;
      pr_interface_body body; close_box()
  | IFDannotation(ih, body) ->
      pr_interface_declaration_head "@interface" ih;
      pr_annotation_type_body body; close_box()

and pr_annotation_type_body atb =
  match atb.atb_member_declarations with
  | [] -> pr_string " {}"
  | eds ->
      pr_block_begin_tall();
      pr_list pr_space pr_annotation_type_member_declaration eds;
      pr_block_end()

and pr_constant_declaration cd = pr_field_declaration cd

and pr_annotation_type_member_declaration atmd =
  match atmd.atmd_desc with
  | ATMDconstant cd -> pr_constant_declaration cd
  | ATMDelement(ms_opt, ty, id, dl, dv_opt) ->
      open_box 0;
      begin
        match ms_opt with None -> () | Some ms -> pr_modifiers ms; pad 1
      end;
      pr_type ty; pad 1; pr_id id; pr_string "()";
      pr_list pr_space pr_annot_dim dl;
      begin
        match dv_opt with
        | Some _ -> pr_string " default "
        | _ -> ()
      end;
      pr_option pr_element_value dv_opt;
      pr_semicolon();
      close_box()

  | ATMDclass cd -> pr_class_declaration cd
  | ATMDinterface id -> pr_interface_declaration id
  | ATMDempty -> pr_semicolon()

and pr_annot_dims adims = pr_list pr_space pr_annot_dim adims;

and pr_annot_dim adim =
  pr_annotations adim.ad_annotations;
  if adim.ad_ellipsis then
    pr_string ""
  else
    pr_string "[]"

and pr_explicit_constructor_invocation eci =
  match eci.eci_desc with
  | ECIthis(tyargs, args) ->
      pr_option pr_type_arguments tyargs;
      pr_string "this"; pr_arguments args;
  | ECIsuper(tyargs, args) ->
      pr_option pr_type_arguments tyargs;
      pr_string "super"; pr_arguments args;
  | ECIprimary(p, tyargs, args) ->
      pr_primary (get_precedence ".") p;
      pr_string ".";
      pr_option pr_type_arguments tyargs;
      pr_string "super"; pr_arguments args;
      pr_semicolon()
  | ECIname(n, tyargs, args) ->
      pr_name n;
      pr_string ".";
      pr_option pr_type_arguments tyargs;
      pr_string "super"; pr_arguments args;
      pr_semicolon()
  | ECIerror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"

and pr_constructor_body cnb =
  match cnb.cnb_explicit_constructor_invocation, cnb.cnb_block with
  | Some eci, [] ->
      pr_block_begin_tall();
      pr_explicit_constructor_invocation eci;
      pr_block_end()
  | Some eci, bss ->
      pr_block_begin_tall();
      pr_explicit_constructor_invocation eci;
      pr_block_statements_tall bss;
      pr_block_end()
  | None, [] -> pr_string " {}"
  | None, bss ->
      pr_block_begin_short();
      pr_block_statements_tall bss; pr_block_end()

and pr_constructor_declaration cnd =
  open_box 0;
  begin
    match cnd.cnd_modifiers with None -> () | Some ms -> pr_modifiers ms; pad 1
  end;
  pr_option pr_type_parameters cnd.cnd_type_parameters;
  pr_id cnd.cnd_name; pr_lparen();
  pr_formal_parameters cnd.cnd_parameters; pr_rparen();
  pr_throws_op cnd.cnd_throws;
  close_box();
  pr_constructor_body cnd.cnd_body


and pr_class_body_declarations cbds =
  pr_list pr_space pr_class_body_declaration cbds

and pr_class_body cb =
  match cb.cb_class_body_declarations with
  | [] -> pr_string " {}"
  | body ->
      pr_block_begin_tall();
      pr_class_body_declarations body;
      pr_block_end()

and pr_record_body_declarations rbds =
  pr_list pr_space pr_record_body_declaration rbds

and pr_record_body rb =
  match rb.rb_record_body_declarations with
  | [] -> pr_string " {}"
  | body ->
      pr_block_begin_tall();
      pr_record_body_declarations body;
      pr_block_end()

and pr_enum_body eb =
  match eb.eb_enum_constants, eb.eb_class_body_declarations with
  | [], [] -> pr_string " {}"
  | ecs, body ->
      pr_block_begin_short();
      pr_enum_constants ecs;
      pr_class_body_declarations body;
      pr_block_end()

and pr_aspect_body ab =
  match ab.abd_aspect_body_declarations with
  | [] -> pr_string " {}"
  | body ->
      pr_block_begin_tall();
      pr_class_body_declarations body;
      pr_block_end()

and pr_arguments args = pr_lparen(); pr_argument_list args; pr_rparen()

and pr_enum_constants ecs = pr_hovlist pr_comma pr_enum_constant ecs

and pr_enum_constant ec =
  pr_annotations ec.ec_annotations;
  pr_id ec.ec_identifier;
  (match ec.ec_arguments with | None -> () | Some args -> pr_arguments args);
  (match ec.ec_class_body with | None -> () | Some body -> pr_class_body body)

and pr_extends_class exc =
  pr_break 1 indent;
  pr_string "extends ";
  pr_type exc.exc_class

and pr_extends_interfaces exi =
  pr_break 1 indent;
  pr_string "extends ";
  pr_types exi.exi_interfaces

and pr_implements im =
    pr_break 1 indent;
    pr_string "implements ";
    pr_types im.im_interfaces

and pr_implements_op = function
  | None -> ()
  | Some cls -> pr_implements cls

and pr_permits pm =
    pr_break 1 indent;
    pr_string "permits ";
    open_box 0; pr_list pr_comma pr_name pm.pm_type_names; close_box()

and pr_permits_op = function
  | None -> ()
  | Some pm -> pr_permits pm

and pr_type_parameters tps =
  pr_string "<";
  pr_list pr_comma pr_type_parameter tps.tps_type_parameters;
  pr_string ">"

and pr_type_parameter tp =
  pr_annotations tp.tp_annotations;
  pr_id tp.tp_type_variable;
  match tp.tp_type_bound with
  | None -> ()
  | Some tb ->
      pr_string " extends ";
      pr_type tb.tb_reference_type;
      pr_list pr_space (fun ab -> pr_string "& "; pr_type ab.ab_interface) tb.tb_additional_bounds

and pr_class_declaration_head kind ch =
  open_vbox 0;
  open_box 0;
  begin
    match ch.ch_modifiers with None -> () | Some ms -> pr_modifiers ms; pr_space()
  end;
  pr_string (kind^" "); pr_id ch.ch_identifier;
  pr_option pr_type_parameters ch.ch_type_parameters;
  close_box();
  pr_option pr_extends_class ch.ch_extends_class;
  pr_implements_op ch.ch_implements;
  pr_permits_op ch.ch_permits;
  close_box()

and pr_record_declaration_head kind rh =
  open_vbox 0;
  open_box 0;
  begin
    match rh.rh_modifiers with None -> () | Some ms -> pr_modifiers ms; pr_space()
  end;
  pr_string (kind^" "); pr_id rh.rh_identifier;
  pr_option pr_type_parameters rh.rh_type_parameters;
  pr_lparen(); pr_formal_parameters rh.rh_record_header; pr_rparen();
  close_box();
  pr_implements_op rh.rh_implements;
  close_box()

and pr_module_declaration m =
  pr_module_declaration_head m.mod_head;
  pr_space();
  pr_module_body m.mod_body

and pr_module_declaration_head mdh =
  begin
    match mdh.mdh_annotations with
    | [] -> ()
    | a -> pr_annotations a; pr_space()
  end;
  begin
    match mdh.mdh_open with
    | Some _ -> pr_string "open "
    | _ -> ()
  end;
  pr_string "module "; pr_name mdh.mdh_name

and pr_module_body mb =
  match mb.mb_module_directives with
  | [] -> pr_string " {}"
  | ds ->
      pr_block_begin_tall();
      pr_list pr_space pr_module_directive ds;
      pr_block_end()

and pr_module_name mn = pr_name mn.mn_name

and pr_module_directive md =
  match md.md_desc with
  | MDrequires(ms, n) ->
      open_box 0;
      pr_string "requires ";
      begin
        match ms with
        | [] -> ()
        | _ -> pr_list pr_space pr_modifier ms; pr_space()
      end;
      pr_name n;
      pr_semicolon();
      close_box()

  | MDexports(n, ns) ->
      open_box 0;
      pr_string "exports "; pr_name n;
      begin
        match ns with
        | [] -> ()
        | _ ->
            pr_space(); pr_string "to";
            open_box 0; pr_space(); pr_list pr_comma pr_module_name ns; close_box()
      end;
      pr_semicolon();
      close_box()

  | MDopens(n, ns) ->
      open_box 0;
      pr_string "opens "; pr_name n;
      begin
        match ns with
        | [] -> ()
        | _ ->
            pr_space(); pr_string "to";
            open_box 0; pr_space(); pr_list pr_comma pr_module_name ns; close_box()
      end;
      pr_semicolon();
      close_box()

  | MDuses n -> pr_string "uses "; pr_name n; pr_semicolon()

  | MDprovides(n, ns) ->
      open_box 0;
      pr_string "provides "; pr_name n;
      begin
        match ns with
        | [] -> ()
        | _ ->
            pr_space(); pr_string "with";
            open_box 0; pr_space(); pr_list pr_comma pr_module_name ns; close_box()
      end;
      pr_semicolon();
      close_box()

and pr_class_declaration cd =
  match cd.cd_desc with
  | CDclass(ch, body) -> pr_class_declaration_head "class" ch; pr_class_body body; close_box()
  | CDenum(eh, body)  -> pr_class_declaration_head "enum" eh; pr_enum_body body; close_box()
  | CDrecord(rh, body) -> pr_record_declaration_head "record" rh; pr_record_body body; close_box()
  | CDaspect(ah, body) -> pr_class_declaration_head "aspect" ah; pr_aspect_body body; close_box()

let pr_type_declaration td =
  match td.td_desc with
  | TDclass cd -> pr_class_declaration cd
  | TDinterface id -> pr_interface_declaration id
  | TDempty -> pr_semicolon()
  | TDerror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"
  | TDorphan cbd -> pr_class_body_declaration cbd

let pr_type_declarations = pr_list pr_newline pr_type_declaration

let pr_package_declaration pd =
  pr_annotations pd.pd_annotations;
  pr_string "package ";
  pr_name pd.pd_name;
  pr_semicolon()

let pr_import_declaration id =
  match id.id_desc with
  | IDsingle n -> pr_string "import "; pr_name n; pr_semicolon()
  | IDtypeOnDemand n -> pr_string "import "; pr_name n; pr_string ".*;"
  | IDsingleStatic(n, i) ->
      pr_string "import static ";
      pr_name n; pr_string ".";
      pr_id i;
      pr_semicolon()
  | IDstaticOnDemand n ->
      pr_string "import static "; pr_name n; pr_string ".*;"
  | IDerror s -> pr_string "<ERROR:"; pr_string s; pr_string ">"

let pr_import_declarations = pr_list pr_newline pr_import_declaration

let pr_compilation_unit { cu_package=pd_op; cu_imports=ids; cu_tydecls=tds; cu_modecl=mo } =
  let _ =
    match pd_op with
    | Some pd -> pr_package_declaration pd; pr_newline()
    | None -> ()
  in
  let _ =
    match ids with
    | [] -> ()
    | _ -> pr_import_declarations ids; pr_newline()
  in
  pr_type_declarations tds;
  pr_option pr_module_declaration mo;
  pr_newline()
