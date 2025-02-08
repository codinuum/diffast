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
(* java/java_label.ml *)

module Xset = Diffast_misc.Xset
module Xlist = Diffast_misc.Xlist
module Xhash = Diffast_misc.Xhash
module XML = Diffast_misc.XML
module Loc = Diffast_misc.Loc
module Astml = Diffast_core.Astml
module Spec = Diffast_core.Spec
module Lang_base = Diffast_core.Lang_base
module Charpool = Diffast_core.Charpool

module Ast = Java_parsing.Ast
module Printer = Java_parsing.Printer

open Printf


type name = string
type identifier = string
type signature = string

let lang_prefix = Astml.java_prefix


let ident_attr_name   = Astml.ident_attr_name
(*let vdids_attr_name   = Astml.vdids_attr_name*)
let label_attr_name   = Astml.label_attr_name
let dims_attr_name    = Astml.dims_attr_name
let islocal_attr_name = Astml.islocal_attr_name
let isstmt_attr_name  = Astml.isstmt_attr_name

let keyroot_depth_min = 4

type tie_id = Lang_base.tie_id

let null_tid      = Lang_base.null_tid
let mktid         = Lang_base.mktid
let hash_of_tid   = Lang_base.hash_of_tid
let tid_to_string = Lang_base.tid_to_string
let anonymize_tid = Lang_base.anonymize_tid
let mktidattr     = Lang_base.mktidattr
let mkstmttidattr = Lang_base.mkstmttidattr

let xmlenc = XML.encode_string
let xmldec = XML.decode_string


module type T = sig
  include Spec.LABEL_T

  val lang_prefix              : string

  val is_method                : t -> bool
  val is_if                    : t -> bool
  val is_while                 : t -> bool
  val is_do                    : t -> bool
  val is_return                : t -> bool
  val is_parameter             : t -> bool
  val is_parameters            : t -> bool
  val is_typeparameter         : t -> bool
  val is_typeparameters        : t -> bool
  val is_typearguments         : ?nth:int -> t -> bool
  (*val is_statement             : t -> bool*)
  val is_field                 : t -> bool
  val is_type                  : t -> bool
  val is_class                 : t -> bool
  val is_interface             : t -> bool
  val is_class_or_interface    : t -> bool
  val is_typedeclaration       : t -> bool
  val is_enum                  : t -> bool
  val is_implements            : t -> bool
  val is_classbody             : t -> bool
  val is_classbodydecl         : t -> bool
  val is_enumbody              : t -> bool
  val is_interfacebody         : t -> bool
  val is_annotationtype        : t -> bool
  val is_annotationtypebody    : t -> bool
  val is_annotations           : t -> bool
  val is_annotation            : t -> bool
  val is_enumconstant          : t -> bool
  val is_final                 : t -> bool
  val is_public                : t -> bool
  val is_protected             : t -> bool
  val is_private               : t -> bool
  val is_methodbody            : t -> bool
  val is_methodinvocation      : t -> bool
  val is_extends               : t -> bool
  val is_extendsinterfaces     : t -> bool
  val is_modifiers             : t -> bool
  val is_modifier              : t -> bool
  val is_localvariabledecl     : t -> bool
  val is_variabledeclarator    : t -> bool
  val is_literal               : t -> bool
  val is_name                  : t -> bool
  val is_instancecreation      : t -> bool
  val is_ctorinvocation        : t -> bool
  val is_assert                : t -> bool
  val is_forinit               : t -> bool
  val is_forcond               : t -> bool
  val is_forupdate             : t -> bool
  val is_assignment            : t -> bool
  val is_qualifier             : t -> bool
  val is_arguments             : t -> bool
  val is_arraycreation         : t -> bool
  val is_importdeclarations    : t -> bool
  val is_throws                : t -> bool
  val is_expression            : t -> bool
  val is_invocation            : t -> bool
  val is_primary               : t -> bool
  val is_unaryop               : t -> bool
  val is_binaryop              : t -> bool
  val is_block                 : t -> bool
  val is_ctor                  : t -> bool
  val is_ctorbody              : t -> bool
  val is_staticinit            : t -> bool
  val is_instanceinit          : t -> bool
  val is_packagedeclaration    : t -> bool
  val is_compilationunit       : t -> bool
  val is_fieldaccess           : t -> bool
  val is_primarythis           : t -> bool
  val is_primaryname           : t -> bool
  val is_specifier             : t -> bool
  val is_switchblock           : t -> bool
  val is_switchblockstmtgroup  : t -> bool
  val is_switchlabel           : t -> bool
  val is_arrayinitializer      : t -> bool
  val is_explicitctorinvok     : t -> bool
  val is_blockstatement        : t -> bool
  val is_elementvalue          : t -> bool
  val is_type_bound            : t -> bool

  val getlab                   : Spec.node_t -> t

end




type dims = int (* dimension *)

let vdid_to_string (n, d) = n ^ "[" ^ (string_of_int d)
let vdids_to_string = Xlist.to_string vdid_to_string ";"

(*!20240205!*)let vdid_to_name (n, _) = n
let vdids_to_name = Xlist.to_string vdid_to_name ";"

let rec conv_name ?(resolve=true) n =
  match n.Ast.n_desc with
  | Ast.Nsimple(attr, ident) -> begin
      if resolve then
        try
          Ast.get_resolved_name !attr
        with
          Not_found -> ident
      else
        ident
  end
  | Ast.Nqualified(attr, name, al, ident) -> begin
      let sep =
        match (Ast.get_name_attribute name), !attr with
        | Ast.NAtype _, Ast.NAtype _ when resolve -> "$"
        | _ -> "."
      in
      if resolve then
        try
          Ast.get_resolved_name !attr
        with
          Not_found -> (conv_name name)^sep^ident
      else
        (conv_name ~resolve name)^sep^(Printer.annotations_to_string al)^ident
  end
  | Ast.Nerror s -> s

let conv_loc
    { Ast.Loc.start_offset = so;
      Ast.Loc.end_offset   = eo;
      Ast.Loc.start_line   = sl;
      Ast.Loc.start_char   = sc;
      Ast.Loc.end_line     = el;
      Ast.Loc.end_char     = ec;
      _
    } =
  Loc.make so eo sl sc el ec

open Charpool

module Type = struct
  type t =
    | Byte | Short | Int | Long | Char
    | Float | Double
    | Boolean
    | ClassOrInterface of name
    | Class of name | Interface of name
    | Array of t (* other than array *) * dims
    | Void (* not a type (only for convenience) *)

  let common_classes =
    let s = Xset.create 0 in
    List.iter (Xset.add s)
      ["java.lang.Object";
       "java.lang.Void";
       "java.lang.Character";
       "java.lang.String";
       "java.lang.Byte";
       "java.lang.Short";
       "java.lang.Integer";
       "java.lang.Long";
       "java.lang.Float";
       "java.lang.Double";
       "java.lang.reflect.Array";
       "java.lang.reflect.Modifier";
       "java.lang.reflect.Constructor";
       "java.lang.reflect.Method";
       "java.lang.reflect.Parameter";
       "java.lang.reflect.Field";
       "java.lang.NullPointerException";
       "java.util.List";
       "java.util.Collection";
       "java.util.Iterator";
       "java.util.Map";
       "java.util.Set";
       "java.util.ArrayList";
       "java.util.HashMap";
       "java.util.BitSet";
       "java.util.HashSet";
     ];
    s

  let rec is_common = function
    | Byte | Short | Int | Long | Char
    | Float | Double | Boolean | Void
      -> true
    | ClassOrInterface n
    | Class n
      -> Xset.mem common_classes n
    | Array(ty, _) -> is_common ty
    | _ -> false

  let rec get_name = function
    | ClassOrInterface name
    | Class name
    | Interface name -> name
    | Array(ty, _) -> get_name ty
(*    | Array(ty, dims) -> begin
        let dims_str = Printer.dims_to_short_string dims in
        let ty_str =
          try
            get_name ty
          with _ ->
            match ty with
            | Byte    -> "B"
            | Short   -> "S"
            | Int     -> "I"
            | Long    -> "J"
            | Char    -> "C"
            | Float   -> "F"
            | Double  -> "D"
            | Boolean -> "Z"
            | _ -> ""
        in
        ty_str^dims_str
    end*)
    | _ -> raise Not_found

  let get_dimensions = function
    | Array(_, dims) -> dims
    | _ -> 0

  let rec is_named = function
    | ClassOrInterface _
    | Class _
    | Interface _ -> true
    | Array(ty, _) -> (*true*)is_named ty
    | _ -> false

  let rec is_named_orig = function
    | ClassOrInterface _
    | Class _
    | Interface _ -> true
    | Array(ty, _) -> is_named_orig ty
    | _ -> false

  let rec type_argument_to_string ?(resolve=true) ta =
    match ta.Ast.ta_desc with
    | Ast.TAreferenceType ty -> to_simple_string (of_javatype ~resolve ty)
    | Ast.TAwildcard wc      -> wildcard_to_string ~resolve wc

  and wildcard_bounds_to_string ?(resolve=true) wb =
    match wb.Ast.wb_desc with
    | Ast.WBextends ty -> "extends "^(to_simple_string (of_javatype ~resolve ty))
    | Ast.WBsuper ty   -> "super "^(to_simple_string (of_javatype ~resolve ty))

  and wildcard_to_string ?(resolve=true) = function
    | al, None    -> (Printer.annotations_to_string al)^"?"
    | al, Some wb ->
        (Printer.annotations_to_string al)^"? "^(wildcard_bounds_to_string ~resolve wb)

  and type_arguments_to_string ?(resolve=true) tas =
    "<"^
    (Xlist.to_string (type_argument_to_string ~resolve) "," tas.Ast.tas_type_arguments)^
    ">"

  and type_spec_to_string ?(resolve=true) = function
    | Ast.TSname(_, n)       -> conv_name ~resolve n
    | Ast.TSapply(_, n, tas) -> (conv_name ~resolve n)^(type_arguments_to_string ~resolve tas)

  and type_spec_to_name ?(resolve=true) = function
    | Ast.TSname(_, n)
    | Ast.TSapply(_, n, _) -> conv_name ~resolve n

  and conv_type_specs ?(resolve=true) tss =
    Xlist.to_string (type_spec_to_name ~resolve) "." tss

  and to_string ty =
    let rec conv = function
      | Byte    -> "Byte"
      | Short   -> "Short"
      | Int     -> "Int"
      | Long    -> "Long"
      | Char    -> "Char"
      | Float   -> "Float"
      | Double  -> "Double"
      | Boolean -> "Boolean"
      | ClassOrInterface n -> sprintf "ClassOrInterface(%s)" n
      | Class n            -> sprintf "Class(%s)" n
      | Interface n        -> sprintf "Interface(%s)" n
      | Array(lab, dim)    -> sprintf "Array(%s,%d)" (conv lab) dim
      | Void               -> "Void"
    in
    "Type." ^ (conv ty)

  and strip = function
    | Array(lab, _) -> Array(strip lab, 0)
    | ty            -> ty

  and anonymize = function
    | ClassOrInterface _ -> ClassOrInterface ""
    | Class _            -> Class ""
    | Interface _        -> Interface ""
    | Array(lab, _)    -> Array(anonymize lab, 0)
    (*| Byte
    | Short | Int | Long -> Byte
    | Float | Double     -> Float*)
    | ty                 -> ty

  and anonymize2 = function
    | _ -> Void
  (*and anonymize2 = function
    | ClassOrInterface n
    | Class n
    | Interface n     -> ClassOrInterface ""
    | Array(lab, dim) -> Array(anonymize2 lab, 0)
    | _               -> Void*)

  and dims_to_string dims = if dims = 0 then "" else "[]"^(dims_to_string (dims - 1))

  and to_simple_string = function
    | Byte    -> "byte"
    | Short   -> "short"
    | Int     -> "int"
    | Long    -> "long"
    | Char    -> "char"
    | Float   -> "float"
    | Double  -> "double"
    | Boolean -> "boolean"
    | ClassOrInterface n -> n
    | Class n            -> n
    | Interface n        -> n
    | Array(lab, dim)    -> (to_simple_string lab)^(dims_to_string dim)
    | Void -> "void"

  and to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Byte    -> mkstr 0
    | Short   -> mkstr 1
    | Int     -> mkstr 2
    | Long    -> mkstr 3
    | Char    -> mkstr 4
    | Float   -> mkstr 5
    | Double  -> mkstr 6
    | Boolean -> mkstr 7
    | ClassOrInterface n -> combo 8 [n]
    | Class n            -> combo 9 [n]
    | Interface n        -> combo 10 [n]
    | Array(lab, dim)    -> catstr [mkstr 11; to_short_string ~ignore_identifiers_flag lab; string_of_int dim]
    | Void -> mkstr 12


  and to_tag ty =
    let rec conv = function
      | Byte               -> "ByteType", []
      | Short              -> "ShortType", []
      | Int                -> "IntType", []
      | Long               -> "LongType", []
      | Char               -> "CharType", []
      | Float              -> "FloatType", []
      | Double             -> "DoubleType", []
      | Boolean            -> "BooleanType", []
      | ClassOrInterface n -> "ReferenceType", ["name",xmlenc n]
      | Class n            -> "ClassType", ["name",xmlenc n]
      | Interface n        -> "InterfaceType", ["name",xmlenc n]
      | Array(lab, dims)   ->
          let name, attrs = conv lab in
          name, attrs @ ["dimensions",string_of_int dims]
      | Void               -> "Void", []
    in
    let name, attrs = conv ty in
    name, attrs

  and of_primitive_type = function
    | Ast.PTbyte    -> Byte
    | Ast.PTshort   -> Short
    | Ast.PTint     -> Int
    | Ast.PTlong    -> Long
    | Ast.PTchar    -> Char
    | Ast.PTfloat   -> Float
    | Ast.PTdouble  -> Double
    | Ast.PTboolean -> Boolean

  and of_javatype ?(resolve=true) ty =
    match ty.Ast.ty_desc with
    | Ast.Tprimitive(_, p)      -> of_primitive_type p
    | Ast.TclassOrInterface tss -> ClassOrInterface (conv_type_specs ~resolve tss)
    | Ast.Tclass tss            -> Class (conv_type_specs ~resolve tss)
    | Ast.Tinterface tss        -> Interface (conv_type_specs ~resolve tss)
    | Ast.Tarray(ty, dims)      -> Array(of_javatype ~resolve ty, List.length dims)
    | Ast.Tvoid                 -> Void


  let make_class ?(resolve=true) name = Class (conv_name ~resolve name)

end (* of module Type *)


module Literal = struct
  type t =
    | Integer of string
    | FloatingPoint of string
    | True | False
    | Character of string
    | String of string
    | TextBlock of string
    | Null

  let utf8_escape_pat = Str.regexp "\\\\u\\([0-9a-fA-F]+\\)"
  let unescape_utf8 s =
    let enc1 i =
      let l =
        if i < 0x80 then
          [i land 0x7f]
        else if i < 0x0800 then
          [i lsr 6 land 0x1f lor 0xc0;
           i land 0x3f lor 0x80]
        else if i < 0x010000 then
          [i lsr 12 land 0x0f lor 0xe0;
           i lsr 6 land 0x3f lor 0x80;
           i land 0x3f lor 0x80]
        else if i < 0x110000 then
          [i lsr 18 land 0x07 lor 0xf0;
           i lsr 12 land 0x3f lor 0x80;
           i lsr 6 land 0x3f lor 0x80;
           i land 0x3f lor 0x80]
        else
          invalid_arg "enc1"
      in
      "\\" ^ (String.concat "\\" (List.map string_of_int l))
    in
    let conv = function
      | Str.Delim u -> begin
          try
            let i = int_of_string (Str.replace_first utf8_escape_pat "0x\\1" u) in
            if i < 8 then
              "\\" ^ (string_of_int i)
            else if i = 0xb then
              "\\u000b"
            else
              try
                Scanf.unescaped (enc1 i)
              with _ -> u
          with _ -> u
      end
      | Str.Text t -> t
    in
    String.concat "" (List.map conv (Str.full_split utf8_escape_pat s))

  let escaped_double_quote_pat = Str.regexp_string "\\\""

  let reduce_char s = (* remove slash followed by double quote *)
    let s0 = unescape_utf8 s in
    Str.global_replace escaped_double_quote_pat "\"" s0

  let escaped_single_quote_pat = Str.regexp_string "\\'"
  let tab_pat = Str.regexp_string "\t"

  let reduce_string s = (* remove slash followed by single quote and unescape UTF8 *)
    let s0 = unescape_utf8 s in
    let s1 = Str.global_replace escaped_single_quote_pat "'" s0 in
    Str.global_replace tab_pat "\\t" s1


  let of_literal
      ?(anonymize_int=false)
      ?(anonymize_float=false)
      ?(anonymize_string=false)
      ?(reduce=false)
      =
    function
      | Ast.Linteger _ when anonymize_int -> (Integer "")
      | Ast.LfloatingPoint _ when anonymize_float -> (FloatingPoint "")
      | Ast.Lstring _ when anonymize_string -> (String "")
      | Ast.LtextBlock _ when anonymize_string -> (TextBlock "")

      | Ast.Lcharacter str when reduce -> (Character (reduce_char str))
      | Ast.Lstring str when reduce -> (String (reduce_string str))
      | Ast.LtextBlock str when reduce -> (TextBlock (reduce_string str))

      | Ast.Linteger str -> (Integer str)
      | Ast.LfloatingPoint str -> (FloatingPoint str)
      | Ast.Ltrue -> True
      | Ast.Lfalse -> False
      | Ast.Lcharacter str -> (Character str)
      | Ast.Lstring str -> (String str)
      | Ast.LtextBlock str -> (TextBlock str)
      | Ast.Lnull -> Null

  let to_string lit =
    let str =
      match lit with
      | Integer str -> sprintf "Integer(%s)" str
      | FloatingPoint str -> sprintf "FloatingPoint(%s)" str
      | True -> "True"
      | False -> "False"
      | Character str -> sprintf "Character(%s)" str
      | String str -> sprintf "String(%s)" str
      | TextBlock str -> sprintf "TextBlock(%s)" str
      | Null -> "Null"
    in
    "Literal." ^ str

  let anonymize = function
    | Integer _       -> Integer ""
    | FloatingPoint _ -> FloatingPoint ""
    | Character _     -> Character ""
    | String _        -> String ""
    | TextBlock _     -> TextBlock ""
    (*| True | False    -> False*)
    | lit             -> lit

  (*let anonymize2 = function
    | Integer _ | FloatingPoint _ -> Integer ""
    | Character _ | String _      -> Character ""
    | True | False                -> False
    | lit                         -> lit*)

  let to_simple_string = function
    | Integer str       -> str
    | FloatingPoint str -> str
    | True              -> "true"
    | False             -> "false"
    | Character str     -> sprintf "'%s'" str
    | String str        ->
        if (String.length str) > string_len_threshold then
          "\""^(Digest.to_hex (Digest.string str))^"\""
        else
          "\""^(String.escaped str)^"\""
    | TextBlock str     ->
        if (String.length str) > string_len_threshold then
          "\""^(Digest.to_hex (Digest.string str))^"\""
        else
          "\""^(String.escaped str)^"\""
    | Null              -> "null"

  let to_value = function
    | Integer str       -> str
    | FloatingPoint str -> str
    | True              -> "true"
    | False             -> "false"
    | Character str     -> sprintf "'%s'" str
    | String str        -> "\""^str^"\""
    | TextBlock str     -> "\"\"\""^str^"\"\"\""
    | Null              -> "null"

  let to_short_string = function
    | Integer str       -> catstr [mkstr 0; str]
    | FloatingPoint str -> catstr [mkstr 1; str]
    | True              -> mkstr 2
    | False             -> mkstr 3
    | Character str     -> catstr [mkstr 4; str]
    | String str        ->
        if (String.length str) > string_len_threshold then
          catstr [mkstr 5; Digest.to_hex (Digest.string str)]
        else
          catstr [mkstr 6; str]
    | TextBlock str     ->
        if (String.length str) > string_len_threshold then
          catstr [mkstr 7; Digest.to_hex (Digest.string str)]
        else
          catstr [mkstr 8; str]
    | Null              -> mkstr 9

  let to_tag lit =
    let name, attrs =
      match lit with
      | Integer str       -> "IntegerLiteral", ["value",xmlenc str]
      | FloatingPoint str -> "FloatingPointLiteral", ["value",xmlenc str]
      | True              -> "True", []
      | False             -> "False", []
      | Character str     -> "CharacterLiteral", ["value",xmlenc str]
      | String str        -> "StringLiteral", ["value",xmlenc str]
      | TextBlock str     -> "TextBlockLiteral", ["value",xmlenc str]
      | Null              -> "NullLiteral", []
    in
    name, attrs

end (* of module Literal *)


module AssignmentOperator = struct
  type t =
    | Eq | MulEq | DivEq | ModEq | AddEq | SubEq | ShiftLEq
    | ShiftREq | ShiftRUEq | AndEq | XorEq | OrEq

  let to_string ao =
    let str =
      match ao with
      | Eq        -> "Eq"
      | MulEq     -> "MulEq"
      | DivEq     -> "DivEq"
      | ModEq     -> "ModEq"
      | AddEq     -> "AddEq"
      | SubEq     -> "SubEq"
      | ShiftLEq  -> "ShiftLEq"
      | ShiftREq  -> "ShiftREq"
      | ShiftRUEq -> "ShiftRUEq"
      | AndEq     -> "AndEq"
      | XorEq     -> "XorEq"
      | OrEq      -> "OrEq"
    in
    "AssignmentOperator." ^ str

  let to_simple_string = function
    | Eq        -> "="
    | MulEq     -> "*="
    | DivEq     -> "/="
    | ModEq     -> "%="
    | AddEq     -> "+="
    | SubEq     -> "-="
    | ShiftLEq  -> "<<="
    | ShiftREq  -> ">>="
    | ShiftRUEq -> ">>>="
    | AndEq     -> "&="
    | XorEq     -> "^="
    | OrEq      -> "|="

  let to_short_string = function
    | Eq        -> mkstr 0
    | MulEq     -> mkstr 1
    | DivEq     -> mkstr 2
    | ModEq     -> mkstr 3
    | AddEq     -> mkstr 4
    | SubEq     -> mkstr 5
    | ShiftLEq  -> mkstr 6
    | ShiftREq  -> mkstr 7
    | ShiftRUEq -> mkstr 8
    | AndEq     -> mkstr 9
    | XorEq     -> mkstr 10
    | OrEq      -> mkstr 11


  let of_assignment_operator ao =
    let conv = function
      | Ast.AOeq        -> Eq
      | Ast.AOmulEq     -> MulEq
      | Ast.AOdivEq     -> DivEq
      | Ast.AOmodEq     -> ModEq
      | Ast.AOaddEq     -> AddEq
      | Ast.AOsubEq     -> SubEq
      | Ast.AOshiftLEq  -> ShiftLEq
      | Ast.AOshiftREq  -> ShiftREq
      | Ast.AOshiftRUEq -> ShiftRUEq
      | Ast.AOandEq     -> AndEq
      | Ast.AOxorEq     -> XorEq
      | Ast.AOorEq      -> OrEq
    in
    conv ao.Ast.ao_desc

  let to_tag ao attrs =
    let name =
      match ao with
      | Eq        -> "Assign"
      | MulEq     -> "MultAssign"
      | DivEq     -> "DivAssign"
      | ModEq     -> "ModAssign"
      | AddEq     -> "AddAssign"
      | SubEq     -> "SubtAssign"
      | ShiftLEq  -> "ShiftLAssign"
      | ShiftREq  -> "ShiftRAssign"
      | ShiftRUEq -> "ShiftRUAssign"
      | AndEq     -> "AndAssign"
      | XorEq     -> "XorAssign"
      | OrEq      -> "OrAssign"
    in
    name, attrs

end (* of module AssignmentOperator *)


module UnaryOperator = struct
  type t =
    | PostIncrement | PostDecrement | PreIncrement | PreDecrement
    | Positive | Negative | Complement | Not

  let to_string uo =
    let str =
      match uo with
      | PostIncrement -> "PostIncrement"
      | PostDecrement -> "PostDecrement"
      | PreIncrement  -> "PreIncrement"
      | PreDecrement  -> "PreDecrement"
      | Positive      -> "Positive"
      | Negative      -> "Negative"
      | Complement    -> "Complement"
      | Not           -> "Not"
    in
    "UnaryOperator." ^ str

  let to_simple_string = function
    | PostIncrement -> "++"
    | PostDecrement -> "--"
    | PreIncrement  -> "++"
    | PreDecrement  -> "--"
    | Positive      -> "+"
    | Negative      -> "-"
    | Complement    -> "~"
    | Not           -> "!"

  let to_short_string = function
    | PostIncrement -> mkstr 0
    | PostDecrement -> mkstr 1
    | PreIncrement  -> mkstr 2
    | PreDecrement  -> mkstr 3
    | Positive      -> mkstr 4
    | Negative      -> mkstr 5
    | Complement    -> mkstr 6
    | Not           -> mkstr 7

  let of_unary_operator = function
    | Ast.UOpostIncrement -> PostIncrement
    | Ast.UOpostDecrement -> PostDecrement
    | Ast.UOpreIncrement  -> PreIncrement
    | Ast.UOpreDecrement  -> PreDecrement
    | Ast.UOpositive      -> Positive
    | Ast.UOnegative      -> Negative
    | Ast.UOcomplement    -> Complement
    | Ast.UOnot           -> Not

  let to_tag uo =
    let name =
      match uo with
      | PostIncrement -> "PostIncrement"
      | PostDecrement -> "PostDecrement"
      | PreIncrement  -> "PreIncrement"
      | PreDecrement  -> "PreDecrement"
      | Positive      -> "Plus"
      | Negative      -> "Minus"
      | Complement    -> "Complement"
      | Not           -> "Negation"
    in
    name, []

end (* of module UnaryOperator *)


module BinaryOperator = struct
  type t =
    | Mul | Div | Mod | Add | Sub
    | ShiftL | ShiftR | ShiftRU
    | Eq | Neq | Lt | Gt | Le | Ge
    | BitAnd | BitOr | BitXor | And | Or

  let to_string bo =
    let str =
      match bo with
      | Mul     -> "Mul"
      | Div     -> "Div"
      | Mod     -> "Mod"
      | Add     -> "Add"
      | Sub     -> "Sub"
      | ShiftL  -> "ShiftL"
      | ShiftR  -> "ShiftR"
      | ShiftRU -> "ShiftRU"
      | Eq      -> "Eq"
      | Neq     -> "Neq"
      | Lt      -> "Lt"
      | Gt      -> "Gt"
      | Le      -> "Le"
      | Ge      -> "Ge"
      | BitAnd  -> "BitAnd"
      | BitOr   -> "BitOr"
      | BitXor  -> "BitXor"
      | And     -> "And"
      | Or      -> "Or"
    in
    "BinaryOperator." ^ str

  let to_simple_string = function
    | Mul     -> "*"
    | Div     -> "/"
    | Mod     -> "%"
    | Add     -> "+"
    | Sub     -> "-"
    | ShiftL  -> "<<"
    | ShiftR  -> ">>"
    | ShiftRU -> ">>>"
    | Eq      -> "=="
    | Neq     -> "!="
    | Lt      -> "<"
    | Gt      -> ">"
    | Le      -> "<="
    | Ge      -> ">="
    | BitAnd  -> "&"
    | BitOr   -> "|"
    | BitXor  -> "^"
    | And     -> "&&"
    | Or      -> "||"

  let to_short_string = function
    | Mul     -> mkstr 0
    | Div     -> mkstr 1
    | Mod     -> mkstr 2
    | Add     -> mkstr 3
    | Sub     -> mkstr 4
    | ShiftL  -> mkstr 5
    | ShiftR  -> mkstr 6
    | ShiftRU -> mkstr 7
    | Eq      -> mkstr 8
    | Neq     -> mkstr 9
    | Lt      -> mkstr 10
    | Gt      -> mkstr 11
    | Le      -> mkstr 12
    | Ge      -> mkstr 13
    | BitAnd  -> mkstr 14
    | BitOr   -> mkstr 15
    | BitXor  -> mkstr 16
    | And     -> mkstr 17
    | Or      -> mkstr 18


  let of_binary_operator = function
    | Ast.BOmul     -> Mul
    | Ast.BOdiv     -> Div
    | Ast.BOmod     -> Mod
    | Ast.BOadd     -> Add
    | Ast.BOsub     -> Sub
    | Ast.BOshiftL  -> ShiftL
    | Ast.BOshiftR  -> ShiftR
    | Ast.BOshiftRU -> ShiftRU
    | Ast.BOeq      -> Eq
    | Ast.BOneq     -> Neq
    | Ast.BOlt      -> Lt
    | Ast.BOgt      -> Gt
    | Ast.BOle      -> Le
    | Ast.BOge      -> Ge
    | Ast.BObitAnd  -> BitAnd
    | Ast.BObitOr   -> BitOr
    | Ast.BObitXor  -> BitXor
    | Ast.BOand     -> And
    | Ast.BOor      -> Or

  let to_tag bo =
    let name =
      match bo with
      | Mul     -> "Mult"
      | Div     -> "Div"
      | Mod     -> "Mod"
      | Add     -> "Add"
      | Sub     -> "Subt"
      | ShiftL  -> "ShiftL"
      | ShiftR  -> "ShiftR"
      | ShiftRU -> "ShiftRU"
      | Eq      -> "Eq"
      | Neq     -> "NotEq"
      | Lt      -> "Lt"
      | Gt      -> "Gt"
      | Le      -> "Le"
      | Ge      -> "Ge"
      | BitAnd  -> "BitAnd"
      | BitOr   -> "BitOr"
      | BitXor  -> "BitXor"
      | And     -> "And"
      | Or      -> "Or"
    in
    name, []

  let anonymize3 = function
      | Mul
      | Div
      | Mod
      | Add
      | Sub -> Add
      | ShiftL
      | ShiftR
      | ShiftRU -> ShiftL
      | Eq
      | Neq
      | Lt
      | Gt
      | Le
      | Ge -> Eq
      | BitAnd
      | BitOr
      | BitXor -> BitAnd
      | And
      | Or -> And

end (* of module BinaryOperator *)


module Modifier = struct
  type t =
    | Public
    | Protected
    | Private
    | Static
    | Abstract
    | Final
    | Native
    | Synchronized
    | Transient
    | Volatile
    | Strictfp
(*    | Annotation*)
    | Default
    | Transitive
    | Sealed
    | NonSealed
    | Error of string

  let to_string m =
    let str =
      match m with
      | Public       -> "Public"
      | Protected    -> "Protected"
      | Private      -> "Private"
      | Static       -> "Static"
      | Abstract     -> "Abstract"
      | Final        -> "Final"
      | Native       -> "Native"
      | Synchronized -> "Synchronized"
      | Transient    -> "Transient"
      | Volatile     -> "Volatile"
      | Strictfp     -> "Strictfp"
(*      | Annotation   -> "Annotation"*)
      | Default      -> "Default"
      | Transitive   -> "Transitive"
      | Sealed       -> "Sealed"
      | NonSealed    -> "NonSealed"
      | Error s      -> "Error:"^s
    in
    "Modifier." ^ str

  let anonymize = function
    | Public       -> Public
    | Protected    -> Public
    | Private      -> Public
    | lab -> lab

  let to_simple_string = function
    | Public       -> "public"
    | Protected    -> "protected"
    | Private      -> "private"
    | Static       -> "static"
    | Abstract     -> "abstract"
    | Final        -> "final"
    | Native       -> "native"
    | Synchronized -> "synchronized"
    | Transient    -> "transient"
    | Volatile     -> "volatile"
    | Strictfp     -> "strictfp"
(*    | Annotation   -> "@"*)
    | Default      -> "default"
    | Transitive   -> "transitive"
    | Sealed       -> "sealed"
    | NonSealed    -> "non-sealed"
    | Error s      -> s

  let to_short_string = function
    | Public       -> mkstr 0
    | Protected    -> mkstr 1
    | Private      -> mkstr 2
    | Static       -> mkstr 3
    | Abstract     -> mkstr 4
    | Final        -> mkstr 5
    | Native       -> mkstr 6
    | Synchronized -> mkstr 7
    | Transient    -> mkstr 8
    | Volatile     -> mkstr 9
    | Strictfp     -> mkstr 10
(*    | Annotation   -> mkstr 11*)
    | Default      -> mkstr 12
    | Transitive   -> mkstr 13
    | Sealed       -> mkstr 14
    | NonSealed    -> mkstr 15
    | Error s      -> combo 16 [s]

  let to_tag m =
    match m with
    | Public       -> "Public", []
    | Protected    -> "Protected", []
    | Private      -> "Private", []
    | Static       -> "Static", []
    | Abstract     -> "Abstract", []
    | Final        -> "Final", []
    | Native       -> "Native", []
    | Synchronized -> "Synchronized", []
    | Transient    -> "Transient", []
    | Volatile     -> "Volatile", []
    | Strictfp     -> "Strictfp", []
(*    | Annotation   -> "Annotation"*)
    | Default      -> "Default", []
    | Transitive   -> "Transitive", []
    | Sealed       -> "Sealed", []
    | NonSealed    -> "NonSealed", []
    | Error s      -> "ErrorModifier", ["contents",xmlenc s]

end (* of module Modifier *)


module Primary = struct
  type t =
    | Name of name
    | This
    | Literal of Literal.t
    | ClassLiteral
    | ClassLiteralVoid
    | QualifiedThis of name

    | InstanceCreation of name
    | QualifiedInstanceCreation of name
    | NameQualifiedInstanceCreation of name * identifier

    | FieldAccess of identifier
    | SuperFieldAccess of identifier
    | ClassSuperFieldAccess of identifier

    | PrimaryMethodInvocation of name
    | SimpleMethodInvocation of name
    | SuperMethodInvocation of name
    | ClassSuperMethodInvocation of name
    | TypeMethodInvocation of name * identifier

    | ArrayAccess
    | ArrayCreationInit
    | ArrayCreationDims of dims
    | Paren of tie_id

    | NameMethodReference of name * identifier
    | PrimaryMethodReference of identifier
    | SuperMethodReference of identifier
    | TypeSuperMethodReference of name * identifier
    | TypeNewMethodReference of name

    | AmbiguousName of name
    | AmbiguousMethodInvocation of name

  let get_name = function
    | Name name
    | QualifiedThis name
    | InstanceCreation name
    | QualifiedInstanceCreation name
    | PrimaryMethodInvocation name
    | SimpleMethodInvocation name
    | SuperMethodInvocation name
    | ClassSuperMethodInvocation name
    | FieldAccess name
    | SuperFieldAccess name
    | ClassSuperFieldAccess name
    | PrimaryMethodReference name
    | SuperMethodReference name
    | TypeNewMethodReference name
    | AmbiguousName name
    | AmbiguousMethodInvocation name
      -> name

    | NameQualifiedInstanceCreation(name, ident)
    | TypeMethodInvocation(name, ident)
      -> String.concat "." [name; ident]

    | NameMethodReference(name, ident)
    | TypeSuperMethodReference(name, ident)
      -> String.concat "::" [name; ident]

    | Literal (Literal.String s) ->
        if s = "" then
          raise Not_found
        else
          s
    | Literal (Literal.TextBlock s) ->
        if s = "" then
          raise Not_found
        else
          s
    (*| Literal (Literal.String s) -> s
    | Literal (Literal.Character s|Literal.Integer s|Literal.FloatingPoint s) -> s*)

    |  _ -> raise Not_found

  let is_named = function
    | Name _
    | QualifiedThis _
    | InstanceCreation _
    | QualifiedInstanceCreation _
    | NameQualifiedInstanceCreation _
    | FieldAccess _
    | SuperFieldAccess _
    | ClassSuperFieldAccess _
    | PrimaryMethodInvocation _
    | SimpleMethodInvocation _
    | SuperMethodInvocation _
    | ClassSuperMethodInvocation _
    | TypeMethodInvocation _
    | NameMethodReference _
    | PrimaryMethodReference _
    | SuperMethodReference _
    | TypeSuperMethodReference _
    | TypeNewMethodReference _
    | AmbiguousName _
    | AmbiguousMethodInvocation _
      -> true

    | Literal (Literal.String s) -> s <> ""
    | Literal (Literal.TextBlock s) -> s <> ""
    (*| Literal (Literal.String s) -> true
    | Literal (Literal.Character _|Literal.Integer _|Literal.FloatingPoint _) -> true*)

    | _ -> false

  let is_named_orig = function
    | InstanceCreation _ -> false
    | x -> is_named x

  let to_string p =
    let str =
      match p with
      | Name name -> sprintf "Name(%s)" name
      | This -> "This"
      | Literal lit -> Literal.to_string lit
      | ClassLiteral -> "ClassLiteral"
      | ClassLiteralVoid -> "ClassLiteralVoid"
      | QualifiedThis name -> sprintf "QualifiedThis(%s)" name
(*      | QualifiedNew name -> sprintf "QualifiedNew(%s)" name *)
      | InstanceCreation n -> sprintf "InstanceCreation(%s)" n
      | QualifiedInstanceCreation name ->
          sprintf "QualifiedInstanceCreation(%s)" name

      | NameQualifiedInstanceCreation(name, ident) ->
          sprintf "NameQualifiedInstanceCreation(%s,%s)" name ident

      | FieldAccess name           -> sprintf "FieldAccess(%s)" name
      | SuperFieldAccess name      -> sprintf "SuperFieldAccess(%s)" name
      | ClassSuperFieldAccess name -> sprintf "ClassSuperFieldAccess(%s)" name

      | PrimaryMethodInvocation name -> sprintf "PrimaryMethodInvocation(%s)" name

      | SimpleMethodInvocation name -> sprintf "SimpleMethodInvocation(%s)" name

      | SuperMethodInvocation name -> sprintf "SuperMethodInvocation(%s)" name

      | ClassSuperMethodInvocation name ->
          sprintf "ClassSuperMethodInvocation(%s)" name

      | TypeMethodInvocation(name, ident) ->
          sprintf "TypeMethodInvocation(%s,%s)" name ident

      | ArrayAccess -> "ArrayAccess"

      | ArrayCreationInit      -> "ArrayCreationInit"
      | ArrayCreationDims dims -> sprintf "ArrayCreationDims(%d)" dims

      | Paren tid -> sprintf "Paren(%s)" (tid_to_string tid)

      | NameMethodReference(name, ident)      -> sprintf "NameMethodReference(%s,%s)" name ident
      | PrimaryMethodReference ident          -> sprintf "PrimaryMethodReference(%s)" ident
      | SuperMethodReference ident            -> sprintf "SuperMethodReference(%s)" ident
      | TypeSuperMethodReference(name, ident) -> sprintf "TypeSuperMethodReference(%s,%s)" name ident
      | TypeNewMethodReference _              -> "TypeNewMethodReference"
      | AmbiguousName name                    -> sprintf "AmbiguousName(%s)" name
      | AmbiguousMethodInvocation name        -> sprintf "AmbiguousMethodInvocation(%s)" name
    in
    "Primary." ^ str

  let strip = function
    | ArrayCreationDims _ -> ArrayCreationDims 0
    | Paren _             -> Paren null_tid
    | prim                -> prim

  let anonymize ?(more=false) = function
    | Name _                              -> Name ""
    | Literal lit                         -> Literal (Literal.anonymize lit)
    | QualifiedThis _                     -> QualifiedThis ""
    | InstanceCreation _                  -> InstanceCreation ""
    | QualifiedInstanceCreation _         -> QualifiedInstanceCreation ""
    | NameQualifiedInstanceCreation(_, _) -> NameQualifiedInstanceCreation("", "")
    | FieldAccess _                       -> FieldAccess ""
    | SuperFieldAccess _                  -> SuperFieldAccess ""
    | ClassSuperFieldAccess _             -> ClassSuperFieldAccess ""
    | PrimaryMethodInvocation _           -> PrimaryMethodInvocation ""
    | SimpleMethodInvocation _            -> SimpleMethodInvocation ""
    | SuperMethodInvocation _             -> SuperMethodInvocation ""
    | ClassSuperMethodInvocation _        -> ClassSuperMethodInvocation ""
    | AmbiguousMethodInvocation _         -> AmbiguousMethodInvocation ""
    | TypeMethodInvocation(_, _)          -> TypeMethodInvocation("", "")
    | ArrayCreationDims _                 -> ArrayCreationDims 0
    | Paren tid                           -> Paren (anonymize_tid ~more tid)
    | NameMethodReference(_, _)           -> NameMethodReference("", "")
    | PrimaryMethodReference _            -> PrimaryMethodReference ""
    | SuperMethodReference _              -> SuperMethodReference ""
    | TypeSuperMethodReference(_, _)      -> TypeSuperMethodReference("", "")
    | TypeNewMethodReference _            -> TypeNewMethodReference ""
    | AmbiguousName _                     -> AmbiguousName ""
    | prim                                -> prim

  let anonymize2 = function
    | FieldAccess _
    | SuperFieldAccess _
    | ClassSuperFieldAccess _
    | AmbiguousName _
      -> Name ""

    (*| PrimaryMethodInvocation _
    | SimpleMethodInvocation _
    | SuperMethodInvocation _
    | ClassSuperMethodInvocation _
    | TypeMethodInvocation _
      -> SimpleMethodInvocation ""*)

    (*| Literal lit -> Literal (Literal.anonymize2 lit)*)

    | lab -> anonymize ~more:true lab

  let to_simple_string = function
    | Name name                              -> name
    | This                                   -> "this"
    | Literal lit                            -> Literal.to_simple_string lit
    | ClassLiteral                           -> "class"
    | ClassLiteralVoid                       -> "void.class"
    | QualifiedThis name                     -> name^".this"
    | InstanceCreation _                     -> "new"
    | QualifiedInstanceCreation name         -> name^".new"
    | NameQualifiedInstanceCreation(name, ident) -> name^".new "^ident
    | FieldAccess name                       -> sprintf "<field_acc:%s>" name
    | SuperFieldAccess name                  -> "super."^name
    | ClassSuperFieldAccess name             -> "class.super."^name
    | PrimaryMethodInvocation name           -> name
    | SimpleMethodInvocation name            -> name
    | SuperMethodInvocation name             -> "super."^name
    | ClassSuperMethodInvocation name        -> "class.super."^name
    | TypeMethodInvocation(name, ident)      -> name^"."^ident
    | ArrayAccess                            -> "<array_acc>"
    | ArrayCreationInit                      -> "<array_init>"
    | ArrayCreationDims dims                 -> sprintf "<array_new:%d>" dims
    | Paren _                                -> "paren"
    | NameMethodReference(name, ident)       -> name^"::"^ident
    | PrimaryMethodReference ident           -> "::"^ident
    | SuperMethodReference ident             -> "super::"^ident
    | TypeSuperMethodReference(name, ident)  -> name^".super::"^ident
    | TypeNewMethodReference name            -> name^"::new"
    | AmbiguousName name                     -> "?"^name
    | AmbiguousMethodInvocation name         -> "?"^name

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Name name          -> combo 0 [name]
    | This               -> mkstr 1
    | Literal lit        -> combo 2 [Literal.to_short_string lit]
    | ClassLiteral       -> mkstr 3
    | ClassLiteralVoid   -> mkstr 4
    | QualifiedThis name -> combo 5 [name]
    | InstanceCreation n                     -> combo 6 [n]
    | QualifiedInstanceCreation name         -> combo 7 [name]
    | NameQualifiedInstanceCreation(name, ident) -> combo 8 [name; ident]

    | FieldAccess name           -> catstr [mkstr 9; name]
    | SuperFieldAccess name      -> catstr [mkstr 10; name]
    | ClassSuperFieldAccess name -> catstr [mkstr 11; name]

    | PrimaryMethodInvocation name           -> combo 12 [name]
    | SimpleMethodInvocation name            -> combo 13 [name]
    | SuperMethodInvocation name             -> combo 14 [name]
    | ClassSuperMethodInvocation name        -> combo 15 [name]
    | TypeMethodInvocation(name, ident)      -> combo 16 [name; ident]
    | ArrayAccess                            -> mkstr 17

    | ArrayCreationInit      -> mkstr 18
    | ArrayCreationDims dims -> catstr [mkstr 19; string_of_int dims]

    | Paren tid                              -> catstr [mkstr 20; tid_to_string tid]

    | NameMethodReference(name, ident)      -> combo 21 [name; ident]
    | PrimaryMethodReference ident          -> combo 22 [ident]
    | SuperMethodReference ident            -> combo 23 [ident]
    | TypeSuperMethodReference(name, ident) -> combo 24 [name; ident]
    | TypeNewMethodReference name           -> combo 25 [name]
    | AmbiguousName name                    -> combo 26 [name]
    | AmbiguousMethodInvocation name        -> combo 27 [name]

  let to_tag p =
    let name, attrs =
      match p with
      | Name name                              -> "Name", ["name",xmlenc name]
      | This                                   -> "This", []
      | Literal lit                            -> Literal.to_tag lit
      | ClassLiteral                           -> "ClassLiteral", []
      | ClassLiteralVoid                       -> "ClassLiteralVoid", []
      | QualifiedThis name                     -> "QualifiedThis", ["name",xmlenc name]
(*      | QualifiedNew name                     -> "qualified_new", ["name",name] *)
      | InstanceCreation n                     -> "StandardInstanceCreation", ["name",xmlenc n]
      | QualifiedInstanceCreation name         -> "QualifiedInstanceCreation", ["name",xmlenc name]
      | NameQualifiedInstanceCreation(name, ident) -> "NameQualifiedInstanceCreation", (if name = "" then [] else ["name",xmlenc name]) @ [ident_attr_name,xmlenc ident]
      | FieldAccess name                       -> "FieldAccess", ["name",xmlenc name]
      | SuperFieldAccess name                  -> "SuperFieldAccess", ["name",xmlenc name]
      | ClassSuperFieldAccess name             -> "ClassSuperFieldAccess", ["name",xmlenc name]
      | PrimaryMethodInvocation name           -> "PrimaryMethodInvocation", ["name",xmlenc name]
      | SimpleMethodInvocation name            -> "SimpleMethodInvocation", ["name",xmlenc name]
      | SuperMethodInvocation name             -> "SuperMethodInvocation",  ["name",xmlenc name]
      | ClassSuperMethodInvocation name        -> "ClassSuperMethodInvocation", ["name",xmlenc name]
      | TypeMethodInvocation(name, ident)      -> "TypeMethodInvocation", (if name = "" then [] else ["name",xmlenc name]) @ [ident_attr_name,xmlenc ident]
      | ArrayAccess                            -> "ArrayAccess", []
      | ArrayCreationInit                      -> "ArrayCreationInit", []
      | ArrayCreationDims dims                 -> "ArrayCreationDims", [dims_attr_name,string_of_int dims]
      | Paren tid                              -> "ParenthesizedExpression", mktidattr tid
      | NameMethodReference(name, ident)       -> "NameMethodReference", (if name = "" then [] else ["name",xmlenc name]) @ [ident_attr_name,xmlenc ident]
      | PrimaryMethodReference ident           -> "PrimaryMethodReference", ["ident",xmlenc ident]
      | SuperMethodReference ident             -> "SuperMethodReference", ["ident",xmlenc ident]
      | TypeSuperMethodReference(name, ident)  -> "TypeSuperMethodReference", ["name",xmlenc name;ident_attr_name,xmlenc ident]
      | TypeNewMethodReference name            -> "TypeNewMethodReference", ["name",xmlenc name]
      | AmbiguousName name                     -> "AmbiguousName", ["name",xmlenc name]
      | AmbiguousMethodInvocation name         -> "AmbiguousMethodInvocation", ["name",xmlenc name]
    in
    name, attrs


  let of_literal
      ?(anonymize_int=false)
      ?(anonymize_float=false)
      ?(anonymize_string=false)
      ?(reduce=false)
      lit =
    Literal (Literal.of_literal ~anonymize_int ~anonymize_float ~anonymize_string ~reduce lit)

  let sep_pat = Str.regexp "[.$]"
  let last_of_lname lname =
    if lname = "" then
      ""
    else
      Xlist.last (Str.split sep_pat lname)

  let is_compatible p1 p2 =
    match p1, p2 with
    | AmbiguousName name1, FieldAccess name2
    | FieldAccess name2, AmbiguousName name1 -> last_of_lname name1 = name2
    | Name name1, FieldAccess name2
    | FieldAccess name2, Name name1 -> name1 = name2
    | _ -> false

  let common_methods =
    let s = Xset.create 0 in
    List.iter (Xset.add s)
      [
       "add#1";
       "print#1";
       "println#1";
       "assertNull#1";
       "assertTrue#1";
       "assertFalse#1";
       "assertEquals#2";
       "assertNotEquals#2";
      ];
    s

  let is_common = function
    | PrimaryMethodInvocation x | SimpleMethodInvocation x -> Xset.mem common_methods x
    | _ -> false

end (* of module Primary *)


module Expression = struct
  type t =
    | Cond
    | BinaryOperator of BinaryOperator.t
    | Instanceof
    | UnaryOperator of UnaryOperator.t
    | Cast
    | Primary of Primary.t
    | AssignmentOperator of AssignmentOperator.t * tie_id
    | Lambda
    | Switch
    | NaryAdd

  let get_name = function
    | Primary prim -> Primary.get_name prim
    | _ -> raise Not_found

  let is_named = function
    | Primary p -> Primary.is_named p
    | _ -> false

  let is_named_orig = function
    | Primary p -> Primary.is_named_orig p
    | _ -> false

  let to_string e =
    let str =
      match e with
      | Cond                  -> "Cond"
      | BinaryOperator bo     -> BinaryOperator.to_string bo
      | Instanceof            -> "Instanceof"
      | UnaryOperator uo      -> UnaryOperator.to_string uo
      | Cast                  -> "Cast"
      | Primary p             -> Primary.to_string p
      | AssignmentOperator(ao, tid) -> sprintf "%s(%s)" (AssignmentOperator.to_string ao) (tid_to_string tid)
      | Lambda                -> "Lambda"
      | Switch                -> "Switch"
      | NaryAdd               -> "NaryAdd"
    in
    "Expression." ^ str

  let strip = function
    | Primary p                 -> Primary (Primary.strip p)
    | AssignmentOperator(ao, _) -> AssignmentOperator(ao, null_tid)
    | expr                      -> expr

  let anonymize ?(more=false) = function
    | Primary p                   -> Primary (Primary.anonymize ~more p)
    (*| AssignmentOperator(ao, tid) when more -> AssignmentOperator(AssignmentOperator.Eq, anonymize_tid ~more tid)*)
    | AssignmentOperator(ao, tid) -> AssignmentOperator(ao, anonymize_tid ~more tid)
    | expr                        -> expr

  let to_simple_string = function
    | Cond                  -> "<?:>"
    | BinaryOperator bo     -> BinaryOperator.to_simple_string bo
    | Instanceof            -> "instanceof"
    | UnaryOperator uo      -> UnaryOperator.to_simple_string uo
    | Cast                  -> "<cast>"
    | Primary p             -> Primary.to_simple_string p
    | AssignmentOperator(ao, _) -> AssignmentOperator.to_simple_string ao
    | Lambda                -> "<lambda>"
    | Switch                -> "switch"
    | NaryAdd               -> "(+)()"

  let to_short_string = function
    | Cond                  -> mkstr 0
    | BinaryOperator bo     -> catstr [mkstr 1; BinaryOperator.to_short_string bo]
    | Instanceof            -> mkstr 2
    | UnaryOperator uo      -> catstr [mkstr 3; UnaryOperator.to_short_string uo]
    | Cast                  -> mkstr 4
    | Primary p             -> catstr [mkstr 5; Primary.to_short_string p]
    | AssignmentOperator(ao, tid) -> catstr [mkstr 6; AssignmentOperator.to_short_string ao; tid_to_string tid]
    | Lambda                -> mkstr 7
    | Switch                -> mkstr 8
    | NaryAdd               -> mkstr 9

  let to_tag e =
    let name, attrs =
      match e with
      | Cond                  -> "Conditional", []
      | BinaryOperator bo     -> BinaryOperator.to_tag bo
      | Instanceof            -> "Instanceof", []
      | UnaryOperator uo      -> UnaryOperator.to_tag uo
      | Cast                  -> "Cast", []
      | Primary p             -> Primary.to_tag p
      | AssignmentOperator(ao, tid) -> AssignmentOperator.to_tag ao (mktidattr tid)
      | Lambda                -> "Lambda", []
      | Switch                -> "Switch", []
      | NaryAdd               -> "NaryAdd", []
    in
    name, attrs

  let of_unary_operator uo = UnaryOperator (UnaryOperator.of_unary_operator uo)
  let of_binary_operator bo = BinaryOperator (BinaryOperator.of_binary_operator bo)
  let of_assignment_operator ao tid =
    AssignmentOperator((AssignmentOperator.of_assignment_operator ao), tid)

  let make_primary p = Primary p

end (* of module Expression *)


module Annotation = struct
  type t =
    | Normal of name
    | Marker of name
    | SingleElement of name

  let get_name = function
    | Normal name
    | Marker name
    | SingleElement name -> name

  let is_named_orig = function
    | _ -> true

  let move_disallowed = function
    (*| Marker "Target"
    | Marker "Retention"
    | Marker "Inherited"
    | Marker "Override"
    | Marker "SuppressWarnings"
    | Marker "Deprecated"
    | Marker "SafeVarargs"
    | Marker "Repeatable"
    | Marker "FunctionalInterface"*)
    | Marker _ | Normal _
      -> true
    | _ -> false

  let to_string a =
    let str =
      match a with
      | Normal name -> sprintf "Normal(%s)" name
      | Marker name -> sprintf "Marker(%s)" name
      | SingleElement name -> sprintf "SingleElement(%s)" name
    in
    "Annotation." ^ str

  let anonymize ?(more=false) = function
    | Marker _ when more -> Normal ""
    | Normal _        -> Normal ""
    | Marker _        -> Marker ""
    | SingleElement _ -> SingleElement ""

  let to_simple_string = function
    | Normal name        -> "@"^name
    | Marker name        -> "@"^name
    | SingleElement name -> "@"^name

  let to_short_string = function
    | Normal name        -> catstr [mkstr 0; name]
    | Marker name        -> catstr [mkstr 1; name]
    | SingleElement name -> catstr [mkstr 2; name]

  let to_tag a =
    let name, attrs =
      match a with
      | Normal name        -> "NormalAnnotation", ["name",xmlenc name]
      | Marker name        -> "MarkerAnnotation", ["name",xmlenc name]
      | SingleElement name -> "SingleElementAnnotation", ["name",xmlenc name]
    in
    name, attrs

end (* of module Annotation *)


module Statement = struct
  type t =
    | Empty
    | Assert
    | If of tie_id
    | For
    | ForEnhanced
    | While
    | Do
    | Try
    | Yield
    | Switch
    | Synchronized
    | Return
    | Throw
    | Break of identifier option
    | Continue of identifier option
    | Labeled of identifier
    | Expression of Expression.t * tie_id
    (*| FlattenedIf of tie_id*)
    | ElseIf of tie_id
    | Else

  let get_tid = function
    | If tid -> tid
    (*| FlattenedIf tid | ElseIf tid -> tid*)
    (*| Expression tid -> tid*)
    | _ -> raise Not_found

  let get_name = function
    | Break (Some ident)
    | Continue (Some ident)
    | Labeled ident -> ident
    | Expression(expr, _) -> Expression.get_name expr
    | _ -> raise Not_found

  let is_named = function
    | Break (Some _)
    | Continue (Some _)
    | Labeled _ -> true
    | Expression(expr, _) -> Expression.is_named expr
    | _ -> false

  let is_named_orig = function
    | Break (Some _)
    | Continue (Some _)
    | Labeled _ -> true
    | Expression(expr, _) -> Expression.is_named_orig expr
    | _ -> false


  let to_string s =
    let str =
      match s with
      | Empty        -> "Empty"
      | Assert       -> "Assert"
      | If tid       -> sprintf "If(%s)" (tid_to_string tid)
      | For          -> "For"
      | ForEnhanced  -> "ForEnhanced"
      | While        -> "While"
      | Do           -> "Do"
      | Try          -> "Try"
      | Yield        -> "Yield"
      | Switch       -> "Switch"
      | Synchronized -> "Synchronized"
      | Return       -> "Return"
      | Throw        -> "Throw"
      | Break ident_opt ->
          let s =
            match ident_opt with None -> "" | Some ident -> "(" ^ ident ^ ")"
          in
          "Break" ^ s

      | Continue ident_opt ->
          let s =
            match ident_opt with None -> "" | Some ident -> "(" ^ ident ^ ")"
          in
          "Continue" ^ s

      | Labeled ident -> sprintf "Labeled(%s)" ident
      | Expression(se, tid) -> (Expression.to_string se)^"("^(tid_to_string tid)^")"

      (*| FlattenedIf tid -> sprintf "FlattenedIf(%s)" (tid_to_string tid)*)
      | ElseIf tid      -> sprintf "ElseIf(%s)" (tid_to_string tid)
      | Else            -> "Else"
    in
    "Statement." ^ str

  let strip = function
    | Expression(se, _) -> Expression(Expression.strip se, null_tid)
    | If _              -> If null_tid
    (*| FlattenedIf _   -> FlattenedIf null_tid*)
    | ElseIf _          -> ElseIf null_tid
    | stmt              -> stmt

  let anonymize ?(more=false) = function
    (*| ForEnhanced when more -> For*)
    | Break _       -> Break None
    | Continue _    -> Continue None
    | Labeled _     -> Labeled ""
    | Expression(se, tid) -> Expression(Expression.anonymize ~more se, anonymize_tid ~more tid)
    | If _          -> If null_tid(*(anonymize_tid ~more tid)*)
    (*| FlattenedIf tid     -> FlattenedIf null_tid(*(anonymize_tid ~more tid)*)*)
    | ElseIf _      -> ElseIf null_tid(*(anonymize_tid ~more tid)*)
    | stmt          -> stmt

  let to_simple_string = function
    | Empty        -> "<empty>"
    | Assert       -> "assert"
    | If _         -> "if"
    | For          -> "for"
    | ForEnhanced  -> "for"
    | While        -> "while"
    | Do           -> "do"
    | Try          -> "try"
    | Yield        -> "yield"
    | Switch       -> "switch"
    | Synchronized -> "synchronized"
    | Return       -> "return"
    | Throw        -> "throw"
    | Break ident_opt    -> (match ident_opt with None -> "break" | Some ident -> "break "^ident)
    | Continue ident_opt -> (match ident_opt with None -> "continue" | Some ident -> "continue "^ident)
    | Labeled ident      -> ident
    | Expression(_, _) -> "<se>" (* Expression.to_simple_string se *)
    (*| FlattenedIf tid -> "<flattened-if>"*)
    | ElseIf _        -> "else if"
    | Else            -> "else"

  let to_short_string = function
    | Empty        -> mkstr 0
    | Assert       -> mkstr 1
    | If tid       -> catstr [mkstr 2; tid_to_string tid]
    | For          -> mkstr 3
    | ForEnhanced  -> mkstr 4
    | While        -> mkstr 5
    | Do           -> mkstr 6
    | Try          -> mkstr 7
    | Yield        -> mkstr 8
    | Switch       -> mkstr 9
    | Synchronized -> mkstr 10
    | Return       -> mkstr 11
    | Throw        -> mkstr 12
    | Break ident_opt ->
        let l =
          match ident_opt with None -> [] | Some ident -> [ident]
        in
        catstr ([mkstr 13] @ l)

    | Continue ident_opt ->
        let l =
          match ident_opt with None -> [] | Some ident -> [ident]
        in
        catstr ([mkstr 14] @ l)

    | Labeled ident       -> catstr [mkstr 15; ident]
    | Expression(se, tid) -> catstr [mkstr 16; Expression.to_short_string se; tid_to_string tid]
    (*| FlattenedIf tid -> catstr [mkstr 17; tid_to_string tid]*)
    | ElseIf tid      -> catstr [mkstr 18; tid_to_string tid]
    | Else            -> mkstr 19

  let to_index = function
    | Empty            -> 3
    | Assert           -> 90
    | If _             -> 91
    | For              -> 92
    | ForEnhanced      -> 93
    | While            -> 94
    | Do               -> 95
    | Try              -> 96
    | Yield            -> 97
    | Switch           -> 98
    | Synchronized     -> 99
    | Return           -> 100
    | Throw            -> 101
    | Break _          -> 102
    | Continue _       -> 103
    | Labeled _        -> 104
    | Expression(_, _) -> 105
    (*| FlattenedIf _    -> 106*)
    | ElseIf _         -> 107
    | Else             -> 108

  let to_tag ?(strip=false) s =
    let name, attrs =
      match s with
      | Empty           -> "EmptyStatement", []
      | Assert          -> "AssertStatement", []
      | If _ when strip -> "IfStatement", []
      | If tid          -> "IfStatement", mktidattr tid
      | For             -> "BasicForStatement", []
      | ForEnhanced     -> "EnhancedForStatement", []
      | While           -> "WhileStatement", []
      | Do              -> "DoStatement", []
      | Try             -> "TryStatement", []
      | Yield           -> "YieldStatement", []
      | Switch          -> "SwitchStatement", []
      | Synchronized    -> "SynchronizedStatement", []
      | Return          -> "ReturnStatement", []
      | Throw           -> "ThrowStatement", []
      | Break ident_opt ->
          let attrs =
            match ident_opt with None -> [] | Some ident -> [label_attr_name,ident]
          in
          "BreakStatement", attrs

      | Continue ident_opt ->
          let attrs =
            match ident_opt with None -> [] | Some ident -> [label_attr_name,ident]
          in
          "ContinueStatement", attrs

      | Labeled ident       -> "LabeledStatement", [label_attr_name,ident]

      | Expression(se, (*tid*)_) -> (*"ExpressionStatement", (mkstmttidattr tid)*)
          let t, a = Expression.to_tag se in
          t^"Statement",  a(* @ (mkstmttidattr tid)*)

      (*| FlattenedIf _ when strip -> "FlattenedIfStatement", []
      | FlattenedIf tid          -> "FlattenedIfStatement", mktidattr tid*)
      | ElseIf _ when strip      -> "ElseIfStatement", []
      | ElseIf tid               -> "ElseIfStatement", mktidattr tid
      | Else                     -> "ElseStatement", []

    in
    name, attrs

  let make_statement_expression e tid = Expression(e, tid)

  let relabel_allowed = function
    | Expression _, Expression _
    | Empty, _ | _, Empty
    | Break _, Return | Return, Break _
    | Continue _, Return | Return, Continue _
    | Throw, Return | Return, Throw
    | Throw, Expression _ | Expression _, Throw
    | Assert, If _ | If _, Assert
    | If _, Switch | Switch, If _
    | If _, If _
    (*| FlattenedIf _, Switch | Switch, FlattenedIf _*)
    | ElseIf _, If _ | If _, ElseIf _
    | For, ForEnhanced | ForEnhanced, For
    | For, While | While, For
    | ForEnhanced, While | While, ForEnhanced
    | For, Do | Do, For
    | ForEnhanced, Do | Do, ForEnhanced
    | While, Do | Do, While
    | Break _, Continue _ | Continue _, Break _
    (*| Return, Expression(Expression.AssignmentOperator _, _) |
      Expression(Expression.AssignmentOperator _, _), Return*)
    (*| Method _, Constructor _ | Constructor _, Method _ !!! should be activated after patchast test *)
        -> true
    | l1, l2 -> anonymize l1 = anonymize l2

end (* of module Statement *)


type annotation = string option

let null_annotation = None

let annotation_to_string : annotation -> string = function
  | None -> "<none>"
  | Some x -> x

let make_annotation s =
  (Some s : annotation)

type kind =
  | Kclass of name
  | Kinterface of name
  | Kenum of name
  | Krecord of name
  | Kannotation of name
  | Kfield of name
  | Kconstructor of name
  | Kmethod of name
  | Kparameter of name
  | Klocal of name
  | Kany
  | Kaspect of name
  | Kpointcut of name

(*let kind_sep = "#"

let kind_to_suffix k =
  kind_sep^
  match k with
  | Kclass _     -> "C"
  | Kinterface   -> "I"
  | Kenum        -> "E"
  | Krecord      -> "R"
  | Kannotation  -> "@"
  | Kfield       -> "f"
  | Kconstructor -> "c"
  | Kmethod      -> "m"
  | Kparameter   -> "p"
  | Klocal       -> "l"
  | Kany         -> "*"
  | Kaspect      -> "A"
  | Kpointcut    -> "/"*)

let anonymize_kind = function
  | Kclass _       -> Kclass ""
  | Kinterface _   -> Kinterface ""
  | Kenum _        -> Kenum ""
  | Krecord _      -> Krecord ""
  | Kannotation _  -> Kannotation ""
  | Kfield _       -> Kfield ""
  | Kconstructor _ -> Kconstructor ""
  | Kmethod _      -> Kmethod ""
  | Kparameter _   -> Kparameter ""
  | Klocal _       -> Klocal ""
  | Kany           -> Kany
  | Kaspect _      -> Kaspect ""
  | Kpointcut _    -> Kpointcut ""

let kind_to_anonymous_string = function
  | Kclass _       -> "Class"
  | Kinterface _   -> "Interface"
  | Kenum _        -> "Enum"
  | Krecord _      -> "Record"
  | Kannotation _  -> "Annotation"
  | Kfield _       -> "Field"
  | Kconstructor _ -> "Constructor"
  | Kmethod _      -> "Method"
  | Kparameter _   -> "Parameter"
  | Klocal _       -> "Local"
  | Kany           -> ""
  | Kaspect _      -> "Aspect"
  | Kpointcut _    -> "Pointcut"

let kind_to_string = function
  | Kclass n       -> "Class:"^n
  | Kinterface n   -> "Interface:"^n
  | Kenum n        -> "Enum:"^n
  | Krecord n      -> "Record:"^n
  | Kannotation n  -> "Annotation:"^n
  | Kfield n       -> "Field:"^n
  | Kconstructor n -> "Constructor:"^n
  | Kmethod n      -> "Method:"^n
  | Kparameter n   -> "Parameter:"^n
  | Klocal n       -> "Local:"^n
  | Kany           -> ""
  | Kaspect n      -> "Aspect:"^n
  | Kpointcut n    -> "Pointcut:"^n

let kind_to_attrs = function
  | Kclass n       -> ["kind","class";"name",xmlenc n]
  | Kinterface n   -> ["kind","interface";"name",xmlenc n]
  | Kenum n        -> ["kind","enum";"name",xmlenc n]
  | Krecord n      -> ["kind","record";"name",xmlenc n]
  | Kannotation n  -> ["kind","annotation";"name",xmlenc n]
  | Kfield n       -> ["kind","field";"name",xmlenc n]
  | Kconstructor n -> ["kind","constructor";"name",xmlenc n]
  | Kmethod n      -> ["kind","method";"name",xmlenc n]
  | Kparameter n   -> ["kind","parameter";"name",xmlenc n]
  | Klocal n       -> ["kind","local";"name",xmlenc n]
  | Kaspect n      -> ["kind","aspect";"name",xmlenc n]
  | Kpointcut n    -> ["kind","pointcut";"name",xmlenc n]
  | Kany           -> []

let kind_to_name_attrs = function
  | Kclass n
  | Kinterface n
  | Kenum n
  | Krecord n
  | Kannotation n
  | Kfield n
  | Kconstructor n
  | Kmethod n
  | Kparameter n
  | Klocal n
  | Kaspect n
  | Kpointcut n    -> ["name",xmlenc n]
  | Kany           -> []

let kind_to_name = function
  | Kclass n
  | Kinterface n
  | Kenum n
  | Krecord n
  | Kannotation n
  | Kfield n
  | Kconstructor n
  | Kmethod n
  | Kparameter n
  | Klocal n
  | Kaspect n
  | Kpointcut n    -> n
  | Kany           -> ""

let kind_to_short_string = function
  | Kclass n       -> combo 0 [n]
  | Kinterface n   -> combo 1 [n]
  | Kenum n        -> combo 2 [n]
  | Krecord n      -> combo 3 [n]
  | Kannotation n  -> combo 4 [n]
  | Kfield n       -> combo 5 [n]
  | Kconstructor n -> combo 6 [n]
  | Kmethod n      -> combo 7 [n]
  | Kparameter n   -> combo 8 [n]
  | Klocal n       -> combo 9 [n]
  | Kany           -> mkstr 10
  | Kaspect n      -> combo 11 [n]
  | Kpointcut n    -> combo 12 [n]

type t = (* Label *)
(*    Dummy *)
  | Type of Type.t
  | Primary of Primary.t
  | Expression of Expression.t
  | Statement of Statement.t
  | Modifier of Modifier.t
  | Annotation of Annotation.t

  | TypeBound

(* constructor invocation *)
  | ThisInvocation
  | SuperInvocation
  | PrimaryInvocation
  | NameInvocation of name (* a kind of primary invocation *)

(* switch labels *)
  | SLconstant of tie_id
  | SLdefault

(* element value *)
  | EVconditional | EVannotation | EVarrayInit
  | ElementValuePair of name

(* class body declaration *)
  | Constructor of name * signature (* signature *)
  | ConstructorBody of name * signature
  | StaticInitializer
  | InstanceInitializer

(* misc *)
  | Block of tie_id
  | LocalVariableDeclaration of bool (* is stmt *) * (name * dims) list
  | VariableDeclarator of name * dims
  | CatchClause of tie_id
  | Finally
  | ForInit of tie_id
  | ForCond of tie_id
  | ForUpdate of tie_id
  | SwitchBlock
  | SwitchBlockStatementGroup
  | DimExpr
  | TypeArguments of int (* nth *) * name
  | Wildcard
  | WildcardBoundsExtends
  | WildcardBoundsSuper
  | Annotations
  | Arguments
  | NamedArguments of name (* method *)
  | Parameters of name (* method *)
  | Parameter of identifier * dims * bool
  | ReceiverParameter of identifier option
  | TypeParameter of name (* type variable *)
  | TypeParameters of name
  | ArrayInitializer
  | Modifiers of kind
  | FieldDeclaration of (name * dims) list
  | VariableDeclaration
  | Method of name * signature
  | Super
  | Qualifier of name
  | Throws of name (* method or ctor name *)
  | MethodBody of name (* method name *) * signature
  | Specifier of kind
  | Class of name
  | Enum of name
  | EnumConstant of name
  | Record of name
  | Extends
  | Implements
  | Permits
  | ClassBody of name (* class name *)
  | EnumBody of name (* enum name *)
  | Interface of name
  | AnnotationType of name
  | AnnotationTypeBody of name
  | ExtendsInterfaces
  | InterfaceBody of name (* interface name *)
  | PackageDeclaration of name

  | Module of name
  | Open
  | ModuleName of name
  | ModuleBody of name
  | Requires of name
  | Exports of name
  | Opens of name
  | Uses of name
  | Provides of name
  | TypeName of name

(* import declarations *)
  | IDsingle of name (* type name *)
  | IDtypeOnDemand of name
  | IDsingleStatic of name * name
  | IDstaticOnDemand of name (* package name or type name *)

(* *)
  | ImportDeclarations
  | TypeDeclarations
  | CompilationUnit

  | ElementDeclaration of name

  | FieldDeclarations of name

  | InferredFormalParameters
  | InferredFormalParameter of identifier

  | ResourceSpec
  (*| Resource of name * dims*)

  | CatchParameter of name * dims

  | AnnotDim of bool (* is_ellipsis *)

  | Error of string

  | HugeArray of int * string
  | HugeExpr of int * string

  | EmptyDeclaration

  | ForHead of tie_id

  | Aspect of name
  | Pointcut of name
  | DeclareParents
  | DeclareMessage of string
  | DeclareSoft
  | DeclarePrecedence
  | PointcutAnd
  | PointcutOr
  | PointcutNot
  | PointcutParen
  | PointcutWithin
  | ClassnamePatternAnd
  | ClassnamePatternOr
  | ClassnamePatternNot
  | ClassnamePatternParen
  | ClassnamePatternName of name
  | ClassnamePatternNamePlus of name

  | SwitchRule
  | SRLconstant
  | SRLdefault


let to_string = function
(*    Dummy -> "Dummy" *)
  | Error s                                 -> sprintf "Error(%s)" s
  | Type ty                                 -> Type.to_string ty
  | Primary p                               -> Primary.to_string p
  | Expression e                            -> Expression.to_string e
  | Statement s                             -> Statement.to_string s
  | Modifier m                              -> Modifier.to_string m
  | Annotation a                            -> Annotation.to_string a
  | TypeBound                               -> "TypeBound"
  | ThisInvocation                          -> "ThisInvocation"
  | SuperInvocation                         -> "SuperInvocation"
  | PrimaryInvocation                       -> "PrimaryInvocation"
  | NameInvocation name                     -> sprintf "NameInvocation(%s)" name
  | SLconstant tid                          -> sprintf "SLconstant(%s)" (tid_to_string tid)
  | SLdefault                               -> "SLdefault"
  | EVconditional                           -> "EVconditional"
  | EVannotation                            -> "EVannotation"
  | EVarrayInit                             -> "EVarrayInit"
  | ElementValuePair name                   -> sprintf "ElementValuePair(%s)" name
  | Constructor(name, msig)                 -> sprintf "Constructor(%s%s)" name msig
  | ConstructorBody(name, msig)             -> sprintf "ConstructorBody(%s%s)" name msig
  | StaticInitializer                       -> "StaticInitializer"
  | InstanceInitializer                     -> "InstanceInitializer"
  | Block tid                               -> sprintf "Block(%s)" (tid_to_string tid)
  | LocalVariableDeclaration(isstmt, vdids) ->
      sprintf "LocalVariableDeclaration(%B,%s)" isstmt (vdids_to_string vdids)
  | VariableDeclarator(name, dims)          -> sprintf "VariableDeclarator(%s,%d)" name dims
  | CatchClause tid                         -> sprintf "CatchClause(%s)" (tid_to_string tid)
  | Finally                                 -> "Finally"
  | ForInit tid                             -> sprintf "ForInit(%s)" (tid_to_string tid)
  | ForCond tid                             -> sprintf "ForCond(%s)" (tid_to_string tid)
  | ForUpdate tid                           -> sprintf "ForUpdate(%s)" (tid_to_string tid)
  | SwitchBlock                             -> "SwitchBlock"
  | SwitchBlockStatementGroup               -> "SwitchBlockStatementGroup"
  | DimExpr                                 -> "DimExpr"
  | Arguments                               -> "Arguments"
  | Annotations                             -> "Annotations"
  | NamedArguments name                     -> sprintf "NamedArguments(%s)" name
  | TypeArguments(nth, name)                -> sprintf "TypeArguments(%d,%s)" nth name
  | Wildcard                                -> "Wildcard"
  | WildcardBoundsExtends                   -> "WildcardBoundsExtends"
  | WildcardBoundsSuper                     -> "WildcardBoundsSuper"
  | Parameters name                         -> sprintf "Parameters(%s)" name
  | Parameter(id, dims, va)               ->
      sprintf "Parameter(%s,%d,%s)" id dims (if va then "..." else "")
  | ReceiverParameter id_opt                ->
      sprintf "ReceiverParameter(%s)" (match id_opt with Some id -> id^".this" | _ -> "this")

  | TypeParameter name                      -> sprintf "TypeParameter(%s)" name
  | TypeParameters name                     -> sprintf "TypeParameters(%s)" name
  | ArrayInitializer                        -> "ArrayInitializer"
  | Modifiers k                             -> sprintf "Modifiers(%s)" (kind_to_string k)
  | FieldDeclaration vdids                  -> sprintf "FieldDeclaration(%s)" (vdids_to_string vdids)
  | VariableDeclaration                     -> "VariableDeclaration"
  | Method(name, msig)                      -> sprintf "Method(%s%s)" name msig
  | Super                                   -> "Super"
  | Qualifier q                             -> sprintf "Qualifier(%s)" q
  | Throws name                             -> sprintf "Throws(%s)" name
  | MethodBody(name, msig)                  -> sprintf "MethodBody(%s%s)" name msig
  | Specifier k                             -> sprintf "Specifier(%s)" (kind_to_string k)
  | Class name                              -> sprintf "Class(%s)" name
  | Enum name                               -> sprintf "Enum(%s)" name
  | EnumConstant name                       -> sprintf "EnumConstant(%s)" name
  | Record name                             -> sprintf "Record(%s)" name
  | Extends                                 -> "Extends"
  | Implements                              -> "Implements"
  | Permits                                 -> "Permits"
  | ClassBody name                          -> sprintf "ClassBody(%s)" name
  | EnumBody name                           -> sprintf "EnumBody(%s)" name
  | Interface name                          -> sprintf "Interface(%s)" name
  | AnnotationType name                     -> sprintf "AnnotationType(%s)" name
  | AnnotationTypeBody name                 -> sprintf "AnnotationTypeBody(%s)" name
  | ExtendsInterfaces                       -> "ExtendsInterfaces"
  | InterfaceBody name                      -> sprintf "InterfaceBody(%s)" name
  | PackageDeclaration name                 -> sprintf "PackageDeclaration(%s)" name
  | IDsingle name                           -> sprintf "IDsingle(%s)" name
  | IDtypeOnDemand name                     -> sprintf "IDtypeOnDemand(%s)" name
  | IDsingleStatic(name, ident)             -> sprintf "IDsingleStatic(%s,%s)" name ident
  | IDstaticOnDemand name                   -> sprintf "IDstaticOnDemand(%s)" name
  | ImportDeclarations                      -> "ImportDeclarations"
  | TypeDeclarations                        -> "TypeDeclarations"
  | CompilationUnit                         -> "CompilationUnit"
  | ElementDeclaration name                 -> sprintf "ElementDeclaration(%s)" name
  | FieldDeclarations name                  -> sprintf "FieldDeclarations(%s)" name
  | InferredFormalParameters                -> "InferredFormalParameters"
  | InferredFormalParameter ident           -> sprintf "InferredFormalParameter(%s)" ident

  | ResourceSpec                            -> sprintf "ResourceSpec"
  (*| Resource(name, dims)                    -> sprintf "Resource(%s,%d)" name dims*)

  | CatchParameter(name, dims)              -> sprintf "CatchParameter(%s,%d)" name dims

  | AnnotDim ellipsis                       -> sprintf "AnnotDim(%B)" ellipsis

  | HugeArray(sz, c)                        -> sprintf "HugeArray(%d):%s\n" sz c
  | HugeExpr(sz, c)                         -> sprintf "HugeExpr(%d):%s\n" sz c

  | EmptyDeclaration                        -> "EmptyDeclaration"

  | ForHead tid                   -> sprintf "ForHead(%s)" (tid_to_string tid)

  | Aspect name                   -> sprintf "Aspect(%s)" name
  | Pointcut name                 -> sprintf "Pointcut(%s)" name
  | DeclareParents                -> "DeclareParents"
  | DeclareMessage kwd            -> sprintf "DeclareMessage(%s)" kwd
  | DeclareSoft                   -> "DeclareSoft"
  | DeclarePrecedence             -> "DeclarePrecedence"
  | PointcutAnd                   -> "PointcutAnd"
  | PointcutOr                    -> "PointcutOr"
  | PointcutNot                   -> "PointcutNot"
  | PointcutParen                 -> "PointcutParen"
  | PointcutWithin                -> "PointcutWithin"
  | ClassnamePatternAnd           -> "ClassnamePatternAnd"
  | ClassnamePatternOr            -> "ClassnamePatternOr"
  | ClassnamePatternNot           -> "ClassnamePatternNot"
  | ClassnamePatternParen         -> "ClassnamePatternParen"
  | ClassnamePatternName name     -> sprintf "ClassnamePatternName(%s)" name
  | ClassnamePatternNamePlus name -> sprintf "ClassnamePatternNamePlus(%s)" name

  | SwitchRule -> "SwitchRule"
  | SRLconstant -> "SRLconstant"
  | SRLdefault -> "SRLdefault"

  | Module name -> sprintf "Module(%s)" name
  | Open -> "Open"
  | ModuleName name -> sprintf "ModuleName(%s)" name
  | ModuleBody name -> sprintf "ModuleBody(%s)" name
  | Requires name -> sprintf "Requires(%s)" name
  | Exports name -> sprintf "Exports(%s)" name
  | Opens name -> sprintf "Opens(%s)" name
  | Uses name -> sprintf "Uses(%s)" name
  | Provides name -> sprintf "Provides(%s)" name
  | TypeName name -> sprintf "TypeName(%s)" name

let strip = function (* strip non-name attributes from label *)
  | Type ty      -> Type (Type.strip ty)
  | Primary p    -> Primary (Primary.strip p)
  | Expression e -> Expression (Expression.strip e)
  | Statement s  -> Statement (Statement.strip s)

  | Constructor(name, _)     -> Constructor(name, "")
  | ConstructorBody(name, _) -> ConstructorBody(name, "")
  | Method(name, _)          -> Method(name, "")
  | MethodBody(name, _)      -> MethodBody(name, "")

  | Block _       -> Block null_tid
  | CatchClause _ -> CatchClause null_tid
  | ForInit _     -> ForInit null_tid
  | ForCond _     -> ForCond null_tid
  | ForUpdate _   -> ForUpdate null_tid

  | LocalVariableDeclaration(_, l) -> LocalVariableDeclaration(true, List.map (fun (n, _) -> n, 0) l)
  | FieldDeclaration l             -> FieldDeclaration (List.map (fun (n, _) -> n, 0) l)
  | VariableDeclarator(name, _)    -> VariableDeclarator(name, 0)

  | TypeArguments(_, name)  -> TypeArguments(1, name)
  | Parameter(name, _, _)   -> Parameter(name, 0, false)
  | CatchParameter(name, _) -> CatchParameter(name, 0)
  | ForHead _ -> ForHead null_tid

  | lab -> lab


let anonymize ?(more=false) = function
  | Constructor(_, _) when more     -> Constructor("", "")
  | ConstructorBody(_, _) when more -> ConstructorBody("", "")
  | Method(_, _) when more          -> Method("", "")
  | MethodBody(_, _) when more      -> MethodBody("", "")

  | LocalVariableDeclaration _ when more -> VariableDeclaration
  | FieldDeclaration _ when more         -> VariableDeclaration
  | VariableDeclarator(_, _) when more -> VariableDeclarator("", 0)
  | Modifiers _ when more -> Modifiers Kany

  | Type ty                        -> Type (Type.anonymize ty)
  | Primary p                      -> Primary (Primary.anonymize ~more p)
  | Expression (Primary p)         -> Primary (Primary.anonymize ~more p)
(*  | Statement (Statement.Expression (Expression.Primary p, _)) -> Primary (Primary.anonymize ~more p)*)
  | Expression e                   -> Expression (Expression.anonymize ~more e)
  | Statement s                    -> Statement (Statement.anonymize ~more s)
  | Annotation a                   -> Annotation (Annotation.anonymize ~more a)
  (*| Modifier m                     -> Modifier (Modifier.anonymize m)*)
  | NameInvocation _               -> NameInvocation ""
  | ElementValuePair _             -> ElementValuePair ""

  (*| Constructor(name, msig)        -> Constructor(name, "")
  | ConstructorBody(name, msig)    -> ConstructorBody(name, "")
  | Method(name, msig)             -> Method(name, "")
  | MethodBody(name, msig)         -> MethodBody(name, "")*)
  | ConstructorBody(_, msig)    -> ConstructorBody("", msig)
  (*| ConstructorBody(name, msig)    -> ConstructorBody("", "")*)
  | MethodBody(_, msig)         -> MethodBody("", msig)
  (*| MethodBody(name, msig)         -> MethodBody("", "")*)
  | Constructor(_, _)        -> Constructor("", "")
  (*| Constructor(name, msig)        -> Constructor("", msig)*)
  | Method(_, _)             -> Method("", "")
  (*| Method(name, msig)             -> Method("", msig)*)

  | LocalVariableDeclaration(b, _) -> LocalVariableDeclaration(b, [])
  | VariableDeclarator(_, _)       -> VariableDeclarator("", 0)
  | NamedArguments _               -> NamedArguments ""
  | TypeArguments(_, _)            -> TypeArguments(1, "")
  | Parameters _                   -> Parameters ""
  | Parameter _                    -> Parameter("", 0, false)
  | ReceiverParameter _            -> ReceiverParameter None
  | TypeParameter _                -> TypeParameter ""
  | TypeParameters _               -> TypeParameters ""
  | Modifiers kind                 -> Modifiers (anonymize_kind kind)
  | FieldDeclaration _             -> FieldDeclaration []
  | Qualifier _                    -> Qualifier ""
  | Throws _                       -> Throws ""
  | Specifier _                    -> Specifier Kany
  | Class _                        -> Class ""
  | Enum _                         -> Enum ""
  | EnumConstant _                 -> EnumConstant ""
  | Record _                       -> Record ""
  | ClassBody _                    -> ClassBody ""
  | EnumBody _                     -> EnumBody ""
  | Interface _                    -> Interface ""
  | AnnotationType _               -> AnnotationType ""
  | AnnotationTypeBody _           -> AnnotationTypeBody ""
  | InterfaceBody _                -> InterfaceBody ""
  | PackageDeclaration _           -> PackageDeclaration ""
  | IDsingle _                     -> IDsingle ""
  | IDtypeOnDemand _               -> IDtypeOnDemand ""
  | IDsingleStatic _               -> IDsingleStatic("", "")
  | IDstaticOnDemand _             -> IDstaticOnDemand ""
  | ElementDeclaration _           -> ElementDeclaration ""
  | FieldDeclarations _            -> FieldDeclarations ""
  | ForInit tid                    -> ForInit (anonymize_tid ~more tid)
  | ForCond tid                    -> ForCond (anonymize_tid ~more tid)
  | ForUpdate tid                  -> ForUpdate (anonymize_tid ~more tid)
  | InferredFormalParameter _      -> InferredFormalParameter ""
  (*| Resource(name, dims)           -> Resource("", 0)*)
  | CatchParameter(_, _)           -> CatchParameter("", 0)
  | ForHead tid                    -> ForHead (anonymize_tid ~more tid)
  | HugeArray _                    -> HugeArray(0, "")
  | HugeExpr _                     -> HugeExpr(0, "")
  | Block _                        -> Block null_tid

  | WildcardBoundsExtends when more -> Wildcard
  | WildcardBoundsSuper when more   -> Wildcard
  | CatchClause tid                 -> CatchClause (anonymize_tid ~more tid)

  | Module _ -> Module ""
  | ModuleBody _ -> ModuleBody ""
  | Requires _ -> Requires ""
  | Exports _ -> Exports ""
  | Opens _ -> Opens ""
  | Uses _ -> Uses ""
  | Provides _ -> Provides ""
  | TypeName _ -> TypeName ""

  | Aspect _ -> Aspect ""
  | Pointcut _ -> Pointcut ""
  | DeclareMessage _ -> DeclareMessage ""

  | SLconstant tid -> SLconstant (anonymize_tid ~more tid)

  | lab -> lab


let anonymize2 = function
  | Type ty                                                    -> Type (Type.anonymize2 ty)
  | Primary p                                                  -> Primary (Primary.anonymize2 p)
  | Expression (Primary p)                                     -> Primary (Primary.anonymize2 p)
(*  | Statement (Statement.Expression (Expression.Primary p, _)) -> Primary (Primary.anonymize2 p)*)
  | Qualifier _                                                -> Primary (Primary.Name "")
  | VariableDeclarator _                                       -> Primary (Primary.Name "")
  | Interface _ | Enum _                                       -> Class ""
  | InterfaceBody _ | EnumBody _                               -> ClassBody ""
  | Constructor _ | ConstructorBody _ | Method _ | MethodBody _ as lab -> anonymize ~more:false lab
  (*| Constructor _ | Method _ as lab -> anonymize ~more:false lab
  | ConstructorBody _ | MethodBody _ as lab -> anonymize ~more:true lab*)
  | Modifier m -> Modifier (Modifier.anonymize m)
  | Statement Statement.ForEnhanced -> Statement Statement.For
  | lab -> anonymize ~more:true lab

let anonymize3 = function
  | Constructor _ | Method _ as lab  -> anonymize ~more:true lab
  | MethodBody _ | ConstructorBody _ -> Block null_tid
  (*| Type _                      -> Type (Type.Void)*)
  (*| Primary (Primary.Literal _) -> Primary (Primary.Literal Literal.Null)*)
  (*| Statement Statement.ForEnhanced -> Statement Statement.For*)
  (*| Expression (Expression.BinaryOperator bop) ->
      Expression (Expression.BinaryOperator (BinaryOperator.anonymize3 bop))*)

  | Statement Statement.Expression(Expression.Primary p, _) when begin
      match p with
      | PrimaryMethodInvocation _
      | SimpleMethodInvocation _
      | SuperMethodInvocation _
      | ClassSuperMethodInvocation _
      | TypeMethodInvocation _ -> true
      | _ -> false
  end ->
    Statement (Statement.Expression(Expression.Primary(Primary.SimpleMethodInvocation ""), null_tid))

  | lab -> anonymize ~more:true lab


let to_simple_string = function
  | Type ty             -> Type.to_simple_string ty
  | Primary p           -> Primary.to_simple_string p
  | Expression e        -> Expression.to_simple_string e
  | Statement s         -> Statement.to_simple_string s
  | Modifier m          -> Modifier.to_simple_string m
  | Annotation a        -> Annotation.to_simple_string a
  | TypeBound           -> "<ty_bound>"
  | ThisInvocation      -> "this"
  | SuperInvocation     -> "super"
  | PrimaryInvocation   -> "<p_invok>"
  | NameInvocation name -> name
  | SLconstant _        -> "<sw_label>"
  | SLdefault           -> "default"
  | EVconditional       -> "<elem_val>"
  | EVannotation        -> "<elem_val>"
  | EVarrayInit         -> "<elem_val>"
  | ElementValuePair name       -> name
  | Constructor(name, msig)     -> sprintf "%s%s" name msig
  | ConstructorBody(_, _)       -> "<body>"
  | StaticInitializer           -> "<static_init>"
  | InstanceInitializer         -> "<init>"
  | Block _                     -> "<block>"
  | LocalVariableDeclaration(_, _) -> "<vdecl>"
  | VariableDeclarator(name, dims) -> name^(if dims = 0 then "" else sprintf "[%d" dims)
  | CatchClause _             -> "catch"
  | Finally                   -> "finally"
  | ForInit _                 -> "<for_init>"
  | ForCond _                 -> "<for_cond>"
  | ForUpdate _               -> "<for_update>"
  | SwitchBlock               -> "<sw_block>"
  | SwitchBlockStatementGroup -> "<sw_block_stmt_grp>"
  | DimExpr                   -> "<dim>"
  | Arguments                 -> "<args>"
  | Annotations               -> "<annots>"
  | NamedArguments _          -> "<args>"
  | TypeArguments(_, _)       -> "<ty_args>"
  | Wildcard                  -> "?"
  | WildcardBoundsExtends     -> "? extends"
  | WildcardBoundsSuper       -> "? super"
  | Parameters _              -> "<params>"
  | Parameter(id, dims, va)   ->
      id^(if dims = 0 then "" else sprintf "[%d]" dims)^(if va then "..." else "")
  | ReceiverParameter id_opt    -> (match id_opt with Some id -> id^".this" | _ -> "this")
  | TypeParameter name          -> name
  | TypeParameters _            -> "<ty_params>"
  | ArrayInitializer            -> "<array-init>"
  | Modifiers _                 -> "<mods>"
  | FieldDeclaration _          -> "<fdecl>"
  | VariableDeclaration         -> "<vdecl>"
  | Method(name, _)             -> name
  | Super                       -> "super"
  | Qualifier q                 -> q
  | Throws name                 -> "throws "^name
  | MethodBody(_, _)            -> "<body>"
  | Specifier k                 -> "<spec:"^(kind_to_string k)^">"
  | Class name                  -> "class "^name
  | Enum name                   -> "enum "^name
  | EnumConstant name           -> name
  | Record name                 -> "record "^name
  | Extends                     -> "extends"
  | Implements                  -> "implements"
  | Permits                     -> "permits"
  | ClassBody _                 -> "<body>"
  | EnumBody _                  -> "<body>"
  | Interface name              -> name
  | AnnotationType name         -> "@interface "^name
  | AnnotationTypeBody _        -> "<body>"
  | ExtendsInterfaces           -> "extends"
  | InterfaceBody _             -> "<body>"
  | PackageDeclaration _        -> "package"
  | IDsingle name               -> "import "^name
  | IDtypeOnDemand name         -> sprintf "import %s*" name
  | IDsingleStatic(name, ident) -> sprintf "import static %s.%s" name ident
  | IDstaticOnDemand name       -> sprintf "import static %s*" name
  | ImportDeclarations          -> "<imports>"
  | TypeDeclarations            -> "<ty_decls>"
  | CompilationUnit             -> "<compilation_unit>"
  | ElementDeclaration name     -> name^"()"
  | FieldDeclarations _         -> "<fdecls>"
  | InferredFormalParameters    -> "<inferred_formal_parameters>"
  | InferredFormalParameter id   -> id
  | ResourceSpec                -> "<resource-spec>"
  (*| Resource(name, dims)        -> name^(if dims = 0 then "" else sprintf "[%d]" dims)*)
  | CatchParameter(name, dims)  -> name^(if dims = 0 then "" else sprintf "[%d]" dims)
  | AnnotDim ellipsis           -> if ellipsis then "..." else "[]"
  | Error s                     -> s
  | HugeArray(_ , c)            -> c
  | HugeExpr(_ , c)             -> c
  | EmptyDeclaration            -> ";"
  | ForHead _                   -> "<for_head>"
  | Aspect name                   -> "aspect "^name
  | Pointcut name                 -> "pointcut "^name
  | DeclareParents                -> "declare parents"
  | DeclareMessage kwd            -> sprintf "declare %s" kwd
  | DeclareSoft                   -> "declare soft"
  | DeclarePrecedence             -> "declare precedence"
  | PointcutAnd                   -> "&&"
  | PointcutOr                    -> "||"
  | PointcutNot                   -> "!"
  | PointcutParen                 -> "()"
  | PointcutWithin                -> "within"
  | ClassnamePatternAnd           -> "&&"
  | ClassnamePatternOr            -> "||"
  | ClassnamePatternNot           -> "!"
  | ClassnamePatternParen         -> "()"
  | ClassnamePatternName name     -> name
  | ClassnamePatternNamePlus name -> name^"+"
  | SwitchRule                    -> "<switch-rule>"
  | SRLconstant                   -> "<sw-label>"
  | SRLdefault                    -> "default"

  | Module name -> sprintf "module %s" name
  | Open -> "open"
  | ModuleName name -> name
  | ModuleBody name -> sprintf "<module-body:%s>" name
  | Requires name -> sprintf "requires %s" name
  | Exports name -> sprintf "exports %s" name
  | Opens name -> sprintf "opens %s" name
  | Uses name -> sprintf "uses %s" name
  | Provides name -> sprintf "provides %s" name
  | TypeName name -> name


let to_short_string ?(ignore_identifiers_flag=false) =
  let combo = combo ~ignore_identifiers_flag in function
  | Type ty                                 -> catstr [mkstr 0; Type.to_short_string ~ignore_identifiers_flag ty]
  | Primary p                               -> catstr [mkstr 1; Primary.to_short_string ~ignore_identifiers_flag p]
  | Expression e                            -> catstr [mkstr 2; Expression.to_short_string e]
  | Statement s                             -> catstr [mkstr 3; Statement.to_short_string s]
  | Modifier m                              -> catstr [mkstr 4; Modifier.to_short_string m]
  | Annotation a                            -> catstr [mkstr 5; Annotation.to_short_string a]
  | TypeBound                               -> mkstr 6
  | ThisInvocation                          -> mkstr 7
  | SuperInvocation                         -> mkstr 8
  | PrimaryInvocation                       -> mkstr 9
  | NameInvocation name                     -> combo 10 [name]
  | SLconstant tid                          -> catstr [mkstr 11; tid_to_string tid]
  | SLdefault                               -> mkstr 12
  | EVconditional                           -> mkstr 13
  | EVannotation                            -> mkstr 14
  | EVarrayInit                             -> mkstr 15
  | ElementValuePair name                   -> combo 16 [name]
  | Constructor(name, msig)                 -> combo 17 [name;msig]
  | StaticInitializer                       -> mkstr 18
  | InstanceInitializer                     -> mkstr 19
  | Block tid                               -> catstr [mkstr 20; tid_to_string tid]
  | VariableDeclarator(name, dims)          -> combo 21 [name; string_of_int dims]
  | CatchClause tid                         -> catstr [mkstr 23; tid_to_string tid]
  | Finally                                 -> mkstr 24
  | ForInit tid                             -> catstr [mkstr 25; tid_to_string tid]
  | ForCond tid                             -> catstr [mkstr 26; tid_to_string tid]
  | ForUpdate tid                           -> catstr [mkstr 27; tid_to_string tid]
  | SwitchBlockStatementGroup               -> mkstr 28
  | DimExpr                                 -> mkstr 29
  | Arguments                               -> mkstr 32
  | Annotations                             -> mkstr 33
  | NamedArguments name                     -> combo 34 [name]
  | TypeArguments(_, name)                  -> combo 35 [name]
  | Wildcard                                -> mkstr 36
  | Parameters name                         -> combo 37 [name]
  | Parameter(id, dims, va)                 -> combo 38 [id; (string_of_int dims); (if va then "..." else "")]
  | TypeParameter name                      -> combo 39 [name]
  | TypeParameters name                     -> combo 40 [name]
  | ArrayInitializer                        -> mkstr 41
  | Modifiers k                             -> catstr [mkstr 42; kind_to_short_string k]
  | FieldDeclaration vdids                  -> catstr [mkstr 43; vdids_to_string vdids]
  | Method(name, msig)                      -> combo 44 [name; msig]
  | Super                                   -> mkstr 45
  | Qualifier q                             -> catstr [mkstr 46; q]
  | Throws name                             -> combo 48 [name]
  | MethodBody(name, msig)                  -> combo 49 [name; msig]
  | Specifier k                             -> catstr [mkstr 50; kind_to_short_string k]
  | Class name                              -> combo 51 [name]
  | Enum name                               -> combo 52 [name]
  | EnumConstant name                       -> catstr [mkstr 53; name]
  | Extends                                 -> mkstr 54
  | Implements                              -> mkstr 55
  | ClassBody name                          -> combo 56 [name]
  | EnumBody name                           -> combo 57 [name]
  | Interface name                          -> combo 58 [name]
  | AnnotationType name                     -> catstr [mkstr 59; name]
  | AnnotationTypeBody name                 -> combo 60 [name]
  | ExtendsInterfaces                       -> mkstr 61
  | InterfaceBody name                      -> combo 62 [name]
  | PackageDeclaration name                 -> catstr [mkstr 63; name]
  | IDsingle name                           -> catstr [mkstr 64; name]
  | IDtypeOnDemand name                     -> catstr [mkstr 65; name]
  | IDsingleStatic(name, ident)             -> catstr [mkstr 66; name; ident]
  | IDstaticOnDemand name                   -> catstr [mkstr 67; name]
  | ImportDeclarations                      -> mkstr 68
  | TypeDeclarations                        -> mkstr 69
  | CompilationUnit                         -> mkstr 70
  | ElementDeclaration name                 -> catstr [mkstr 71; name]
  | FieldDeclarations name                  -> catstr [mkstr 72; name]
  | LocalVariableDeclaration(isstmt, vdids) -> catstr [mkstr 73; if isstmt then "S" else ""; vdids_to_string vdids]
  | WildcardBoundsExtends                   -> mkstr 74
  | WildcardBoundsSuper                     -> mkstr 75
  | InferredFormalParameters                -> mkstr 76
  | InferredFormalParameter id              -> combo 77 [id]
  | Error _                                 -> mkstr 79
  | SwitchBlock                             -> mkstr 80
  | ConstructorBody(name, msig)             -> combo 81 [name;msig]
  | ResourceSpec                            -> mkstr 82
  (*| Resource(name, dims)                    -> combo 83 [name; string_of_int dims]*)
  | CatchParameter(name, dims)              -> combo 84 [name; string_of_int dims]
  | AnnotDim ellipsis                       -> combo 85 [if ellipsis then "..." else "[]"]
  | HugeArray(sz, c) ->
      let h = Xhash.digest_hex_of_string Xhash.MD5 c in
      combo 86 [string_of_int sz; h]
  | EmptyDeclaration                        -> mkstr 87
  | ForHead tid                           -> catstr [mkstr 105; tid_to_string tid]
  | Aspect name                   -> combo 88 [name]
  | Pointcut name                 -> combo 89 [name]
  | DeclareParents                -> mkstr 90
  | DeclareMessage kwd            -> combo 91 [kwd]
  | DeclareSoft                   -> mkstr 92
  | DeclarePrecedence             -> mkstr 93
  | PointcutAnd                   -> mkstr 94
  | PointcutOr                    -> mkstr 95
  | PointcutNot                   -> mkstr 96
  | PointcutParen                 -> mkstr 97
  | PointcutWithin                -> mkstr 98
  | ClassnamePatternAnd           -> mkstr 99
  | ClassnamePatternOr            -> mkstr 100
  | ClassnamePatternNot           -> mkstr 101
  | ClassnamePatternParen         -> mkstr 102
  | ClassnamePatternName name     -> combo 103 [name]
  | ClassnamePatternNamePlus name -> combo 104 [name]

  | HugeExpr(sz, c) ->
      let h = Xhash.digest_hex_of_string Xhash.MD5 c in
      combo 105 [string_of_int sz; h]

  | SwitchRule -> mkstr 106
  | SRLconstant -> mkstr 107
  | SRLdefault -> mkstr 107
  | Record name -> combo 108 [name]

  | ReceiverParameter None -> mkstr 109
  | ReceiverParameter (Some id) -> combo 109 [id]

  | Module name -> combo 110 [name]
  | Open -> mkstr 111
  | ModuleName name -> combo 112 [name]
  | ModuleBody name -> combo 113 [name]
  | Requires name -> combo 114 [name]
  | Exports name -> combo 115 [name]
  | Opens name -> combo 116 [name]
  | Uses name -> combo 117 [name]
  | Provides name -> combo 118 [name]
  | Permits -> mkstr 119
  | TypeName name -> combo 120 [name]

  | VariableDeclaration -> mkstr 121

let sig_attr_name = "___signature"

let to_tag ?(strip=false) l =
  let name, attrs =
    match l with
    | Type ty                     -> Type.to_tag ty
    | Primary p                   -> Primary.to_tag p
    | Expression e                -> Expression.to_tag e
    | Statement s                 -> Statement.to_tag ~strip s
    | Modifier m                  -> Modifier.to_tag m
    | Annotation a                -> Annotation.to_tag a
    | TypeBound                   -> "TypeBound", []
    | ThisInvocation              -> "ThisInvocation", []
    | SuperInvocation             -> "SuperInvocation", []
    | PrimaryInvocation           -> "PrimaryInvocation", []
    | NameInvocation name         -> "NameInvocation", ["name",xmlenc name]

(* switch label *)
    | SLconstant tid              -> "ConstantLabel", mktidattr tid
    | SLdefault                   -> "DefaultLabel", []

(* element value *)
    | EVconditional               -> "ConditionalElementValue", []
    | EVannotation                -> "AnnotationElementValue", []
    | EVarrayInit                 -> "ArrayInitElementValue", []
    | ElementValuePair name       -> "ElementValuePair", ["name",xmlenc name]

(* class body declaration *)
    | Constructor(name, msig)     -> "ConstructorDeclaration", ["name",xmlenc name;sig_attr_name,xmlenc msig]
    | ConstructorBody _ when strip -> "ConstructorBody", []
    | ConstructorBody(name, msig) -> "ConstructorBody", ["name",xmlenc name;sig_attr_name,xmlenc msig]

    | StaticInitializer        -> "StaticInitializer", []
    | InstanceInitializer      -> "InstanceInitializer", []

    | Block _ when strip          -> "Block", []
    | Block tid                   -> "Block", mktidattr tid
    | VariableDeclarator(name, d) -> "VariableDeclarator", ["name",xmlenc name;dims_attr_name,string_of_int d;]
    | CatchClause tid             -> "CatchClause", mktidattr tid
    | Finally                     -> "Finally", []
    | ForInit _ when strip        -> "ForInit", []
    | ForCond _ when strip        -> "ForCond", []
    | ForUpdate _ when strip      -> "ForUpdate", []
    | ForInit tid                 -> "ForInit", mktidattr tid
    | ForCond tid                 -> "ForCond", mktidattr tid
    | ForUpdate tid               -> "ForUpdate", mktidattr tid
    | SwitchBlock                 -> "SwitchBlock", []
    | SwitchBlockStatementGroup   -> "SwitchBlockStatementGroup", []
    | DimExpr                     -> "DimExpression", []

    | Arguments                   -> "Arguments", []
    | Annotations                 -> "Annotations", []

    | NamedArguments _ when strip -> "Arguments", []
    | NamedArguments name         -> "Arguments", ["name",xmlenc name]

    | TypeArguments(nth, name)    -> "TypeArguments", ["nth",string_of_int nth;"name",xmlenc name]
    | Wildcard                    -> "Wildcard", []
    | WildcardBoundsExtends       -> "WildcardBoundsExtends", []
    | WildcardBoundsSuper         -> "WildcardBoundsSuper", []
    | Parameters name             -> "Parameters", ["name",xmlenc name]
    | Parameter(id, dims, va)     -> "Parameter", ["name",xmlenc id;dims_attr_name,string_of_int dims;"va",string_of_bool va]
    | ReceiverParameter None      -> "ReceiverParameter", []
    | ReceiverParameter (Some id) -> "ReceiverParameter", ["name",xmlenc id]
    | TypeParameter name          -> "TypeParameter", ["name",xmlenc name]
    | TypeParameters name         -> "TypeParameters", ["name",xmlenc name]
    | ArrayInitializer            -> "ArrayInitializer", []
    | Modifiers _ when strip      -> "Modifiers", []
    | Modifiers k                 -> "Modifiers", kind_to_attrs k
    | FieldDeclaration vdids      -> "FieldDeclaration", [(*vdids_attr_name*)"name",vdids_to_string vdids]
    | VariableDeclaration         -> "VariableDeclaration", []
    | Method(name, msig)          -> "MethodDeclaration", ["name",xmlenc name;sig_attr_name,xmlenc msig]
    | MethodBody _ when strip     -> "MethodBody", []
    | MethodBody(name, msig)      -> "MethodBody", ["name",xmlenc name;sig_attr_name,xmlenc msig]
    | Super                       -> "Super", []
    | Qualifier q                 -> "Qualifier", ["name",xmlenc q]
    | Throws name                 -> "Throws", ["name",xmlenc name]
    | Specifier k                 -> (kind_to_anonymous_string k)^"Specifier", kind_to_name_attrs k
    | Class name                  -> "ClassDeclaration", ["name",xmlenc name]
    | Enum name                   -> "EnumDeclaration", ["name",xmlenc name]
    | EnumConstant name           -> "EnumConstant", ["name",xmlenc name]
    | Record name                 -> "RecordDeclaration", ["name",xmlenc name]
    | Extends                     -> "Extends", []
    | Implements                  -> "Implements", []
    | Permits                     -> "Permits", []
    | ClassBody name              -> "ClassBody", ["name",xmlenc name]
    | EnumBody name               -> "EnumBody", ["name",xmlenc name]
    | Interface name              -> "InterfaceDeclaration", ["name",xmlenc name]
    | AnnotationType name         -> "AnnotationTypeDeclaration", ["name",xmlenc name]
    | AnnotationTypeBody name     -> "AnnotationTypeBody", ["name",xmlenc name]
    | ExtendsInterfaces           -> "ExtendsInterfaces", []
    | InterfaceBody name          -> "InterfaceBody", ["name",xmlenc name]
    | PackageDeclaration name     -> "PackageDeclaration", ["name",xmlenc name]

(* import declaration *)
    | IDsingle name               -> "SingleTypeImportDeclaration", ["name",xmlenc name]
    | IDtypeOnDemand name         -> "TypeImportOnDemandDeclaration", ["name",xmlenc name]
    | IDsingleStatic(name, ident) -> "SingleStaticImportDeclaration", ["name",xmlenc name;ident_attr_name,ident]
    | IDstaticOnDemand name       -> "StaticImportOnDemandDeclaration", ["name",xmlenc name]

    | ImportDeclarations          -> "ImportDeclarations", []
    | TypeDeclarations            -> "TypeDeclarations", []

(* annotation type element declaration *)
    | ElementDeclaration name     -> "AnnotationTypeElementDeclaration", ["name",xmlenc name]

    | FieldDeclarations name      -> "FieldDeclarations", ["name",xmlenc name]

    | InferredFormalParameters     -> "InferredFormalParameters", []
    | InferredFormalParameter id   -> "InferredFormalParameter", ["name",xmlenc id]

    | CompilationUnit             -> "CompilationUnit", []
    | LocalVariableDeclaration(isstmt, vdids) ->
        (if isstmt then
          "LocalVariableDeclarationStatement"
        else
          "LocalVariableDeclaration"), [(*vdids_attr_name*)"name",vdids_to_string vdids]

    | ResourceSpec                -> "ResourceSpec", []
    (*| Resource(name, dims)        -> "Resource", ["name",xmlenc name;
                                                  dims_attr_name,string_of_int dims]*)

    | CatchParameter(name, dims)  -> "CatchParameter", ["name",xmlenc name;
                                                        dims_attr_name,string_of_int dims]

    | AnnotDim ellipsis -> "AnnotDim", ["ellipsis",string_of_bool ellipsis]

    | Error s -> "Error", ["contents",xmlenc s]

    | HugeArray(sz, c) -> "HugeArray", ["size",string_of_int sz;"code",xmlenc c]
    | HugeExpr(sz, c) -> "HugeExpr", ["size",string_of_int sz;"code",xmlenc c]

    | EmptyDeclaration -> "EmptyDeclaration", []

    | ForHead tid -> "ForHead", mktidattr tid

    | Aspect name                   -> "Aspect", ["name",xmlenc name]
    | Pointcut name                 -> "Pointcut", ["name",xmlenc name]
    | DeclareParents                -> "DeclareParents", []
    | DeclareMessage kwd            -> "DeclareMessage", ["level",kwd]
    | DeclareSoft                   -> "DeclareSoft", []
    | DeclarePrecedence             -> "DeclarePrecedence", []
    | PointcutAnd                   -> "PointcutAnd", []
    | PointcutOr                    -> "PointcutOr", []
    | PointcutNot                   -> "PointcutNot", []
    | PointcutParen                 -> "PointcutParen", []
    | PointcutWithin                -> "PointcutWithin", []
    | ClassnamePatternAnd           -> "ClassnamePatternAnd", []
    | ClassnamePatternOr            -> "ClassnamePatternOr", []
    | ClassnamePatternNot           -> "ClassnamePatternNot", []
    | ClassnamePatternParen         -> "ClassnamePatternParen", []
    | ClassnamePatternName name     -> "ClassnamePatternName", ["name",xmlenc name]
    | ClassnamePatternNamePlus name -> "ClassnamePatternNamePlus", ["name",xmlenc name]
    | SwitchRule                    -> "SwitchRule", []
    | SRLconstant                   -> "ConstantRuleLabel", []
    | SRLdefault                    -> "DefaultRuleLabel", []

    | Module name     -> "ModuleDeclaration", ["name",xmlenc name]
    | Open            -> "Open", []
    | ModuleName name -> "ModuleName", ["name",xmlenc name]
    | ModuleBody name -> "ModuleBody", ["name",xmlenc name]
    | Requires name   -> "RequiresDirective", ["name",xmlenc name]
    | Exports name    -> "ExportsDirective", ["name",xmlenc name]
    | Opens name      -> "OpensDirective", ["name",xmlenc name]
    | Uses name       -> "UsesDirective", ["name",xmlenc name]
    | Provides name   -> "ProvidesDirective", ["name",xmlenc name]
    | TypeName name   -> "TypeName", ["name",xmlenc name]
  in
  name, attrs



let to_char lab =
  let to_index = function
    | Type _ -> 0
    | Primary _ -> 1
    | Expression _ -> 2
    | Statement s -> (* 3 *) Statement.to_index s (* 90 - *)
    | Modifier _ -> 4
    | Annotation _ -> 5

    | TypeBound -> 6
    | ThisInvocation -> 7
    | SuperInvocation -> 8
    | PrimaryInvocation -> 9
    | NameInvocation _ -> 10
    | SLconstant _ -> 11
    | SLdefault -> 12
    | EVconditional -> 13
    | EVannotation -> 14
    | EVarrayInit -> 15
    | ElementValuePair _ -> 16
    | Constructor(_, _) -> 17
    | StaticInitializer -> 18
    | InstanceInitializer -> 19
    | Block _ -> 20
    | VariableDeclarator(_, _) -> 21
    | CatchClause _ -> 23
    | Finally -> 24
    | ForInit _ -> 25
    | ForCond _ -> 26
    | ForUpdate _ -> 27
    | SwitchBlockStatementGroup -> 28
    | DimExpr -> 29
    | Arguments -> 32
    | Annotations -> 33
    | NamedArguments _ -> 34
    | TypeArguments(_, _) -> 35
    | Wildcard -> 36
    | Parameters _ -> 37
    | Parameter(_, _, _) -> 38
    | TypeParameter _ -> 39
    | TypeParameters _ -> 40
    | ArrayInitializer -> 41
    | Modifiers _ -> 42
    | FieldDeclaration _ -> 43
    | Method(_, _) -> 48
    | Super -> 49
    | Qualifier _ -> 50
    | Throws _ -> 52
    | MethodBody(_, _) -> 53
    | Specifier _ -> 54
    | Class _ -> 55
    | Enum _ -> 56
    | EnumConstant _ -> 57
    | Extends -> 58
    | Implements -> 59
    | ClassBody _ -> 60
    | EnumBody _ -> 61
    | Interface _ -> 62
    | AnnotationType _ -> 63
    | AnnotationTypeBody _ -> 64
    | ExtendsInterfaces -> 65
    | InterfaceBody _ -> 66
    | PackageDeclaration _ -> 67
    | IDsingle _ -> 68
    | IDtypeOnDemand _ -> 69
    | IDsingleStatic(_, _) -> 70
    | IDstaticOnDemand _ -> 71
    | ImportDeclarations -> 72
    | TypeDeclarations -> 73
    | CompilationUnit -> 74
    | ElementDeclaration _ -> 75
    | FieldDeclarations _ -> 76
    | LocalVariableDeclaration(_, _) -> 77
    | WildcardBoundsExtends -> 78
    | WildcardBoundsSuper -> 79
    | InferredFormalParameters -> 80
    | InferredFormalParameter _ -> 81
    | Error _ -> 83
    | SwitchBlock -> 84
    | ConstructorBody _ -> 85
    | ResourceSpec -> 86
    (*| Resource _ -> 87*)
    | CatchParameter(_, _) -> 88
    | AnnotDim _ -> 89
    | HugeArray _ -> 90
    | EmptyDeclaration -> 91
    | ForHead _ -> 109
    | Aspect _                   -> 92
    | Pointcut _                 -> 93
    | DeclareParents             -> 94
    | DeclareMessage _           -> 95
    | DeclareSoft                -> 96
    | DeclarePrecedence          -> 97
    | PointcutAnd                -> 98
    | PointcutOr                 -> 99
    | PointcutNot                -> 100
    | PointcutParen              -> 101
    | PointcutWithin             -> 102
    | ClassnamePatternAnd        -> 103
    | ClassnamePatternOr         -> 104
    | ClassnamePatternNot        -> 105
    | ClassnamePatternParen      -> 106
    | ClassnamePatternName _     -> 107
    | ClassnamePatternNamePlus _ -> 108
    | HugeExpr _ -> 109
    | SwitchRule -> 110
    | SRLconstant -> 111
    | SRLdefault -> 112
    | Record _ -> 113
    | ReceiverParameter _ -> 114
    | Module _ -> 115
    | Open -> 116
    | ModuleName _ -> 117
    | ModuleBody _ -> 118
    | Requires _ -> 119
    | Exports _ -> 120
    | Opens _ -> 121
    | Uses _ -> 122
    | Provides _ -> 123
    | Permits -> 124
    | TypeName _ -> 125
    | VariableDeclaration -> 126
  in
  char_pool.(to_index lab)


let to_elem_data = Astml.to_elem_data lang_prefix to_tag


let of_javatype ?(resolve=true) ty = (Type (Type.of_javatype ~resolve ty))

let of_classname ?(resolve=true) name = Type (Type.make_class ~resolve name)

let of_literal
    ?(anonymize_int=false)
    ?(anonymize_float=false)
    ?(anonymize_string=false)
    ?(reduce=false)
    lit =
  Primary (Primary.of_literal ~anonymize_int ~anonymize_float ~anonymize_string ~reduce lit)

let of_binary_operator bo =
  Expression (Expression.of_binary_operator bo)


let mkelab ?(tid=null_tid) se e =
  if se then
    Statement (Statement.make_statement_expression e tid)
  else
    Expression e

let mkplab ?(tid=null_tid) se p =
  if se then
    mkelab ~tid se (Expression.make_primary p)
  else
    Primary p

let of_assignment_operator ?(is_stmt=false) ao tid =
  mkelab is_stmt (Expression.of_assignment_operator ao tid)

let of_unary_operator ?(is_stmt=false) uo =
  mkelab is_stmt (Expression.of_unary_operator uo)

let get_expr = function
  | Expression e -> e
  | Primary p -> Expression.Primary p
  | _ -> raise (Failure "Langs.Java.Label.get_expr")

(* *)

let is_hunk_boundary plab clab =
  match plab with
  | ConstructorBody _ | MethodBody _ | Block _ -> begin
      match clab with
      | Statement _ -> true
      | _ -> false
  end
  | ClassBody _ | EnumBody _ | InterfaceBody _ | AnnotationTypeBody _
  | FieldDeclarations _ -> true
  | _ -> false


(* These labels are collapsible whether they are leaves or not. *)
let forced_to_be_collapsible _ =
  false

let is_collapse_target options lab =
  if options#no_collapse_flag then
    false
  else
    match lab with
    | Statement _
    | Primary _
    | Expression _
    | Type (Type.ClassOrInterface _ | Type.Class _ | Type.Interface _ | Type.Array _)

    | Class _
    | Enum _
    | Interface _
    | AnnotationType _
    | Specifier _
    | ClassBody _
    | EnumBody _
    | InterfaceBody _
    | AnnotationTypeBody _
    | SwitchBlock
    | LocalVariableDeclaration(true, _)
    | VariableDeclarator _
    | Method _
    | StaticInitializer
    | InstanceInitializer
    | Constructor _
    | ForInit _
    | ForCond _
    | ForUpdate _
    | ForHead _
    | Block _
    | Parameters _
    | Parameter _
    | MethodBody _
    | ConstructorBody _
    | TypeArguments _
    | TypeParameters _
    | Arguments
    | NamedArguments _
    | Modifiers _
    | Annotations
    | FieldDeclarations _
    | InferredFormalParameters
    | ArrayInitializer
(*    | CatchParameter _*)
(*    | CatchClause _*)

    | Aspect _
    | Pointcut _
    | DeclareParents
    | DeclareMessage _
    | DeclareSoft
    | DeclarePrecedence
    | PointcutAnd
    | PointcutOr
    | PointcutNot
    | PointcutParen
    | PointcutWithin
    | ClassnamePatternAnd
    | ClassnamePatternOr
    | ClassnamePatternNot
    | ClassnamePatternParen
      -> true
    | _ -> false

let is_statement_expression = function
  (*| Primary p -> begin
      match p with
      | Primary.InstanceCreation _
      | Primary.QualifiedInstanceCreation _
      | Primary.NameQualifiedInstanceCreation _
      | Primary.PrimaryMethodInvocation _
      | Primary.SimpleMethodInvocation _
      | Primary.SuperMethodInvocation _
      | Primary.ClassSuperMethodInvocation _
      | Primary.TypeMethodInvocation _ -> true
      | _ -> false
  end*)
  | Expression e -> begin
      match e with
      | Expression.AssignmentOperator _ -> true
      | Expression.Primary p -> begin
          match p with
          | Primary.InstanceCreation _
          | Primary.QualifiedInstanceCreation _
          | Primary.NameQualifiedInstanceCreation _
          | Primary.PrimaryMethodInvocation _
          | Primary.SimpleMethodInvocation _
          | Primary.SuperMethodInvocation _
          | Primary.ClassSuperMethodInvocation _
          | Primary.TypeMethodInvocation _ -> true
          | _ -> false
      end
      | Expression.UnaryOperator uop -> begin
          match uop with
          | UnaryOperator.PreIncrement
          | UnaryOperator.PreDecrement
          | UnaryOperator.PostIncrement
          | UnaryOperator.PostDecrement -> true
          | _ -> false
      end
      | _ -> false
  end
  | _ -> false

let is_compatible ?(weak=false) lab1 lab2 =
  match lab1, lab2 with
  | Primary p1, Primary p2 -> Primary.is_compatible p1 p2
  | Method(n1, _), Method(n2, _) -> n1 = n2
  | Constructor(n1, _), Constructor(n2, _) -> n1 = n2

  | Statement (Statement.Expression(Expression.Primary _p, _)), Primary p
  | Primary p, Statement (Statement.Expression(Expression.Primary _p, _)) -> begin
      match p with
      | Primary.InstanceCreation _
      | Primary.QualifiedInstanceCreation _
      | Primary.NameQualifiedInstanceCreation _
      | Primary.PrimaryMethodInvocation _
      | Primary.SimpleMethodInvocation _
      | Primary.SuperMethodInvocation _
      | Primary.ClassSuperMethodInvocation _
      | Primary.TypeMethodInvocation _ -> _p = p
      | _ -> false
  end

  | ClassBody _, InterfaceBody _ | InterfaceBody _, ClassBody _ when weak -> true (* invalid when dumping delta *)
  | ClassBody _, EnumBody _ | EnumBody _, ClassBody _ when weak -> true
  | EnumBody _, InterfaceBody _ | InterfaceBody _, EnumBody _ when weak -> true
  | _ -> false

let quasi_eq lab1 lab2 =
  match lab1, lab2 with
  | Primary prim1, Primary prim2 -> begin
      match prim1, prim2 with
      | Primary.SimpleMethodInvocation n1, Primary.FieldAccess n2 -> begin
          let n1_ = String.lowercase_ascii n1 in
          let n2_ = String.lowercase_ascii n2 in
          n1_ = "get"^n2_^"#0"
      end
      | Primary.FieldAccess n1, Primary.SimpleMethodInvocation n2 -> begin
          let n1_ = String.lowercase_ascii n1 in
          let n2_ = String.lowercase_ascii n2 in
          n2_ = "get"^n1_^"#0"
      end
      | _ -> false
  end
  | _ -> false

let relabel_allowed (lab1, lab2) =
  let allowed =
    match lab1, lab2 with
    | Statement stmt1, Statement stmt2 -> Statement.relabel_allowed(stmt1, stmt2)

    | Statement (Statement.Expression(Expression.Primary _p, _)), Primary p
    | Primary p, Statement (Statement.Expression(Expression.Primary _p, _)) -> begin
        match p with
        | Primary.InstanceCreation _
        | Primary.QualifiedInstanceCreation _
        | Primary.NameQualifiedInstanceCreation _
        | Primary.PrimaryMethodInvocation _
        | Primary.SimpleMethodInvocation _
        | Primary.SuperMethodInvocation _
        | Primary.ClassSuperMethodInvocation _
        | Primary.TypeMethodInvocation _ -> begin
            try
              Primary.get_name _p = Primary.get_name p
            with _ -> false
        end
        | _ -> false
    end

    | Statement (Statement.Expression(e, _)), Primary p
    | Primary p, Statement (Statement.Expression(e, _)) -> begin
        match p with
        | Primary.InstanceCreation _
        | Primary.QualifiedInstanceCreation _
        | Primary.NameQualifiedInstanceCreation _
        | Primary.PrimaryMethodInvocation _
        | Primary.SimpleMethodInvocation _
        | Primary.SuperMethodInvocation _
        | Primary.ClassSuperMethodInvocation _
        | Primary.TypeMethodInvocation _ -> begin
            try
              Expression.get_name e = Primary.get_name p
            with _ -> false
        end
        | _ -> false
    end

    (*| Statement (Statement.Expression(Expression.AssignmentOperator _, _)), VariableDeclarator _
    | VariableDeclarator _, Statement (Statement.Expression(Expression.AssignmentOperator _, _)) -> true*)

    (*| Statement (Statement.Expression _), lab
    | lab, Statement (Statement.Expression _) -> is_statement_expression lab*)

    (*| Expression (Expression.Primary _), Primary _
    | Primary _, Expression (Expression.Primary _)*)

    | Primary (Primary.Name _), Qualifier _
    | Qualifier _, Primary (Primary.Name _)
    | Primary (Primary.FieldAccess _), Qualifier _
    | Qualifier _, Primary (Primary.FieldAccess _)

    | Primary (Primary.Name _), Primary (Primary.FieldAccess _)
    | Primary (Primary.FieldAccess _), Primary (Primary.Name _)

    | Type (Type.Class _), Primary (Primary.FieldAccess _)
    | Primary (Primary.FieldAccess _), Type (Type.Class _)

    | Type (Type.Class _), Primary (Primary.Name _)
    | Primary (Primary.Name _), Type (Type.Class _)

    | Primary _, Expression _
    | Expression _, Primary _

    | Expression Expression.Cond, Statement Statement.If _
    | Statement Statement.If _, Expression Expression.Cond

    | Expression Expression.Switch, Statement Statement.If _
    | Statement Statement.If _, Expression Expression.Switch

    | Implements, Extends | Extends, Implements
    | Implements, ExtendsInterfaces | ExtendsInterfaces, Implements
    | ExtendsInterfaces, Extends | Extends, ExtendsInterfaces

    | Method _, Constructor _ | Constructor _, Method _

    | MethodBody _, MethodBody _
    | MethodBody _, ConstructorBody _ | ConstructorBody _, MethodBody _
    | ConstructorBody _, ConstructorBody _

    | MethodBody _, Block _ | Block _, MethodBody _
    | ConstructorBody _, Block _ | Block _, ConstructorBody _

    | Type _, Type _
    | Primary _, Primary _
    | Expression _, Expression _
    | Modifier _, Modifier _
    | LocalVariableDeclaration _, LocalVariableDeclaration _

    | Wildcard, Type _ | Type _, Wildcard
    | WildcardBoundsExtends, Type _ | Type _, WildcardBoundsExtends
    | WildcardBoundsSuper, Type _ | Type _, WildcardBoundsSuper

    | CatchClause _, CatchClause _

    (*| LocalVariableDeclaration _, Resource _ | Resource _, LocalVariableDeclaration _*)

    (*| VariableDeclarator _, Primary (Primary.Name _|Primary.FieldAccess _)
    | Primary (Primary.Name _|Primary.FieldAccess _), VariableDeclarator _*)

    | VariableDeclarator _, InferredFormalParameter _
    | InferredFormalParameter _, VariableDeclarator _

    | LocalVariableDeclaration _, FieldDeclaration _
    | FieldDeclaration _, LocalVariableDeclaration _

    | Parameter _, CatchParameter _ | CatchParameter _, Parameter _
    | Parameter _, LocalVariableDeclaration _ | LocalVariableDeclaration _, Parameter _
    | LocalVariableDeclaration _, CatchParameter _ | CatchParameter _, LocalVariableDeclaration _

      -> true

    | l1, l2 -> anonymize2 l1 = anonymize2 l2
  in
  let disallowed =
    match lab1, lab2 with
    | _ -> false
  in
  let b = allowed && not disallowed in
  (*begin%debug
    [%debug_log "%s vs %s -> %B" (to_string lab1) (to_string lab2) b;
    let tag1, _ = to_tag lab1 in
    let tag2, _ = to_tag lab2 in
    [%debug_log "%s vs %s -> %B" tag1 tag2 b;
  end%debug;*)
  b

let move_disallowed = function
  | Annotation a -> Annotation.move_disallowed a
  (*| Type t -> Type.is_common t*)
  | _ -> false

let is_common = function
  | Annotation a -> Annotation.move_disallowed a
  | Type t -> Type.is_common t
  | Primary p
  | Expression (Expression.Primary p)
  | Statement (Statement.Expression (Expression.Primary p, _)) -> Primary.is_common p
  | IDsingle n -> Xset.mem Type.common_classes n
  | _ -> false

let is_order_insensitive = function
  | FieldDeclaration _
  | Constructor _
  | Method _
  | Class _
  | Enum _
  | Interface _
  | IDsingle _
  | IDtypeOnDemand _
  | IDsingleStatic _
  | IDstaticOnDemand _
  | Modifier _
  | Annotation _
      -> true
  | _ -> false

let is_named = function
  | Type t -> Type.is_named t
  | Primary p -> Primary.is_named p
  | Expression e -> Expression.is_named e
  | Statement s -> Statement.is_named s
  | Annotation _
  | NameInvocation _
  | ElementValuePair _
  | Constructor _
  | ConstructorBody _
  | VariableDeclarator _
  | NamedArguments _
  | TypeArguments _
  | Parameters _
  | Parameter _
  | TypeParameter _
  | TypeParameters _
  | Modifiers _
  | FieldDeclaration _
  | Method _
  | Qualifier _
  | Throws _
  | MethodBody _
  | Class _
  | Enum _
  | EnumConstant _
  | Record _
  | ClassBody _
  | EnumBody _
  | Interface _
  | Specifier _
  | AnnotationType _
  | AnnotationTypeBody _
  | InterfaceBody _
  | PackageDeclaration _
  | IDsingle _
  | IDtypeOnDemand _
  | IDsingleStatic _
  | IDstaticOnDemand _
  | ElementDeclaration _
  | FieldDeclarations _
  | LocalVariableDeclaration _
  | InferredFormalParameter _
  (*| Resource _*)
  | CatchParameter _
    -> true

  | ClassnamePatternName _
  | ClassnamePatternNamePlus _
      -> true

  | Module _
  | ModuleName _
  | ModuleBody _
  | Requires _
  | Exports _
  | Opens _
  | Uses _
  | Provides _
  | TypeName _
    -> true

  | _ -> false

let is_named_orig = function
  | Type t -> Type.is_named(*_orig*) t
  | Primary p -> Primary.is_named_orig p
  | Expression e -> Expression.is_named_orig e
  | Statement s -> Statement.is_named_orig s
  | Annotation a -> Annotation.is_named_orig a
  | NameInvocation _
  | ElementValuePair _
  | Constructor _
  | VariableDeclarator _
  | FieldDeclaration _ (* for merging (potential duplication detection) *)
  | Parameter _
  | TypeParameter _
  | Method _
  | Qualifier _
  | Class _
  | Enum _
  | EnumConstant _
  | Record _
  | Interface _ 
  | Specifier _
  | AnnotationType _
  | ElementDeclaration _
  | PackageDeclaration _
  | IDsingle _
  | IDtypeOnDemand _
  | IDsingleStatic _
  | IDstaticOnDemand _
  | InferredFormalParameter _
  (*| Resource _*)
  | CatchParameter _
  | HugeArray _
  | HugeExpr _
    -> true

  | ClassnamePatternName _
  | ClassnamePatternNamePlus _
      -> true

  | Module _
  | ModuleName _
  | Requires _
  | Exports _
  | Opens _
  | Uses _
  | Provides _
  | TypeName _
    -> true

  | _ -> false


let is_to_be_notified = function
  | Module _
  | Class _
  | Interface _
  | Method _ -> true
  | _ -> false

let is_partition = function
  | IDsingle _
  | IDtypeOnDemand _
  | IDsingleStatic _
  | IDstaticOnDemand _
  | Module _
  | Class _
  | Enum _
  | Interface _
  | Method _ -> true
  | Pointcut _ -> true
  | _ -> false


let is_boundary = function
  | Module _
  | Class _
  | Interface _
  (*| FieldDeclaration _*)
  | Method _
  | Constructor _
  | InstanceInitializer
  | StaticInitializer
  | ImportDeclarations
  | FieldDeclarations _
  | TypeDeclarations
  | CompilationUnit
  | Aspect _
    -> true
  | _ -> false

let is_sequence = function
  | ModuleBody _
  | Block _
  | MethodBody _
  | ConstructorBody _
  | SwitchBlock
  | ClassBody _
  | EnumBody _
  | AnnotationTypeBody _
  | ImportDeclarations
  | TypeDeclarations
  | CompilationUnit
  | FieldDeclarations _
(*  | Statement Statement.Try*)
(*  | ArrayInitializer*)
(*  | InferredFormalParameters*)
    -> true

  | _ -> false

let is_ntuple = function
  | Parameters _
  | TypeParameters _
  | InferredFormalParameters
  | Arguments
  | NamedArguments _
  | TypeArguments _
      -> true
  | _ -> false

(* for change pattern detection *)

let is_wildcard_bounds = function
  | WildcardBoundsExtends
  | WildcardBoundsSuper -> true
  | _ -> false

let is_if = function
  | Statement Statement.If _ -> true
  (*| Statement Statement.FlattenedIf _ -> true*)
  | _ -> false

let is_elseif = function
  | Statement Statement.ElseIf _ -> true
  | _ -> false

let is_else = function
  | Statement Statement.Else -> true
  | _ -> false

let is_while = function
  | Statement Statement.While -> true
  | _ -> false

let is_do = function
  | Statement Statement.Do -> true
  | _ -> false

let is_try = function
  | Statement Statement.Try -> true
  | _ -> false

let is_yield = function
  | Statement Statement.Yield -> true
  | _ -> false

let is_return = function
  | Statement Statement.Return -> true
  | _ -> false

let is_method = function
  | Method _ -> true
  | _ -> false

let is_parameter = function
  | Parameter _ -> true
  | _ -> false

let is_va_parameter = function
  | Parameter(_, _, va) -> va
  | _ -> false

let is_parameters = function
  | Parameters _ -> true
  | _ -> false

let is_typeparameter = function
  | TypeParameter _ -> true
  | _ -> false

let is_typeparameters = function
  | TypeParameters _ -> true
  | _ -> false

let is_typearguments ?(nth=1) = function
  | TypeArguments(n, _) -> n = nth
  | _ -> false

let is_statement = function
  | Statement _ -> true
  | LocalVariableDeclaration(true, _) -> true
  | _ -> false

let is_statement_or_block = function
  | Statement _
  | Block _ -> true
  | _ -> false

let is_field = function
  | FieldDeclaration _ -> true
  | _ -> false

let is_fieldaccess = function
  | Primary (Primary.FieldAccess _) -> true
  | _ -> false

let is_import_single = function
  | IDsingle _ -> true
  | _ -> false

let is_type = function
  | Type _ -> true
  | _ -> false

let is_module = function
  | Module _ -> true
  | _ -> false

let is_module_body = function
  | ModuleBody _ -> true
  | _ -> false

let is_open = function
  | Open -> true
  | _ -> false

let is_module_directive = function
  | Requires _
  | Exports _
  | Opens _
  | Uses _
  | Provides _ -> true
  | _ -> false

let is_class = function
  | Class _ -> true
  | _ -> false

let is_implements = function
  | Implements -> true
  | _ -> false

let is_permits = function
  | Permits -> true
  | _ -> false

let is_classbody = function
  | ClassBody _ -> true
  | _ -> false

let is_classbodydecl = function
  | FieldDeclaration _
  | Method _
  | Class _
  | Enum _
  | Interface _
  | StaticInitializer
  | InstanceInitializer
  | Constructor _
  | EmptyDeclaration
  | Aspect _
    -> true
  | _ -> false

let is_emptydecl = function
  | EmptyDeclaration -> true
  | _ -> false

let is_enumbody = function
  | EnumBody _ -> true
  | _ -> false

let is_interface = function
  | Interface _ -> true
  | _ -> false

let is_interfacebody = function
  | InterfaceBody _ -> true
  | _ -> false

let is_annotationtype = function
  | AnnotationType _ -> true
  | _ -> false

let is_annotationtypebody = function
  | AnnotationTypeBody _ -> true
  | _ -> false

let is_annotations = function
  | Annotations -> true
  | _ -> false

let is_annotation = function
  | Annotation _ -> true
  | _ -> false

let is_class_or_interface = function
  | Class _ | Interface _ -> true
  | _ -> false

let is_enum = function
  | Enum _ -> true
  | _ -> false

let is_enumconstant = function
  | EnumConstant _ -> true
  | _ -> false

let is_record = function
  | Record _ -> true
  | _ -> false

let is_typedeclaration = function
  | Class _ | Interface _ | Enum _ | AnnotationType _ -> true
  | _ -> false

let is_modifier = function
  | Modifier _ -> true
  | _ -> false

let is_final = function
  | Modifier Modifier.Final -> true
  | _ -> false

let is_public = function
  | Modifier Modifier.Public -> true
  | _ -> false

let is_private = function
  | Modifier Modifier.Private -> true
  | _ -> false

let is_protected = function
  | Modifier Modifier.Protected -> true
  | _ -> false

let is_modifiers = function
  | Modifiers _ -> true
  | _ -> false

let is_methodbody = function
  | MethodBody _ -> true
  | _ -> false

let is_ctorbody = function
  | ConstructorBody _ -> true
  | _ -> false

let is_extends = function
  | Extends -> true
  | _ -> false

let is_extendsinterfaces = function
  | ExtendsInterfaces -> true
  | _ -> false

let is_localvariabledecl = function
  | LocalVariableDeclaration _ -> true
  | _ -> false

let is_assert = function
  | Statement Statement.Assert -> true
  | _ -> false

let is_for = function
  | Statement
      (Statement.For
  | Statement.ForEnhanced) -> true
  | _ -> false

let is_forinit = function
  | ForInit _ -> true
  | _ -> false

let is_forcond = function
  | ForCond _ -> true
  | _ -> false

let is_forupdate = function
  | ForUpdate _ -> true
  | _ -> false

let is_forhead = function
  | ForHead _ -> true
  | _ -> false

let is_switchblock = function
  | SwitchBlock -> true
  | _ -> false

let is_switchblockstmtgroup = function
  | SwitchBlockStatementGroup -> true
  | _ -> false

let is_switchrule = function
  | SwitchRule -> true
  | _ -> false

let is_switchlabel = function
  | SLconstant _ | SLdefault -> true
  | _ -> false

let is_switchrulelabel = function
  | SRLconstant | SRLdefault -> true
  | _ -> false

let is_arrayinitializer = function
  | ArrayInitializer | HugeArray _ -> true
  | _ -> false

let is_variabledeclarator = function
  | VariableDeclarator _ -> true
  | _ -> false

let is_literal = function
  | Primary (Primary.Literal _)
  | Expression (Expression.Primary (Primary.Literal _)) -> true
  | _ -> false

let is_string_literal = function
  | Primary (Primary.Literal (Literal.String _)) -> true
  | _ -> false

let is_text_block = function
  | Primary (Primary.Literal (Literal.TextBlock _)) -> true
  | _ -> false

let is_int_literal = function
  | Primary (Primary.Literal (Literal.Integer _)) -> true
  | _ -> false

let is_real_literal = function
  | Primary (Primary.Literal (Literal.FloatingPoint _)) -> true
  | _ -> false

let is_name = function
  | Primary (Primary.Name _) -> true
  | _ -> false

let is_ambiguous_name = function
  | Primary (Primary.AmbiguousName _) -> true
  | _ -> false

let is_ambiguous_method_invocation = function
  | Primary (Primary.AmbiguousMethodInvocation _) -> true
  | _ -> false

let is_instancecreation = function
  | Primary
      (Primary.InstanceCreation _
  | Primary.QualifiedInstanceCreation _
  | Primary.NameQualifiedInstanceCreation _) -> true
  | _ -> false


let is_assignment = function
  | Expression (Expression.AssignmentOperator _)
  | Statement (Statement.Expression(Expression.AssignmentOperator _, _)) -> true
  | _ -> false

let is_qualifier = function
  | Qualifier _ -> true
  | _ -> false

let is_arguments = function
  | NamedArguments _ | Arguments -> true
  | _ -> false

let is_arraycreation = function
  | Primary (Primary.ArrayCreationDims _ | Primary.ArrayCreationInit) -> true
  | _ -> false

let is_importdeclarations = function
  | ImportDeclarations -> true
  | _ -> false

let is_throws = function
  | Throws _ -> true
  | _ -> false

let is_expression = function
  | Primary _
  | Expression _
  | HugeExpr _
    -> true
  | _ -> false

let is_op = function
  | Expression (
    Expression.UnaryOperator _ |
    Expression.BinaryOperator _ |
    Expression.Instanceof |
    Expression.AssignmentOperator _ |
    Expression.Cast)
      -> true
  | _ -> false

let is_methodinvocation = function
  | Primary (
    Primary.PrimaryMethodInvocation _
  | Primary.SimpleMethodInvocation _
  | Primary.SuperMethodInvocation _
  | Primary.ClassSuperMethodInvocation _
  | Primary.TypeMethodInvocation _)

  | Statement (
    Statement.Expression (
    Expression.Primary (
    Primary.PrimaryMethodInvocation _
  | Primary.SimpleMethodInvocation _
  | Primary.SuperMethodInvocation _
  | Primary.ClassSuperMethodInvocation _
  | Primary.TypeMethodInvocation _), _))
    -> true

  | _ -> false

let is_ctorinvocation = function
  | Primary (
    Primary.InstanceCreation _
  | Primary.QualifiedInstanceCreation _
  | Primary.NameQualifiedInstanceCreation _)

  | Statement (
    Statement.Expression (
    Expression.Primary (
    Primary.InstanceCreation _
  | Primary.QualifiedInstanceCreation _
  | Primary.NameQualifiedInstanceCreation _), _))

  | ThisInvocation
  | SuperInvocation
  | PrimaryInvocation
  | NameInvocation _ -> true

  | _ -> false

let is_invocation = function
  | Primary (
    Primary.PrimaryMethodInvocation _
  | Primary.SimpleMethodInvocation _
  | Primary.SuperMethodInvocation _
  | Primary.ClassSuperMethodInvocation _
  | Primary.TypeMethodInvocation _)

  | Statement (
    Statement.Expression (
    Expression.Primary (
    Primary.PrimaryMethodInvocation _
  | Primary.SimpleMethodInvocation _
  | Primary.SuperMethodInvocation _
  | Primary.ClassSuperMethodInvocation _
  | Primary.TypeMethodInvocation _), _))

  | ThisInvocation
  | SuperInvocation
  | PrimaryInvocation
  | NameInvocation _
    -> true

  | _ -> false

let is_simple_invocation = function
  | Primary (Primary.SimpleMethodInvocation _)
  | Statement (Statement.Expression (Expression.Primary (Primary.SimpleMethodInvocation _), _))
    -> true

  | _ -> false

let is_instance_creation = function
  | Primary (
    Primary.InstanceCreation _
  | Primary.QualifiedInstanceCreation _
  | Primary.NameQualifiedInstanceCreation _)

  | Statement (
    Statement.Expression (
    Expression.Primary (
    Primary.InstanceCreation _
  | Primary.QualifiedInstanceCreation _
  | Primary.NameQualifiedInstanceCreation _), _))
    -> true

  | _ -> false

let is_invocation_or_instance_creation = function
  | Primary (
    Primary.InstanceCreation _
  | Primary.QualifiedInstanceCreation _
  | Primary.NameQualifiedInstanceCreation _
  | Primary.PrimaryMethodInvocation _
  | Primary.SimpleMethodInvocation _
  | Primary.SuperMethodInvocation _
  | Primary.ClassSuperMethodInvocation _
  | Primary.TypeMethodInvocation _)

  | Statement (
    Statement.Expression (
    Expression.Primary (
    Primary.InstanceCreation _
  | Primary.QualifiedInstanceCreation _
  | Primary.NameQualifiedInstanceCreation _
  | Primary.PrimaryMethodInvocation _
  | Primary.SimpleMethodInvocation _
  | Primary.SuperMethodInvocation _
  | Primary.ClassSuperMethodInvocation _
  | Primary.TypeMethodInvocation _), _))

  | ThisInvocation
  | SuperInvocation
  | PrimaryInvocation
  | NameInvocation _
    -> true

  | _ -> false


let is_specifier = function
  | Specifier _ -> true
  | _ -> false

let is_primary = function
  | Primary _ -> true
  (*| Statement (Statement.Expression (Expression.Primary _, _)) -> true*)
  | _ -> false

let is_primarythis = function
  | Primary (Primary.This) -> true
  | _ -> false

let is_primaryname = function
  | Primary (Primary.Name _) -> true
  | _ -> false

let is_unaryop = function
  | Expression (
    Expression.UnaryOperator _
(*
  | Expression.PreIncrement | Expression.PreDecrement
  | Expression.PostIncrement | Expression.PostDecrement*)) -> true
  | _ -> false

let is_binaryop = function
  | Expression (
    Expression.Cast
  | Expression.BinaryOperator _
  | Expression.Instanceof
  | Expression.AssignmentOperator _) -> true
  | _ -> false

let is_binary_add = function
  | Expression (Expression.BinaryOperator BinaryOperator.Add) -> true
  | _ -> false

let is_block = function
  | Block _ -> true
  | _ -> false

let get_ident_use = function
  | Primary (Primary.Name n) -> n
  | Expression (Expression.Primary (Primary.Name n)) -> n
  | _ -> ""

let is_explicitctorinvok = function
  | ThisInvocation
  | SuperInvocation
  | PrimaryInvocation
  | NameInvocation _
    -> true
  | _ -> false

let is_blockstatement = function
  | LocalVariableDeclaration(true, _)
  | Class _
  | Block _
  | Statement _ -> true
  | _ -> false

let is_elementvalue = function
  | EVconditional
  | EVannotation
  | EVarrayInit -> true
  | _ -> false

let is_ctor = function
  | Constructor _ -> true
  | _ -> false

let is_staticinit = function
  | StaticInitializer -> true
  | _ -> false

let is_instanceinit = function
  | InstanceInitializer -> true
  | _ -> false

let is_packagedeclaration = function
  | PackageDeclaration _ -> true
  | _ -> false

let is_compilationunit = function
  | CompilationUnit -> true
  | _ -> false

let is_type_bound = function
  | TypeBound -> true
  | _ -> false

let is_catch_clause = function
  | CatchClause _ -> true
  | _ -> false

let is_finally = function
  | Finally -> true
  | _ -> false

let is_resource_spec = function
  | ResourceSpec -> true
  | _ -> false

(*let is_resource = function
  | Resource _ -> true
  | _ -> false*)

let is_catch_parameter = function
  | CatchParameter _ -> true
  | _ -> false

let is_annot_dim = function
  | AnnotDim _ -> true
  | _ -> false

let is_aspect = function
  | Aspect _ -> true
  | _ -> false

let is_pointcut = function
  | Pointcut _ -> true
  | _ -> false

let is_declare = function
  | DeclareParents
  | DeclareMessage _
  | DeclareSoft
  | DeclarePrecedence
    -> true
  | _ -> false

let is_pointcut_expr = function
  | PointcutAnd
  | PointcutOr
  | PointcutNot
  | PointcutParen
  | PointcutWithin
      -> true
  | _ -> false

let is_classname_pattern_expr = function
  | ClassnamePatternAnd
  | ClassnamePatternOr
  | ClassnamePatternNot
  | ClassnamePatternParen
  | ClassnamePatternName _
  | ClassnamePatternNamePlus _
      -> true
  | _ -> false

let is_scope_creating lab =
  is_compilationunit lab ||
  is_class lab ||
  is_interface lab ||
  is_enum lab ||
  is_class_or_interface lab ||
  is_method lab ||
  is_methodbody lab ||
  is_for lab ||
  is_block lab ||
  is_try lab ||
  is_aspect lab


(* for fact extraction *)

let get_category lab =
  let name, _ = to_tag lab in
  name

let get_dims = function
  | Parameter(_, dims, _)
  | CatchParameter(_, dims)
      -> dims
  | _ -> failwith "Java_label.get_dims: no dimensions"

let get_name ?(strip=false) lab =
  let n =
    match lab with
    | LocalVariableDeclaration(_, vdids) when strip -> vdids_to_name vdids
    | FieldDeclaration vdids             when strip -> vdids_to_name vdids


    | Type ty -> Type.get_name ty
    | Primary prim -> Primary.get_name prim
    | Expression expr -> Expression.get_name expr
    | Statement stmt -> Statement.get_name stmt
    | Annotation anno -> Annotation.get_name anno

    | NameInvocation name
    | ElementValuePair name
    | Constructor(name, _)
    | ConstructorBody(name, _)
    | VariableDeclarator(name, _)
    | TypeArguments(_, name)
    | NamedArguments name
    | Parameters name
    | Parameter(name, _, _)
    | TypeParameter name
    | TypeParameters name
    | Method(name, _)
    | Qualifier name
    | Throws name
    | MethodBody(name, _)
    | Class name
    | Enum name
    | EnumConstant name
    | Record name
    | ClassBody name
    | EnumBody name
    | Interface name
    | AnnotationType name
    | AnnotationTypeBody name
    | InterfaceBody name
    | PackageDeclaration name
    | ElementDeclaration name
    | IDsingle name
    | IDtypeOnDemand name
    | IDstaticOnDemand name
    | FieldDeclarations name
    | InferredFormalParameter name
    (*| Resource(name, _)*)
    | CatchParameter(name, _)
      -> name

    | LocalVariableDeclaration(_, vdids) -> vdids_to_string vdids
    | FieldDeclaration vdids -> vdids_to_string vdids

    | IDsingleStatic(name1, name2) -> String.concat "." [name1; name2]

    | HugeArray(_, c) ->
      let h = Xhash.digest_hex_of_string Xhash.MD5 c in
      "HUGE_ARRAY_"^h

    | HugeExpr(_, c) ->
      let h = Xhash.digest_hex_of_string Xhash.MD5 c in
      "HUGE_EXPR_"^h

    | ClassnamePatternName name
    | ClassnamePatternNamePlus name
        -> name

    | Modifiers k
    | Specifier k -> kind_to_name k

    | Module name
    | ModuleName name
    | ModuleBody name
    | Requires name
    | Exports name
    | Opens name
    | Uses name
    | Provides name -> name
    | TypeName name -> name

    | _ -> begin
        (*WARN_MSG "name not found: %s" (to_string lab);*)
        raise Not_found
    end
  in
  if n = "" then begin
    (*Printf.printf "!!! get_name: lab=%s" (to_string lab);*)
    raise Not_found
  end
  else
    n


let get_value = function
  | Primary (Primary.Literal lit)
  | Expression (Expression.Primary (Primary.Literal lit)) ->
      Literal.to_value lit
  | Primary (Primary.ArrayCreationDims dims)
  | Expression (Expression.Primary (Primary.ArrayCreationDims dims)) -> Type.dims_to_string dims
  | _ -> raise Not_found

let has_value = function
  | Primary (Primary.Literal _|Primary.ArrayCreationDims _)
  | Expression (Expression.Primary (Primary.Literal _|Primary.ArrayCreationDims _)) -> true
  | _ -> false

let has_non_trivial_value lab =
  try
    let v = get_value lab in
    v <> "0" && v <> "1" && v <> "-1" && v <> "" && v <> "true" && v <> "false" && v <> "null"
  with
    Not_found -> false

let has_non_trivial_tid lab =
  try
    match lab with
    | Statement stmt when (hash_of_tid (Statement.get_tid stmt) <> "") -> true
    | _ -> false
  with
    Not_found -> false

let get_signature = function
  | Method(_, s) | Constructor(_, s) -> s
  | _ -> raise Not_found

let getlab nd = (Obj.obj nd#data#_label : t)

let get_dimensions = function
  | Type t -> Type.get_dimensions t
  | _ -> 0

let cannot_be_keyroot nd =
  match getlab nd with
  | Class _
  | ClassBody _ -> true
  | _ -> false


let is_phantom = function
  | Annotations
(*
  | TypeParameters _
  | TypeArguments _
  | NamedArguments _
  | Arguments
  | Parameters _
*)
  | ForInit _
  | ForCond _
  | ForUpdate _
  | Modifiers _
  | ImportDeclarations
  | TypeDeclarations
  | Specifier _
    -> true
  | _ -> false

let is_special _ = false

let is_error = function
  | Error _ -> true
  | _ -> false


open Astml.Attr

let find_name x = Scanf.unescaped (find_name x)
let find_code x =
  let s = (find_attr x "code") in
  try
    Scanf.unescaped s
  with
    e -> print_string s; raise e

let find_kind a =
  try
    let n = find_name a in
    match find_attr a "kind" with
    | "class" -> Kclass n
    | "interface" -> Kinterface n
    | "enum" -> Kenum n
    | "record" -> Krecord n
    | "annotation" -> Kannotation n
    | "field" -> Kfield n
    | "constructor" -> Kconstructor n
    | "method" -> Kmethod n
    | "parameter" -> Kparameter n
    | "local" -> Klocal n
    | "aspect" -> Kaspect n
    | "pointcut" -> Kpointcut n
    | _ -> Kany
  with
    _ -> Kany

let of_elem_data =

  let mkty a ty =
    try
      let dim = int_of_string (_find_attr a "dimensions") in
      Type (Type.Array(ty, dim))
    with
      _ -> Type ty

  in
  let mks s = Statement s in
  let mke a e =
    try
      let tid = _find_stmttid a in
      mks (Statement.Expression(e, tid))
    with
      Not_found -> Expression e
  in
  let mkp a p =
    try
      let tid = _find_stmttid a in
      mks (Statement.Expression(Expression.Primary p, tid))
    with
      Not_found -> Primary p
  in
  let mkps p = mks (Statement.Expression(Expression.Primary p, null_tid)) in
  let mklit a lit = mkp a (Primary.Literal lit) in
  let mkaop a aop = mke a (Expression.AssignmentOperator(aop, null_tid)) in
  let mkaops aop = mks (Statement.Expression(Expression.AssignmentOperator(aop, null_tid), null_tid)) in
  let mkuop a uop = mke a (Expression.UnaryOperator uop) in
  let mkuops uop = mks (Statement.Expression(Expression.UnaryOperator uop, null_tid)) in
  let mkbop a bop = mke a (Expression.BinaryOperator bop) in
  let mkmod m = Modifier m in


  let tag_list = [

    "ByteType",      (fun a -> mkty a Type.Byte);
    "ShortType",     (fun a -> mkty a Type.Short);
    "IntType",       (fun a -> mkty a Type.Int);
    "LongType",      (fun a -> mkty a Type.Long);
    "CharType",      (fun a -> mkty a Type.Char);
    "FloatType",     (fun a -> mkty a Type.Float);
    "DoubleType",    (fun a -> mkty a Type.Double);
    "BooleanType",   (fun a -> mkty a Type.Boolean);
    "ReferenceType", (fun a -> mkty a (Type.ClassOrInterface (find_name a)));
    "ClassType",     (fun a -> mkty a (Type.Class(find_name a)));
    "InterfaceType", (fun a -> mkty a (Type.Interface(find_name a)));
    "Void",          (fun a -> mkty a Type.Void);

    "IntegerLiteral",       (fun a -> mklit a (Literal.Integer(find_value a)));
    "FloatingPointLiteral", (fun a -> mklit a (Literal.FloatingPoint(find_value a)));
    "True",                 (fun a -> mklit a Literal.True);
    "False",                (fun a -> mklit a Literal.False);
    "CharacterLiteral",     (fun a -> mklit a (Literal.Character(Scanf.unescaped(find_value a))));
    "StringLiteral",        (fun a -> mklit a (Literal.String(Scanf.unescaped(find_value a))));
    "TextBlockLiteral",     (fun a -> mklit a (Literal.TextBlock(Scanf.unescaped(find_value a))));
    "NullLiteral",          (fun a -> mklit a Literal.Null);

    "Assign",        (fun a -> mkaop a AssignmentOperator.Eq);
    "MultAssign",    (fun a -> mkaop a AssignmentOperator.MulEq);
    "DivAssign",     (fun a -> mkaop a AssignmentOperator.DivEq);
    "ModAssign",     (fun a -> mkaop a AssignmentOperator.ModEq);
    "AddAssign",     (fun a -> mkaop a AssignmentOperator.AddEq);
    "SubtAssign",    (fun a -> mkaop a AssignmentOperator.SubEq);
    "ShiftLAssign",  (fun a -> mkaop a AssignmentOperator.ShiftLEq);
    "ShiftRAssign",  (fun a -> mkaop a AssignmentOperator.ShiftREq);
    "ShiftRUAssign", (fun a -> mkaop a AssignmentOperator.ShiftRUEq);
    "AndAssign",     (fun a -> mkaop a AssignmentOperator.AndEq);
    "XorAssign",     (fun a -> mkaop a AssignmentOperator.XorEq);
    "OrAssign",      (fun a -> mkaop a AssignmentOperator.OrEq);

    "PostIncrement", (fun a -> mkuop a UnaryOperator.PostIncrement);
    "PostDecrement", (fun a -> mkuop a UnaryOperator.PostDecrement);
    "PreIncrement",  (fun a -> mkuop a UnaryOperator.PreIncrement);
    "PreDecrement",  (fun a -> mkuop a UnaryOperator.PreDecrement);
    "Plus",          (fun a -> mkuop a UnaryOperator.Positive);
    "Minus",         (fun a -> mkuop a UnaryOperator.Negative);
    "Complement",    (fun a -> mkuop a UnaryOperator.Complement);
    "Negation",      (fun a -> mkuop a UnaryOperator.Not);

    "Mult",    (fun a -> mkbop a BinaryOperator.Mul);
    "Div",     (fun a -> mkbop a BinaryOperator.Div);
    "Mod",     (fun a -> mkbop a BinaryOperator.Mod);
    "Add",     (fun a -> mkbop a BinaryOperator.Add);
    "Subt",    (fun a -> mkbop a BinaryOperator.Sub);
    "ShiftL",  (fun a -> mkbop a BinaryOperator.ShiftL);
    "ShiftR",  (fun a -> mkbop a BinaryOperator.ShiftR);
    "ShiftRU", (fun a -> mkbop a BinaryOperator.ShiftRU);
    "Eq",      (fun a -> mkbop a BinaryOperator.Eq);
    "NotEq",   (fun a -> mkbop a BinaryOperator.Neq);
    "Lt",      (fun a -> mkbop a BinaryOperator.Lt);
    "Gt",      (fun a -> mkbop a BinaryOperator.Gt);
    "Le",      (fun a -> mkbop a BinaryOperator.Le);
    "Ge",      (fun a -> mkbop a BinaryOperator.Ge);
    "BitAnd",  (fun a -> mkbop a BinaryOperator.BitAnd);
    "BitOr",   (fun a -> mkbop a BinaryOperator.BitOr);
    "BitXor",  (fun a -> mkbop a BinaryOperator.BitXor);
    "And",     (fun a -> mkbop a BinaryOperator.And);
    "Or",      (fun a -> mkbop a BinaryOperator.Or);

    "Public",       (fun _ -> mkmod Modifier.Public);
    "Protected",    (fun _ -> mkmod Modifier.Protected);
    "Private",      (fun _ -> mkmod Modifier.Private);
    "Static",       (fun _ -> mkmod Modifier.Static);
    "Abstract",     (fun _ -> mkmod Modifier.Abstract);
    "Final",        (fun _ -> mkmod Modifier.Final);
    "Native",       (fun _ -> mkmod Modifier.Native);
    "Synchronized", (fun _ -> mkmod Modifier.Synchronized);
    "Transient",    (fun _ -> mkmod Modifier.Transient);
    "Volatile",     (fun _ -> mkmod Modifier.Volatile);
    "Strictfp",     (fun _ -> mkmod Modifier.Strictfp);
(*    "Annotation",   (fun _ -> mkmod Modifier.Annotation);*)
    "Default",      (fun _ -> mkmod Modifier.Default);
    "Transitive",   (fun _ -> mkmod Modifier.Transitive);
    "Sealed",       (fun _ -> mkmod Modifier.Sealed);
    "NonSealed",    (fun _ -> mkmod Modifier.NonSealed);
    "ErrorModifier", (fun a -> mkmod (Modifier.Error(find_attr a "contents")));

    "Name",                          (fun a -> mkp a Primary.(Name(find_name a)));
    "This",                          (fun a -> mkp a Primary.This);
    "ClassLiteral",                  (fun a -> mkp a Primary.ClassLiteral);
    "ClassLiteralVoid",              (fun a -> mkp a Primary.ClassLiteralVoid);
    "QualifiedThis",                 (fun a -> mkp a (Primary.QualifiedThis(find_name a)));
    "StandardInstanceCreation",      (fun a -> mkp a (Primary.InstanceCreation(find_name a)));
    "QualifiedInstanceCreation",     (fun a -> mkp a (Primary.QualifiedInstanceCreation(find_name a)));
    "NameQualifiedInstanceCreation", (fun a -> mkp a (Primary.NameQualifiedInstanceCreation(find_name a, find_ident a)));
    "FieldAccess",                   (fun a -> mkp a (Primary.FieldAccess(find_name a)));
    "SuperFieldAccess",              (fun a -> mkp a (Primary.SuperFieldAccess(find_name a)));
    "ClassSuperFieldAccess",         (fun a -> mkp a (Primary.ClassSuperFieldAccess(find_name a)));
    "PrimaryMethodInvocation",       (fun a -> mkp a (Primary.PrimaryMethodInvocation(find_name a)));
    "SimpleMethodInvocation",        (fun a -> mkp a (Primary.SimpleMethodInvocation(find_name a)));
    "SuperMethodInvocation",         (fun a -> mkp a (Primary.SuperMethodInvocation(find_name a)));
    "ClassSuperMethodInvocation",    (fun a -> mkp a (Primary.ClassSuperMethodInvocation(find_name a)));
    "TypeMethodInvocation",          (fun a -> mkp a (Primary.TypeMethodInvocation(find_name a, find_ident a)));
    "ArrayAccess",                   (fun a -> mkp a Primary.ArrayAccess);
    "ArrayCreationInit",             (fun a -> mkp a Primary.ArrayCreationInit);
    "ArrayCreationDims",             (fun a -> mkp a (Primary.ArrayCreationDims(find_dims a)));
    "ParenthesizedExpression",       (fun a -> mkp a (Primary.Paren(find_tid a)));
    "NameMethodReference",           (fun a -> mkp a (Primary.NameMethodReference(find_name a, find_ident a)));
    "PrimaryMethodReference",        (fun a -> mkp a (Primary.PrimaryMethodReference(find_ident a)));
    "SuperMethodReference",          (fun a -> mkp a (Primary.SuperMethodReference(find_ident a)));
    "TypeSuperMethodReference",      (fun a -> mkp a (Primary.TypeSuperMethodReference(find_name a, find_ident a)));
    "TypeNewMethodReference",        (fun a -> mkp a (Primary.TypeNewMethodReference(find_name a)));

    "Conditional", (fun a -> mke a Expression.Cond);
    "Instanceof",  (fun a -> mke a Expression.Instanceof);
    "Cast",        (fun a -> mke a Expression.Cast);
    "Lambda",      (fun a -> mke a Expression.Lambda);
    "Switch",      (fun a -> mke a Expression.Switch);
    "NaryAdd",     (fun a -> mke a Expression.NaryAdd);

    "NormalAnnotation",        (fun a -> Annotation (Annotation.Normal(find_name a)));
    "MarkerAnnotation",        (fun a -> Annotation (Annotation.Marker(find_name a)));
    "SingleElementAnnotation", (fun a -> Annotation (Annotation.SingleElement(find_name a)));

    "EmptyStatement",           (fun _ -> mks Statement.Empty);
    "AssertStatement",          (fun _ -> mks Statement.Assert);
    "IfStatement",              (fun a -> mks (Statement.If(find_tid a)));
    (*"FlattenedIfStatement",     (fun a -> mks (Statement.FlattenedIf(find_tid a)));*)
    "ElseIfStatement",          (fun a -> mks (Statement.ElseIf(find_tid a)));
    "ElseStatement",            (fun _ -> mks Statement.Else);
    "BasicForStatement",        (fun _ -> mks Statement.For);
    "EnhancedForStatement",     (fun _ -> mks Statement.ForEnhanced);
    "WhileStatement",           (fun _ -> mks Statement.While);
    "DoStatement",              (fun _ -> mks Statement.Do);
    "TryStatement",             (fun _ -> mks Statement.Try);
    "YieldStatement",           (fun _ -> mks Statement.Yield);
    "SwitchStatement",          (fun _ -> mks Statement.Switch);
    "SynchronizedStatement",    (fun _ -> mks Statement.Synchronized);
    "ReturnStatement",          (fun _ -> mks Statement.Return);
    "ThrowStatement",           (fun _ -> mks Statement.Throw);
    "BreakStatement",           (fun a -> mks (Statement.Break(find_attr_opt a label_attr_name)));
    "ContinueStatement",        (fun a -> mks (Statement.Continue(find_attr_opt a label_attr_name)));
    "LabeledStatement",         (fun a -> mks (Statement.Labeled(find_attr a label_attr_name)));

    "StandardInstanceCreationStatement",      (fun a -> mkps (Primary.InstanceCreation(find_name a)));
    "QualifiedInstanceCreationStatement",     (fun a -> mkps (Primary.QualifiedInstanceCreation(find_name a)));
    "NameQualifiedInstanceCreationStatement", (fun a -> mkps (Primary.NameQualifiedInstanceCreation(find_name a, find_ident a)));

    "PrimaryMethodInvocationStatement",    (fun a -> mkps (Primary.PrimaryMethodInvocation(find_name a)));
    "SimpleMethodInvocationStatement",     (fun a -> mkps (Primary.SimpleMethodInvocation(find_name a)));
    "SuperMethodInvocationStatement",      (fun a -> mkps (Primary.SuperMethodInvocation(find_name a)));
    "ClassSuperMethodInvocationStatement", (fun a -> mkps (Primary.ClassSuperMethodInvocation(find_name a)));
    "TypeMethodInvocationStatement",       (fun a -> mkps (Primary.TypeMethodInvocation(find_name a, find_ident a)));

    "PreIncrementStatement",     (fun _ -> mkuops UnaryOperator.PreIncrement);
    "PreDecrementStatement",     (fun _ -> mkuops UnaryOperator.PreDecrement);
    "PostIncrementStatement",    (fun _ -> mkuops UnaryOperator.PostIncrement);
    "PostDecrementStatement",    (fun _ -> mkuops UnaryOperator.PostDecrement);

    "AssignStatement",           (fun _ -> mkaops AssignmentOperator.Eq);
    "MultAssignStatement",       (fun _ -> mkaops AssignmentOperator.MulEq);
    "DivAssignStatement",        (fun _ -> mkaops AssignmentOperator.DivEq);
    "ModAssignStatement",        (fun _ -> mkaops AssignmentOperator.ModEq);
    "AddAssignStatement",        (fun _ -> mkaops AssignmentOperator.AddEq);
    "SubtAssignStatement",       (fun _ -> mkaops AssignmentOperator.SubEq);
    "ShiftLAssignStatement",     (fun _ -> mkaops AssignmentOperator.ShiftLEq);
    "ShiftRAssignStatement",     (fun _ -> mkaops AssignmentOperator.ShiftREq);
    "ShiftRUAssignStatement",    (fun _ -> mkaops AssignmentOperator.ShiftRUEq);
    "AndAssignStatement",        (fun _ -> mkaops AssignmentOperator.AndEq);
    "OrAssignStatement",         (fun _ -> mkaops AssignmentOperator.OrEq);
    "XorAssignStatement",        (fun _ -> mkaops AssignmentOperator.XorEq);

    "TypeBound",                 (fun _ -> TypeBound);
    "ThisInvocation",            (fun _ -> ThisInvocation);
    "SuperInvocation",           (fun _ -> SuperInvocation);
    "PrimaryInvocation",         (fun _ -> PrimaryInvocation);
    "NameInvocation",            (fun a -> NameInvocation(find_name a));
    "ConstantLabel",             (fun a -> SLconstant(find_tid a));
    "DefaultLabel",              (fun _ -> SLdefault);
    "ConstantRuleLabel",         (fun _ -> SRLconstant);
    "DefaultRuleLabel",          (fun _ -> SRLdefault);
    "ConditionalElementValue",   (fun _ -> EVconditional);
    "AnnotationElementValue",    (fun _ -> EVannotation);
    "ArrayInitElementValue",     (fun _ -> EVarrayInit);
    "ElementValuePair",          (fun a -> ElementValuePair(find_name a));
    "ConstructorDeclaration",    (fun a -> Constructor(find_name a, find_sig a));
    "ConstructorBody",           (fun a -> ConstructorBody(find_name a, find_sig a));
    "StaticInitializer",         (fun _ -> StaticInitializer);
    "InstanceInitializer",       (fun _ -> InstanceInitializer);
    "Block",                     (fun a -> Block(find_tid a));
    "LocalVariableDeclaration",  (fun a -> LocalVariableDeclaration(false, find_vdids ~attr_name:"name" a));
    "LocalVariableDeclarationStatement",  (fun a -> LocalVariableDeclaration(true, find_vdids ~attr_name:"name" a));
    "VariableDeclarator",        (fun a -> VariableDeclarator(find_name a, find_dims a));
    "CatchClause",               (fun a -> CatchClause(find_tid a));
    "Finally",                   (fun _ -> Finally);
    "ForInit",                   (fun a -> ForInit(find_tid a));
    "ForCond",                   (fun a -> ForCond(find_tid a));
    "ForUpdate",                 (fun a -> ForUpdate(find_tid a));
    "SwitchBlock",               (fun _ -> SwitchBlock);
    "SwitchBlockStatementGroup", (fun _ -> SwitchBlockStatementGroup);
    "SwitchRule",                (fun _ -> SwitchRule);
    "DimExpression",             (fun _ -> DimExpr);
    "Arguments",                 (fun _ -> Arguments);
    "Annotations",               (fun _ -> Annotations);
    "Arguments",                 (fun a -> NamedArguments(find_name a));
    "TypeArguments",             (fun a -> TypeArguments(find_nth a, find_name a));
    "Wildcard",                  (fun _ -> Wildcard);
    "WildcardBoundsExtends",     (fun _ -> WildcardBoundsExtends);
    "WildcardBoundsSuper",       (fun _ -> WildcardBoundsSuper);
    "Parameters",                (fun a -> Parameters(find_name a));
    "Parameter",                 (fun a -> Parameter(find_name a, find_dims a, find_bool a "va"));
    "ReceiverParameter",         (fun a -> ReceiverParameter(try Some (find_name a) with _ -> None));
    "TypeParameter",             (fun a -> TypeParameter(find_name a));
    "TypeParameters",            (fun a -> TypeParameters(find_name a));
    "ArrayInitializer",          (fun _ -> ArrayInitializer);
    "Modifiers",                 (fun a -> Modifiers(find_kind a));
    "FieldDeclaration",          (fun a -> FieldDeclaration(find_vdids ~attr_name:"name" a));
    "MethodDeclaration",         (fun a -> Method(find_name a, find_sig a));
    "Super",                     (fun _ -> Super);
    "Qualifier",                 (fun a -> Qualifier(find_name a));
    "Throws",                    (fun a -> Throws(find_name a));
    "MethodBody",                (fun a -> MethodBody(find_name a, find_sig a));

    "Specifier",                 (fun _ -> Specifier Kany);
    "ClassSpecifier",            (fun a -> Specifier (Kclass(find_name a)));
    "InterfaceSpecifier",        (fun a -> Specifier (Kinterface(find_name a)));
    "EnumSpecifier",             (fun a -> Specifier (Kenum(find_name a)));
    "RecordSpecifier",           (fun a -> Specifier (Krecord(find_name a)));
    "AnnotationSpecifier",       (fun a -> Specifier (Kannotation(find_name a)));

    "ClassDeclaration",          (fun a -> Class(find_name a));
    "EnumDeclaration",           (fun a -> Enum(find_name a));
    "EnumConstant",              (fun a -> EnumConstant(find_name a));
    "RecordDeclaration",         (fun a -> Record(find_name a));
    "Extends",                   (fun _ -> Extends);
    "Implements",                (fun _ -> Implements);
    "Permits",                   (fun _ -> Permits);
    "ClassBody",                 (fun a -> ClassBody(find_name a));
    "EnumBody",                  (fun a -> EnumBody(find_name a));
    "InterfaceDeclaration",      (fun a -> Interface(find_name a));
    "AnnotationTypeDeclaration", (fun a -> AnnotationType(find_name a));
    "AnnotationTypeBody",        (fun a -> AnnotationTypeBody(find_name a));
    "ExtendsInterfaces",         (fun _ -> ExtendsInterfaces);
    "InterfaceBody",             (fun a -> InterfaceBody(find_name a));

    "PackageDeclaration",              (fun a -> PackageDeclaration(find_name a));
    "SingleTypeImportDeclaration",     (fun a -> IDsingle(find_name a));
    "TypeImportOnDemandDeclaration",   (fun a -> IDtypeOnDemand(find_name a));
    "SingleStaticImportDeclaration",   (fun a -> IDsingleStatic(find_name a, find_ident a));
    "StaticImportOnDemandDeclaration", (fun a -> IDstaticOnDemand(find_name a));
    "ImportDeclarations",                       (fun _ -> ImportDeclarations);
    "TypeDeclarations",                         (fun _ -> TypeDeclarations);
    "AnnotationTypeElementDeclaration",         (fun a -> ElementDeclaration(find_name a));
    "FieldDeclarations",                        (fun a -> FieldDeclarations(find_name a));
    "InferredFormalParameters",                 (fun _ -> InferredFormalParameters);
    "InferredFormalParameter",                  (fun a -> InferredFormalParameter(find_name a));
    "CompilationUnit",                          (fun _ -> CompilationUnit);
    "ResourceSpec",                             (fun _ -> ResourceSpec);
    (*"Resource",                                 (fun a -> Resource(find_name a, find_dims a));*)
    "CatchParameter",                           (fun a -> CatchParameter(find_name a, find_dims a));
    "AnnotDim",                                 (fun a -> AnnotDim(find_bool a "ellipsis"));

    "AmbiguousName",                            (fun a -> mkp a Primary.(AmbiguousName(find_name a)));
    "AmbiguousMethodInvocation",                (fun a -> mkp a Primary.(AmbiguousMethodInvocation(find_name a)));

    "Error",                                    (fun a -> Error(find_attr a "contents"));
    "HugeArray", (fun a -> HugeArray (int_of_string (find_attr a "size"), (find_code a)));
    "HugeExpr", (fun a -> HugeExpr (int_of_string (find_attr a "size"), (find_code a)));

    "EmptyDeclaration", (fun _ -> EmptyDeclaration);

    "ForHead", (fun a -> ForHead(find_tid a));

    "Aspect",                   (fun a -> Aspect(find_name a));
    "Pointcut",                 (fun a -> Pointcut(find_name a));
    "DeclareParents",           (fun _ -> DeclareParents);
    "DeclareMessage",           (fun a -> DeclareMessage(find_attr a "level"));
    "DeclareSoft",              (fun _ -> DeclareSoft);
    "DeclarePrecedence",        (fun _ -> DeclarePrecedence);
    "PointcutAnd",              (fun _ -> PointcutAnd);
    "PointcutOr",               (fun _ -> PointcutOr);
    "PointcutNot",              (fun _ -> PointcutNot);
    "PointcutParen",            (fun _ -> PointcutParen);
    "PointcutWithin",           (fun _ -> PointcutWithin);
    "ClassnamePatternAnd",      (fun _ -> ClassnamePatternAnd);
    "ClassnamePatternOr",       (fun _ -> ClassnamePatternOr);
    "ClassnamePatternNot",      (fun _ -> ClassnamePatternNot);
    "ClassnamePatternParen",    (fun _ -> ClassnamePatternParen);
    "ClassnamePatternName",     (fun a -> ClassnamePatternName(find_name a));
    "ClassnamePatternNamePlus", (fun a -> ClassnamePatternNamePlus(find_name a));

    "ModuleDeclaration", (fun a -> Module(find_name a));
    "Open",              (fun _ -> Open);
    "ModuleName",        (fun a -> ModuleName(find_name a));
    "ModuleBody",        (fun a -> ModuleBody(find_name a));
    "RequiresDirective", (fun a -> Requires(find_name a));
    "ExportsDirective",  (fun a -> Exports(find_name a));
    "OpensDirective",    (fun a -> Opens(find_name a));
    "UsesDirective",     (fun a -> Uses(find_name a));
    "ProvidesDirective", (fun a -> Provides(find_name a));

    "TypeName", (fun a -> TypeName(find_name a));
   ]
  in
  let tbl = Hashtbl.create (List.length tag_list) in
  let _ =
    List.iter (fun (tname, lab) -> Hashtbl.add tbl tname lab) tag_list
  in
  let of_elem name attrs (_ : string) =
    try
      (Hashtbl.find tbl name) attrs
    with
    | Not_found -> failwith ("Java_label.of_elem_data: tag not found: "^name)
    | e -> failwith ("Java_label.of_elem_data: "^(Printexc.to_string e))
  in
  of_elem
