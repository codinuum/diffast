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
module Binding = Diffast_misc.Binding
module Astloc = Langs_common.Astloc

module BID = Binding.ID

open Common

module C = Context
module L = Label

let encode_ident i = sprintf "%d%s" (String.length i) i

let decode_pat = Str.regexp "[0-9]+"

let decode_ident = Str.replace_first decode_pat ""

type pp_if_cond = PP_IF of string * Obj.t list | PP_IFDEF of ident | PP_IFNDEF of ident
type pp_if_cond_sub = PP_NONE | PP_CLOSING | PP_STR | PP_EXPR | PP_INIT

type pp_compl = {
    mutable c_brace : int;
    mutable c_paren : int;
}

type pp_if_section_info = {
    mutable i_line                  : int;
    mutable i_context               : C.t;
    mutable i_sub_context           : C.sub;
    mutable i_label                 : L.t;
    mutable i_brace_level           : int;
    mutable i_paren_level           : int;
    mutable i_templ_param_arg_level : int;
    mutable i_cond                  : pp_if_cond;
    mutable i_cond_sub              : pp_if_cond_sub;
    mutable i_pp_elif               : int list;
    mutable i_pp_else               : int option;
    mutable i_lbraces               : int;
    mutable i_rbraces               : int;
    mutable i_odd                   : bool;
    mutable i_odd_canceled          : bool;
    mutable i_broken                : bool;
    mutable i_paren_closing         : bool;
    mutable i_brace_closing         : int;
    mutable i_brace_opening         : bool;
    mutable i_func_head             : bool;
    mutable i_func_body             : bool;
    mutable i_semicolon             : bool;
    mutable i_comma                 : bool;
    mutable i_cond_expr             : bool;
    mutable i_cond_expr_            : bool;
    mutable i_asm                   : bool;
    mutable i_begin_asm             : bool;
    mutable i_pp_if_compl           : pp_compl;
    mutable i_lack_of_dtor          : bool;
    mutable i_class_brace_opening   : bool;
    mutable i_follows_comma         : bool;
    mutable i_brace_paren_closing   : bool;
    mutable i_broken_func_head      : bool;
    mutable i_templ_closing         : bool;
  }

let pp_if_cond_to_string = function
  | PP_IF(s, _) -> sprintf "#if(%s)" s
  | PP_IFDEF s  -> sprintf "#ifdef(%s)" s
  | PP_IFNDEF s -> sprintf "#ifndef(%s)" s

let pp_if_cond_sub_to_string = function
  | PP_NONE -> ""
  | PP_CLOSING -> "closing"
  | PP_STR -> "str"
  | PP_EXPR -> "expr"
  | PP_INIT -> "init"

let pp_compl_to_string {
  c_brace=blv;
  c_paren=plv;
} =
  if blv = 0 && plv = 0 then
    ""
  else
    sprintf "{B:%d;P:%d}" blv plv

let pp_if_section_info_to_string {
  i_line=ln;
  i_context=c;
  i_sub_context=sc;
  i_label=lab;
  i_brace_level=blv;
  i_paren_level=plv;
  i_templ_param_arg_level=tlv;
  i_cond=cond;
  i_cond_sub=cond_sub;
  i_pp_elif=ei;
  i_pp_else=es;
  i_lbraces=lb;
  i_rbraces=rb;
  i_odd=o;
  i_odd_canceled=oc;
  i_broken=b;
  i_paren_closing=pcl;
  i_brace_closing=bcl;
  i_brace_opening=bo;
  i_func_head=fh;
  i_func_body=fb;
  i_semicolon=s;
  i_comma=cm;
  i_cond_expr=ce;
  i_cond_expr_=ce_;
  i_asm=a;
  i_begin_asm=ba;
  i_pp_if_compl=cmpl;
  i_lack_of_dtor=lod;
  i_class_brace_opening=cbo;
  i_follows_comma=fcm;
  i_brace_paren_closing=bpc;
  i_broken_func_head=bfh;
  i_templ_closing=tcl;
} =
  let l =
    ["odd",       o;
     "odd_canceled", oc;
     "broken",    b;
     ")",         pcl;
     sprintf "}%d" bcl, bcl > 0;
     "{",         bo;
     "func_head", fh;
     "func_body", fb;
     ";",         s;
     ",",         cm;
     "?",         ce;
     "?_",        ce_;
     "asm",       a;
     "begin_asm", ba;
     "lack_of_dtor", lod;
     "C{",        cbo;
     ",_",        fcm;
     "})",        bpc;
     "broken_func_head", bfh;
     ">",         tcl;
   ] in
  let flags = String.concat "" (List.map (fun (k, _) -> "["^k^"]") (List.filter (fun (_, v) -> v) l)) in
  sprintf "{%s%s@%d;%s,%s;%sLv{:%d;Lv(:%d;Lv<:%d;\"{\":%d;\"}\":%d;%s%s%s%s}"
    (pp_if_cond_to_string cond) (pp_if_cond_sub_to_string cond_sub) ln
    (C.to_string c) (C.sub_to_string sc)
    (match lab with DUMMY -> "" | _ -> (L.to_string lab)^";")
    blv plv tlv lb rb
    (match ei with
    | _::_ -> sprintf "#elif:[%s];" (String.concat ";" (List.map string_of_int ei))
    | [] -> "")
    (match es with Some i -> sprintf "#else:%d;" i | None -> "")
    (pp_compl_to_string cmpl)
    flags

let make_pp_if_section_info ?(cond_sub=PP_NONE) ?(pp_elif=[]) ?(pp_else=None) ln c sc blv plv tlv cond = {
  i_line=ln;
  i_context=c;
  i_sub_context=sc;
  i_label=L.DUMMY;
  i_brace_level=blv;
  i_paren_level=plv;
  i_templ_param_arg_level=tlv;
  i_cond=cond;
  i_cond_sub=cond_sub;
  i_pp_elif=pp_elif;
  i_pp_else=pp_else;
  i_lbraces=0;
  i_rbraces=0;
  i_odd=false;
  i_odd_canceled=false;
  i_broken=false;
  i_paren_closing=false;
  i_brace_closing=0;
  i_brace_opening=false;
  i_func_head=false;
  i_func_body=false;
  i_semicolon=false;
  i_comma=false;
  i_cond_expr=false;
  i_cond_expr_=false;
  i_asm=false;
  i_begin_asm=false;
  i_pp_if_compl={c_brace=0;c_paren=0};
  i_lack_of_dtor=false;
  i_class_brace_opening=false;
  i_follows_comma=false;
  i_brace_paren_closing=false;
  i_broken_func_head=false;
  i_templ_closing=false;
}

let dummy_info = make_pp_if_section_info 0 C.TOP C.INI 0 0 0 (PP_IF("", []))


module ElaboratedType = struct
  type t =
    | Class of name
    | Struct of name
    | Union of name
    | Enum of name
    | EnumClass of name
    | Macro of name

  let to_string = function
    | Class n -> "class "^n
    | Struct n -> "struct "^n
    | Union n -> "union "^n
    | Enum n -> "enum "^n
    | EnumClass n -> "enum_class"^n
    | Macro n -> n

  let get_name = function
    | Class n -> n
    | Struct n -> n
    | Union n -> n
    | Enum n -> n
    | EnumClass n -> n
    | Macro n -> n

  let encode = function
    | Class n | Struct n -> "Ts"^n
    | Union n -> "Tu"^n
    | Enum n -> "Te"^n
    | EnumClass n -> "Tes"^n
    | Macro n -> n

  let is_type_type = function
    | Class _
    | Struct _
    | Union _
    | EnumClass _ -> true
    | _ -> false

end (* module Pinfo.ElaboratedType *)

module PlaceholderType = struct
  type t =
    | Auto
    | Decltype

  let to_string = function
    | Auto     -> "auto"
    | Decltype -> "decltype(auto)"

  let encode = function
    | Auto     -> "Da"
    | Decltype -> "Dc"

end (* module Pinfo.PlaceholderType *)

module CvQualifier = struct
  type t =
    | Const
    | Volatile
    | Restrict
    | Cdecl
    | Stdcall

  let to_string = function
    | Const    -> "const"
    | Volatile -> "volatile"
    | Restrict -> "restrict"
    | Cdecl    -> "__cdecl"
    | Stdcall  -> "__stdcall"

  let encode = function
    | Const    -> "K"
    | Volatile -> "V"
    | Restrict -> "r"
    | Cdecl    -> "U7__cdecl"
    | Stdcall  -> "U9__stdcall"

end (* module Pinfo.CvQualifier *)

module TypeSpec = struct
  type t =
    | Simple of name
    | Decltype of string
    | Placeholder of PlaceholderType.t
    | Char
    | Char8_t
    | Char16_t
    | Char32_t
    | Wchar_t
    | Bool
    | Short
    | Int
    | Long
    | Signed
    | Unsigned
    | Float
    | Double
    | Void
    | UnsignedInt
    | UnsignedLong
    | Elaborated of ElaboratedType.t
    | Typename of string
    | CvQualifier of CvQualifier.t

  let get_cv_qualifier = function
    | CvQualifier cvq -> cvq
    | _ -> raise Not_found

 let get_ident_opt = function
    | Simple n
    | Decltype n
    | Typename n -> Some n
    | Elaborated e -> Some (ElaboratedType.get_name e)
    | _ -> None

  let get_name = function
    | Simple n
    | Typename n -> n
    | Elaborated e -> ElaboratedType.get_name e
    | _ -> raise Not_found

  let to_string = function
    | Simple n        -> n
    | Decltype e      -> sprintf "decltype(%s)" e
    | Placeholder p   -> PlaceholderType.to_string p
    | Char            -> "char"
    | Char8_t         -> "char8_t"
    | Char16_t        -> "char16_t"
    | Char32_t        -> "char32_t"
    | Wchar_t         -> "wchar_t"
    | Bool            -> "bool"
    | Short           -> "short"
    | Int             -> "int"
    | Long            -> "long"
    | Signed          -> "signed"
    | Unsigned        -> "unsigned"
    | Float           -> "float"
    | Double          -> "double"
    | Void            -> "void"
    | UnsignedInt     -> "unsigned int"
    | UnsignedLong    -> "unsigned long"
    | Elaborated e    -> ElaboratedType.to_string e
    | Typename e      -> "typename "^e
    | CvQualifier cvq -> CvQualifier.to_string cvq

  let is_definite_type = function
    | Decltype _
    | Placeholder _
    | Char
    | Char8_t
    | Char16_t
    | Char32_t
    | Wchar_t
    | Bool
    | Short
    | Int
    | Long
    | Signed
    | Unsigned
    | Float
    | Double
    | Void
    | UnsignedInt
    | UnsignedLong
    | Elaborated _
      -> true
    | _ -> false

  let is_basic_type = function
    | Char
    | Char8_t
    | Char16_t
    | Char32_t
    | Wchar_t
    | Bool
    | Short
    | Int
    | Long
    | Signed
    | Unsigned
    | Float
    | Double
    | Void
    | UnsignedInt
    | UnsignedLong
      -> true
    | _ -> false

  let is_elaborated_type = function
    | Elaborated _ -> true
    | _ -> false

  let is_elaborated_type_type = function
    | Elaborated e -> ElaboratedType.is_type_type e
    | _ -> false

  let is_elaborated_type_enum_class = function
    | Elaborated (ElaboratedType.EnumClass _) -> true
    | _ -> false

  let is_typename = function
    | Typename _ -> true
    | _ -> false

  let encode tl =
    let signed = ref false in
    let unsigned = ref false in
    let long_count = ref 0 in
    let cv_qualifiers = ref [] in
    let filtered_tl =
      List.filter
        (function
          | Long     -> incr long_count; false
          | Signed   -> signed := true; false
          | Unsigned -> unsigned := true; false
          | CvQualifier cvq -> begin
              cv_qualifiers := (CvQualifier.encode cvq) :: !cv_qualifiers;
              false
          end
          | _ -> true
        ) tl
    in
    if !signed && !unsigned then begin
      [%warn_log "signed and unsigned coexist"];
      signed := false;
      unsigned := false;
    end;
    cv_qualifiers := List.fast_sort (fun x y -> compare y x) (!cv_qualifiers);
    let _encoded =
      String.concat ""
        (List.map
           (function
             | Simple n -> n
             | Decltype e -> e
             | Placeholder p -> PlaceholderType.encode p
             | Char when !signed -> "a"
             | Char when !unsigned -> "h"
             | Char -> "c"
             | Char8_t -> "Du"
             | Char16_t -> "Ds"
             | Char32_t -> "Di"
             | Wchar_t -> "w"
             | Bool -> "b"
             | Short when !unsigned -> "t"
             | Short -> "s"
             | Int when !unsigned -> "j"
             | Int -> "i"
             | Float -> "f"
             | Double when !long_count = 1 -> "e"
             | Double -> "d"
             | Void -> "v"
             | UnsignedInt -> "j"
             | UnsignedLong -> "m"
             | Elaborated e -> ElaboratedType.encode e
             | Typename e -> e
             | _ -> ""
           ) filtered_tl)
    in
    let _encoded =
      if _encoded = "" then
        (match !unsigned, !long_count with
        | true, 0 -> "j"
        | false, 0 -> "i"
        | true, 1 -> "m"
        | false, 1 -> "l"
        | true, 2 -> "y"
        | false, 2 -> "x"
        | true, _ -> "y"
        | false, _ -> "x")
      else
        _encoded
    in
    (String.concat "" (!cv_qualifiers))^_encoded

end (* module Pinfo.TypeSpec *)

class decl_specs = object (self)

  val mutable vec = 0

  val storage_class_static = 1
  val storage_class_thread_local = 1 lsl 1
  val storage_class_extern = 1 lsl 2
  val storage_class_mutable = 1 lsl 3
  val function_spec_virtual = 1 lsl 4
  val function_spec_explicit = 1 lsl 5
  val friend = 1 lsl 6
  val typedef = 1 lsl 7
  val constexpr = 1 lsl 8
  val consteval = 1 lsl 9
  val inline = 1 lsl 10

  val typedef_mask = 1 lxor (1 lsl 7)

  method set_storage_class_static () = vec <- vec lor storage_class_static
  method set_storage_class_thread_local () = vec <- vec lor storage_class_thread_local
  method set_storage_class_extern () = vec <- vec lor storage_class_extern
  method set_storage_class_mutable () = vec <- vec lor storage_class_mutable
  method set_function_spec_virtual () = vec <- vec lor function_spec_virtual
  method set_function_spec_explicit () = vec <- vec lor function_spec_explicit
  method set_friend () = vec <- vec lor friend
  method set_typedef () = vec <- vec lor typedef
  method set_constexpr () = vec <- vec lor constexpr
  method set_consteval () = vec <- vec lor consteval
  method set_inline () = vec <- vec lor inline

  method clear_typedef () = vec <- vec land typedef_mask

  method is_storage_class_static = vec land storage_class_static = storage_class_static
  method is_storage_class_thread_local =
    vec land storage_class_thread_local = storage_class_thread_local
  method is_storage_class_extern = vec land storage_class_extern = storage_class_extern
  method is_storage_class_mutable = vec land storage_class_mutable = storage_class_mutable
  method is_function_spec_virtual = vec land function_spec_virtual = function_spec_virtual
  method is_function_spec_explicit =
    vec land function_spec_explicit = function_spec_explicit
  method is_friend = vec land friend = friend
  method is_typedef = vec land typedef = typedef
  method is_constexpr = vec land constexpr = constexpr
  method is_consteval = vec land consteval = consteval
  method is_inline = vec land inline = inline

  method to_string =
    let l = ref [] in
    if self#is_inline then
      l := "inline" :: !l;
    if self#is_consteval then
      l := "consteval" :: !l;
    if self#is_constexpr then
      l := "constexpr" :: !l;
    if self#is_typedef then
      l := "typedef" :: !l;
    if self#is_friend then
      l := "friend" :: !l;
    if self#is_function_spec_explicit then
      l := "explicit" :: !l;
    if self#is_function_spec_virtual then
      l := "virtual" :: !l;
    if self#is_storage_class_mutable then
      l := "mutable" :: !l;
    if self#is_storage_class_extern then
      l := "extern" :: !l;
    if self#is_storage_class_thread_local then
      l := "thread_local" :: !l;
    if self#is_storage_class_static then
      l := "static" :: !l;
    String.concat " " !l

end (* class Pinfo.decl_specs *)

class qualifiers =
  let const = 1 in
  let volatile = 1 lsl 1 in
  let amp = 1 lsl 2 in
  let amp_amp = 1 lsl 3 in
  let noexcept_computed = 1 lsl 4 in
  let noexcept = 1 lsl 5 in
  let throw = 1 lsl 6 in
  let restrict = 1 lsl 7 in
  let cdecl = 1 lsl 8 in
  let stdcall = 1 lsl 9 in
object (self)
  val mutable vec = 0

  val tbl = Hashtbl.create 0

  method set_const () = vec <- vec lor const
  method set_volatile () = vec <- vec lor volatile
  method set_amp () = vec <- vec lor amp
  method set_amp_amp () = vec <- vec lor amp_amp
  method set_noexcept_computed e =
    vec <- vec lor noexcept_computed;
    Hashtbl.add tbl noexcept_computed e
  method set_noexcept () = vec <- vec lor noexcept
  method set_throw () = vec <- vec lor throw
  method set_restrict () = vec <- vec lor restrict
  method set_cdecl () = vec <- vec lor cdecl
  method set_stdcall () = vec <- vec lor stdcall

  method is_const = vec land const = const
  method is_volatile = vec land volatile = volatile
  method is_amp = vec land amp = amp
  method is_amp_amp = vec land amp_amp = amp_amp
  method is_noexcept_computed = vec land noexcept_computed = noexcept_computed
  method is_noexcept = vec land noexcept = noexcept
  method is_throw = vec land throw = throw
  method is_restrict = vec land restrict = restrict
  method is_cdecl = vec land cdecl = cdecl
  method is_stdcall = vec land stdcall = stdcall

  method to_string =
    let l = ref [] in
    if self#is_const then
      l := "const" :: !l;
    if self#is_volatile then
      l := "volatile" :: !l;
    if self#is_amp then
      l := "&" :: !l;
    if self#is_amp_amp then
      l := "&&" :: !l;
    if self#is_noexcept_computed then
      l := "noexcept()" :: !l;
    if self#is_noexcept then
      l := "noexcept" :: !l;
    if self#is_throw then
      l := "throw()" :: !l;
    if self#is_restrict then
      l := "restrict" :: !l;
    if self#is_cdecl then
      l := "__cdecl" :: !l;
    if self#is_stdcall then
      l := "__stdcall" :: !l;
    String.concat " " !l

  method encode_cv =
    let cvq = ref "" in
    if self#is_restrict then
      cvq := !cvq ^ "r";
    if self#is_volatile then
      cvq := !cvq ^ "V";
    if self#is_const then
      cvq := !cvq ^ "K";
    !cvq

  method encode_ref =
    let refq = ref "" in
    if self#is_amp then
      refq := "R";
    if self#is_amp_amp then
      refq := "O";
    !refq

  method encode_exc =
    let exc = ref "" in
    if self#is_noexcept || self#is_throw then
      exc := "Do";
    if self#is_noexcept_computed then
      exc := sprintf "DO%sE" (Hashtbl.find tbl noexcept_computed);
    !exc

  method encode_ms =
    let msq = ref "" in
    if self#is_cdecl then
      msq := "U7__cdecl";
    if self#is_stdcall then
      msq := "U9__stdcall";
    !msq

end (* class Pinfo.qualifiers *)

class virt_specs = object (self)
  val mutable vec = 0

  val final = 1
  val override = 1 lsl 1

  method set_final () = vec <- vec lor final
  method set_override () = vec <- vec lor override

  method is_final = vec land final = final
  method is_override = vec land override = override

  method to_string =
    let l = ref [] in
    if self#is_final then
      l := "final" :: !l;
    if self#is_override then
      l := "override" :: !l;
    String.concat " " !l

end (* class Pinfo.virt_specs *)

module Type = struct

  type simple_ty = {
      st_decl_specs : decl_specs;
      st_type_specs : TypeSpec.t list;
      st_encoded    : string;
    }

  type pointer_op =
    | Star of string * qualifiers
    | Amp
    | AmpAmp
    | Hat
    | Macro of string

  type t =
    | SimpleTy of simple_ty
    | ArrayTy of t * int
    | PointerTy of pointer_ty
    | FunctionTy of function_ty
    | AltTy of t list

  and pointer_ty = {
      pt_op         : pointer_op;
      pt_type       : t;
      pt_qualifiers : qualifiers;
    }

  and function_ty = {
      ft_param_types  : t list;
      ft_qualifiers   : qualifiers;
      ft_return_type  : t;
      ft_is_vararg    : bool;
      ft_params_macro : string;
      ft_virt_specs   : virt_specs;
    }

  type t_ = {
      mutable t_typedef : bool;
      t_desc    : t;
    }

  let simple_ty_to_string {
    st_decl_specs=ds;
    st_type_specs=ts;
    st_encoded=_;
  } =
    let ds_str = ds#to_string in
    if ds_str = "" then begin
      match ts with
      | [] -> ""
      | [t] -> TypeSpec.to_string t
      | _ -> sprintf "(%s)" (list_to_string TypeSpec.to_string " " ts)
    end
    else
      sprintf "(%s %s)" ds_str (list_to_string TypeSpec.to_string " " ts)

  let get_name_of_simple_ty {
    st_decl_specs=_;
    st_type_specs=ts;
    st_encoded=_;
  } =
    match ts with
    | [] -> raise Not_found
    | [t] -> [TypeSpec.get_name t]
    | _ -> List.filter_map (fun t -> try Some (TypeSpec.get_name t) with _ -> None) ts

  let simple_ty_has_definite_ty {
    st_type_specs=ts;_
  } = List.exists TypeSpec.is_definite_type ts

  let simple_ty_has_basic_ty {
    st_type_specs=ts;_
  } = List.exists TypeSpec.is_basic_type ts

  let simple_ty_has_elaborated_ty {
    st_type_specs=ts;_
  } = List.exists TypeSpec.is_elaborated_type ts

  let simple_ty_has_elaborated_ty_enum_class {
    st_type_specs=ts;_
  } = List.exists TypeSpec.is_elaborated_type_enum_class ts

  let simple_ty_has_typename {
    st_type_specs=ts;_
  } = List.exists TypeSpec.is_typename ts

  let simple_ty_has_type_type ?(name="") {
    st_type_specs=ts;_
  } =
    List.exists
      (fun t ->
        TypeSpec.is_elaborated_type_type t &&
        (
         name = "" ||
         match TypeSpec.get_ident_opt t with
         | Some x -> x = name
         | None -> true
        )
      ) ts
    (* || List.exists TypeSpec.is_typename ts*)

  let get_cv_qualifiers_of_simple_ty sty =
    List.fold_left
      (fun l t ->
        try
          (TypeSpec.get_cv_qualifier t)::l
        with
          Not_found -> l
      ) [] sty.st_type_specs

  let pointer_op_to_string = function
    | Star(n, q) -> begin
        let q_str = q#to_string in
        if q_str = "" then
          sprintf "%s*" n
        else
          sprintf "(%s* %s)" n q_str
    end
    | Amp -> "&"
    | AmpAmp -> "&&"
    | Hat -> "^"
    | Macro i -> i

  let rec get_name = function
    | SimpleTy sty -> get_name_of_simple_ty sty
    | ArrayTy(ty, _) -> get_name ty
    | PointerTy pty -> get_name_of_pointer_ty pty
    | FunctionTy _ -> raise Not_found
    | AltTy ts ->
        List.flatten
          (List.filter_map (fun t -> try Some (get_name t) with _ -> None) ts)

  and get_name_of_pointer_ty {
    pt_op=_;
    pt_type=ty;
    pt_qualifiers=_;
  } = get_name ty

  let rec to_string = function
    | SimpleTy sty -> simple_ty_to_string sty
    | ArrayTy(ty, dims) ->
        sprintf "%s[%d]" (to_string ty) dims
        (*(to_string ty)^(String.concat "" (List.init dims (fun _ -> "[]")))*)
    | PointerTy pty -> pointer_ty_to_string pty
    | FunctionTy fty -> function_ty_to_string fty
    | AltTy ts -> sprintf "(%s)" (list_to_string to_string " | " ts)

  and pointer_ty_to_string {
    pt_op=op;
    pt_type=ty;
    pt_qualifiers=q;
  } =
    let q_str = q#to_string in
    let o_str = pointer_op_to_string op in
    if q_str = "" then
      (to_string ty)^o_str
    else
      sprintf "(%s %s)%s" (to_string ty) q_str o_str

  and function_ty_to_string {
    ft_param_types=ptys;
    ft_qualifiers=q;
    ft_return_type=rty;
    ft_is_vararg=is_va;
    ft_params_macro=params_macro;
    ft_virt_specs=v;
  } =
    if params_macro = "" then
      sprintf "(%s%s->%s%s%s)"
        (String.concat "," (List.map to_string ptys))
        (if is_va then "..." else "")
        (to_string rty)
        (let s = q#to_string in if s <> "" then " "^s else "")
        (let s = v#to_string in if s <> "" then " "^s else "")
    else
      params_macro

  let get_name_ { t_typedef=_; t_desc=x } = get_name x

  let to_string_ { t_typedef=b; t_desc=x } =
    let s = to_string x in
    sprintf "%s%s"
      (if b then "TYPEDEF:" else "")
      s

  let wrap x = { t_typedef=false; t_desc=x }
  let unwrap x = x.t_desc

  let is_typedef x = x.t_typedef

  let rec get_top_level_type = function
    | SimpleTy sty -> [sty]
    | ArrayTy(ty, _) -> get_top_level_type ty
    | PointerTy pty -> get_top_level_type pty.pt_type
    | FunctionTy fty -> get_top_level_type fty.ft_return_type
    | AltTy ts -> List.concat_map get_top_level_type ts

  let rec _is_type_type ?(name="") = function
    | SimpleTy sty -> simple_ty_has_type_type ~name sty
    | AltTy ts -> List.exists (_is_type_type ~name) ts
    | _ -> false

  let is_type_type ?(name="") x = _is_type_type ~name (unwrap x)

  let _is_function_type = function
    | FunctionTy _ -> true
    | _ -> false

  let is_function_type x = _is_function_type (unwrap x)

  let hoist_typedef x =
    let tl = get_top_level_type x.t_desc in
    let b = List.exists (fun t -> t.st_decl_specs#is_typedef) tl in
    x.t_typedef <- b

  let encode_simple_ty {
    st_encoded=e;_
  } = e

  let make_simple_type ds ts e =
    SimpleTy { st_decl_specs=ds;
               st_type_specs=ts;
               st_encoded=e;
             }

  let idents_of_simple_type = function
    | SimpleTy { st_decl_specs=_; st_type_specs=ts; _} -> begin
        Xlist.filter_map TypeSpec.get_ident_opt ts
    end
    | _ -> invalid_arg "Cpp.Pinfo.Type.idents_of_simple_type"

  let make_array_type ty dims = ArrayTy(ty, dims)

  let make_pointer_type ?(qualifiers=new qualifiers) op ty =
    PointerTy { pt_op=op; pt_type=ty; pt_qualifiers=qualifiers; }

  let make_function_type
      ?(qualifiers=new qualifiers)
      ?(params_macro="")
      ?(is_vararg=false)
      ?(virt_specs=new virt_specs)
      ptys rty =
    FunctionTy { ft_param_types=ptys;
                 ft_qualifiers=qualifiers;
                 ft_return_type=rty;
                 ft_is_vararg=is_vararg;
                 ft_params_macro=params_macro;
                 ft_virt_specs=virt_specs;
               }

  let make_alt_type ts = AltTy ts

  let int_t = make_simple_type (new decl_specs) [TypeSpec.Int] "i"

end (* module Type *)


[%%capture_path
module Name = struct

  let mes fmt = _mes "Name" fmt

  module Namespace = struct
    type t =
      | Normal of ident
      | Inline of ident

    let to_string = function
      | Normal i -> i
      | Inline i -> i^"?"

    let encode = function
      | Normal i -> encode_ident i
      | Inline i -> encode_ident i

    let mk ?(inline=false) i =
      if inline then
        Inline i
      else
        Normal i

  end (* Name.Namespace *)

  module NestedNamespace = struct
    type t = Namespace.t list

    let to_string nl = String.concat "::" (List.rev_map Namespace.to_string nl)

    let encode nl = String.concat "" (List.rev_map Namespace.encode nl)

    let mk1 n = ([n] : t)

    let append nn n = n :: nn

  end (* Name.NestedNamespace *)

  module Scope = struct
    type t =
      | Top
      | Namespace of NestedNamespace.t
      | Template
      | Class of ident
      | Enum of ident
      | EnumClass of ident
      | Params
      | Block of int * string ref(* prefix*) * string ref(* qname *) * bool ref(*is_body*)

    let to_string = function
      | Top          -> "Top"
      | Namespace nn -> sprintf "Namespece(%s)" (NestedNamespace.to_string nn)
      | Template     -> "Template"
      | Class i      -> sprintf "Class(%s)" i
      | Enum i       -> sprintf "Enum(%s)" i
      | EnumClass i  -> sprintf "EnumClass(%s)" i
      | Params       -> "Params"
      | Block(ln, p, q, b) ->
          sprintf "Block@%d%s%s%s" ln
            (if !p = "" then "" else "["^(!p)^"]")
            (if !q = "" then "" else "["^(!q)^"]")
            (if !b then "[body]" else "")

    let get_name = function
      | Namespace nn -> NestedNamespace.to_string nn
      | Class i
      | Enum i
      | EnumClass i -> i
      | _ -> raise Not_found

    let is_top = (==) Top

    let is_namespace = function
      | Namespace _ -> true
      | _ -> false

    let is_template = (==) Template

    let is_class = function
      | Class _ -> true
      | _ -> false

    let is_enum = function
      | Enum _ -> true
      | EnumClass _ -> true
      | _ -> false

    let is_enumclass = function
      | EnumClass _ -> true
      | _ -> false

    let is_params = (==) Params

    let is_block = function
      | Block _ -> true
      | _ -> false

    let is_body = function
      | Block(_, _, _, b) -> !b
      | _ -> false

    let is_lambda_body = function
      | Block(_, _, q, b) -> !q = "" && !b
      | _ -> false

  end (* Name.Scope *)


  module Spec = struct

    type access_spec =
      | Aprivate
      | Aprotected
      | Apublic
      | Amacro of ident

    let access_spec_to_string = function
      | Aprivate   -> "private"
      | Aprotected -> "protected"
      | Apublic    -> "public"
      | Amacro i   -> i

    type param_spec =
      | Pclass
      | Ptypename
      | PclassPack
      | PtypenamePack
      | Pconcept of string * ident

    let param_spec_to_string = function
      | Pclass         -> "class"
      | Ptypename      -> "typename"
      | PclassPack     -> "class..."
      | PtypenamePack  -> "typename..."
      | Pconcept(q, c) -> "concept:"^q^c

    let param_spec_is_concept = function
      | Pconcept _ -> true
      | _ -> false

    class base_spec
        ?(access_spec=None)
        ?(is_virtual=false)
        ?(is_pack_expansion=false)
        ident
        =
      object
        val mutable is_pack_expansion = is_pack_expansion
        method ident = ident
        method access_spec = access_spec
        method is_virtual = is_virtual
        method is_pack_expansion = is_pack_expansion
        method set_is_pack_expansion () = is_pack_expansion <- true
        method to_string =
          let a_str = opt_to_string access_spec_to_string access_spec in
          sprintf "%s%s%s%s"
            (if a_str = "" then "" else a_str^" ")
            (if is_virtual then "virtual " else "")
            ident
            (if is_pack_expansion then "..." else "")
      end (* class base_spec *)

    class class_spec ?(base_specs=[]) ?(alt_base_specs_list=[]) qn = object
      val virt_specs = new virt_specs
      method qn = qn
      method base_specs : base_spec list = base_specs
      method alt_base_specs_list : base_spec list list = alt_base_specs_list
      method virt_specs : virt_specs = virt_specs
      method to_string =
        let v_str = virt_specs#to_string in
        let bs_str = list_to_string (fun x -> x#to_string) ", " base_specs in
        sprintf "%s%s%s" qn
          (if v_str = "" then "" else " "^v_str)
          (if bs_str = "" then "" else " : "^bs_str)

    end (* class class_spec *)

    class enum_base ?(macro_name="") type_specs = object
      method macro_name = macro_name
      method type_specs : TypeSpec.t list = type_specs
      method to_string =
        if macro_name = "" then
          list_to_string TypeSpec.to_string " " type_specs
        else
          macro_name
    end (* class enum_base *)

    class enum_spec ?(enum_base=None) ident = object
      method ident : ident = ident
      method enum_base : enum_base option = enum_base
      method to_string =
        let eb_str = opt_to_string (fun x -> x#to_string) enum_base in
        sprintf "%s%s" ident (if eb_str = "" then "" else " : "^eb_str)
    end (* class enum_spec *)

    class mem_spec access_spec ty = object
      method access_spec = access_spec
      method ty = ty
      method is_public =
        match access_spec with
        | Some Apublic -> true
        | _ -> false
      method to_string =
        let a_str = opt_to_string access_spec_to_string access_spec in
        sprintf "%s%s" (if a_str = "" then "" else a_str^" ") (Type.to_string_ ty)
    end (* class mem_spec *)

    type kind =
      | Namespace of (unit -> unit)
      | UsingDecl
      | UsingEnumDecl
      | Template of kind
      | TypeParam of param_spec
      | Param of Type.t_
      | Class of class_spec
      | Struct of class_spec
      | Union of class_spec
      | Enum of enum_spec
      | EnumClass of enum_spec
      | EnumStruct of enum_spec
      | EnumMacro of ident * enum_spec
      | Type
      | Function of Type.t_
      | FParam of Type.t_
      | Member of mem_spec
      | Variable of Type.t_
      | Enumerator of Type.t_
      | MacroObj
      | MacroFun
      | IdMacroFun
      | Label

    let rec kind_to_string = function
      | Namespace _  -> "Namespace"
      | UsingDecl    -> "UsingDecl"
      | UsingEnumDecl -> "UsingEnumDecl"
      | Template k   -> sprintf "Template:%s" (kind_to_string k)
      | TypeParam s  -> sprintf "TypeParam:%s" (param_spec_to_string s)
      | Param ty     -> sprintf "Param:%s" (Type.to_string_ ty)
      | Class s      -> "Class:"^s#to_string
      | Struct s     -> "Struct:"^s#to_string
      | Union s      -> "Union:"^s#to_string
      | Enum s       -> "Enum:"^s#to_string
      | EnumClass s  -> "EnumClass:"^s#to_string
      | EnumStruct s -> "EnumStruct:"^s#to_string
      | EnumMacro(i, s) -> sprintf "EnumStruct:%s:%s" i s#to_string
      | Type         -> "Type"
      | Function ty  -> sprintf "Function:%s" (Type.to_string_ ty)
      | FParam ty    -> sprintf "FParam:%s" (Type.to_string_ ty)
      | Member s     -> sprintf "Member:%s" s#to_string
      | Variable ty  -> sprintf "Variable:%s" (Type.to_string_ ty)
      | Enumerator ty -> sprintf "Enumerator:%s" (Type.to_string_ ty)
      | MacroObj     -> "MacroObj"
      | MacroFun     -> "MacroFun"
      | IdMacroFun   -> "IdMacroFun"
      | Label        -> "Label"

    let rec type_of_kind = function
      | Template k   -> type_of_kind k
      | Param ty
      | Function ty
      | FParam ty
      | Variable ty -> ty
      | Enumerator ty -> ty
      | _ -> raise Not_found

    let make_templ k = Template k

    let make_typaram s = TypeParam s

    let make_param ty =
      let ty_ = Type.wrap ty in
      Type.hoist_typedef ty_;
      Param ty_

    let make_function ty =
      let ty_ = Type.wrap ty in
      Type.hoist_typedef ty_;
      Function ty_

    let make_fparam ty =
      let ty_ = Type.wrap ty in
      Type.hoist_typedef ty_;
      FParam ty_

    let make_variable ty =
      let ty_ = Type.wrap ty in
      Type.hoist_typedef ty_;
      Variable ty_

    let make_enumerator ty =
      let ty_ = Type.wrap ty in
      Type.hoist_typedef ty_;
      Enumerator ty_

    let make_member aspec ty =
      let ty_ = Type.wrap ty in
      Type.hoist_typedef ty_;
      let mspec = new mem_spec aspec ty_ in
      Member mspec

    class c
        ?(bid_opt=None) ?(prefix="") ?(is_local=false) ?(section_info_opt=None)
        (lod : Astloc.t) (iod : int) (ident : ident) (_kind : kind)
        =
      object
        val mutable kind = _kind
        val mutable prefix = prefix

        method get_qualified_name () = prefix^ident
        method bid_opt : BID.t option = bid_opt
        method section_info_opt : pp_if_section_info option = section_info_opt
        method prefix = prefix
        method append_prefix p = prefix <- prefix ^ p
        method lod = lod
        method iod = iod
        method is_local = is_local
        method is_public =
          match kind with
          | Member mspec -> mspec#is_public
          | _ -> false
        method is_fparam =
          match kind with
          | FParam _ -> true
          | _ -> false
        method is_variable =
          match kind with
          | Variable _ -> true
          | _ -> false
        method ident = ident
        method kind = kind

        method templatize () =
          match kind with
          | Class _ | Struct _ | Union _
          | Enum _ | EnumClass _ | EnumStruct _ | EnumMacro _
          | Member _ | Function _ -> kind <- (make_templ kind)
          | Variable t when Type.is_function_type t -> kind <- (make_templ kind)
          | _ -> ()

        method to_string =
          sprintf "%s%s [%s]"
            (if prefix = "" then "" else sprintf "%s " prefix)
            (kind_to_string kind)
            (Astloc.to_string lod)

        method def_adder =
          match kind with
          | Namespace f -> f
          | _ -> failwith "Cpp.Pinfo.Name.Spec.c#def_adder"

        method get_type () = type_of_kind kind

      end (* class Name.Spec.c *)

  end (* module Name.Spec *)

  class stack_frame (_scope : Scope.t) = object

    val _tbl = (Hashtbl.create 0 : (ident, Spec.c) Hashtbl.t)
    val mutable scope = _scope

    method scope = scope
    method change_scope scp = scope <- scp

    method block_scope =
      match scope with
      | Block _ -> true
      | _ -> false

    method iter (f : ident -> Spec.c -> unit) = Hashtbl.iter f _tbl

    method register ?(templatize=true) ?(replace=false) i spec =
      [%debug_log "@%s: %s => %s" (Scope.to_string scope) i spec#to_string];
      if templatize && Scope.is_template scope then
        spec#templatize();
      if replace then
        Hashtbl.replace _tbl i spec
      else
        Hashtbl.add _tbl i spec

    method remove_macro i =
      Hashtbl.filter_map_inplace
        (fun k v ->
          if k = i then begin
            match v#kind with
            | Spec.MacroObj | MacroFun | IdMacroFun -> None
            | _ -> Some v
          end
          else
            Some v
        ) _tbl

    method find_all ?(filt=fun _ -> true) n =
      List.filter filt (Hashtbl.find_all _tbl n)

    method find ?(filt=fun _ -> true) n =
      match List.filter filt (Hashtbl.find_all _tbl n) with
      | [] -> raise Not_found
      | x::_ -> x

    method to_string =
      let buf = Buffer.create 0 in
      Buffer.add_string buf (sprintf "@%s\n" (Scope.to_string scope));
      Hashtbl.iter
        (fun n s ->
          Buffer.add_string buf (sprintf "%s -> %s\n" n s#to_string);
        ) _tbl;
      Buffer.contents buf

  end (* class Name.stack_frame *)

  exception Scope_found
  exception Found of Spec.c

  class stack = object (self)

    val _stack = (Stack.create() : stack_frame Stack.t)
    val mutable popped_frame = new stack_frame Scope.Top

    method copy = {<_stack = Stack.copy _stack;>}

    method get_prefix ?(prefix="") ?(ns_only=false) ?(class_only=false) () =
      let q = ref "" in
      Stack.iter
        (fun frm ->
          match (frm#scope : Scope.t) with
          | Namespace nn when not class_only -> begin
              q := (NestedNamespace.encode nn)^(!q);
              if prefix = !q then
                q := ""
          end
          | Class i | Enum i when not ns_only -> begin
              q := i^(!q);
              if prefix = !q then
                q := ""
          end
          | Block(_, p, _, _) when not class_only && not ns_only && !p != "" -> begin
              q := (!p)^(!q);
              if prefix = !q then
                q := ""
          end
          | _ -> ()
        ) _stack;
      [%debug_log "qualifier=%s" !q];
      !q

    method top =
      Stack.top _stack

    method peek_nth nth =
      match nth with
      | 1 -> self#top
      | n when n < 0 -> invalid_arg "Pinfo.Name.stack#peek_nth"
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
                ) _stack
            with
              Exit -> ()
          end;
          match !res with
          | Some x -> x
          | _ -> raise Stack.Empty

    method push frm = Stack.push frm _stack

    method reset_popped_frame () =
      popped_frame <- new stack_frame Scope.Top

    method reset () =
      Stack.clear _stack;
      self#reset_popped_frame()

    method after_params = popped_frame#scope == Scope.Params

    method set_popped_frame_scope_from_params_to_top () =
      if popped_frame#scope == Scope.Params then
        popped_frame#change_scope Top

    method enter_scope scope =
      [%debug_log "entering %s scope" (Scope.to_string scope)];
      Stack.push (new stack_frame scope) _stack

    method enter_namespace nn = self#enter_scope (Scope.Namespace nn)
    method enter_template () = self#enter_scope Scope.Template
    method enter_class i = self#enter_scope (Scope.Class i)
    method enter_enum i = self#enter_scope (Scope.Enum i)
    method enter_enumclass i = self#enter_scope (Scope.EnumClass i)
    method enter_params () = self#enter_scope Scope.Params
    method enter_block ?(prefix="") ?(qname="") ?(no_tweak=false) ln =
      if popped_frame#scope == Scope.Params && not no_tweak then begin
        [%debug_log "changing last poped frame to Block"];
        popped_frame#change_scope (Scope.Block(ln, ref prefix, ref qname, ref false));
        [%debug_log "entering %s scope" (Scope.to_string popped_frame#scope)];
        Stack.push popped_frame _stack;
        [%debug_log "%s" self#top#to_string];
        popped_frame <- new stack_frame Scope.Top
      end
      else
        self#enter_scope (Scope.Block(ln, ref "", ref "", ref false))

    method set_body_flag () =
      match self#top#scope with
      | Scope.Block(_, _, _, b) -> b := true
      | _ -> ()

    method reset_body_name () =
      match self#top#scope with
      | Scope.Block(_, p, q, _) -> p := ""; q := ""
      | _ -> ()

    method _exit_scope chk_scp =
      let frm = Stack.pop _stack in
      [%debug_log "%s scope poped" (Scope.to_string frm#scope)];
      assert (chk_scp frm#scope);
      [%debug_log "%s scope exited" (Scope.to_string frm#scope)];
      popped_frame <- frm

    method exit_namespace () =
      [%debug_log "exiting Namespace scope..."];
      self#_exit_scope Scope.is_namespace;
      popped_frame

    method exit_template () =
      [%debug_log "exiting Template scope..."];
      self#_exit_scope Scope.is_template;
      popped_frame#iter
        (fun i (spec : Spec.c) ->
          [%debug_log "%s %s" i spec#to_string];
          match spec#kind with
          | Template _ -> self#top#register ~templatize:false i spec
          | Class _ | Struct _ | Union _
          | Enum _ | EnumClass _ | EnumStruct _ | EnumMacro _
          (*| Member _ *)| Function _ -> begin
              spec#templatize();
              self#top#register ~templatize:false i spec
          end
          | Member _ -> begin
              self#top#register ~templatize:false i spec
          end
          | Variable t when Type.is_function_type t -> begin
              spec#templatize();
              self#top#register ~templatize:false i spec
          end
          | _ -> ()
        )

    method exit_class () =
      [%debug_log "exiting Class scope..."];
      self#_exit_scope Scope.is_class;
      popped_frame#iter
        (fun i (spec : Spec.c) ->
          if spec#is_public then begin
            [%debug_log "%s is a public member" i];
            self#top#register ~templatize:false i spec
          end
        )

    method exit_enum () =
      [%debug_log "exiting Enum scope..."];
      self#_exit_scope Scope.is_enum;
      let scope = popped_frame#scope in
      let enumclass_flag = Scope.is_enumclass scope in
      if enumclass_flag then begin
        let p = Scope.get_name scope in
        popped_frame#iter
          (fun i (spec : Spec.c) ->
            [%debug_log "%s %s" i spec#to_string];
            spec#append_prefix p;
            [%debug_log " -> %s" spec#to_string];
            self#top#register ~templatize:false i spec
          )
      end
      else
        popped_frame#iter
          (fun i (spec : Spec.c) ->
            self#top#register ~templatize:false i spec
          )

    (*method exit_function () =
      [%debug_log "exiting Function scope..."];
      self#_exit_scope ((=) Scope.Function)*)

    (*method exit_function_if_any () =
      [%debug_log "exiting Function scope (if any)..."];
      let frm = Stack.top _stack in
      [%debug_log "stack top is %s scope" (Scope.to_string frm#scope)];
      if frm#scope = Scope.Function then begin
        let _ = Stack.pop _stack in
        [%debug_log "%s scope exited" (Scope.to_string frm#scope)]
      end*)

    method exit_params () =
      [%debug_log "exiting Params scope..."];
      self#_exit_scope Scope.is_params

    method exit_block () =
      [%debug_log "exiting Block scope..."];
      self#_exit_scope Scope.is_block


    method in_scope chk_scope =
      try
        Stack.iter
          (fun frm ->
            if chk_scope frm#scope then
              raise Scope_found
          ) _stack;
        false
      with
        Scope_found -> true

    method at_scope chk_scope =
      try
        chk_scope self#top#scope
      with
        _ -> false

    method in_template = self#in_scope Scope.is_template
    method in_class = self#in_scope Scope.is_class
    method in_block = self#in_scope Scope.is_block
    method in_body = self#in_scope Scope.is_body
    method in_lambda_body = self#in_scope Scope.is_lambda_body
    method in_params = self#in_scope Scope.is_params

    method at_top = self#at_scope Scope.is_top
    method at_namespace = self#at_scope Scope.is_namespace
    method at_template = self#at_scope Scope.is_template
    method at_class = self#at_scope Scope.is_class
    method at_enum = self#at_scope Scope.is_enum
    method at_enumclass = self#at_scope Scope.is_enumclass
    method at_block = self#at_scope Scope.is_block
    method at_body = self#at_scope Scope.is_body
    method at_lambda_body = self#at_scope Scope.is_lambda_body
    method at_params = self#at_scope Scope.is_params

    method block_level =
      let count = ref 0 in
      Stack.iter
        (fun frm ->
          match frm#scope with
          | Scope.Block _ -> incr count
          | _ -> ()
        ) _stack;
      !count

    method find_name ?(filt=fun _ -> true) n =
      [%debug_log "%s" n];
      try
        Stack.iter
          (fun frm ->
            (*[%debug_log "%s" frm#to_string];*)
            try
              raise (Found (frm#find ?filt:(Some filt) n))
            with
              Not_found -> ()
          ) _stack;
      if popped_frame#scope == Scope.Params then begin
        popped_frame#find ~filt n
      end
      else
        raise Not_found
      with
        Found x -> [%debug_log "found: %s" x#to_string]; x

    method find_namespace n =
      let filt x =
        match x#kind with
        | Spec.Namespace _ -> true
        | _ -> false
      in
      self#find_name ~filt n

    method find_obj n =
      let filt x =
        match x#kind with
        | Spec.Variable _ | FParam _ | Param _ | Function _ -> true
        | _ -> false
      in
      self#find_name ~filt n

    method find_type n =
      let filt x =
        match x#kind with
        | Spec.TypeParam _ | Class _ | Struct _ | Union _
        | Enum _ | EnumClass _ | EnumStruct _ | EnumMacro _ | Type -> true
        | _ -> false
      in
      self#find_name ~filt n

    method find_templ n =
      let filt x =
        match x#kind with
        | Spec.Template _ -> true
        | _ -> false
      in
      self#find_name ~filt n

    method to_string =
      let buf = Buffer.create 0 in
      Stack.iter
        (fun frm ->
          Buffer.add_string buf frm#to_string;
          Buffer.add_string buf "\n";
        ) _stack;
      Buffer.contents buf

    method scopes_to_string =
      let buf = Buffer.create 0 in
      Stack.iter
        (fun frm ->
          Buffer.add_string buf (Scope.to_string frm#scope);
          Buffer.add_string buf "\n";
        ) _stack;
      Buffer.contents buf

    method make_def_adder (frm : stack_frame) =
      let def_adder () =
        frm#iter
          (fun i spec ->
            [%debug_log "%s -> %s" i spec#to_string];
            self#top#register ~templatize:false i spec
          )
      in
      def_adder

  end (* class Name.stack *)

end (* module Name *)
]

type t =
  | NoInfo
  | NameSpec of Name.Spec.c
  | External of name

let from_spec spec =
  NameSpec spec

let from_name name =
  External name

let get_external = function
  | External n -> n
  | _ -> raise Not_found

let get_spec = function
  | NameSpec s -> s
  | _ -> raise Not_found

let merge i j =
  match i with
  | NoInfo -> j
  | _ -> failwith "Cpp.Pinfo.merge"

let to_string = function
  | NoInfo -> ""
  | NameSpec spec -> "NameSpec:"^spec#to_string
  | External n -> "External:"^n
