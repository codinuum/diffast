(*
   Copyright 2012-2023 Codinuum Software Lab <https://codinuum.com>

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
(* common/astml.ml *)

module Xstring = Diffast_misc.Xstring
module XML = Diffast_misc.XML
module Loc = Diffast_misc.Loc

(*let sprintf = Printf.sprintf*)

exception External_parser_not_found of string

let extension = ".ast"

let ccs_ext = ".ccs"

let compressors = (* EXT * DECOMP_CMD_FMT *)
  [ ".bz2", format_of_string "bunzip2 --keep --stdout %s > %s";
    ".gz", format_of_string "gunzip --stdout %s > %s";
  ]
let comp_ext_list = "" :: (fst (List.split compressors))

let extensions =
  List.concat_map
    (fun base_ext ->
      List.map
	(fun comp_ext ->
	  base_ext^comp_ext
	) comp_ext_list
    ) [extension; ccs_ext]

let default_file_name = "src"^extension

let default_ns = "http://codinuum.com/ontologies/2012/10/"
let default_ns2 = "http://codinuum.com/ontologies/2013/05/"
let default_ns3 = "http://codinuum.com/ontologies/2013/12/"
let default_ns4 = "http://codinuum.com/ontologies/2019/02/"

let ast_ns = default_ns^"source-code-entity#"

let c_ns       = default_ns^"c-entity#"
let cx_ns      = default_ns^"cx-entity#"
let ccx_ns     = default_ns3^"ccx-entity#"
let cpp_ns     = default_ns4^"cpp-entity#"
let java_ns    = default_ns^"java-entity#"
let python_ns  = default_ns^"python-entity#"
let verilog_ns = default_ns^"verilog-entity#"
let fortran_ns = default_ns2^"fortran-entity#"

let default_prefix = "a"
let c_prefix       = "c"
let cx_prefix      = "cx"
let ccx_prefix     = "ccx"
let cpp_prefix     = "cpp"
let java_prefix    = "java"
let python_prefix  = "py"
let verilog_prefix = "v"
let fortran_prefix = "f"


let parser_tbl = (* PREFIX * NS *)
  [ c_prefix,       c_ns;
    java_prefix,    java_ns;
    python_prefix,  python_ns;
    verilog_prefix, verilog_ns;
    fortran_prefix, fortran_ns;

    cx_prefix,      cx_ns;
    ccx_prefix,     ccx_ns;
    cpp_prefix,     cpp_ns;
  ]


let get_prefix_by_ns ns =
  let rec loop = function
    | (p, ns')::rest ->
        if ns = ns' then
          p
        else
          loop rest
    | [] ->
        raise Not_found
  in
  loop parser_tbl




(***********)


let add_prefix p x = p^":"^x


let add_default_prefix = add_prefix default_prefix

let astml_tag = (* add_default_prefix *) "astml"


(* attributes *)

let local_parser_attr_name        = "parser"
let local_source_attr_name        = "source"
let local_source_digest_attr_name = "source_digest"

(* default *)
let parser_attr_name        = add_default_prefix local_parser_attr_name
let source_attr_name        = add_default_prefix local_source_attr_name
let source_digest_attr_name = add_default_prefix local_source_digest_attr_name

let location_attr_name  = add_default_prefix "loc"
(* let conf_attr_name      = add_default_prefix "conf" *)
(* let line_terminator_attr_name = add_default_prefix "line_terminator" *)
let frommacro_attr_name = add_default_prefix "frommacro" (* for C, C++, etc. *)
let is_initializer_list_attr_name = add_default_prefix "is_initializer_list"


let mk_ar_attr_name n = "__"^n

let tid_attr_name       = "tid"
let ar_tid_attr_name = mk_ar_attr_name tid_attr_name

let stmttid_attr_name   = "stid"
let ar_stmttid_attr_name = mk_ar_attr_name stmttid_attr_name

let is_anonymization_resistant_attr a =
  try
    String.sub a 0 2 = "__"
  with
    Invalid_argument _ -> false

let vars_attr_name    = "vars" (* C *)
let vdids_attr_name   = "vdids" (* Java *)
let ident_attr_name   = "ident"
let label_attr_name   = "label"
let dims_attr_name    = "dims"
let islocal_attr_name = "islocal"
let isstmt_attr_name  = "isstmt"
let path_attr_name    = "path"


let str_lit_to_path = Xstring.remove_quotes


let to_elem_data lang_prefix to_tag ?(strip=false) ?(afilt=(fun _ -> true)) loc lab =
  let add_lang_prefix = add_prefix lang_prefix in
  let name, _attrs = to_tag ?strip:(Some strip) lab in
  let attrs =
    List.filter_map
      (fun (a, v) ->
        if afilt a then begin
          Some ((if strip then a else add_lang_prefix a), v)
        end
        else
          None
      ) _attrs
  in
  let attrs =
    if strip then
      attrs
    else
      (location_attr_name, Loc.to_attr_value loc) :: attrs
  in
  (if strip then name else add_lang_prefix name),
  attrs,
  ""


module Attr = struct

  let _find_attr attrs n =
    let v = List.assoc n attrs in
(*
    let v_ = XML.decode_string v in
    DEBUG_MSG "%s -> \"%s\" (orig=\"%s\")" n v_ v;
    v_
*)
    v (* already decoded? *)

  let find_attr ?(default="") attrs n =
    try
      _find_attr attrs n
    with
      Not_found -> default

  let find_attr_opt attrs n =
    try
      Some (_find_attr attrs n)
    with
      Not_found -> None

  let _find_tid attrs =
    let e = _find_attr attrs tid_attr_name in
    let a = find_attr attrs ar_tid_attr_name in
    (e, a)

  let find_tid attrs =
    try
      _find_tid attrs
    with _ -> ("", "")

  let _find_stmttid attrs =
    let e = _find_attr attrs stmttid_attr_name in
    let a = find_attr attrs ar_stmttid_attr_name in
    (e, a)

  let find_stmttid attrs =
    try
      _find_stmttid attrs
    with _ -> ("", "")


  let base64enc s =
    try
      Base64.encode_exn s
    with
      e -> [%warn_log "failed to base64 encode: ^%s$" s]; raise e

  let base64dec s =
    try
      Base64.decode_exn s
    with
      e -> [%warn_log "failed to base64 decode: %s" s]; raise e


  let find_bool attrs n = bool_of_string (find_attr attrs n)
  let find_int attrs n = int_of_string (find_attr attrs n)

  let find_name attrs  = find_attr attrs "name"
  let find_value attrs = find_attr attrs "value"
  let find_kind attrs  = find_attr attrs "kind"
  let find_sig attrs   = find_attr attrs "signature"
  let find_nth attrs   = int_of_string (find_attr attrs "nth")

  let find_value_u attrs = Scanf.unescaped (find_attr attrs "value")
  let find_value_x attrs = XML.decode_string (find_attr attrs "value")
  let find_value_b64 attrs = base64dec (find_attr attrs "value")

  let find_path attrs  = find_attr attrs path_attr_name
  let find_ident ?(default="") attrs = find_attr ~default attrs ident_attr_name

  let find_name_opt attrs  = find_attr_opt attrs "name"

  let _vdid_of_string = Str.split (Str.regexp_string "[")
  let vdid_of_string s =
    match _vdid_of_string s with
    | [n; d] -> n, int_of_string d
    | _ -> failwith "Astml.Attr.vdid_of_string"

  let _vdids_of_string = Str.split (Str.regexp_string ";")
  let vdids_of_string s =
    List.map vdid_of_string (_vdids_of_string s)

  let split_comma = Str.split (Str.regexp_string ",")
  let split_colon = Str.split (Str.regexp_string ":")

  let find_vdids ?(attr_name=vdids_attr_name) attrs = vdids_of_string (find_attr attrs attr_name)
  let find_dims attrs  = int_of_string (find_attr attrs dims_attr_name)
  let find_vars attrs  = split_comma (find_attr attrs vars_attr_name)
  let find_args attrs  = split_comma (find_attr attrs "args")

end (* of Astml.Attr *)
