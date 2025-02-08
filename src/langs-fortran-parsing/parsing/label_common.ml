(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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

module XML = Diffast_misc.XML
module Xstring = Diffast_misc.Xstring


type name  = Common.name
type label = Common.label
type var   = Common.var

let opt_to_string         = Common.opt_to_string
let string_opt_to_string  = Common.string_opt_to_string
let int_opt_to_string     = Common.int_opt_to_string
let opt_to_list           = Common.opt_to_list
let opt_to_list_map       = Common.opt_to_list_map
let string_list_to_string = Common.string_list_to_string
let int_list_to_string    = Common.int_list_to_string

let lang_prefix = "fortran"

let name_attr_name   = "name"
let label_attr_name  = "label"
let slabel_attr_name = "slabel"
(*let value_attr_name  = "value"*)
let path_attr_name   = "path"
let spec_attr_name   = "spec"
let desc_attr_name   = "desc"
let var_attr_name    = "var"
let rank_attr_name   = "rank"
let proc_name_attr_name = "pname"
let value_attr_name = "value"

let opt_to_attr to_string aname x_opt =
  List.map (fun x -> aname, to_string x) (opt_to_list x_opt)

let string_opt_to_attr an = opt_to_attr (fun (x : string) -> x) an
let int_opt_to_attr an = opt_to_attr string_of_int an

let list_to_attr to_string prefix xs =
  let a = Array.of_list xs in
  Array.to_list (Array.mapi (fun i x -> prefix^(string_of_int i), to_string x) a)

let name_list_to_attr p = list_to_attr (fun (x : string) -> x) p
let int_list_to_attr p = list_to_attr string_of_int p

let strlit_to_encoded_path s =
  XML.encode_string (Xstring.remove_quotes s)

