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

module Loc = Diffast_misc.Loc


exception External_parser_not_found of string

val extension : string
val ccs_ext : string
val compressors : (string * (string -> string -> string, unit, string, string, string, string) format6) list
val comp_ext_list : string list
val extensions : string list
val default_file_name : string
val default_ns : string
val default_ns2 : string
val default_ns3 : string
val ast_ns : string
val c_ns : string
val cx_ns : string
val ccx_ns : string
val cpp_ns : string
val java_ns : string
val python_ns : string
val verilog_ns : string
val fortran_ns : string
val default_prefix : string
val c_prefix : string
val cx_prefix : string
val ccx_prefix : string
val cpp_prefix : string
val java_prefix : string
val python_prefix : string
val verilog_prefix : string
val fortran_prefix : string
val parser_tbl : (string * string) list
val get_prefix_by_ns : string -> string
val add_prefix : string -> string -> string
val add_default_prefix : string -> string
val astml_tag : string
val local_parser_attr_name : string
val local_source_attr_name : string
val local_source_digest_attr_name : string
val parser_attr_name : string
val source_attr_name : string
val source_digest_attr_name : string
val location_attr_name : string
val frommacro_attr_name : string
val is_initializer_list_attr_name : string
val mk_ar_attr_name : string -> string
val tid_attr_name : string
val ar_tid_attr_name : string
val stmttid_attr_name : string
val ar_stmttid_attr_name : string
val is_anonymization_resistant_attr : string -> bool
val vars_attr_name : string
val vdids_attr_name : string
val ident_attr_name : string
val label_attr_name : string
val dims_attr_name : string
val islocal_attr_name : string
val isstmt_attr_name : string
val path_attr_name : string
val str_lit_to_path : string -> string
val to_elem_data :
  string ->
  (?strip:bool -> 'a -> string * (string * string) list) ->
  ?strip:bool -> ?afilt:(string -> bool) -> Loc.t -> 'a -> string * (string * string) list * string

module Attr : sig
  val _find_attr : ('a * 'b) list -> 'a -> 'b
  val find_attr : ?default:string -> ('a * string) list -> 'a -> string
  val find_attr_opt : ('a * 'b) list -> 'a -> 'b option
  val find_tid : (string * string) list -> string * string
  val _find_stmttid : (string * string) list -> string * string
  val find_stmttid : (string * string) list -> string * string
  val find_bool : ('a * string) list -> 'a -> bool
  val find_int : ('a * string) list -> 'a -> int
  val find_name : (string * string) list -> string
  val find_value : (string * string) list -> string
  val find_kind : (string * string) list -> string
  val find_sig : (string * string) list -> string
  val find_nth : (string * string) list -> int
  val find_value_u : (string * string) list -> string
  val find_value_x : (string * string) list -> string
  val find_value_b64 : (string * string) list -> string
  val find_path : (string * string) list -> string
  val find_ident : ?default:string -> (string * string) list -> string
  val find_name_opt : (string * 'a) list -> 'a option
  val _vdid_of_string : string -> string list
  val vdid_of_string : string -> string * int
  val _vdids_of_string : string -> string list
  val vdids_of_string : string -> (string * int) list
  val split_comma : string -> string list
  val split_colon : string -> string list
  val find_vdids : ?attr_name:string -> (string * string) list -> (string * int) list
  val find_dims : (string * string) list -> int
  val find_vars : (string * string) list -> string list
  val find_args : (string * string) list -> string list
end
