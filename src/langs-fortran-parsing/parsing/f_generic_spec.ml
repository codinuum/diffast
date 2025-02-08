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

open Label_common

type record_kind = 
  | RK_formatted 
  | RK_unformatted
  | RK_weird of name

type t = 
  | Name of name
  | DefinedOperator of F_defined_operator.t
  | IntrinsicOperator of F_intrinsic_operator.t
  | Assignment
  | Read of record_kind
  | Write of record_kind

let record_kind_to_string = function
  | RK_formatted   -> "RK_formatted"
  | RK_unformatted -> "RK_unformatted"
  | RK_weird n     -> "RK_weird:"^n

let record_kind_to_simple_string = function
  | RK_formatted   -> "formatted"
  | RK_unformatted -> "unformatted"
  | RK_weird n     -> n

let to_string = function
  | Name n               -> "Name:"^n
  | DefinedOperator op   -> "DefinedOperator:"^(F_defined_operator.to_string op)
  | IntrinsicOperator op -> "IntrinsicOperator:"^(F_intrinsic_operator.to_string op)
  | Assignment           -> "Assignment"
  | Read k               -> "Read:"^(record_kind_to_string k)
  | Write k              -> "Write:"^(record_kind_to_string k)

let to_simple_string = function
  | Name n               -> n
  | DefinedOperator op   -> "operator("^(F_defined_operator.to_simple_string op)^")"
  | IntrinsicOperator op -> "operator("^(F_intrinsic_operator.to_simple_string op)^")"
  | Assignment           -> "assignment(=)"
  | Read k               -> "read("^(record_kind_to_string k)^")"
  | Write k              -> "write("^(record_kind_to_string k)^")"

let to_tag = function
  | Name n               -> "NameGenericSpec", [name_attr_name,n]
  | DefinedOperator op   -> "DefinedOperatorGenericSpec", ["op",F_defined_operator.to_string op]
  | IntrinsicOperator op -> "IntrinsicOperatorGenericSpec", ["op",F_intrinsic_operator.to_string op]
  | Assignment           -> "AssignmentGenericSpec", []
  | Read k               -> "ReadGenericSpec", ["kind",record_kind_to_simple_string k]
  | Write k              -> "WriteGenericSpec", ["kind",record_kind_to_simple_string k]

let get_name = function
  | Name n      -> n
  | DefinedOperator op -> F_defined_operator.get_name op
  | _ -> raise Not_found

let get_name_opt = function
  | Name n      -> Some n
  | DefinedOperator op -> F_defined_operator.get_name_opt op
  | _ -> None


let record_kind_of_keyword kw =
  match String.lowercase_ascii kw with
  | "formatted"   -> RK_formatted
  | "unformatted" -> RK_unformatted
  | _ -> RK_weird kw

let anonymize = function
  | Name _ -> Name ""
  | l -> l

