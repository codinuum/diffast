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

type t =
  | Designator of name
  | NamedTuple of name
  | Tuple             

  | Primary
  | NamedDataObject of name
  | Subobject
  | TripletOrRange
  | First
  | Second
  | DataStmtConstant

  | Assumed
  | Deferred
  | AssumedSize

  | ArrayAccess of name (* named for Diff/TS *)
(*
  | PpExpr of name
  | PpTypeSpec of name
*)
  | GenericSpecOrUseName of name


let to_string = function
  | Designator n -> "Designator:"^n
  | NamedTuple n -> "NamedTuple:"^n
  | Tuple        -> "Tuple"

  | Primary           -> "Primary"
  | NamedDataObject n -> "NamedDataObject:"^n
  | Subobject         -> "Subobject"
  | TripletOrRange    -> "TripletOrRange"
  | First             -> "First"
  | Second            -> "Second"
  | DataStmtConstant  -> "DataStmtConstant"
  | Assumed           -> "Assumed"
  | Deferred          -> "Deferred"
  | AssumedSize       -> "AssumedSize"

  | ArrayAccess n     -> "ArrayAccess:"^n
(*
  | PpExpr n          -> "PpExpr:"^n
  | PpTypeSpec n      -> "PpTypeSpec:"^n
*)
  | GenericSpecOrUseName n -> "GenericSpecOrUseName:"^n

let to_simple_string = function
  | Designator n -> "<designator:"^n^">"
  | NamedTuple n -> "<named-tuple:"^n^">"
  | Tuple        -> "<tuple>"

  | Primary           -> "<primary>"
  | NamedDataObject n -> Printf.sprintf "<named-data-object:%s>" n
  | Subobject         -> "<subobject>"
  | TripletOrRange    -> "<triplet-or-range>"
  | First             -> "<first>"
  | Second            -> "<second>"
  | DataStmtConstant  -> "<data-stmt-constant>"
  | Assumed           -> "<assumed>"
  | Deferred          -> "<deferred>"
  | AssumedSize       -> "<assumed-size>"

  | ArrayAccess n     -> Printf.sprintf "<array-access:%s>" n
(*
  | PpExpr n          -> Printf.sprintf "<pp-expr:%s>" n
  | PpTypeSpec n      -> Printf.sprintf "<pp-type-spec:%s>" n
*)
  | GenericSpecOrUseName n -> Printf.sprintf "<generic-spec-or-use-name:%s>" n

let to_tag = function
  | Designator n -> "Designator", [name_attr_name,n]
  | NamedTuple n -> "NamedTuple", [name_attr_name,n]
  | Tuple        -> "Tuple", []

  | Primary           -> "Primary", []
  | NamedDataObject n -> "NamedDataObject", [name_attr_name,n]
  | Subobject         -> "Subobject", []
  | TripletOrRange    -> "TripletOrRange", []
  | First             -> "First", []
  | Second            -> "Second", []
  | DataStmtConstant  -> "DataStmtConstant", []
  | Assumed           -> "Assumed", []
  | Deferred          -> "Deferred", []
  | AssumedSize       -> "AssumedSize", []

  | ArrayAccess n     -> "ArrayAccess", [name_attr_name,n]
(*
  | PpExpr n          -> "PpExpr", [name_attr_name,n]
  | PpTypeSpec n      -> "PpTypeSpec", [name_attr_name,n]
*)
  | GenericSpecOrUseName n -> "GenericSpecOrUseName", [name_attr_name,n]

let get_name = function
  | Designator n 
  | NamedTuple n 
  | NamedDataObject n 
  | ArrayAccess n
(*
  | PpExpr n     
  | PpTypeSpec n 
*)
  | GenericSpecOrUseName n
    -> n

  | _ -> raise Not_found

let get_name_opt = function
  | Designator n 
  | NamedTuple n 
  | NamedDataObject n 
  | ArrayAccess n
(*
  | PpExpr n     
  | PpTypeSpec n 
*)
  | GenericSpecOrUseName n
    -> Some n

  | _ -> None

let is_array_spec = function
  | Assumed
  | Deferred
  | AssumedSize -> true
  | _ -> false

let anonymize = function
  | Designator _      -> Designator ""
  | NamedTuple _      -> NamedTuple ""
  | NamedDataObject _ -> NamedDataObject ""
  | ArrayAccess _     -> ArrayAccess ""
(*
  | PpExpr _          -> PpExpr ""
  | PpTypeSpec _      -> PpTypeSpec ""
*)
  | GenericSpecOrUseName _ -> GenericSpecOrUseName ""
  | l -> l

