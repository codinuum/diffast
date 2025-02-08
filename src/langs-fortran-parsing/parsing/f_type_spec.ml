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
  | Character
  | Complex
  | DoublePrecision
  | Integer
  | Logical
  | Real
  | Type of name
  | Byte            (* some Fortran77 compilers support byte type *)
  | DoubleComplex   (* some compilers support double complex type *)
  | Derived of name (* F2003 *)
  | Class of name   (* F2003 *)
  | PpMacroTypeSpec of name

let to_string = function
  | Character       -> "Character"
  | Complex         -> "Complex"
  | DoublePrecision -> "DoublePrecision"
  | Integer         -> "Integer"
  | Logical         -> "Logical"
  | Real            -> "Real"
  | Type n          -> "Type:"^n
  | Byte            -> "Byte"
  | DoubleComplex   -> "DoubleComplex"
  | Derived n       -> "Derived:"^n
  | Class n         -> "Class:"^n
  | PpMacroTypeSpec n -> "PpMacroTypeSpec:"^n

let to_simple_string = function
  | Character       -> "character"
  | Complex         -> "complex"
  | DoublePrecision -> "double precision"
  | Integer         -> "integer"
  | Logical         -> "logical"
  | Real            -> "real"
  | Type n          -> "type("^n^")"
  | Byte            -> "byte"
  | DoubleComplex   -> "double complex"
  | Derived n       -> n
  | Class n         -> "class("^n^")"
  | PpMacroTypeSpec n -> n

let to_tag = function
  | Character       -> "Character", []
  | Complex         -> "Complex", []
  | DoublePrecision -> "DoublePrecision", []
  | Integer         -> "Integer", []
  | Logical         -> "Logical", []
  | Real            -> "Real", []
  | Type n          -> "Type", [name_attr_name,n]
  | Byte            -> "Byte", []
  | DoubleComplex   -> "DoubleComplex", []
  | Derived n       -> "Derived", [name_attr_name,n]
  | Class n         -> "Class", [name_attr_name,n]
  | PpMacroTypeSpec n -> "PpMacroTypeSpec", [name_attr_name,n]

let get_name = function
  | Type n 
  | Derived n
  | PpMacroTypeSpec n
  | Class n
    -> n
  | _ -> raise Not_found

let get_name_opt = function
  | Type n 
  | Derived n
  | PpMacroTypeSpec n
  | Class n
    -> Some n
  | _ -> None

let of_keyword kw =
  match String.lowercase_ascii kw with
  | "complex" -> Complex
  | "integer" -> Integer
  | "logical" -> Logical
  | "real"    -> Real
  | _ -> failwith "F_type_spec.of_keyword"

let anonymize = function
  | Type _            -> Type ""
  | Derived _         -> Derived ""
  | Class _           -> Class ""
  | PpMacroTypeSpec _ -> PpMacroTypeSpec ""
  | l -> l
