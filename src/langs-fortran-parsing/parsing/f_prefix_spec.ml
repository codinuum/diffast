(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2020 Chiba Institude of Technology

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

(*open Label_common*)

type t =
  | TypeSpec of F_type_spec.t
  | Recursive
  | Pure
  | Elemental
  | Impure
  | Module

  | Attributes of string (* PGI CUDA *)

let to_string = function
  | TypeSpec t -> F_type_spec.to_string t
  | Recursive  -> "Private"
  | Pure       -> "Pure"
  | Elemental  -> "Elemental"
  | Impure     -> "Impure"
  | Module     -> "Module"
  | Attributes a -> "Attributes:"^a

let to_simple_string = function
  | TypeSpec t -> F_type_spec.to_simple_string t
  | Recursive  -> "private"
  | Pure       -> "pure"
  | Elemental  -> "elemental"
  | Impure     -> "impure"
  | Module     -> "module"
  | Attributes a -> "attributes("^a^")"

let to_tag = function
  | TypeSpec t -> F_type_spec.to_tag t
  | Recursive  -> "PrivatePrefixSpec", []
  | Pure       -> "PurePrefixSpec", []
  | Elemental  -> "ElementalPrefixSpec", []
  | Impure     -> "ImpurePrefixSpec", []
  | Module     -> "ModulePrefixSpec", []
  | Attributes a -> "AttributesPrefixSpec", ["attribute",a]

let get_name = function
  | TypeSpec t -> F_type_spec.get_name t
  | _ -> raise Not_found

let get_name_opt = function
  | TypeSpec t -> F_type_spec.get_name_opt t
  | _ -> None

let of_keyword kw =
  match String.lowercase_ascii kw with
  | "recursive" -> Recursive
  | "pure"      -> Pure
  | "elemental" -> Elemental
  | "impure"    -> Impure

  | _ -> failwith "F_prefix_spec.of_keyword"

let of_keyword_name kw n =
  match String.lowercase_ascii kw with
  | "attributes" -> Attributes n

  | _ -> failwith "F_prefix_spec.of_keyword_name"

let anonymize = function
  | TypeSpec t -> TypeSpec (F_type_spec.anonymize t)
  | Attributes _ -> Attributes ""
  | l -> l

