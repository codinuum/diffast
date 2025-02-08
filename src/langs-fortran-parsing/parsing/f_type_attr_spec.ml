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
  | Private
  | Public
  | Abstract
  | Bind
  | Extends of name

let to_string = function
  | Private   -> "Private"
  | Public    -> "Public"
  | Abstract  -> "Abstract"
  | Bind      -> "Bind"
  | Extends n -> "Extends:"^n

let to_simple_string = function
  | Private   -> "private"
  | Public    -> "public"
  | Abstract  -> "abstract"
  | Bind      -> "bind(C)"
  | Extends n -> Printf.sprintf "extends(%s)" n

let to_tag = function
  | Private   -> "Private", []
  | Public    -> "Public", []
  | Abstract  -> "Abstract", []
  | Bind      -> "Bind", []
  | Extends n -> "Extends", [name_attr_name,n]

let anonymize = function
  | Extends _ -> Extends ""
  | l -> l

