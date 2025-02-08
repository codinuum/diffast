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
  | Public
  | Private
  | Bind         (* F2003 *)
  | Intent of F_intent_spec.t
  | Optional
  | Pointer
  | Protected (* GNU *)
  | Save

  | Weird of name


let to_string = function
  | Public      -> "Public"
  | Private     -> "Private"
  | Bind        -> "Bind"
  | Intent i    -> "Intent:"^(F_intent_spec.to_string i)
  | Optional    -> "Optional"
  | Pointer     -> "Pointer"
  | Protected   -> "Protected"
  | Save        -> "Save"

  | Weird n     -> "Weird:"^n

let to_simple_string = function
  | Public      -> "public"
  | Private     -> "private"
  | Bind        -> "bind"
  | Intent i    -> "intent("^(F_intent_spec.to_simple_string i)^")"
  | Optional    -> "optional"
  | Pointer     -> "pointer"
  | Protected   -> "protected"
  | Save        -> "save"

  | Weird n     -> "<weird:"^n^">"

let to_tag = function
  | Public      -> "Public", []
  | Private     -> "Private", []
  | Bind        -> "Bind", []
  | Intent i    -> "Intent", [spec_attr_name,F_intent_spec.to_string i]
  | Optional    -> "Optional", []
  | Pointer     -> "Pointer", []
  | Protected   -> "Protected", []
  | Save        -> "Save", []

  | Weird n     -> "Weird", [name_attr_name,n]


let of_keyword kw =
  match String.lowercase_ascii kw with
  | "protected" -> Protected

  | _ -> Weird kw

let anonymize = function
  | Weird _     -> Weird ""
  | l -> l
