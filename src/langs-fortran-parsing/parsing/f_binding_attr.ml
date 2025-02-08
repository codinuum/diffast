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
  | Pass of name
  | Nopass
  | NonOverridable
  | Deferred
  | Private
  | Public

let to_string = function
  | Pass n         -> "Pass:"^n
  | Nopass         -> "Nopass"
  | NonOverridable -> "NonOverridable"
  | Deferred       -> "Deferred"
  | Private        -> "Private"
  | Public         -> "Public"

let to_simple_string = function
  | Pass n         -> "pass("^n^")"
  | Nopass         -> "nopass"
  | NonOverridable -> "non_overridable"
  | Deferred       -> "deferred"
  | Private        -> "private"
  | Public         -> "public"

let to_tag = function
  | Pass n         -> "Pass", [name_attr_name,n]
  | Nopass         -> "Nopass", []
  | NonOverridable -> "NonOverridable", []
  | Deferred       -> "Deferred", []
  | Private        -> "Private", []
  | Public         -> "Public", []

let get_name = function
  | Pass n         -> n
  | _ -> raise Not_found

let get_name_opt = function
  | Pass n         -> Some n
  | _ -> None

let anonymize = function
  | Pass _ -> Pass ""
  | l -> l
