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
  | In
  | Out
  | Inout

let to_string = function
  | In    -> "In"
  | Out   -> "Out"
  | Inout -> "Inout"

let to_simple_string = function
  | In    -> "in"
  | Out   -> "out"
  | Inout -> "inout"

let to_tag = function
  | In    -> "In", []
  | Out   -> "Out", []
  | Inout -> "Inout", []

let of_keyword kw =
  match String.lowercase_ascii kw with
  | "in"    -> In
  | "out"   -> Out
  | "inout" -> Inout
  | _ -> failwith "F_intent_spec.of_keyword"


