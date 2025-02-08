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
  | Err of label
  | Iomsg (* F2003 *)
  | Iostat
  | Unit

let to_string = function
  | Err lab     -> "Err:"^lab
  | Iomsg       -> "Iomsg"
  | Iostat      -> "Iostat"
  | Unit        -> "Unit"

let to_simple_string = function
  | Err lab     -> "err="^lab
  | Iomsg       -> "iomsg"
  | Iostat      -> "iostat"
  | Unit        -> "unit"

let to_tag = function
  | Err lab     -> "Err", [label_attr_name,lab]
  | Iomsg       -> "Iomsg", []
  | Iostat      -> "Iostat", []
  | Unit        -> "Unit", []

let get_label = function
  | Err lab -> lab
  | _ -> raise Not_found

let anonymize = function
  | Err _ -> Err ""
  | l -> l
