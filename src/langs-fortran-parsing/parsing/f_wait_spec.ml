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
  | End of label
  | Eor of label
  | Err of label
  | Id
  | Iomsg (* F2003 *)
  | Iostat
  | Unit

let to_string = function
  | End lab     -> "End:"^lab
  | Eor lab     -> "Eor:"^lab
  | Err lab     -> "Err:"^lab
  | Id          -> "Id"
  | Iomsg       -> "Iomsg"
  | Iostat      -> "Iostat"
  | Unit        -> "Unit"

let to_simple_string = function
  | End lab     -> "end="^lab
  | Eor lab     -> "eor="^lab
  | Err lab     -> "err="^lab
  | Id          -> "id"
  | Iomsg       -> "iomsg"
  | Iostat      -> "iostat"
  | Unit        -> "unit"

let to_tag = function
  | End lab     -> "End", [label_attr_name,lab]
  | Eor lab     -> "Eor", [label_attr_name,lab]
  | Err lab     -> "Err", [label_attr_name,lab]
  | Id          -> "Id", []
  | Iomsg       -> "Iomsg", []
  | Iostat      -> "Iostat", []
  | Unit        -> "Unit", []

let get_label = function
  | End lab 
  | Err lab
  | Eor lab -> lab
  | _ -> raise Not_found

let anonymize = function
  | End _ -> End ""
  | Eor _ -> Eor ""
  | Err _ -> Err ""
  | l -> l

