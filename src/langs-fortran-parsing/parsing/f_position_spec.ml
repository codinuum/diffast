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


let to_inquire_spec = function
  | Err lab     -> F_inquire_spec.Err lab
  | Iomsg       -> F_inquire_spec.Iomsg
  | Iostat      -> F_inquire_spec.Iostat
  | Unit        -> F_inquire_spec.Unit

let to_close_spec = function
  | Err lab     -> F_close_spec.Err lab
  | Iomsg       -> F_close_spec.Iomsg
  | Iostat      -> F_close_spec.Iostat
  | Unit        -> F_close_spec.Unit

let to_io_control_spec = function
  | Err lab     -> F_io_control_spec.Err lab
  | Iomsg       -> F_io_control_spec.Iomsg
  | Iostat      -> F_io_control_spec.Iostat
  | Unit        -> F_io_control_spec.Unit

let to_wait_spec = function
  | Err lab     -> F_wait_spec.Err lab
  | Iomsg       -> F_wait_spec.Iomsg
  | Iostat      -> F_wait_spec.Iostat
  | Unit        -> F_wait_spec.Unit

let to_flush_spec = function
  | Err lab     -> F_flush_spec.Err lab
  | Iomsg       -> F_flush_spec.Iomsg
  | Iostat      -> F_flush_spec.Iostat
  | Unit        -> F_flush_spec.Unit

let anonymize = function
  | Err _ -> Err ""
  | l -> l
