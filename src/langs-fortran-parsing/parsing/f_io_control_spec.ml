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
  | Advance
  | Asynchronous      (* F2003 *)
  | Blank             (* F2003 *)
  | Decimal     (* F2003 *)
  | Delim      (* F2003 *)
  | End of label
  | Eor of label
  | Err of label
  | Fmt
  | Id      (* F2003 *)
  | Iomsg (* F2003 *)
  | Iostat
  | Nml of name
  | Num      (* IBM *)
  | Pad      (* F2003 *)
  | Pos   (* F2003 *)
  | PreconnectedUnit
  | Rec
  | Round      (* F2003 *)
  | Sign      (* F2003 *)
  | Size
  | Unit

let to_string = function
  | Advance -> "Advance"
  | Asynchronous -> "Asynchronous"
  | Blank   -> "Blank"
  | Decimal -> "Decimal"
  | Delim   -> "Delim"
  | End lab -> "End:"^lab
  | Eor lab -> "Eor:"^lab
  | Err lab -> "Err:"^lab
  | Fmt     -> "Fmt"
  | Id      -> "Id"
  | Iomsg   -> "Iomsg"
  | Iostat  -> "Iostat"
  | Nml n   -> "Nml:"^n
  | Num     -> "Num"
  | Pad     -> "Pad"
  | Pos     -> "Pos"
  | PreconnectedUnit -> "PreconnectedUnit"
  | Rec     -> "Rec"
  | Round   -> "Round"
  | Sign    -> "Sign"
  | Size    -> "Size"
  | Unit    -> "Unit"

let to_simple_string = function
  | Advance -> "advance"
  | Asynchronous -> "asynchronous"
  | Blank   -> "blank"
  | Decimal -> "decimal"
  | Delim   -> "delim"
  | End lab -> "end="^lab
  | Eor lab -> "eor="^lab
  | Err lab -> "err="^lab
  | Fmt     -> "fmt"
  | Id      -> "id"
  | Iomsg   -> "iomsg"
  | Iostat  -> "iostat"
  | Nml n   -> "nml="^n
  | Num     -> "num"
  | Pad     -> "pad"
  | Pos     -> "pos"
  | PreconnectedUnit -> "unit=*"
  | Rec     -> "rec"
  | Round   -> "round"
  | Sign    -> "sign"
  | Size    -> "size"
  | Unit    -> "unit"

let to_tag = function
  | Advance -> "Advance", []
  | Asynchronous -> "Asynchronous", []
  | Blank   -> "Blank", []
  | Decimal -> "Decimal", []
  | Delim   -> "Delim", []
  | End lab -> "End", [label_attr_name,lab]
  | Eor lab -> "Eor", [label_attr_name,lab]
  | Err lab -> "Err", [label_attr_name,lab]
  | Fmt     -> "Fmt", []
  | Id      -> "Id", []
  | Iomsg   -> "Iomsg", []
  | Iostat  -> "Iostat", []
  | Nml n   -> "Nml", [name_attr_name,n]
  | Num     -> "Num", []
  | Pad     -> "Pad", []
  | Pos     -> "Pos", []
  | PreconnectedUnit -> "PreconnectedUnit", []
  | Rec     -> "Rec", []
  | Round   -> "Round", []
  | Sign    -> "Sign", []
  | Size    -> "Size", []
  | Unit    -> "Unit", []

let get_name = function
  | Nml n   -> n
  | _ -> raise Not_found

let get_name_opt = function
  | Nml n   -> Some n
  | _ -> None

let get_label = function
  | End lab 
  | Err lab
  | Eor lab -> lab
  | _ -> raise Not_found

let of_keyword kw =
  match String.lowercase_ascii kw with
  | "advance" -> Advance
  | "blank"   -> Blank
  | "decimal" -> Decimal
  | "delim"   -> Delim
  | "id"      -> Id
  | "num"     -> Num
  | "pad"     -> Pad
  | "pos"     -> Pos
  | "rec"     -> Rec
  | "round"   -> Round
  | "sign"    -> Sign
  | "size"    -> Size

  | _ -> failwith "F_io_control_spec.of_keyword"

let anonymize = function
  | Nml _ -> Nml ""
  | Err _ -> Err ""
  | End _ -> End ""
  | Eor _ -> Eor ""
  | l -> l
