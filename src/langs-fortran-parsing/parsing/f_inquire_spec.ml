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
  | Access
  | Action
  | Asynch       (* IBM *)
  | Asynchronous (* F2003 *)
  | Blank
  | Decimal      (* F2003 *)
  | Delim
  | Direct
  | Encoding     (* F2003 *)
  | Err of label
  | Exist
  | File
  | Form
  | Formatted
  | Id           (* F2003 *)
  | Iomsg        (* F2003 *)
  | Iostat
  | Name            
  | Named
  | Nextrec
  | Number
  | Opened
  | Pad
  | Pending       (* F2003 *)
  | Pos           (* F2003 *)
  | Position
  | Read
  | Readwrite
  | Recl
  | Round
  | Sequential
  | Sign          (* F2003 *)
  | Size          (* F2003 *)
  | Stream        (* F2003 *)
  | Strid         (* Apollo *)
  | Unformatted
  | Unit
  | Write

  | Binary          (* Compaq Fortran *)
  | Buffered        (* Compaq Fortran *)
  | Blocksize       (* Compaq Fortran *)
  | Carriagecontrol (* Compaq Fortran *)
  | Convert         (* Compaq Fortran *)
  | Defaultfile     (* Compaq Fortran *)
  | Iofocus         (* Compaq Fortran *)
  | Mode            (* Compaq Fortran *)
  | Organization    (* Compaq Fortran *)
  | Recordsize      (* Compaq Fortran *)
  | Recordtype      (* Compaq Fortran *)
  | Share           (* Compaq Fortran *)

let to_string = function
  | Access      -> "Access"
  | Action      -> "Action"
  | Asynch       -> "Asynch"
  | Asynchronous -> "Asynchronous"
  | Blank       -> "Blank"
  | Decimal     -> "Decimal"
  | Delim       -> "Delim"
  | Direct      -> "Direct"
  | Encoding    -> "Encoding"
  | Err lab     -> "Err:"^lab
  | Exist       -> "Exist"
  | File        -> "File"
  | Form        -> "Form"
  | Formatted   -> "Formatted"
  | Id          -> "Id"
  | Iomsg       -> "Iomsg"
  | Iostat      -> "Iostat"
  | Name        -> "Name"
  | Named       -> "Named"
  | Nextrec     -> "Nextrec"
  | Number      -> "Number"
  | Opened      -> "Opened"
  | Pad         -> "Pad"
  | Pending     -> "Pending"
  | Pos         -> "Pos"
  | Position    -> "Position"
  | Read        -> "Read"
  | Readwrite   -> "Readwrite"
  | Recl        -> "Recl"
  | Round       -> "Round"
  | Sequential  -> "Sequential"
  | Sign        -> "Sign"
  | Size        -> "Size"
  | Stream      -> "Stream"
  | Strid       -> "Strid"
  | Unformatted -> "Unformatted"
  | Unit        -> "Unit"
  | Write       -> "Write"

  | Binary          -> "Binary"
  | Blocksize       -> "Blocksize"
  | Buffered        -> "Buffered"
  | Carriagecontrol -> "Carriagecontrol"
  | Convert         -> "Convert"
  | Defaultfile     -> "Defaultfile"
  | Iofocus         -> "Iofocus"
  | Mode            -> "Mode"
  | Organization    -> "Organization"
  | Recordsize      -> "Recordsize"
  | Recordtype      -> "Recordtype"
  | Share           -> "Share"

let to_simple_string = function
  | Access      -> "access"
  | Action      -> "action"
  | Asynch       -> "asynch"
  | Asynchronous -> "asynchronous"
  | Blank       -> "blank"
  | Decimal     -> "decimal"
  | Delim       -> "delim"
  | Direct      -> "direct"
  | Encoding    -> "encoding"
  | Err lab     -> "err="^lab
  | Exist       -> "exist"
  | File        -> "file"
  | Form        -> "form"
  | Formatted   -> "formatted"
  | Id          -> "id"
  | Iomsg       -> "iomsg"
  | Iostat      -> "iostat"
  | Name        -> "name"
  | Named       -> "named"
  | Nextrec     -> "nextrec"
  | Number      -> "number"
  | Opened      -> "opened"
  | Pad         -> "pad"
  | Pending     -> "pending"
  | Pos         -> "pos"
  | Position    -> "position"
  | Read        -> "read"
  | Readwrite   -> "readwrite"
  | Recl        -> "recl"
  | Round       -> "round"
  | Sequential  -> "sequential"
  | Sign        -> "sign"
  | Size        -> "size"
  | Stream      -> "stream"
  | Strid       -> "strid"
  | Unformatted -> "unformatted"
  | Unit        -> "unit"
  | Write       -> "write"

  | Binary          -> "binary"
  | Blocksize       -> "blocksize"
  | Buffered        -> "buffered"
  | Carriagecontrol -> "carriagecontrol"
  | Convert         -> "convert"
  | Defaultfile     -> "defaultfile"
  | Iofocus         -> "iofocus"
  | Mode            -> "mode"
  | Organization    -> "organization"
  | Recordsize      -> "recordsize"
  | Recordtype      -> "recordtype"
  | Share           -> "share"

let to_tag = function
  | Access      -> "Access", []
  | Action      -> "Action", []
  | Asynch      -> "Asynch", []
  | Asynchronous -> "Asynchronous", []
  | Blank       -> "Blank", []
  | Decimal     -> "Decimal", []
  | Delim       -> "Delim", []
  | Direct      -> "Direct", []
  | Encoding    -> "Encoding", []
  | Err lab     -> "Err", [label_attr_name,lab]
  | Exist       -> "Exist", []
  | File        -> "File", []
  | Form        -> "Form", []
  | Formatted   -> "Formatted", []
  | Id          -> "Id", []
  | Iomsg       -> "Iomsg", []
  | Iostat      -> "Iostat", []
  | Name        -> "NameInquireSpec", []
  | Named       -> "Named", []
  | Nextrec     -> "Nextrec", []
  | Number      -> "Number", []
  | Opened      -> "Opened", []
  | Pad         -> "Pad", []
  | Pending     -> "Pending", []
  | Pos         -> "Pos", []
  | Position    -> "Position", []
  | Read        -> "Read", []
  | Readwrite   -> "Readwrite", []
  | Recl        -> "Recl", []
  | Round       -> "Round", []
  | Sequential  -> "Sequential", []
  | Sign        -> "Sign", []
  | Size        -> "Size", []
  | Stream      -> "Stream", []
  | Strid       -> "Strid", []
  | Unformatted -> "Unformatted", []
  | Unit        -> "Unit", []
  | Write       -> "Write", []

  | Binary          -> "Binary", []
  | Blocksize       -> "Blocksize", []
  | Buffered        -> "Buffered", []
  | Carriagecontrol -> "Carriagecontrol", []
  | Convert         -> "Convert", []
  | Defaultfile     -> "Defaultfile", []
  | Iofocus         -> "Iofocus", []
  | Mode            -> "Mode", []
  | Organization    -> "Organization", []
  | Recordsize      -> "Recordsize", []
  | Recordtype      -> "Recordtype", []
  | Share           -> "Share", []

let get_label = function
  | Err lab -> lab
  | _ -> raise Not_found



let of_keyword kw =
  match String.lowercase_ascii kw with
  | "access"      -> Access
  | "action"      -> Action
  | "blank"       -> Blank
  | "delim"       -> Delim
  | "decimal"     -> Decimal
  | "direct"      -> Direct
  | "encoding"    -> Encoding
  | "exist"       -> Exist
  | "form"        -> Form
  | "formatted"   -> Formatted
  | "id"          -> Id
  | "named"       -> Named
  | "nextrec"     -> Nextrec
  | "number"      -> Number
  | "opened"      -> Opened
  | "pad"         -> Pad
  | "pending"     -> Pending
  | "pos"         -> Pos
  | "position"    -> Position
  | "readwrite"   -> Readwrite
  | "recl"        -> Recl
  | "round"       -> Round
  | "sequential"  -> Sequential
  | "sign"        -> Sign
  | "size"        -> Size
  | "stream"      -> Stream
  | "strid"       -> Strid
  | "unformatted" -> Unformatted

  | "binary"          -> Binary
  | "blocksize"       -> Blocksize
  | "buffered"        -> Buffered
  | "carriagecontrol" -> Carriagecontrol
  | "convert"         -> Convert
  | "defaultfile"     -> Defaultfile
  | "iofocus"         -> Iofocus
  | "mode"            -> Mode
  | "organization"    -> Organization
  | "recordsize"      -> Recordsize
  | "recordtype"      -> Recordtype
  | "share"           -> Share

  | _ -> failwith "F_inquire_spec.of_keyword"

let anonymize = function
  | Err _ -> Err ""
  | l -> l

