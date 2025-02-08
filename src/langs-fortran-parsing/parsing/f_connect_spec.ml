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
  | Asynch        (* IBM *)
  | Asynchronous  (* F2003 *)
  | Blank
  | Decimal
  | Delim
  | Encoding
  | Err of label
  | File
  | Form
  | Iomsg         (* F2003 *)
  | Iostat
  | Newunit
  | Pad
  | Position
  | Recl
  | Round
  | Sign
  | Status
  | Unit

  | Associatevariable (* Compaq Fortran *)
  | Blocksize         (* Compaq Fortran *)
  | Buffercount       (* Compaq Fortran *)
  | Buffered          (* Compaq Fortran *)
  | Carriagecontrol   (* Compaq Fortran *)
  | Convert           (* Compaq Fortran *)
  | Defaultfile       (* Compaq Fortran *)
  | Dispose           (* Compaq Fortran *)
  | Iofocus           (* Compaq Fortran *)
  | Maxrec            (* Compaq Fortran *)
  | Mode              (* Compaq Fortran *)
  | Name              (* Compaq Fortran *)
  | Organization      (* Compaq Fortran *)
  | Readonly          (* Compaq Fortran *)
  | Recordsize        (* Compaq Fortran *)
  | Recordtype        (* Compaq Fortran *)
  | Share             (* Compaq Fortran *)
  | Shared            (* Compaq Fortran *)
  | Title             (* Compaq Fortran *)
  | Type              (* Compaq Fortran *)
  | Useropen          (* Compaq Fortran *)

let to_string = function
  | Access            -> "Access"
  | Action            -> "Action"
  | Asynch            -> "Asynch"
  | Asynchronous      -> "Asynchronous"
  | Blank             -> "Blank"
  | Decimal           -> "Decimal"
  | Delim             -> "Delim"
  | Encoding          -> "Encoding"
  | Err lab           -> "Err:"^lab
  | File              -> "File"
  | Form              -> "Form"
  | Iomsg             -> "Iomsg"
  | Iostat            -> "Iostat"
  | Newunit           -> "Newunit"
  | Pad               -> "Pad"
  | Position          -> "Position"
  | Recl              -> "Recl"
  | Round             -> "Round"
  | Sign              -> "Sign"
  | Status            -> "Status"
  | Unit              -> "Unit"

  | Associatevariable -> "Associatevariable"
  | Blocksize         -> "Blocksize"
  | Buffercount       -> "Buffercount"
  | Buffered          -> "Buffered"
  | Carriagecontrol   -> "Carriagecontrol"
  | Convert           -> "Convert"
  | Defaultfile       -> "Defaultfile"
  | Dispose           -> "Dispose"
  | Iofocus           -> "Iofocus"
  | Maxrec            -> "Maxrec"
  | Mode              -> "Mode"
  | Name              -> "Name"
  | Organization      -> "Organization"
  | Readonly          -> "Readonly"
  | Recordsize        -> "Recordsize"
  | Recordtype        -> "Recordtype"
  | Share             -> "Share"
  | Shared            -> "Shared"
  | Title             -> "Title"
  | Type              -> "Type"
  | Useropen          -> "Useropen"

let to_simple_string = function
  | Access            -> "access"
  | Action            -> "action"
  | Asynch            -> "asynch"
  | Asynchronous      -> "asynchronous"
  | Blank             -> "blank"
  | Decimal           -> "decimal"
  | Delim             -> "delim"
  | Encoding          -> "encoding"
  | Err lab           -> "err="^lab
  | File              -> "file"
  | Form              -> "form"
  | Iomsg             -> "iomsg"
  | Iostat            -> "iostat"
  | Newunit           -> "newunit"
  | Pad               -> "pad"
  | Position          -> "position"
  | Recl              -> "recl"
  | Round             -> "round"
  | Sign              -> "sign"
  | Status            -> "status"
  | Unit              -> "unit"

  | Associatevariable -> "associatevariable"
  | Blocksize         -> "blocksize"
  | Buffercount       -> "buffercount"
  | Buffered          -> "buffered"
  | Carriagecontrol   -> "carriagecontrol"
  | Convert           -> "convert"
  | Defaultfile       -> "defaultfile"
  | Dispose           -> "dispose"
  | Iofocus           -> "iofocus"
  | Maxrec            -> "maxrec"
  | Mode              -> "mode"
  | Name              -> "name"
  | Organization      -> "organization"
  | Readonly          -> "readonly"
  | Recordsize        -> "recordsize"
  | Recordtype        -> "recordtype"
  | Share             -> "share"
  | Shared            -> "shared"
  | Title             -> "title"
  | Type              -> "type"
  | Useropen          -> "useropen"

let to_tag = function
  | Access            -> "Access", []
  | Action            -> "Action", []
  | Asynch            -> "Asynch", []
  | Asynchronous      -> "Asynchronous", []
  | Blank             -> "Blank", []
  | Decimal           -> "Decimal", []
  | Delim             -> "Delim", []
  | Encoding          -> "Encoding", []
  | Err lab           -> "Err", [label_attr_name,lab]
  | File              -> "File", []
  | Form              -> "Form", []
  | Iomsg             -> "Iomsg", []
  | Iostat            -> "Iostat", []
  | Newunit           -> "Newunit", []
  | Pad               -> "Pad", []
  | Position          -> "Position", []
  | Recl              -> "Recl", []
  | Round             -> "Round", []
  | Sign              -> "Sign", []
  | Status            -> "Status", []
  | Unit              -> "Unit", []

  | Associatevariable -> "Associatevariable", []
  | Blocksize         -> "Blocksize", []
  | Buffercount       -> "Buffercount", []
  | Buffered          -> "Buffered", []
  | Carriagecontrol   -> "Carriagecontrol", []
  | Convert           -> "Convert", []
  | Defaultfile       -> "Defaultfile", []
  | Dispose           -> "Dispose", []
  | Iofocus           -> "Iofocus", []
  | Maxrec            -> "Maxrec", []
  | Mode              -> "Mode", []
  | Name              -> "Name", []
  | Organization      -> "Organization", []
  | Readonly          -> "Readonly", []
  | Recordsize        -> "Recordsize", []
  | Recordtype        -> "Recordtype", []
  | Share             -> "Share", []
  | Shared            -> "Shared", []
  | Title             -> "Title", []
  | Type              -> "Type", []
  | Useropen          -> "Useropen", []

let get_label = function
  | Err lab -> lab
  | _ -> raise Not_found



let to_inquire_spec = function
  | Access          -> F_inquire_spec.Access
  | Action          -> F_inquire_spec.Action
  | Asynch          -> F_inquire_spec.Asynch
  | Asynchronous    -> F_inquire_spec.Asynchronous
  | Blank           -> F_inquire_spec.Blank
  | Decimal         -> F_inquire_spec.Decimal
  | Delim           -> F_inquire_spec.Delim
  | Encoding        -> F_inquire_spec.Encoding
  | Err lab         -> F_inquire_spec.Err lab
  | File            -> F_inquire_spec.File
  | Form            -> F_inquire_spec.Form
  | Iomsg           -> F_inquire_spec.Iomsg
  | Iostat          -> F_inquire_spec.Iostat
  | Pad             -> F_inquire_spec.Pad
  | Position        -> F_inquire_spec.Position
  | Recl            -> F_inquire_spec.Recl
  | Round           -> F_inquire_spec.Round
  | Sign            -> F_inquire_spec.Sign
  | Unit            -> F_inquire_spec.Unit

  | Blocksize       -> F_inquire_spec.Blocksize
  | Buffered        -> F_inquire_spec.Buffered
  | Carriagecontrol -> F_inquire_spec.Carriagecontrol
  | Convert         -> F_inquire_spec.Convert
  | Defaultfile     -> F_inquire_spec.Defaultfile
  | Iofocus         -> F_inquire_spec.Iofocus
  | Mode            -> F_inquire_spec.Mode
  | Name            -> F_inquire_spec.Name
  | Organization    -> F_inquire_spec.Organization
  | Recordsize      -> F_inquire_spec.Recordsize
  | Recordtype      -> F_inquire_spec.Recordtype
  | Share           -> F_inquire_spec.Share

  | _ -> assert false

let of_keyword kw =
  match String.lowercase_ascii kw with
  | "access"       -> Access
  | "action"       -> Action
  | "asynch"       -> Asynch
  | "asynchronous" -> Asynchronous
  | "blank"        -> Blank
  | "decimal"      -> Decimal
  | "delim"        -> Delim
  | "encoding"     -> Encoding
  | "form"         -> Form
  | "newunit"      -> Newunit
  | "pad"          -> Pad
  | "position"     -> Position
  | "recl"         -> Recl
  | "round"        -> Round
  | "sign"         -> Sign

  | "associatevariable" -> Associatevariable
  | "blocksize"         -> Blocksize
  | "buffercount"       -> Buffercount
  | "buffered"          -> Buffered
  | "carriagecontrol"   -> Carriagecontrol
  | "convert"           -> Convert
  | "defaultfile"       -> Defaultfile
  | "dispose" | "disp"  -> Dispose
  | "iofocus"           -> Iofocus
  | "maxrec"            -> Maxrec
  | "mode"              -> Mode
  | "organization"      -> Organization
  | "organisation"      -> Organization (* ??? *)
  | "readonly"          -> Readonly
  | "recordsize"        -> Recordsize
  | "recordtype"        -> Recordtype
  | "share"             -> Share
  | "shared"            -> Shared
  | "title"             -> Title
  | "type"              -> Type
  | "useropen"          -> Useropen

  | _ -> failwith "F_connect_spec.of_keyword"

let anonymize = function
  | Err _ -> Err ""
  | l -> l

