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

open Label_common

type t =
  | Parameter
  | Public
  | Private
  | Allocatable
  | Dimension
  | External
  | Intent of F_intent_spec.t
  | Intrinsic
  | Optional
  | Pointer
  | Save
  | Target

  | Asynchronous (* F2003 *)
  | Bind         (* F2003 *)
  | Protected    (* F2003 *)
  | Value        (* F2003 *)
  | Volatile     (* F2003 *)

  | Codimension  (* F2008 *)
  | Contiguous   (* F2008 *)

  | Automatic    (* Compaq/Intel and IBM *)
  | Static       (* Compaq/Intel and IBM *)

  | Device   (* PGI(CUDA) *)
  | Managed  (* PGI(CUDA) *)
  | Constant (* PGI(CUDA) *)
  | Shared   (* PGI(CUDA) *)
  | Pinned   (* PGI(CUDA) *)
  | Texture  (* PGI(CUDA) *)

let to_string = function
  | Parameter   -> "Parameter"
  | Public      -> "Public"
  | Private     -> "Private"
  | Allocatable -> "Allocatable"
  | Dimension   -> "Dimension"
  | External    -> "External"
  | Intent i    -> "Intent:"^(F_intent_spec.to_string i)
  | Intrinsic   -> "Intrinsic"
  | Optional    -> "Optional"
  | Pointer     -> "Pointer"
  | Save        -> "Save"
  | Target      -> "Target"

  | Asynchronous -> "Asynchronous"
  | Bind         -> "Bind"
  | Protected    -> "Protected"
  | Value        -> "Value"
  | Volatile     -> "Volatile"

  | Codimension  -> "Codimension"
  | Contiguous   -> "Contiguous"

  | Automatic    -> "Automatic"
  | Static       -> "Static"

  | Device   -> "Device"
  | Managed  -> "Managed"
  | Constant -> "Constant"
  | Shared   -> "Shared"
  | Pinned   -> "Pinned"
  | Texture  -> "Texture"


let to_simple_string = function
  | Parameter   -> "parameter"
  | Public      -> "public"
  | Private     -> "private"
  | Allocatable -> "allocatable"
  | Dimension   -> "dimension"
  | External    -> "external"
  | Intent i    -> "intent("^(F_intent_spec.to_simple_string i)^")"
  | Intrinsic   -> "intrinsic"
  | Optional    -> "optional"
  | Pointer     -> "pointer"
  | Save        -> "save"
  | Target      -> "target"

  | Asynchronous -> "asynchronous"
  | Bind         -> "bind"
  | Protected    -> "protected"
  | Value        -> "value"
  | Volatile     -> "volatile"

  | Codimension  -> "codimension"
  | Contiguous   -> "contiguous"

  | Automatic    -> "automatic"
  | Static       -> "static"

  | Device   -> "device"
  | Managed  -> "managed"
  | Constant -> "constant"
  | Shared   -> "shared"
  | Pinned   -> "pinned"
  | Texture  -> "texture"

let to_tag = function
  | Parameter   -> "Parameter", []
  | Public      -> "Public", []
  | Private     -> "Private", []
  | Allocatable -> "Allocatable", []
  | Dimension   -> "Dimension", []
  | External    -> "External", []
  | Intent i    -> "Intent", [spec_attr_name,F_intent_spec.to_string i]
  | Intrinsic   -> "Intrinsic", []
  | Optional    -> "Optional", []
  | Pointer     -> "Pointer", []
  | Save        -> "Save", []
  | Target      -> "Target", []

  | Asynchronous -> "Asynchronous", []
  | Bind         -> "Bind", []
  | Protected    -> "Protected", []
  | Value        -> "Value", []
  | Volatile     -> "Volatile", []

  | Codimension  -> "Codimension", []
  | Contiguous   -> "Contiguous", []

  | Automatic    -> "Automatic", []
  | Static       -> "Static", []

  | Device   -> "Device", []
  | Managed  -> "Managed", []
  | Constant -> "Constant", []
  | Shared   -> "Shared", []
  | Pinned   -> "Pinned", []
  | Texture  -> "Texture", []


let of_keyword kw =
  match String.lowercase_ascii kw with
  | "external"   -> External
  | "protected"  -> Protected
  | "value"      -> Value
  | "volatile"   -> Volatile
  | "contiguous" -> Contiguous
  | "automatic"  -> Automatic
  | "static"     -> Static
  | "device"     -> Device
  | "managed"    -> Managed
  | "constant"   -> Constant
  | "shared"     -> Shared
  | "pinned"     -> Pinned
  | "texture"    -> Texture

  | _ -> failwith "F_attr_spec.of_keyword"
