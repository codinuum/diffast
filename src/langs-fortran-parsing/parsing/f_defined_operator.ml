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
  | DefinedOp of string
  | DefinedUnaryOp of string
  | DefinedBinaryOp of string

let to_string = function
  | DefinedOp s       -> "DefinedOp:"^s
  | DefinedUnaryOp s  -> "DefinedUnaryOp:"^s
  | DefinedBinaryOp s -> "DefinedBinaryOp:"^s

let to_simple_string = function
  | DefinedOp s       
  | DefinedUnaryOp s  
  | DefinedBinaryOp s -> s

let to_tag = function
  | DefinedOp s       -> "DefinedOp", [name_attr_name,s]
  | DefinedUnaryOp s  -> "DefinedUnaryOp", [name_attr_name,s]
  | DefinedBinaryOp s -> "DefinedBinaryOp", [name_attr_name,s]

let get_name = function
  | DefinedOp s
  | DefinedUnaryOp s
  | DefinedBinaryOp s -> s

let get_name_opt = function
  | DefinedOp s
  | DefinedUnaryOp s
  | DefinedBinaryOp s -> Some s

let mk s = DefinedOp s
let mku s = DefinedUnaryOp s
let mkb s = DefinedBinaryOp s

let anonymize = function
  | DefinedOp _       -> DefinedOp ""
  | DefinedUnaryOp _  -> DefinedUnaryOp ""
  | DefinedBinaryOp _ -> DefinedBinaryOp ""

