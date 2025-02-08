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
  | PositionEditDesc of string
  | EndOfRecord of int option
  | Terminate
  | SignEditDesc of string
  | ScaleFactor of int
  | BlankInterpEditDesc of string
  | Unknown of string

let to_string = function
  | PositionEditDesc s    -> "PositionEditDesc:"^s
  | EndOfRecord i_opt     -> "EndOfRecord"^(int_opt_to_string ~prefix:":" i_opt)
  | Terminate             -> "Terminate"
  | SignEditDesc s        -> "SignEditDesc:"^s
  | ScaleFactor i         -> "ScaleFactor:"^(string_of_int i)
  | BlankInterpEditDesc s -> "BlankInterpEditDesc:"^s
  | Unknown s             -> "Unknown:"^s

let to_simple_string = function
  | PositionEditDesc s    -> s
  | EndOfRecord i_opt     -> (int_opt_to_string i_opt)^"/"
  | Terminate             -> ":"
  | SignEditDesc s        -> s
  | ScaleFactor i         -> (string_of_int i)^"p"
  | BlankInterpEditDesc s -> s
  | Unknown s             -> s

let to_tag = function
  | PositionEditDesc s    -> "PositionEditDesc", [desc_attr_name,s]
  | EndOfRecord i_opt     -> "EndOfRecord", (int_opt_to_attr "repeat" i_opt)
  | Terminate             -> "Terminate", []
  | SignEditDesc s        -> "SignEditDesc", [desc_attr_name,s]
  | ScaleFactor i         -> "ScaleFactor", ["k",string_of_int i]
  | BlankInterpEditDesc s -> "BlankInterpEditDesc", [desc_attr_name,s]
  | Unknown s             -> "Unknown", [desc_attr_name,s]

let anonymize = function
  | PositionEditDesc _    -> PositionEditDesc ""
  | SignEditDesc _        -> SignEditDesc ""
  | BlankInterpEditDesc _ -> BlankInterpEditDesc ""
  | ScaleFactor _         -> ScaleFactor 0
  | EndOfRecord _         -> EndOfRecord None
  | Unknown _             -> Unknown ""
  | l -> l

