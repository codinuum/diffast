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

type special_edit_desc = 
  | Dollar
  | Backslash
  | Plus
  | Zero
  | One
  | Blank

let special_edit_desc_to_string = function
  | Dollar    -> "Dollar"
  | Backslash -> "Backslash"
  | Plus      -> "Plus"
  | Zero      -> "Zero"
  | One       -> "One"
  | Blank     -> "Blank"

let special_edit_desc_to_simple_string = function
  | Dollar    -> "$"
  | Backslash -> "\\"
  | Plus      -> "+"
  | Zero      -> "0"
  | One       -> "1"
  | Blank     -> "<blank>"


type t =
  | DataEditDesc of int option * string
  | ControlEditDesc of F_control_edit_desc.t
  | CharStringEditDesc of string
  | FormatItemList of int option
  | SpecialEditDesc of special_edit_desc (* some Fortran77 compilers support $, <blank>, \, +, 0, 1 *)
  | VariableFormatDesc of int option * string (* Intel/Compaq *)
  | Macro of int option * string

let is_bare_vfe = function
  | VariableFormatDesc(i_opt, s) -> begin
      i_opt = None && s = ""
  end
  | _ -> false

let to_string = function
  | DataEditDesc(i_opt, s)       -> "DataEditDesc"^(int_opt_to_string ~prefix:":" i_opt)^":"^s
  | ControlEditDesc c            -> "ControlEditDesc."^(F_control_edit_desc.to_string c)
  | CharStringEditDesc s         -> "CharStringEditDesc:"^s
  | FormatItemList i_opt         -> "FormatItemList"^(int_opt_to_string ~prefix:":" i_opt)
  | SpecialEditDesc sd           -> "SpecialEditDesc:"^(special_edit_desc_to_string sd)
  | VariableFormatDesc(i_opt, s) -> 
      "VariableFormatDesc"^(int_opt_to_string ~prefix:":" i_opt)^(if s = "" then "" else ":"^s)
  | Macro(i_opt, id)             -> "Macro"^(int_opt_to_string ~prefix:":" i_opt)^":"^id

let to_simple_string = function
  | DataEditDesc(i_opt, s)       -> (int_opt_to_string i_opt)^s
  | ControlEditDesc c            -> F_control_edit_desc.to_simple_string c
  | CharStringEditDesc s         -> s
  | FormatItemList i_opt         -> (int_opt_to_string i_opt)^"<format-item-list>"
  | SpecialEditDesc sd           -> special_edit_desc_to_simple_string sd
  | VariableFormatDesc(i_opt, s) -> (int_opt_to_string i_opt)^s^"<>"
  | Macro(i_opt, id)             -> (int_opt_to_string i_opt)^" "^id

let to_tag = function
  | DataEditDesc(i_opt, s)       -> "DataEditDesc", (int_opt_to_attr "repeat" i_opt) @ [desc_attr_name,s]
  | ControlEditDesc c            -> F_control_edit_desc.to_tag c
  | CharStringEditDesc s         -> "CharStringEditDesc", [desc_attr_name,s]
  | FormatItemList i_opt         -> "FormatItemList", (int_opt_to_attr "repeat" i_opt)
  | SpecialEditDesc sd           -> "SpecialEditDesc", [desc_attr_name,special_edit_desc_to_string sd]
  | VariableFormatDesc(i_opt, s) -> "VariableFormatDesc", (int_opt_to_attr "repeat" i_opt) @ [desc_attr_name,s]
  | Macro(i_opt, id)             -> "MacroFormatItem", (name_attr_name,id)::(int_opt_to_attr "repeat" i_opt)

let anonymize = function
  | DataEditDesc(_, _)       -> DataEditDesc(None, "")
  | ControlEditDesc c        -> ControlEditDesc (F_control_edit_desc.anonymize c)
  | CharStringEditDesc _     -> CharStringEditDesc ""
  | FormatItemList _         -> FormatItemList None
  | SpecialEditDesc _        -> SpecialEditDesc Blank
  | VariableFormatDesc(_, _) -> VariableFormatDesc(None, "")
  | Macro(_, _)              -> Macro(None, "")

