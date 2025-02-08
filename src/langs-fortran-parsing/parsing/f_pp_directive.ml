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

module H = F_header_file

type branch = 
  | If of string
  | Elif of string
  | Ifdef of name
  | Ifndef of name
  | Else
  | Endif of branch * int (* paren level *)

let rec branch_to_string = function
  | If c     -> "If:"^c
  | Elif c   -> "Elif:"^c
  | Ifdef n  -> "Ifdef:"^n
  | Ifndef n -> "Ifndef:"^n
  | Else     -> "Else"
  | Endif(b, p) -> "Endif:"^(branch_to_string b)^":"^(string_of_int p)

let branch_to_simple_string = function
  | If c     -> "#if "^c
  | Elif c   -> "#elif "^c
  | Ifdef n  -> "#ifdef "^n
  | Ifndef n -> "#ifndef "^n
  | Else     -> "#else"
  | Endif _  -> "#endif"

let branch_to_tag = function
  | If c     -> "PpIf", ["cond",XML.encode_string c]
  | Elif c   -> "PpElif", ["cond",XML.encode_string c]
  | Ifdef n  -> "PpIfdef", [name_attr_name,n]
  | Ifndef n -> "PpIfndef", [name_attr_name,n]
  | Else     -> "PpElse", []
  | Endif _  -> "PpEndif", []

let length_of_branch = function
  | If c     -> 3 + (String.length c)
  | Elif c   -> 5 + (String.length c)
  | Ifdef n  -> 6 + (String.length n)
  | Ifndef n -> 7 + (String.length n)
  | Else     -> 5
  | Endif _  -> 6

type message =
  | Error   of string
  | Warning of string

let message_to_string = function
  | Error m   -> "Error:"^m
  | Warning m -> "Warning:"^m

let message_to_simple_string = function
  | Error m   -> "#error "^m
  | Warning m -> "#warning "^m

let message_to_tag = function
  | Error m   -> "PpError", ["message",XML.encode_string m]
  | Warning m -> "PpWarning", ["message",XML.encode_string m]

let length_of_message = function
  | Error m   -> 6 + (String.length m)
  | Warning m -> 8 + (String.length m)


type _t =
  | Define of name * string
  | Undef of name
  | Include of H.t
  | Branch of branch
  | Message of message
  | Unknown of string * string

let _to_string = function
  | Define(n, b)  -> "Define:"^n^":"^b
  | Undef n       -> "Undef:"^n
  | Include h     -> "Include:"^(H.to_string h)
  | Branch b      -> "Branch:"^(branch_to_string b)
  | Message m     -> "Message:"^(message_to_string m)
  | Unknown(d, r) -> "Unknown:"^d^":"^r

let _to_simple_string = function
  | Define(n, b)  -> "#define "^n^" "^b
  | Undef n       -> "#undef "^n
  | Include h     -> "#include "^(H.to_rep h)
  | Branch b      -> branch_to_simple_string b
  | Message m     -> message_to_simple_string m
  | Unknown(d, r) -> d^" "^r

let _to_tag = function
  | Define(n, b)  -> "PpDefine", [name_attr_name,n;"body",XML.encode_string b]
  | Undef n       -> "PpUndef", [name_attr_name,n]
  | Include h     -> "PpInclude", (H.get_attrs h)
  | Branch b      -> branch_to_tag b
  | Message m     -> message_to_tag m
  | Unknown(d, r) -> "PpUnknown", [name_attr_name,d;"rest",XML.encode_string r]

let _get_name = function
  | Define(n, _)
  | Undef n 
  | Branch (
    Ifdef n 
  | Ifndef n) -> n
  | Include h -> H.get_name h
  | _ -> raise Not_found

let _get_name_opt = function
  | Define(n, _)
  | Undef n 
  | Branch (
    Ifdef n 
  | Ifndef n) -> Some n
  | Include h -> H.get_name_opt h
  | _ -> None

type t = { mutable pp_context : Context.tag;
           pp_label   : _t;
         }

let mk ?(context=Context.Tunknown) l = { pp_context=context;
                                         pp_label=l;
                                       }

let get_context lab = lab.pp_context

let set_context c lab = lab.pp_context <- c

let is_specification_part lab = 
  match lab.pp_context with
  | Context.Tspecification_part -> true
  | _ -> false

let is_execution_part lab = 
  match lab.pp_context with
  | Context.Texecution_part -> true
  | _ -> false

let to_string { pp_context=c;
                pp_label=l;
              } = 
  (_to_string l)^"@"^(Context.tag_to_string c)

let to_simple_string lab = _to_simple_string lab.pp_label

let to_tag lab = _to_tag lab.pp_label

let get_name lab = _get_name lab.pp_label

let get_name_opt lab = _get_name_opt lab.pp_label

let anonymize_branch = function
  | If _     -> If ""
  | Elif _   -> Elif ""
  | Ifdef _  -> Ifdef ""
  | Ifndef _ -> Ifndef ""
  | Endif _  -> Endif (If "", 0)
  | l -> l

let anonymize_message = function
  | Error _   -> Error ""
  | Warning _ -> Warning ""

let _anonymize = function
  | Define(_, _)  -> Define("", "")
  | Undef _       -> Undef ""
  | Include h     -> Include (F_header_file.anonymize h)
  | Branch b      -> Branch (anonymize_branch b)
  | Message m     -> Message (anonymize_message m)
  | Unknown(d, _) -> Unknown(d, "")

let anonymize {pp_context=c;pp_label=l} = {pp_context=c;pp_label=_anonymize l}
