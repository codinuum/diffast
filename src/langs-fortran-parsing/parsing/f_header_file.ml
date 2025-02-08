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
  | User of string (* quoted *)
  | System of string (* <...> *)
  | Macro of string * string option (* content *)
  | Generated of string (* not quoted *)

let get_unquoted quoted = 
  try
    String.sub quoted 1 ((String.length quoted) - 2)
  with
    e ->
      let _ = e in
      [%warn_log "%s" (Printexc.to_string e)];
      quoted

let to_string = function
  | User s   -> "User:"^s
  | System s -> "System:"^s
  | Macro(n, s_opt) -> "Macro:"^n^(string_opt_to_string ~prefix:":" s_opt)
  | Generated s -> "Generated:"^s

let to_path = function
  | User s   -> get_unquoted s
  | System s -> get_unquoted s
  | Macro(_, s_opt) -> begin
      match s_opt with
      | None -> "(unknown)"
      | Some s -> get_unquoted s
  end
  | Generated s -> s

let to_rep = function
  | User s   -> s
  | System s -> s
  | Macro(n, _) -> n
  | Generated s -> s

let get_attrs = function
  | User s   -> [path_attr_name,strlit_to_encoded_path s]
  | System s -> [path_attr_name,strlit_to_encoded_path s]
  | Macro(n, s_opt) -> 
      (name_attr_name,n)::
      (match s_opt with
      | None -> []
      | Some s -> [path_attr_name,strlit_to_encoded_path s]
      )
  | Generated s -> [path_attr_name,XML.encode_string s]

let length = function
  | User s   
  | System s -> String.length s
  | Macro(n, _) -> String.length n
  | Generated s -> String.length s

let get_name = function
  | Macro(n, _) -> n
  | _ -> raise Not_found

let get_name_opt = function
  | Macro(n, _) -> Some n
  | _ -> None

let mkuser s   = User s
let mksystem s = System s
let mkmacro ?(content=None) n  = Macro(n, content)
let mkgenerated s = Generated s

let anonymize = function
  | User _   -> User ""
  | System _ -> System ""
  | Macro _ -> Macro("", None)
  | Generated _ -> Generated ""

