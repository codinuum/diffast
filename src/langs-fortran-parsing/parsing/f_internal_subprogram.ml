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
  | FunctionSubprogram of name
  | SubroutineSubprogram of name

let to_string = function
  | FunctionSubprogram n   -> "FunctionSubprogram:"^n
  | SubroutineSubprogram n -> "SubroutineSubprogram:"^n

let to_simple_string = function
  | FunctionSubprogram n   -> "<function-subprogram:"^n^">"
  | SubroutineSubprogram n -> "<subroutine-subprogram:"^n^">"

let to_tag = function
  | FunctionSubprogram n   -> "FunctionInternalSubprogram", [name_attr_name,n]
  | SubroutineSubprogram n -> "SubroutineInternalSubprogram", [name_attr_name,n]

let get_name = function
  | FunctionSubprogram n   
  | SubroutineSubprogram n -> n

let get_name_opt = function
  | FunctionSubprogram n   
  | SubroutineSubprogram n -> Some n

let anonymize = function
  | FunctionSubprogram _   -> FunctionSubprogram ""
  | SubroutineSubprogram _ -> SubroutineSubprogram ""
