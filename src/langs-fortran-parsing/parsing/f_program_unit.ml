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
  | MainProgram of name option
  | FunctionSubprogram of name
  | SubroutineSubprogram of name
  | Module of name
  | Submodule of name
  | BlockData of name option

let to_string = function
  | MainProgram n_opt      -> "MainProgram"^(string_opt_to_string ~prefix:":" n_opt)
  | FunctionSubprogram n   -> "FunctionSubprogram:"^n
  | SubroutineSubprogram n -> "SubroutineSubprogram:"^n
  | Module n               -> "Module:"^n
  | Submodule n            -> "Submodule:"^n
  | BlockData n_opt        -> "BlockData"^(string_opt_to_string ~prefix:":" n_opt)

let to_simple_string = function
  | MainProgram n_opt      -> "<main-program"^(string_opt_to_string ~prefix:":" n_opt)^">"
  | FunctionSubprogram n   -> "<function-subprogram:"^n^">"
  | SubroutineSubprogram n -> "<subroutine-subprogram:"^n^">"
  | Module n               -> "<module:"^n^">"
  | Submodule n            -> "<submodule:"^n^">"
  | BlockData n_opt        -> "<blockdata"^(string_opt_to_string ~prefix:":" n_opt)^">"

let to_tag = function
  | MainProgram n_opt      -> "MainProgram", (string_opt_to_attr name_attr_name n_opt)
  | FunctionSubprogram n   -> "FunctionExternalSubprogram", [name_attr_name,n]
  | SubroutineSubprogram n -> "SubroutineExternalSubprogram", [name_attr_name,n]
  | Module n               -> "Module", [name_attr_name,n]
  | Submodule n            -> "Submodule", [name_attr_name,n]
  | BlockData n_opt        -> "BlockData", (string_opt_to_attr name_attr_name n_opt)

let get_name = function
  | MainProgram n_opt      
  | BlockData n_opt        -> begin 
      match n_opt with 
      | Some n -> n 
      | _ -> raise Not_found 
  end
  | FunctionSubprogram n   
  | SubroutineSubprogram n 
  | Module n
  | Submodule n            -> n

let get_name_opt = function
  | MainProgram n_opt      
  | BlockData n_opt        -> n_opt
  | FunctionSubprogram n   
  | SubroutineSubprogram n 
  | Module n
  | Submodule n            -> Some n

let anonymize = function
  | MainProgram _          -> MainProgram None
  | FunctionSubprogram _   -> FunctionSubprogram ""
  | SubroutineSubprogram _ -> SubroutineSubprogram ""
  | Module _               -> Module ""
  | Submodule _            -> Submodule ""
  | BlockData _            -> BlockData None

