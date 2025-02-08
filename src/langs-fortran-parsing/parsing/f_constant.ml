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
  | BozLiteralConstant of string
  | CharLiteralConstant of string
  | ComplexLiteralConstant of string * string
  | IntLiteralConstant of string
  | LogicalLiteralConstant of string
  | RealLiteralConstant of string

  | NamedConstant of name

  | HollerithConstant of string

  | PpMacroConstant of name

  | SignedIntLiteralConstant of string
  | SignedRealLiteralConstant of string

let to_string = function
  | BozLiteralConstant s         -> "BozLiteralConstant:"^s
  | CharLiteralConstant s        -> "CharLiteralConstant:"^s
  | ComplexLiteralConstant(r, i) -> "ComplexLiteralConstant:"^r^":"^i
  | IntLiteralConstant s         -> "IntLiteralConstant:"^s
  | LogicalLiteralConstant s     -> "LogicalLiteralConstant:"^s
  | RealLiteralConstant s        -> "RealLiteralConstant:"^s

  | NamedConstant n              -> "NamedConstant:"^n

  | HollerithConstant s          -> "HollerithConstant:"^s

  | PpMacroConstant n            -> "PpMacroConstant:"^n

  | SignedIntLiteralConstant s   -> "SignedIntLiteralConstant:"^s
  | SignedRealLiteralConstant s  -> "SignedRealLiteralConstant:"^s

let to_simple_string = function
  | BozLiteralConstant s         
  | CharLiteralConstant s        
  | IntLiteralConstant s         
  | LogicalLiteralConstant s     
  | RealLiteralConstant s        -> s
  | ComplexLiteralConstant(r, i) -> Printf.sprintf "(%s,%s)" r i

  | NamedConstant n              -> n

  | HollerithConstant s          -> s

  | PpMacroConstant n            -> n

  | SignedIntLiteralConstant s   -> s
  | SignedRealLiteralConstant s  -> s


let to_tag = function
  | BozLiteralConstant s         -> "BozLiteralConstant", [value_attr_name,XML.encode_string s]
  | CharLiteralConstant s        -> "CharLiteralConstant", [value_attr_name,XML.encode_string s]
  | ComplexLiteralConstant(r, i) -> "ComplexLiteralConstant", [value_attr_name,Printf.sprintf "(%s,%s)" r i]
  | IntLiteralConstant s         -> "IntLiteralConstant", [value_attr_name,s]
  | LogicalLiteralConstant s     -> "LogicalLiteralConstant", [value_attr_name,s]
  | RealLiteralConstant s        -> "RealLiteralConstant", [value_attr_name,s]

  | NamedConstant n              -> "NamedConstant", [name_attr_name,n]

  | HollerithConstant s          -> "HollerithConstant", [value_attr_name,XML.encode_string s]

  | PpMacroConstant n            -> "PpMacroConstant", [name_attr_name,n]

  | SignedIntLiteralConstant s   -> "SignedIntLiteralConstant", [value_attr_name,s]
  | SignedRealLiteralConstant s  -> "SignedRealLiteralConstant", [value_attr_name,s]

let get_name = function
  | NamedConstant n 
  | PpMacroConstant n
    -> n
  | _ -> raise Not_found

let get_name_opt = function
  | NamedConstant n 
  | PpMacroConstant n
    -> Some n
  | _ -> None

let get_value = function
  | BozLiteralConstant s         
  | CharLiteralConstant s        
  | IntLiteralConstant s         
  | LogicalLiteralConstant s     
  | RealLiteralConstant s        
  | HollerithConstant s
  | SignedIntLiteralConstant s
  | SignedRealLiteralConstant s
    -> s

  | ComplexLiteralConstant(r, i) -> Printf.sprintf "(%s,%s)" r i

  | NamedConstant _ | PpMacroConstant _ -> raise Not_found


let mkint s = IntLiteralConstant s
let mkreal s = RealLiteralConstant s
let mkboz s  = BozLiteralConstant s
let mkchar s = CharLiteralConstant s
let mkcomp(r, i) = ComplexLiteralConstant(r, i)
let mklogi s = LogicalLiteralConstant s
let mknamed n = NamedConstant n
let mkhollerith s = HollerithConstant s
let mkppm n = PpMacroConstant n
let mksint s = SignedIntLiteralConstant s
let mksreal s = SignedRealLiteralConstant s

let anonymize ?(more=false) = function
  | BozLiteralConstant _         -> BozLiteralConstant ""
  | CharLiteralConstant _        -> CharLiteralConstant ""
  | IntLiteralConstant _         -> IntLiteralConstant ""
  | LogicalLiteralConstant _     -> LogicalLiteralConstant ""
  | RealLiteralConstant _        -> RealLiteralConstant ""
  | ComplexLiteralConstant(_, _) -> ComplexLiteralConstant("", "")
  | NamedConstant _              -> NamedConstant ""
  | HollerithConstant _          -> begin
      if more then
        CharLiteralConstant ""
      else
        HollerithConstant ""
  end
  | PpMacroConstant _            -> PpMacroConstant ""
  | SignedIntLiteralConstant _   -> SignedIntLiteralConstant ""
  | SignedRealLiteralConstant _  -> SignedRealLiteralConstant ""
