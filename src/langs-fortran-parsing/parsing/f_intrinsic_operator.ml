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

(*open Label_common*)

type t =
  | AND
  | OR
  | NOT
  | EQV
  | NEQV
  | GE
  | GT
  | LE
  | LT
  | EQ
  | NE
  | Mult
  | Div
  | Power
  | Add
  | Subt
  | Concat
  | Eq
  | Neq
  | Lt
  | Le
  | Gt
  | Ge
  | Id
  | Neg

let to_string = function
  | AND    -> "AND"
  | OR     -> "OR"
  | NOT    -> "NOT"
  | EQV    -> "EQV"
  | GE     -> "GE"
  | GT     -> "GT"
  | LE     -> "LE"
  | LT     -> "LT"
  | EQ     -> "EQ"
  | NE     -> "NE"
  | NEQV   -> "NEQV"
  | Mult   -> "Mult"
  | Div    -> "Div"
  | Power  -> "Power"
  | Add    -> "Add"
  | Subt   -> "Subt"
  | Concat -> "Concat"
  | Eq     -> "Eq"
  | Neq    -> "Neq"
  | Lt     -> "Lt"
  | Le     -> "Le"
  | Gt     -> "Gt"
  | Ge     -> "Ge"
  | Id     -> "Id"
  | Neg    -> "Neg"

let to_simple_string = function
  | AND    -> ".AND."
  | OR     -> ".OR."
  | NOT    -> ".NOT."
  | EQV    -> ".EQV."
  | GE     -> ".GE."
  | GT     -> ".GT."
  | LE     -> ".LE."
  | LT     -> ".LT."
  | EQ     -> ".EQ."
  | NE     -> ".NE."
  | NEQV   -> ".NEQV."
  | Mult   -> "*"
  | Div    -> "/"
  | Power  -> "**"
  | Add    -> "+"
  | Subt   -> "-"
  | Concat -> "//"
  | Eq     -> "=="
  | Neq    -> "/="
  | Lt     -> "<"
  | Le     -> "<="
  | Gt     -> ">"
  | Ge     -> ">="
  | Id     -> "+"
  | Neg    -> "-"

let to_tag = function
  | AND    -> "AND", []
  | OR     -> "OR", []
  | NOT    -> "NOT", []
  | EQV    -> "EQV", []
  | GE     -> "GE", []
  | GT     -> "GT", []
  | LE     -> "LE", []
  | LT     -> "LT", []
  | EQ     -> "EQ", []
  | NE     -> "NE", []
  | NEQV   -> "NEQV", []
  | Mult   -> "Mult", []
  | Div    -> "Div", []
  | Power  -> "Power", []
  | Add    -> "Add", []
  | Subt   -> "Subt", []
  | Concat -> "Concat", []
  | Eq     -> "Eq", []
  | Neq    -> "Neq", []
  | Lt     -> "Lt", []
  | Le     -> "Le", []
  | Gt     -> "Gt", []
  | Ge     -> "Ge", []
  | Id     -> "Id", []
  | Neg    -> "Neg", []
