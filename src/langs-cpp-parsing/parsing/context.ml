(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>
   Copyright 2020 Chiba Institute of Technology

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

type t =
  | TOP
  | STMT
  | EXPR
  | TY
  | NEW
  | MEM_INIT
  | CLASS
  | MEM
  | ENUM

type sub =
  | INI
  | END_OF_TY_SPEC
  | END_OF_ID_EXPR
  | END_OF_DTOR
  | END_OF_STMT
  | START_OF_STMT of int
  | IN_SIMPLE_TEMPL_ID
  | IN_CASE_LABEL
  | IN_EXPR
  | END_OF_LAM_INTRO

let to_string = function
  | TOP -> "TOP"
  | STMT -> "STMT"
  | EXPR -> "EXPR"
  | TY -> "TY"
  | NEW -> "NEW"
  | MEM_INIT -> "MEM_INIT"
  | CLASS -> "CLASS"
  | MEM -> "MEM"
  | ENUM -> "ENUM"

let sub_to_string = function
  | INI -> "INI"
  | END_OF_TY_SPEC -> "END_OF_TY_SPEC"
  | END_OF_ID_EXPR -> "END_OF_ID_EXPR"
  | END_OF_DTOR -> "END_OF_DTOR"
  | END_OF_STMT -> "END_OF_STMT"
  | START_OF_STMT n -> Printf.sprintf "START_OF_STMT:%d" n
  | IN_SIMPLE_TEMPL_ID -> "IN_SIMPLE_TEMPL_ID"
  | IN_CASE_LABEL -> "IN_CASE_LABEL"
  | IN_EXPR -> "IN_EXPR"
  | END_OF_LAM_INTRO -> "END_OF_LAM_INTRO"
