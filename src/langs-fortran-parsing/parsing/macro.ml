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

(* macro.ml *)

module Macro_base = Langs_common.Macro_base

type kind =
  | K_GENERAL
  | K_TYPE_SPEC
  | K_WRITE
  | K_READ_WRITE

let kind_to_string = function
  | K_GENERAL    -> "GENERAL"
  | K_TYPE_SPEC  -> "TYPE_SPEC"
  | K_WRITE      -> "WRITE"
  | K_READ_WRITE -> "READ|WRITE"

include Macro_base
