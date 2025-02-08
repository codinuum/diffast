(*
   Copyright 2012-2025 Codinuum Software Lab <https://codinuum.com>

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
(* common.ml *)

module Xprint = Diffast_misc.Xprint
module Parserlib_base = Langs_common.Parserlib_base

module PB = Parserlib_base

let extensions = [".v"]

exception Internal_error of string

exception Parse_error = PB.Parse_error

let fail_to_parse = PB.fail_to_parse

let parse_warning spos epos = PB.parse_warning ~head:"[Verilog]" spos epos

let warning_msg = Xprint.warning ~head:"[Verilog]"

type identifier = string

let num_to_ordinal n =
  let suffix =
    match n mod 10 with
    | 1 -> "st"
    | 2 -> "nd"
    | 3 -> "rd"
    | _ -> "th"
  in
  Printf.sprintf "%d%s" n suffix
