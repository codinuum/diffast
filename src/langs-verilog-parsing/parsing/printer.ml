(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>

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
(*
 * A pretty printer for SystemVerilog
 *
 * printer.ml
 *
 *)

open Ast
open Format
(*open Common*)


let dump =
  let rec doit ind (node : node) =
    printf "%s<%s>[%s]\n"
      ind (Label.to_string node#label) (Loc.to_string ~short:true node#loc);
    List.iter (doit (ind^" ")) node#children
  in
  doit ""



