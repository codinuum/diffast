(*
   Copyright 2012-2023 Codinuum Software Lab <https://codinuum.com>

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
(* *)

type t = MOVE of int

let to_string = function
  | MOVE i -> Printf.sprintf "#%dM" i

let to_raw = function
  | MOVE i -> Printf.sprintf "%d" i

let of_string s = MOVE (int_of_string s)

let of_int i = MOVE i

let unknown = MOVE (-1)

let p ch mid = Stdlib.output_string ch (to_string mid)

let r ch mid = Stdlib.output_string ch (to_raw mid)

let ps () mid = to_string mid

class generator = object
  val mutable id = 0
  method reset = id <- 0
  method gen =
    id <- id + 1;
    let mid = MOVE id in
    [%debug_log "%a" ps mid];
    mid
end
