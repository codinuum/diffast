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
(* xprint.ml *)

(* miscellaneous print functions *)

open Printf

let cmd_name = Filename.basename(Sys.argv.(0))

let failure fmt =
  let f s = failwith s in
  ksprintf f fmt


let _message ?(out=stdout) head fmt =
  let f s = fprintf out "[%s]%s %s\n%!" cmd_name head s in
  ksprintf f fmt

let message fmt =
  _message "" fmt

let verbose flag fmt =
  let f s =
    if flag then
      fprintf stderr "[%s][VERBOSE] %s\n%!" cmd_name s
    else
      ()
  in
  ksprintf f fmt

let warning ?(out=stderr) ?(head="") fmt =
  _message ~out ("[WARNING]"^head) fmt

let error ?(out=stderr) ?(head="") fmt =
  _message ~out ("[ERROR]"^head) fmt

let println fmt =
  let f s = printf "%s\n" s in
  ksprintf f fmt

