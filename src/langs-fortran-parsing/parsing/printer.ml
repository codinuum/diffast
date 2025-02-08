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

(*
 * A pretty printer for Fortran
 *
 * printer.ml
 *
 *)

open Printf

(*open Ast*)
(*open Common*)

let subtree_to_string root =
  let buf = Buffer.create 0 in
  let rec doit ind nd =
    Buffer.add_string buf (sprintf "%s%s\n" ind nd#to_string);
    List.iter (doit (ind^"  ")) nd#children
  in
  doit "" root;
  Buffer.contents buf


let to_string root =
  let buf = Buffer.create 0 in
  let rec doit ind nd =
    Buffer.add_string buf (sprintf "%s%s\n" ind nd#to_string);
    List.iter (doit (ind^"  ")) nd#children
  in
  doit "" root;
  Buffer.contents buf

let dump root =
  let rec doit ind nd =
    printf "%s%s\n" ind nd#to_string;
    List.iter (doit (ind^"  ")) nd#children
  in
  doit "" root
