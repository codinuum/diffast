(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>
   Copyright 2020-2025 Chiba Institute of Technology

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

module Xoption = Diffast_misc.Xoption

type ident = string
type name = string
type value = string

let sprintf = Printf.sprintf
let printf = Printf.printf

let _mes head fmt =
  let f s = Printf.fprintf stderr "[%s] %s\n%!" head s in
  Printf.ksprintf f fmt

let rec list_to_string to_str sep = function
  | [] -> ""
  | h::[] -> to_str h
  | h::t -> (to_str h)^sep^(list_to_string to_str sep t)

let opt_to_string = Xoption.to_string
let string_opt_to_string = opt_to_string (fun x -> x)
let int_opt_to_string = opt_to_string string_of_int

let opt_to_list = Xoption.to_list
let list_opt_to_list = Xoption.list_opt_to_list

let opt_to_bool = function
  | Some _ -> true
  | None -> false

let relpath_unix path =
  if Filename.is_relative path then
    path
  else
    let cwd = Unix.realpath (Sys.getcwd()) in
    let pat = Str.regexp (Printf.sprintf "^%s%s" cwd Filename.dir_sep) in
    let path = Unix.realpath path in
    Str.replace_first pat "" path

let relpath =
  if Sys.unix then
    relpath_unix
  else
    fun x -> x
