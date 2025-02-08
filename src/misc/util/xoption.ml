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

let to_string to_string ?(prefix="") ?(suffix="") = function
  | None -> ""
  | Some x -> prefix^(to_string x)^suffix

let to_list = function
  | Some x -> [x]
  | None   -> []

let rec list_to_list = function
  | [] -> []
  | (Some x)::rest -> x :: (list_to_list rest)
  | None::rest -> list_to_list rest

let list_opt_to_list = function
  | Some x -> x
  | None   -> []

let map f = function
  | Some x -> Some (f x)
  | None   -> None

let to_list_map f = function
  | Some x -> [f x]
  | None   -> []

let iter f = function
  | Some x -> f x
  | None   -> ()
