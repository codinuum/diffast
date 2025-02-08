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
(* mapping.ml *)

(*** Mappings ***)

open Common
open Otree

let sprintf = Printf.sprintf

type elem = index * index

let mkelem (p : index * index) = (p : elem)
let elem_to_string (i, j) = sprintf "(t1[%d]->t2[%d])" i j

type t = elem list

let of_elem_list (l : elem list) = (l : t)
let length = List.length

let empty = []

let mem i mapping = List.mem_assoc i mapping
let mem_elem i j mapping = List.mem (i, j) mapping

let rec find_list i = function (* index -> index list *)
    [] -> []
  | (x, y)::rest ->
      if i = x then y::(find_list i rest)
      else find_list i rest

let find i mapping = (* index -> index *)
  let res = find_list i mapping in
  match res with
    [] -> raise Not_found
  | [j] -> j
  | _ -> internal_error "Mapping.find: multiple value"

let inv mapping = List.map (fun (i, j) -> j, i) mapping

let inv_find i mapping = find i (inv mapping)

let dom mapping =
  List.fold_left (fun l (i, (*j*)_) -> if List.mem i l then l else i::l)
    [] mapping

let cod mapping =
  List.fold_left (fun l ((*i*)_, j) -> if List.mem j l then l else j::l)
    [] mapping

let iter f mapping =
  let dom = dom mapping in
  List.iter (fun i -> f i (find i mapping)) dom

let filter f mapping = List.filter (fun (i, j) -> f i j) mapping

let split mapping = List.split mapping

let add elem mapping = elem::mapping
let append m1 m2 = m1 @ m2

let descent_sort m = List.sort (fun (a,_) (b,_) -> compare b a) m

let _to_string to_s1 to_s2 =
  Xlist.to_string (fun (i, j) -> sprintf "%s-%s" (to_s1 i) (to_s2 j)) "\n"

let to_string = Xlist.to_string (fun (i, j) -> sprintf "%d-%d" i j) ";"


