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
(* edit.ml *)

(*** Edit Sequences ***)

open Common
open Otree

let sprintf = Printf.sprintf

type t =
  | Relabel of index * index
  | Delete of index
  | Insert of index * index list ref (* children *)

let mkrel (i, j) = Relabel(i, j)
let mkdel d = Delete d
let mkins i = Insert(i, ref [])

let isrel = function
  | Relabel _ -> true
  | _ -> false

let isdel = function
  | Delete _ -> true
  | _ -> false

let isins = function
  | Insert _ -> true
  | _ -> false

let get_del_idx = function
  | Delete i -> i
  | _ -> raise (Failure "Edit.get_del_idx")

let get_rel_idx1 = function
  | Relabel(i, _) -> i
  | _ -> raise (Failure "Edit.get_rel_idx1")

let _to_string to_s1 to_s2 = function
  | Relabel(i, j) ->
      sprintf "(Relabel:t1[%s]->t2[%s])" (to_s1 i) (to_s2 j)
  | Delete i ->
      sprintf "(Delete:t1[%s])" (to_s1 i)
  | Insert(j, cref) ->
      sprintf "(Insert:t2[%s] children:[%s])" (to_s2 j)
        (Xlist.to_string to_s2 ";" !cref)

let to_string = function
  | Relabel(i, j) -> sprintf "(Relabel:t1[%d]->t2[%d])" i j
  | Delete i -> sprintf "(Delete:t1[%d])" i
  | Insert(i, cref) ->
      sprintf "(Insert:t2[%d] children:[%s])" i
        (Xlist.to_string string_of_int ";" !cref)

type seq = t list
let empty_seq = ([] : seq)
let seq_of_edit_list (l : t list) = (l : seq)
let seq_add ed eds = ed::eds
let seq_append eds1 eds2 = eds1 @ eds2

let normalize_seq eds = (* sorts the sequence *)
  let dels, rels, inss = ref [], ref [], ref [] in
  List.iter
    (fun ed ->
      match ed with
      | Relabel (*(i, j)*)_ -> rels := ed::!rels
      | Delete (*i*)_ -> dels := ed::!dels
      | Insert (*(j, ins)*)_ -> inss := ed::!inss
    ) eds;
  !dels @ !rels @ !inss

let seq_iter = List.iter

let _seq_to_string to_s1 to_s2 seq =
  Xlist.to_string (_to_string to_s1 to_s2) "\n" seq

let seq_to_string seq = Xlist.to_string to_string "\n" seq

let seq_length seq = List.length seq

let seq_map f seq = List.map f seq

let seq_filter = List.filter

let seq_filter_inserts filt eds =
  List.fold_left
    (fun l e ->
      match e with
      | Insert(i, _) -> if filt i then i::l else l
      | _ -> l
    ) [] eds

let seq_filter_deletes filt eds =
  List.fold_left
    (fun l e ->
      match e with
      | Delete i -> if filt i then i::l else l
      | _ -> l
    ) [] eds

let seq_filter_relabels filt eds =
  List.fold_left
    (fun l e ->
      match e with
      | Relabel(i, j) -> if filt(i, j) then (i, j)::l else l
      | _ -> l
    ) [] eds

let seq_split eds = (* dels * inss * rels *)
  List.fold_left
    (fun l e ->
      let dels, inss, rels = l in
      match e with
      | Delete i -> (i::dels, inss, rels)
      | Insert(i, _) -> (dels, i::inss, rels)
      | Relabel(i, j) -> (dels, inss, (i, j)::rels)
    ) ([], [], []) eds

