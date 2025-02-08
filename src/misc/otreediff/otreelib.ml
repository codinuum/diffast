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
(* lib.ml *)

(*open Common*)

[%%prepare_logger]

let sprintf = Printf.sprintf

exception Distance_too_far


let find_trivial tree1 tree2 =
  let rt1, rt2 = tree1#root, tree2#root in
  let res = ref [] in
  let add ed = res := ed::!res in
  let count = ref 1 in
  let eds =
    Array.iter
      (fun nd -> tree1#scan_subtree nd (fun _ -> add (Edit.mkdel !count); incr count))
      rt1#children;
    count := 1;
    Array.iter
      (fun nd -> tree2#scan_subtree nd (fun _ -> add (Edit.mkins !count); incr count))
      rt2#children;
    if not (rt1#data#equals rt2#data) then
      add (Edit.mkrel (rt1#index, rt2#index));
    Edit.seq_of_edit_list !res
  in
  let mapping =
    Mapping.of_elem_list [Mapping.mkelem (rt1#index, rt2#index)]
  in
  let iso = [] in
  eds, mapping, iso


[%%capture_path
let to_dot filename otree1 otree2 eds mapping purges =

  [%debug_log "filename=\"%s\"" filename];

  let purges1, purges2 = List.split purges in
  let mkd1 =
    List.fold_left
      (fun l ed ->
        match ed with
        | Edit.Delete i -> i::l
        | Edit.Relabel(i, _) -> i::l
        | _ -> l
      ) [] eds
  in
  let mkd2 =
    List.fold_left
      (fun l ed ->
        match ed with
          Edit.Insert(i, (*ins*)_) -> i::l
        | Edit.Relabel(_, i) -> i::l
        | _ -> l
      ) [] eds
  in
  let mklab1 nd = "T1:"^(Otree.dot_label_of_node nd) in
  let mklab2 nd = "T2:"^(Otree.dot_label_of_node nd) in

  let dot1 = otree1#to_dot ?mklab:(Some mklab1) mkd1 in
  let dot2 = otree2#to_dot ?mklab:(Some mklab2) mkd2 in

  let buf = Buffer.create 0 in

  Buffer.add_string buf "digraph otree {\nsubgraph cluster_T1 {\nordering=out;\n";
  Buffer.add_buffer buf dot1;
  Buffer.add_string buf "}\nsubgraph cluster_T2 {\n";
  Buffer.add_buffer buf dot2;
  Buffer.add_string buf "}\n";

  List.iter
    (fun (i1, i2) ->
      let nd1, nd2 = otree1#get i1, otree2#get i2 in
      let uid1, uid2 = nd1#uid, nd2#uid in
      Buffer.add_string buf
        (sprintf
           "%a -> %a [ style=dashed dir=none color=gray ];\n%s%s"
           UID.rs uid1 UID.rs uid2
           (if List.mem i1 purges1
           then sprintf "%a [color=blue];\n" UID.rs uid1
           else "")
           (if List.mem i2 purges2
           then sprintf "%a [color=blue];\n" UID.rs uid2
           else "")
        )
    ) mapping;

  List.iter
    (fun ed ->
      match ed with
      | Edit.Relabel(i1, i2) ->
          let nd1, nd2 = otree1#get i1, otree2#get i2 in
          Buffer.add_string buf
            (sprintf "%a -> %a [ style=dashed dir=none color=red ];\n"
               UID.rs nd1#uid UID.rs nd2#uid)
      | _ -> ()
    ) eds;

  Buffer.add_string buf "}";

  let ch = open_out filename in
  Buffer.output_buffer ch buf;
  close_out ch
]
