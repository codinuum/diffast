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
(* clustering.ml *)

open Common
open Otree


let cluster_size_threshold = 3

type t = (index * index) list ref list

exception Cluster

let cluster otree1 otree2 mapping =
  List.fold_left
    (fun clusters (i, j) ->
      try
        List.iter
          (fun cluster ->
            try
              List.iter
                (fun (x, y) ->
                  let xc = Array.to_list (otree1#get x)#children in
                  if List.mem i (List.map (fun c -> c#index) xc) then
                    if (otree2#get j)#parent#index = y then
                      begin
                        cluster := (i, j)::!cluster;
                        raise Cluster
                      end
                ) !cluster
            with Not_found -> () | Parent_not_found _ -> ()
          ) clusters;
        (ref [i, j])::clusters
      with Cluster -> clusters
    ) [] mapping

let exact_cluster otree1 otree2 mapping edits =
  let relabels =
    List.fold_left
      (fun l ed ->
        match ed with
          Edit.Relabel(i, j) -> (i, j)::l
        | _ -> l
      ) [] edits
  in
  let matches =
    List.filter (fun p -> not (List.mem p relabels)) mapping
  in
  let clusters =
    List.filter
      (fun c -> List.length !c > cluster_size_threshold)
      (cluster otree1 otree2 matches)
  in
  List.map
    (function {contents=cluster} ->
(*      let clu1, clu2 = List.split cluster in *)
      List.filter
        (fun (*(i, j)*)_ -> true
(*
          let nd1, nd2 = otree1#get i, otree2#get j in
          let cis1, cis2 = nd1#children_indexes, nd2#children_indexes in
          let cond1 = List.exists (fun i -> not(List.mem i clu1)) cis1 in
          let cond2 = List.exists (fun j -> not(List.mem j clu2)) cis2 in
          not(cond1 || cond2)
*)
        ) cluster
    ) clusters




let roots_of_cluster tree1 tree2 cluster =
  let clu1, clu2 = List.split cluster in
  let clu1_min_idx, clu1_max_idx = minn clu1, maxn clu1 in
  let clu2_min_idx, clu2_max_idx = minn clu2, maxn clu2 in
  let cand1 = tree1#get_roots_of_forest clu1_min_idx clu1_max_idx in
  let cand2 = tree2#get_roots_of_forest clu2_min_idx clu2_max_idx in
  match cand1, cand2 with
  | [r1], [r2] ->
      if List.mem (r1, r2) cluster then
        r1, r2
      else
        internal_error "Clustering.roots_of_cluster: malformed mapping"
  | _ -> internal_error "Clustering.roots_of_cluster: multiple candidates"


let clusters_to_string clusters =
  List.fold_left
    (fun s cluster ->
      Printf.sprintf "[%s]%s"
        (Xlist.to_string (fun (i, _) -> string_of_int i) ";" !cluster) s
    ) "" clusters

let mean_size otree1 otree2 mapping =  (* mean cluster size x 100 *)
  truncate(
  (float(List.length mapping) /.
   float(List.length(cluster otree1 otree2 mapping)))
    *. 100.)

