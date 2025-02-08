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
(* flattreediff.ml *)
(* difference finder for `flat' trees *)

[%%prepare_logger]

module Xarray = Diffast_misc.Xarray
module Xlist = Diffast_misc.Xlist
module UID = Diffast_misc.UID
module Edit = Diffast_misc.Edit
module Mapping = Diffast_misc.Mapping

let sprintf = Printf.sprintf

(* TENTATIVE: bipartite matching algorithm should be used *)
let eliminate_duplication pairs =
  let map, y_dup =
    List.fold_left
      (fun (map, y_dup) (x, y) ->
        let map' =
          try
            let ys, (*score*)_ = List.assoc x map in
            if List.mem_assoc y !ys then map
            else begin
              ys := (y, ref 0)::!ys;
              map
            end
          with Not_found ->
            (x, (ref [y, ref 0], ref 0))::map
        in
        let y_dup' =
          try
            let count = List.assoc y y_dup in
            incr count;
            y_dup
          with Not_found ->
            (y, ref 1)::y_dup
        in
        map', y_dup'
      ) ([], []) pairs
  in
  List.iter
    (fun ((*x*)_, (ys, score)) ->
      List.iter (fun (y, s) -> s :=!( List.assoc y y_dup)) !ys;
      ys := List.fast_sort (fun (_, s1) (_, s2) -> compare !s1 !s2) !ys;
      score := List.fold_left (fun sum (_, s) -> sum + !s) 0 !ys
    ) map;

  let map =
    List.fast_sort (fun (_, (_, s1)) (_, (_, s2)) -> compare !s1 !s2) map
  in
  let result, _ =
    List.fold_left
      (fun (result, yy) (x, (ys, _)) ->
        match !ys with
          [] -> assert false
        | (y, _)::_ ->
            if List.mem y yy then result, yy
            else (x, y)::result, y::yy
      ) ([], []) map
  in
  result


let find_glue_cands nodes1 nodes2 =
  let cands =
    List.fold_left
      (fun l nd1 ->
        let cand =
          List.filter
            (fun nd2 ->
              nd1#data#_label = nd2#data#_label
            ) nodes2
        in
        match cand with
          [] -> l
        | [nd] -> (nd1, nd)::l
        | nd::_ ->
            let cand' =
              List.filter
                (fun nd' -> nd1#data#equals nd'#data) cand
            in
            match cand' with
              [] -> (nd1, nd)::l
            | [nd'] -> (nd1, nd')::l
            | nds -> (List.map (fun nd' -> nd1, nd') nds) @ l
      ) [] nodes1
  in
  let result = eliminate_duplication cands in (* not optimal! *)
  result


(* mimics Otreediff.Lib.find *)
[%%capture_path
let find ?(rely_on_rel=false) tree1 tree2 =
  let c1, c2 = tree1#root#children, tree2#root#children in

  begin %debug_block
    [%debug_log "rt1=%s collapsed=%B" tree1#root#to_string tree1#root#is_collapsed];
    [%debug_log "rt2=%s collapsed=%B" tree2#root#to_string tree2#root#is_collapsed];
    [%debug_log "c1=[|\n%s\n|]"
       (Xarray.to_string
          (fun nd -> sprintf "%s<%s>" nd#data#label nd#data#digest_string) "\n" c1)];
    [%debug_log "c2=[|\n%s\n|]"
       (Xarray.to_string
          (fun nd -> sprintf "%s<%s>" nd#data#label nd#data#digest_string) "\n" c2)];
  end;

  let n1, n2 = Array.length c1, Array.length c2 in
  let conv nd = nd#data#feature in
  let cdat1 = Array.map conv c1 in
  let cdat2 = Array.map conv c2 in

  let mat, rel, del, ins = Adiff.adiff cdat1 cdat2 in

  let mat = List.map (fun (x, y) -> x + 1, y + 1) mat in
  let rel = List.map (fun (x, y) -> x + 1, y + 1) rel in
  let del = List.map (fun x -> x + 1) del in
  let ins = List.map (fun x -> x + 1) ins in

  let mat = List.map (fun (i, j) -> tree1#get i, tree2#get j) mat in
  let rel = List.map (fun (i, j) -> tree1#get i, tree2#get j) rel in
  let del = List.map tree1#get del in
  let ins = List.map tree2#get ins in

  begin %debug_block
    [%debug_log "\nraw mapping:"];
    List.iter
      (fun (n1, n2) ->
        [%debug_log "%s -- %s" n1#data#to_string n2#data#to_string]
      ) (mat @ rel)
  end;

  (* detect permutations *)
  let glue_cands = find_glue_cands del ins in

  [%debug_log "glue_cands: %s"
     (Xlist.to_string
        (fun (nd1, nd2) ->
          sprintf "(%a,%a)" UID.ps nd1#uid UID.ps nd2#uid
        ) "" glue_cands)];

  let mat = mat @ glue_cands in
  let non_del, non_ins = List.split glue_cands in
  let del = Xlist.subtract del non_del in
  let ins = Xlist.subtract ins non_ins in

  let mat_rel =
    List.fold_left
      (fun l (nd1, nd2) ->
        if nd1#data#equals nd2#data then l
        else (nd1, nd2)::l
      ) [] mat
  in
  let mat = Xlist.subtract mat mat_rel in
  let rel = Xlist.union rel mat_rel in

  let iso, _ = List.split mat in

  let rt1, rt2 = tree1#root, tree2#root in
  let i1, i2 = rt1#index, rt2#index in

  let mat, rel =
    assert ((i1 = n1 + 1) && (i2 = n2 + 1));

    if rt1#data#equals rt2#data then
      (rt1, rt2)::mat, rel
    else
      mat, (rt1, rt2)::rel
  in


  (* rels are not reliable *)
  let ext_del, ext_ins, rel =
    List.fold_left
      (fun (d, i, r) (nd1, nd2) ->
        let cond =
          if rely_on_rel then
            nd1#data#label = nd2#data#label
          else
           (not nd1#is_collapsed) && (not nd2#is_collapsed)
        in
        if cond then
          d, i, (nd1, nd2)::r
        else
          nd1::d, nd2::i, r

      ) ([], [], []) rel
  in
  let del = del @ ext_del in
  let ins = ins @ ext_ins in


  let iso =
    if rel = [] && del = [] && ins = [] && glue_cands = [] then
      [i1]
    else
      List.map (fun nd -> nd#index) iso
  in

  let eds =
    Edit.seq_of_edit_list
      ((List.map
          (fun (nd1, nd2) ->
            Edit.mkrel (nd1#index, nd2#index)) rel) @
       (List.map (fun nd -> Edit.mkdel nd#index) del) @
       (List.map (fun nd -> Edit.mkins nd#index) ins))
  in
  let mapping =
    Mapping.of_elem_list
      (List.map
         (fun (nd1, nd2) ->
           Mapping.mkelem (nd1#index, nd2#index)
         ) (mat @ rel))
  in

  [%debug_log "\nedit sequence:\n%s\nmapping:\n%s\niso:[%s]\n"
     (Edit.seq_to_string eds)
     (Mapping.to_string mapping)
     (Xlist.to_string string_of_int "," iso)];

  eds, mapping, iso
]
