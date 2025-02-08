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
(* misc.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xfile = Diffast_misc.Xfile
module UID = Diffast_misc.UID
module GI = Diffast_misc.GIndex
module Otree = Diffast_misc.Otree
module Loc = Diffast_misc.Loc


[%%capture_path
let set_tree_size_limit options sz1 sz2 =
  let comp sz =
    if sz > options#tree_size_threshold then
      int_of_float
        ((float_of_int sz)
           *. ((float_of_int options#tree_size_limit_percent) /. 100.0))
    else
      max_int
  in
  let lim1 = comp sz1 in
  let lim2 = comp sz2 in
  [%debug_log "%d %d" lim1 lim2];
  options#set_tree_size_limit1 lim1;
  options#set_tree_size_limit2 lim2
]

let check_tree_size_limit options sz1 sz2 =
  sz1 > options#tree_size_limit1 || sz2 > options#tree_size_limit2

let check_hard_tree_size_limit options sz1 sz2 =
  sz1 > options#hard_tree_size_limit && sz2 > options#hard_tree_size_limit


class counter =
  object
    val mutable n = 0
    method incr = n <- n + 1
    method value = n
  end

class stopwatch =
  object
    val mutable stime = 0.0
    val mutable time = 0.0
    method start = stime <- (Unix.times()).Unix.tms_utime
    method stop = time <- (Unix.times()).Unix.tms_utime -. stime
    method show = time
  end

let pause() =
  Printf.printf "<<PAUSE!>>\n";
  ignore (input_line stdin)




[%%capture_path
let contract tree1 tree2 clusters =

  let deferred_cluster = ref None in
  let pruned_clusters = ref [] in

  let contract_cluster cluster =
    let clu1, clu2 = List.split cluster in

    begin %debug_block
      let clu1u = List.map (fun i -> (tree1#get i)#uid) clu1 in
      let clu2u = List.map (fun i -> (tree2#get i)#uid) clu2 in
      [%debug_log "clu1=[%s](%d/%d)"
         (Xlist.to_string UID.to_string ";" clu1u) (List.length clu1) tree1#size];
      [%debug_log "clu2=[%s](%d/%d)"
         (Xlist.to_string UID.to_string ";" clu2u) (List.length clu2) tree2#size]
    end;

    let ftr1 = tree1#frontier_of_cluster clu1 in
    let ftr2 = tree2#frontier_of_cluster clu2 in

    begin %debug_block
      let ftr1u = List.map (fun i -> (tree1#get i)#uid) ftr1 in
      let ftr2u = List.map (fun i -> (tree2#get i)#uid) ftr2 in
      [%debug_log "ftr1=[%s]" (Xlist.to_string UID.to_string ";" ftr1u)];
      [%debug_log "ftr2=[%s]" (Xlist.to_string UID.to_string ";" ftr2u)]
    end;

    let path_cands1, topnd_list1, is_rclu1 =
      tree1#contraction_candidates clu1 ftr1
    in
    let path_cands2, topnd_list2, is_rclu2 =
      tree2#contraction_candidates clu2 ftr2
    in

    begin %debug_block
      [%debug_log "topnd_list1=[%s]"
         (Xlist.to_string
            (fun nd -> UID.to_string nd#uid)
            ";" topnd_list1)];
      [%debug_log "topnd_list2=[%s]"
         (Xlist.to_string
            (fun nd -> UID.to_string nd#uid)
            ";" topnd_list2)];
      [%debug_log "path_cands1={%s}"
         (Xlist.to_string
            (fun (i, c) ->
              let u = (tree1#get i)#uid in
              let us = List.map (fun i -> (tree1#get i)#uid) c in
              Printf.sprintf "%a:[%s]"
                UID.ps u (Xlist.to_string UID.to_string ";" us))
            "," path_cands1)];
      [%debug_log "path_cands2={%s}"
         (Xlist.to_string
            (fun (i, c) ->
              let u = (tree2#get i)#uid in
              let us = List.map (fun i -> (tree2#get i)#uid) c in
              Printf.sprintf "%a:[%s]"
                UID.ps u (Xlist.to_string UID.to_string ";" us))
            "," path_cands2)]
    end;


    if is_rclu1 || is_rclu2 then
      deferred_cluster := Some cluster
    else begin
      let prune_cands1 = ref
          (List.concat_map
             (fun tnd ->
               tree1#fast_subtree_members tnd#index
             ) topnd_list1
          )
      in
      let prune_cands2 = ref
          (List.concat_map
             (fun tnd ->
               tree2#fast_subtree_members tnd#index
             ) topnd_list2
          )
      in

      begin %debug_block
        let num_pruned1 =
          match ftr1, ftr2 with
          | [], [] ->
              List.fold_left
                (fun s nd ->
                  s + (tree1#whole_initial_subtree_size nd)
                ) 0 topnd_list1
          | _ ->
              if path_cands1 = [] || path_cands2 = [] then
                0
              else
                List.length (List.filter (fun i -> List.mem i clu1) !prune_cands1)
        in
        let f x = (float num_pruned1) /. (float x) in
        let r1 = f tree1#size in
        let r2 = f tree2#size in
        [%debug_log "num of nodes to be pruned: %d (%d/%d=%f) (%d/%d=%f) %f"
           num_pruned1
           num_pruned1 tree1#size r1
           num_pruned1 tree2#size r2
           (if r1 = 0.0 && r2 = 0.0 then 0.0 else (max r1 r2) /. (min r1 r2))]
      end;


      begin (* prune nodes *)
        match ftr1, ftr2 with
        | [], [] ->
            tree1#prune_nodes topnd_list1;
            tree2#prune_nodes topnd_list2
        | _ ->
            if path_cands1 = [] || path_cands2 = [] then begin
              prune_cands1 := [];
              prune_cands2 := []
            end
            else begin
              tree1#contract path_cands1 topnd_list1;
              prune_cands1 := List.filter (fun i -> List.mem i clu1) !prune_cands1;
              tree2#contract path_cands2 topnd_list2;
              prune_cands2 := List.filter (fun j -> List.mem j clu2) !prune_cands2
            end
      end;

      let pruned_cluster = ref [] in

      begin %debug_block
        let pc1 = List.map (fun i -> (tree1#get i)#uid) !prune_cands1 in
        let pc2 = List.map (fun i -> (tree2#get i)#uid) !prune_cands2 in
        [%debug_log "|prune_cands1|=%d |prune_cands2|=%d" (List.length pc1) (List.length pc2)];
        [%debug_log "prune_cands1=[%s]" (Xlist.to_string UID.to_string ";" pc1)];
        [%debug_log "prune_cands2=[%s]" (Xlist.to_string UID.to_string ";" pc2)]
      end;

      let is_correct =
        (List.length !prune_cands1) = (List.length !prune_cands2) &&
        List.for_all
          (fun i ->
            let j = List.assoc i cluster in
            pruned_cluster := (i, j)::!pruned_cluster;
            List.mem j !prune_cands2
          ) !prune_cands1
      in
      if is_correct then
        pruned_clusters := !pruned_cluster::!pruned_clusters
      else
        failwith "prune_cands mismatch";
    end
  in (* end of contract_cluster *)

  List.iter contract_cluster clusters;


  let mk_nd_cluster cluster =
    List.map (fun (i, j) -> (tree1#get i), (tree2#get j)) cluster
  in
  let deferred_nd_cluster =
    match !deferred_cluster with
      Some clu -> Some (mk_nd_cluster clu) | None -> None
  in
  let pruned_nd_clusters =
    List.map (fun clu -> mk_nd_cluster clu) !pruned_clusters
  in

  deferred_nd_cluster, pruned_nd_clusters
(* end of func contract *)
]


let get_collapsed_children nd =
  List.filter (fun n -> n#pos >= 0) (Array.to_list nd#initial_children)

[%%capture_path
let _moderate_nchildren
    ?(threshold=Const.default_moderate_nchildren_threshold)
    collapsed_children
    nd
    =
  ignore nd;
  let n = List.length collapsed_children in
  let b = n < threshold in
  if not b then
    [%debug_log "too many children: %d" n];
  b
]

let moderate_nchildren ?(threshold=Const.default_moderate_nchildren_threshold) nd =
  let cc = get_collapsed_children nd in
  _moderate_nchildren ~threshold cc nd


let _to_be_flat collapsed_children nd =
  ignore nd;
  List.for_all (fun n -> n#is_leaf) collapsed_children

let to_be_flat nd =
  let cc = get_collapsed_children nd in
  _to_be_flat cc nd


let conv_subtree_node_pairs tree1 tree2 =
  let sea tree nd =
    let gi = nd#gindex in
    if GI.is_valid gi then
      try
        tree#search_node_by_gindex gi
      with
        Not_found ->
          [%warn_log "gindex=%d" nd#gindex];
          assert false
    else
      raise (Invalid_argument "")
  in
  List.filter_map
    (fun (n1, n2) ->
      try
        let gi1 = sea tree1 n1 in
        let gi2 = sea tree2 n2 in
        Some (gi1, gi2)
      with
        Invalid_argument _ -> None
    )

let get_home_dir () =
  try
    Sys.getenv "HOME"
  with
    Not_found ->
      let d = Filename.get_temp_dir_name() in
      [%warn_log "could not find HOME, setting HOME to %s" d];
      d

exception File_found of string

let find_file_name_with_exts fname exts =
  if Xfile.file_exists fname then
    Some fname
  else
    try
      List.iter
        (fun ext ->
          let fn = fname^ext in
          if Xfile.file_exists fn then
            raise (File_found fn)
        ) exts;
      None
    with
      File_found f -> Some f

let node_to_ug_string nd =
  Printf.sprintf "%a(%a)" UID.ps nd#uid GI.ps nd#gindex

let node_to_u_string nd =
  Printf.sprintf "%a" UID.ps nd#uid

let node_to_g_string nd =
  Printf.sprintf "%a" GI.ps nd#gindex

let nodes_to_us_string nds =
  String.concat ";" (List.map node_to_u_string nds)

let nodea_to_us_string nda =
  String.concat ";" (List.map node_to_u_string (Array.to_list nda))

let nodes_to_gs_string nds =
  String.concat ";" (List.map node_to_g_string nds)

let us_to_string = Xlist.to_string UID.to_string ";"

let gs_to_string = Xlist.to_string GI.to_string ";"

let nodes_to_ugs_string nds =
  String.concat ";" (List.map node_to_ug_string nds)

let node_to_loc_string nd = Loc.to_string nd#data#src_loc

let node_to_lab_string nd =
  let v = try nd#data#get_name with _ -> try nd#data#get_value with _ -> "" in
  if v = "" then
    nd#data#get_category
  else
    Printf.sprintf "%s(%s)" nd#data#get_category v

let node_to_data_string nd = Printf.sprintf "[%s]%s" (node_to_loc_string nd) (node_to_lab_string nd)

let node_to_string nd = Printf.sprintf "%a[%s]%s" UID.ps nd#uid (node_to_loc_string nd) (node_to_lab_string nd)

let nups () = node_to_u_string
let ngps () = node_to_g_string
let nugps () = node_to_ug_string
let nsps () = nodes_to_us_string
let naps () = nodea_to_us_string
let ngsps () = nodes_to_gs_string
let nugsps () = nodes_to_ugs_string
let usps () = us_to_string
let gsps () = gs_to_string
let locps () = node_to_loc_string
let labps () = node_to_lab_string
let ndps  () = node_to_data_string
let nps () = node_to_string
let ups = UID.ps
let gps = GI.ps

let next_to_each_other n1 n2 =
  try
    n1#initial_parent == n2#initial_parent && abs (n1#initial_pos - n2#initial_pos) = 1
  with _ -> false


let get_p_ancestor ?(moveon=fun _ -> true) pred nd =
  try
    let cur = ref nd#initial_parent in
    while moveon !cur && not (pred !cur) do
      cur := (!cur)#initial_parent
    done;

    if not (moveon !cur) || not (pred !cur) then
      raise Not_found;
    (*[%debug_log "found: %a" nps !cur];*)
    !cur
  with
    Otree.Parent_not_found _ -> raise Not_found


[%%capture_path
let has_p_ancestor ?(moveon=fun _ -> true) pred nd =
  let b =
    try
      let _ = get_p_ancestor ~moveon pred nd in
      true
    with Not_found -> false
  in
  [%debug_log "%a -> %B" nps nd b];
  b
]

let rec get_p_descendants ?(moveon=fun _ -> true) pred nd =
  if moveon nd then
    List.concat_map
      (fun n ->
        if pred n then
          n ::
          (if moveon n then begin
            let l = get_p_descendants ~moveon pred n in
            (*if l <> [] then
              DEBUG_MSG "!!!! n=%a l=[%a]" nps n nsps l;*)
            l
          end
          else
            [])
        else
          get_p_descendants ~moveon pred n
      )
      (Array.to_list nd#initial_children)
  else
    []

let has_p_descendant ?(count=1) ?(moveon=fun _ -> true) pred nd =
  let c = ref 0 in
  let rec _has_p_descendant ?(moveon=fun _ -> true) pred nd =
    if moveon nd then
      Array.iter
        (fun n ->
          if pred n then begin
            incr c;
            if !c >= count then
              raise Exit
            else
              _has_p_descendant ~moveon pred n
          end
          else
            _has_p_descendant ~moveon pred n
        ) nd#initial_children
  in
  try
    _has_p_descendant ~moveon pred nd;
    false
  with
    Exit -> true

let count_p_descendant ?(limit=0) ?(moveon=fun _ -> true) pred nd =
  let c = ref 0 in
  let rec _count_p_descendant ?(moveon=fun _ -> true) pred nd =
    if moveon nd then
      Array.iter
        (fun n ->
          if pred n then begin
            incr c;
            if limit <= 0 || !c >= limit then
              raise Exit
            else
              _count_p_descendant ~moveon pred n
          end
          else
            _count_p_descendant ~moveon pred n
        ) nd#initial_children
  in
  try
    _count_p_descendant ~moveon pred nd;
    !c
  with
    Exit -> !c

[%%capture_path
let is_cross_boundary nmapping n1 n2 =
  let b =
    try
      let a1 = get_p_ancestor (fun x -> x#data#is_boundary) n1 in
      let a2 = get_p_ancestor (fun x -> x#data#is_boundary) n2 in
      not (try nmapping#find a1 == a2 with _ -> false)
    with
      _ -> false
  in
  [%debug_log "%a - %a -> %B" nps n1 nps n2 b];
  b
]

[%%capture_path
let is_ancestor a n =
  let visited = ref [n] in
  let cur = ref n in
  let b =
    try
      while true do
        cur := (!cur)#initial_parent;
        if List.memq !cur !visited then
          failwith "is_ancestor"
        else begin
          if !cur == a then
            raise Exit;
          visited := !cur :: !visited
        end
      done;
      false
    with
    | Exit -> true
    | _ -> false
  in
  [%debug_log "%a %a --> %B" nups a nups n b];
  b
]

let get_scope_node nd = get_p_ancestor (fun x -> x#data#is_scope_creating) nd

[%%capture_path
let is_scope_compatible nmapping n1 n2 =
  let b =
    try
      let a1 = get_scope_node n1 in
      let a2 = get_scope_node n2 in
      try
        let a1_ = nmapping#find a1 in
        [%debug_log "%a -> %a" nups a1 nups a1_];
        a1_ != a2 && (is_ancestor a1_ a2 || is_ancestor a2 a1_)
      with Not_found -> begin
        try
          let _a2 = nmapping#inv_find a2 in
          [%debug_log "%a <- %a" nups _a2 nups a2];
          is_ancestor a1 _a2 || is_ancestor _a2 a1
        with _ -> false
      end
    with
      _ -> false
  in
  [%debug_log "%a - %a -> %B" nps n1 nps n2 b];
  b
]

[%%capture_path
let is_cross_scope nmapping n1 n2 =
  let b =
    try
      let a1 = get_p_ancestor (fun x -> x#data#is_scope_creating) n1 in
      let a2 = get_p_ancestor (fun x -> x#data#is_scope_creating) n2 in
      not (try nmapping#find a1 == a2 with _ -> false)
    with
      _ -> false
  in
  [%debug_log "%a - %a -> %B" nps n1 nps n2 b];
  b
]

let inv_assq k l =
  let res_opt =
    List.fold_left
      (fun opt (x0, y0) ->
        match opt with
        | None -> begin
            if y0 == k then
              Some x0
            else
              opt
        end
        | _ -> opt
      ) None l
  in
  match res_opt with
  | Some x -> x
  | None -> raise Not_found

module Tbl1 = struct
  type ('a, 'b) t = ('a, 'b) Hashtbl.t

  let create () = (Hashtbl.create 0 : ('a, 'b) t)

  let find tbl k1 = Hashtbl.find tbl k1

  let add tbl k1 v = Hashtbl.replace tbl k1 v

  let clear tbl = Hashtbl.clear tbl

  let length tbl = Hashtbl.length tbl
end

module Tbl2 = struct
  type ('a, 'b, 'c) t = ('a, ('b, 'c) Hashtbl.t) Hashtbl.t

  let create () = (Hashtbl.create 0 : ('a, 'b, 'c) t)

  let find tbl k1 k2 = Hashtbl.find (Hashtbl.find tbl k1) k2

  let add tbl k1 k2 v =
    let tbl1 =
      try
        Hashtbl.find tbl k1
      with
        Not_found ->
          let tbl1 = Hashtbl.create 0 in
          Hashtbl.add tbl k1 tbl1;
          tbl1
    in
    Hashtbl.replace tbl1 k2 v

  let clear tbl = Hashtbl.iter (fun _ tbl1 -> Hashtbl.clear tbl1) tbl

  let length tbl =
    let sz = ref 0 in
    Hashtbl.iter
      (fun _ tbl1 ->
        sz := !sz + Hashtbl.length tbl1
      ) tbl;
    !sz
end

module Tbl3 = struct
  type ('a, 'b, 'c, 'd) t = ('a, ('b, ('c, 'd) Hashtbl.t) Hashtbl.t) Hashtbl.t

  let create () = (Hashtbl.create 0 : ('a, 'b, 'c, 'd) t)

  let find tbl k1 k2 k3 = Hashtbl.find (Hashtbl.find (Hashtbl.find tbl k1) k2) k3

  let add tbl k1 k2 k3 v =
    let tbl1 =
      try
        Hashtbl.find tbl k1
      with
        Not_found ->
          let tbl1 = Hashtbl.create 0 in
          Hashtbl.add tbl k1 tbl1;
          tbl1
    in
    let tbl2 =
      try
        Hashtbl.find tbl1 k2
      with
        Not_found ->
          let tbl2 = Hashtbl.create 0 in
          Hashtbl.add tbl1 k2 tbl2;
          tbl2
    in
    Hashtbl.replace tbl2 k3 v

  let clear tbl =
    Hashtbl.iter
      (fun _ tbl1 ->
        Hashtbl.iter
          (fun _ tbl2 ->
            Hashtbl.clear tbl2
          ) tbl1;
        Hashtbl.clear tbl1
      ) tbl

  let length tbl =
    let sz = ref 0 in
    Hashtbl.iter
      (fun _ tbl1 ->
        Hashtbl.iter
          (fun _ tbl2 ->
            sz := !sz + Hashtbl.length tbl2
          ) tbl1
      ) tbl;
    !sz
end

module Tbl4 = struct
  type ('a, 'b, 'c, 'd, 'e) t = ('a, ('b, ('c, ('d, 'e) Hashtbl.t) Hashtbl.t) Hashtbl.t) Hashtbl.t

  let create () = (Hashtbl.create 0 : ('a, 'b, 'c, 'd, 'e) t)

  let find tbl k1 k2 k3 k4 =
    Hashtbl.find (Hashtbl.find (Hashtbl.find (Hashtbl.find tbl k1) k2) k3) k4

  let add tbl k1 k2 k3 k4 v =
    let tbl1 =
      try
        Hashtbl.find tbl k1
      with
        Not_found ->
          let tbl1 = Hashtbl.create 0 in
          Hashtbl.add tbl k1 tbl1;
          tbl1
    in
    let tbl2 =
      try
        Hashtbl.find tbl1 k2
      with
        Not_found ->
          let tbl2 = Hashtbl.create 0 in
          Hashtbl.add tbl1 k2 tbl2;
          tbl2
    in
    let tbl3 =
      try
        Hashtbl.find tbl2 k3
      with
        Not_found ->
          let tbl3 = Hashtbl.create 0 in
          Hashtbl.add tbl2 k3 tbl3;
          tbl3
    in
    Hashtbl.replace tbl3 k4 v

  let clear tbl =
    Hashtbl.iter
      (fun _ tbl1 ->
        Hashtbl.iter
          (fun _ tbl2 ->
            Hashtbl.iter
              (fun _ tbl3 ->
                Hashtbl.clear tbl3
              ) tbl2;
            Hashtbl.clear tbl2
          ) tbl1;
        Hashtbl.clear tbl1
      ) tbl

  let length tbl =
    let sz = ref 0 in
    Hashtbl.iter
      (fun _ tbl1 ->
        Hashtbl.iter
          (fun _ tbl2 ->
            Hashtbl.iter
              (fun _ tbl3 ->
                sz := !sz + Hashtbl.length tbl3
              ) tbl2
          ) tbl1
      ) tbl;
    !sz
end
