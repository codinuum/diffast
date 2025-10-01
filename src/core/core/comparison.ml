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
(* comparison.ml *)

[%%prepare_logger]

module Xarray = Diffast_misc.Xarray
module Xset = Diffast_misc.Xset
module Xhash = Diffast_misc.Xhash
module Xprint = Diffast_misc.Xprint
module Otree = Diffast_misc.Otree
module SMP = Diffast_misc.SMP

module B = Diffast_misc.Binding
module Nodetbl = Node.Tbl

open Misc

let sprintf = Printf.sprintf

let is_use n = B.is_use n#data#binding
let get_def_node tree n = tree#search_node_by_uid (B.get_uid n#data#binding)
let is_local_def n = B.is_local_def n#data#binding

let subtree_similarity_thresh = 0.7
let subtree_similarity_ratio_thresh = 0.8
let subtree_similarity_ratio_cutoff = 0.15
let adjacency_ratio_cutoff = 0.15
(* let subtree_similarity_ratio_lower_thresh = 0.5 *)
(* let subtree_similarity_lower_thresh = 0.15 *)
let ancestors_similarity_thresh = 0.7
let ancestors_similarity_ratio_thresh = 0.8
(* let ancestors_similarity_ratio_lower_thresh = 0.5 *)
let ncross_sim_ratio_thresh = 0.8
let permutation_hub_count_thresh = 64

let label_match_eq_score = 3
let label_match_eq_named_bonus = 1
(*
let label_match_eq_named_score = label_match_eq_score + label_match_eq_named_bonus
*)
let get_label_match_eq_named_score _ = label_match_eq_score + label_match_eq_named_bonus
(* !!!
  let a =
    try
      String.length nd#data#get_name
    with
      Not_found -> 0
  in
  label_match_eq_score + label_match_eq_named_bonus * a
*)

(* *)

type 'node_t label_match_result = { lm_score   : float;
                                    lm_matches : ('node_t * 'node_t) list;
                                    lm_nmcount : int;
                                  }

exception Found

let compare_pair (x0, y0) (x1, y1) =
  let c = Stdlib.compare x0 x1 in
  if c = 0 then
    Stdlib.compare y0 y1
  else
    c

[%%capture_path
let estimate_cost_of_move tree1 tree2 nmapping nd1 nd2 = (* cost = number of accompanying nodes *)
  let lgi2 = (tree2#initial_leftmost nd2)#gindex in
  let gi2 = nd2#gindex in
  let count = ref 0 in
(*  let mapped = ref [] in *)
  tree1#fast_scan_whole_initial_subtree nd1
    (fun n ->
      try
        let n' = nmapping#find n in
        let gi' = n'#gindex in
        if lgi2 <= gi' && gi' <= gi2 then begin
(*        mapped := (n#uid, n'#uid) :: !mapped; *)
          incr count
        end
      with
        Not_found -> ()
    );
(*
    [%debug_log "%a -> %a (%d) [%s]" nups nd1 nups nd2 !count
      (Xlist.to_string (fun (u1, u2) -> sprintf "%a-%a" ups u1 ups u2) ";" !mapped)];
*)
  [%debug_log "%a -> %a (%d)" nps nd1 nps nd2 !count];

  !count
]

let get_bn = get_p_ancestor (fun x -> x#data#is_boundary)
let get_stmt = get_p_ancestor (fun x -> x#data#is_statement)

let _is_map nmapping n1 n2 =
  try
    nmapping#find n1 == n2
  with
    Not_found -> false

let _get_digest tree n =
  match n#data#_digest with
  | Some d -> d
  | None -> tree#get_digest n

let __same_digest tree1 tree2 n1 n2 =
  try
    let d1 = _get_digest tree1 n1 in
    let d2 = _get_digest tree2 n2 in
    d1 = d2
  with _ -> false

[%%capture_path
let _same_digest tree1 tree2
    ?(leaf_comparison=true)
    ?(digest_for_leaf=false)
    ?(digest_for_all=false)
    n1 n2
    =
  [%debug_log "[leaf_comparison:%B,digest_for_leaf=%B,digest_for_all=%B] %a %a"
    leaf_comparison digest_for_leaf digest_for_all nps n1 nps n2];

  let nc1 = n1#initial_nchildren in
  let nc2 = n2#initial_nchildren in

  (leaf_comparison || nc1 > 0 && nc2 > 0) &&
  if (digest_for_leaf || digest_for_all) && nc1 = 0 && nc2 = 0 then
    __same_digest tree1 tree2 n1 n2
  else if nc1 = 0 && nc2 = 0 then
    n1#data#eq n2#data
  else if digest_for_all then
    __same_digest tree1 tree2 n1 n2
  else
    nc1 = nc2 &&
    __same_digest tree1 tree2 n1 n2
]

[%%capture_path
let boundary_mapped nmap nd nd' =
  try
    let bn = get_bn nd in
    let bn' = get_bn nd' in
    let b = nmap bn == bn' in
    [%debug_log "%a-%a (%a-%a): %B" nups nd nups nd' nups bn nups bn' b];
    b
  with _ -> false
]

[%%capture_path
let boundary_stable umap mem_mov nd nd' =
  try
    let bn = get_bn nd in
    let bn' = get_bn nd' in
    let bu = bn#uid in
    let bu' = bn'#uid in
    let b = umap bu = bu' && mem_mov bu bu' in
    [%debug_log "%a-%a: %B" ups bu ups bu' b];
    b
  with _ -> false
]

let get_bn_opt n =
  try
    Some (get_p_ancestor (fun x -> x#data#is_boundary) n)
  with _ -> None

let is_mapped_boundary_key nmapping = function
  | Some bn1, Some bn2 -> begin
      try nmapping#find bn1 == bn2 with _ -> false
  end
  | _ -> false

let null_boundary_key = None, None

let bn_opt_to_str = function
  | Some bn -> bn#data#to_string
  | None -> "None"

let boundary_key_to_string (bn1_opt, bn2_opt) =
  Printf.sprintf "(%s,%s)" (bn_opt_to_str bn1_opt) (bn_opt_to_str bn2_opt)

[%%capture_path
class ['node_t] multiple_node_matches (label_to_string : Obj.t -> string) = object (self)
  val tbl = (Hashtbl.create 0: (Obj.t, 'node_t list * 'node_t list) Hashtbl.t)
  val uniq_matches = (Xset.create 0 : ('node_t * 'node_t) Xset.t)

  method label_to_string _lab = label_to_string _lab

  method add _lab (nds1, nds2) =
    [%debug_log "%s [%a]-[%a]" (label_to_string _lab) nsps nds1 nsps nds2];
    if not (Hashtbl.mem tbl _lab) then
      Hashtbl.add tbl _lab (nds1, nds2)
    else
      [%warn_log "key(_label) collision?: %s"
        (label_to_string (Obj.obj _lab))]

  method find _lab =
    Hashtbl.find tbl _lab

  method add_uniq_match n1 n2 =
    Xset.add uniq_matches (n1, n2);
    [%debug_log "added %a-%a" nups n1 nups n2]

  method is_uniq_match n1 n2 =
    let b = Xset.mem uniq_matches (n1, n2) in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b

  method replace _lab (nds1, nds2) =
    [%debug_log "%s [%a]-[%a]" (label_to_string _lab) nsps nds1 nsps nds2];
    Hashtbl.replace tbl _lab (nds1, nds2)

  method remove _lab =
    [%debug_log "%s" (label_to_string _lab)];
    Hashtbl.remove tbl _lab

  method iter (f : Obj.t * 'node_t list * 'node_t list -> unit) =
    let list =
      Hashtbl.fold
        (fun _lab (nds1, nds2) l ->
          (_lab, nds1, nds2)::l
        ) tbl []
    in
    let cmp (_, nds11, nds21) (_, nds12, nds22) =
      let gip1 = (List.hd nds11)#gindex, (List.hd nds21)#gindex in
      let gip2 = (List.hd nds12)#gindex, (List.hd nds22)#gindex in
      Stdlib.compare gip1 gip2

    in
    List.iter f (List.fast_sort cmp list)

end (* of class multiple_node_matches *)
]


type 'node_t subroot_members_t = 'node_t * 'node_t list

type 'node_t multiple_subtree_match_tbl_t =
    (Digest.t,                          (* digest *)
     'node_t subroot_members_t list *   (* root * members *)
       'node_t subroot_members_t list * (* root * members *)
       int                              (* size *)
    ) Hashtbl.t


[%%capture_path
class ['node_t] multiple_subtree_matches options = object

  val tbl = (Hashtbl.create 0: 'node_t multiple_subtree_match_tbl_t)
  val mutable match_thresh = 0

  method add d (ndmems1, ndmems2) =
    if not (Hashtbl.mem tbl d) then
      try
        let sz = List.length (snd (List.hd ndmems1)) in
        if sz > options#subtree_match_threshold then
          Hashtbl.add tbl d (ndmems1, ndmems2, sz)
      with
        Failure _(*"hd"*) -> assert false
    else
      [%warn_log "digest collision?: %s" d]

  method mem = Hashtbl.mem tbl

  method find = Hashtbl.find tbl

  method remove d =
    [%debug_log "removing %s" (try Digest.to_hex d with _ -> d)];
    Hashtbl.remove tbl d

  method iter
      (f : Digest.t * 'node_t subroot_members_t list * 'node_t subroot_members_t list * int -> unit)
      =
    let list =
      Hashtbl.fold
        (fun d (ndmems1, ndmems2, sz) l ->
          (d, ndmems1, ndmems2, sz)::l
        ) tbl []
    in
    let cmp (_, ndmems11, ndmems21, sz1) (_, ndmems12, ndmems22, sz2) =
      let c1 = Stdlib.compare sz2 sz1 in
      if c1 = 0 then
        let gip1 = (fst (List.hd ndmems11))#gindex, (fst (List.hd ndmems21))#gindex in
        let gip2 = (fst (List.hd ndmems12))#gindex, (fst (List.hd ndmems22))#gindex in
        Stdlib.compare gip1 gip2
      else
        c1
    in
    List.iter f (List.fast_sort cmp list)

  method align (nmapping : 'node_t Node_mapping.c) =

    let get_digest x =
      match x#data#_digest with
      | Some d -> d
      | None -> raise Not_found
    in

    let inner_ds = Xset.create 0 in
    Hashtbl.iter
      (fun d ->
        function
          | ((_, mems)::_, _, _) -> begin
              List.iter
                (fun nd ->
                  try
                    let d0 = get_digest nd in
                    if d0 <> d then
                      if Hashtbl.mem tbl d0 then
                        Xset.add inner_ds d0
                  with
                    Not_found -> ()
                ) mems
          end
          | _ -> ()
      ) tbl;
    let is_inner d = Xset.mem inner_ds d in

    let ntbl = Hashtbl.create 0 in (* root node -> subtree members *)
    let dtbl1 = Hashtbl.create 0 in (* root node -> digest *)
    let dtbl2 = Hashtbl.create 0 in (* root node -> digest *)
    let bns1 = Xset.create 0 in
    let bns2 = Xset.create 0 in

    let add_bn bns rt =
      try
        Xset.add bns (get_bn rt)
      with _ -> ()
    in
    Hashtbl.iter
      (fun d (ndmems1, ndmems2, _) ->
        if not (is_inner d) then begin
          List.iter
            (fun (rt, nds) ->
              if List.for_all (fun n -> not (nmapping#mem_dom n)) nds then begin
                Hashtbl.add dtbl1 rt d;
                Hashtbl.add ntbl rt nds;
                add_bn bns1 rt
              end
            ) ndmems1;
          List.iter
            (fun (rt, nds) ->
              if List.for_all (fun n -> not (nmapping#mem_cod n)) nds then begin
                Hashtbl.add dtbl2 rt d;
                Hashtbl.add ntbl rt nds;
                add_bn bns1 rt
              end
            ) ndmems2
        end
      ) tbl;

    let is_map = _is_map nmapping in
    let gen_dummy_digest =
      let count = ref 0 in
      fun () ->
        let d = (string_of_int !count : Xhash.t) in
        incr count;
        d
    in
    Xset.iter
      (fun bn1 ->
        Xset.iter
          (fun bn2 ->
              if is_map bn1 bn2 then begin
                if not (Hashtbl.mem dtbl1 bn1) && not (Hashtbl.mem dtbl2 bn2) then begin
                  let d = gen_dummy_digest() in
                  [%debug_log "!!!!! boundary: %s [%s] - %s [%s] d=%s"
                    bn1#data#to_string (Loc.to_string bn1#data#src_loc)
                    bn2#data#to_string (Loc.to_string bn2#data#src_loc)
                    d];
                  Hashtbl.add dtbl1 bn1 d;
                  Hashtbl.add dtbl2 bn2 d;
                end
              end
          ) bns2
      ) bns1;

    let roots1 = Hashtbl.fold (fun nd _ l -> nd::l) dtbl1 [] in
    let roots2 = Hashtbl.fold (fun nd _ l -> nd::l) dtbl2 [] in

    if roots1 = [] || roots2 = [] then
      []
    else

    let cmp nd1 nd2 = Stdlib.compare nd1#gindex nd2#gindex in

    let roota1 = Array.of_list (List.fast_sort cmp roots1) in
    let roota2 = Array.of_list (List.fast_sort cmp roots2) in

    let da1 = Array.map (fun nd -> Hashtbl.find dtbl1 nd) roota1 in
    let da2 = Array.map (fun nd -> Hashtbl.find dtbl2 nd) roota2 in

    let matched, relabeled, _deleted, _inserted = Adiff.adiff da1 da2 in


    begin %debug_block
      [%debug_log "num of relabels: %d" (List.length relabeled)];
      List.iter
        (fun (i, j) ->
          [%debug_log "[relabel] %a - %a" nps roota1.(i) nps roota2.(j)]
        ) relabeled
    end;

    let d, i = List.split relabeled in

    let deleted = List.fast_sort Stdlib.compare (_deleted @ d) in
    let inserted = List.fast_sort Stdlib.compare (_inserted @ i) in

    begin %debug_block
      [%debug_log "alignment:"];
      let cur2 = ref 0 in
      let to_hex x = try Digest.to_hex x with _ -> x in
      let n2s n = UID.to_string n#uid in
      let n2cat n = n#data#get_category in
      let n2loc n = Loc.to_string n#data#src_loc in
      Array.iteri
        (fun i nd ->
          if List.mem i deleted then begin
            [%debug_log "(%s) %7s   %7s %s [%s]" (to_hex da1.(i)) (n2s nd) "" (n2cat nd) (n2loc nd)]
          end
          else if List.mem_assoc i matched then begin
            let j = List.assoc i matched in

            if !cur2 < j then begin
              for p = !cur2 to j - 1 do
                if List.mem p inserted then begin
                  let ra2p = roota2.(p) in
                  [%debug_log "(%s) %7s   %7s %s [%s]" (to_hex da2.(p)) "" (n2s ra2p) (n2cat ra2p) (n2loc ra2p)]
                end
                else
                  [%debug_log "dangling index (right): %d" p]
              done
            end;
            let ra2j = roota2.(j) in
            [%debug_log "(%s) %7s - %7s %s [%s]-[%s]"
               (to_hex da1.(i)) (n2s nd) (n2s ra2j) (n2cat ra2j) (n2loc nd) (n2loc ra2j)];
            cur2 := j + 1
          end
          else
            [%debug_log "dangling index (left): %d" i]

        ) roota1;

      let sz2 = Array.length roota2 in
      if !cur2 < sz2 then
        for p = !cur2 to sz2 - 1 do
          if List.mem p inserted then begin
            let ra2p = roota2.(p) in
            [%debug_log "(%s) %7s   %7s %s [%s]" (to_hex da2.(p)) "" (n2s ra2p) (n2cat ra2p) (n2loc ra2p)]
          end
          else
            [%debug_log "dangling index (right): %d" p]
        done

    end;

    let count = ref 0 in

    let added_pairs = ref [] in

    List.iter
      (fun (i, j) ->
        let pi, pj = i - 1, j - 1 in
        let ni, nj = i + 1, j + 1 in
        let d = da1.(i) in
        let nd1, nd2 = roota1.(i), roota2.(j) in
        if
          (if List.mem pi deleted then d = da1.(pi) else false) ||
          (if List.mem ni deleted then d = da1.(ni) else false) ||
          (if List.mem pj inserted then d = da2.(pj) else false) ||
          (if List.mem nj inserted then d = da2.(nj) else false)
        then begin (* suspicious *)

          [%debug_log "suspicious match: %a-%a" nps nd1 nps nd2]
        end
        else
          try
            let nds1 = Hashtbl.find ntbl nd1 in
            let nds2 = Hashtbl.find ntbl nd2 in
            incr count;

            List.iter2
              (fun n1 n2 ->
                let _ = nmapping#add_settled ~stable:true n1 n2 in
                added_pairs := (n1, n2) :: !added_pairs
              ) nds1 nds2;

            nmapping#add_settled_roots nd1 nd2
          with
            Not_found -> ()
      ) matched;

    [%debug_log "%d pairs (roots) added" !count];

    !added_pairs

    (* end of method align *)


end (* of class multiple_subtree_matches *)
]


class ['a] pairs = object
  val pairs = (Xset.create 0 : ('a * 'a) Xset.t)

  method mem x1 x2 = Xset.mem pairs (x1, x2)

  method add x1 x2 = Xset.add pairs (x1, x2)

  method iter f =
    Xset.iter (fun (x1, x2) -> f x1 x2) pairs

end

[%%capture_path
let get_orig_name n =
  let orig_name =
    let name = try n#data#get_name with _ -> "" in
    let sname = try n#data#get_stripped_name with _ -> "" in
    if name <> sname then
      sname
    else
      try
        n#data#get_orig_name
      with
        _ -> name
  in
  [%debug_log "%s -> \"%s\"" n#data#to_string orig_name];
  orig_name
]

let get_stripped_name n = n#data#get_stripped_name

let stripped_orig_eq n1 n2 = n1#data#_stripped_orig_label = n2#data#_stripped_orig_label

let is_def n = B.is_def n#data#binding
let is_non_local_def n = B.is_non_local_def n#data#binding

exception Elaboration_impossible
exception Abort

let is_crossing = Node_mapping.is_crossing

type weight_t =
  | W_int of int
  | W_float of float
  | W_int_int of int * int

let weight_of_int i = W_int i
let weight_of_float f = W_float f
let weight_of_int_int i j = W_int_int(i, j)

let weight_to_int = function
  | W_int i -> i
  | _ -> failwith "Compare.weight_to_int"

let weight_to_int_int = function
  | W_int_int(i, j) -> i, j
  | _ -> failwith "Compare.weight_to_int_int"

let weight_to_float = function
  | W_float f -> f
  | _ -> failwith "Compare.weight_to_float"

let weight_to_string = function
  | W_int i -> string_of_int i
  | W_float f -> string_of_float f
  | W_int_int(i, j) -> Printf.sprintf "(%d, %d)" i j

let wps () = weight_to_string

let weight_compare x0 x1 =
  match x0, x1 with
  | W_int i0, W_int i1 -> Stdlib.compare i0 i1
  | W_float f0, W_float f1 -> Stdlib.compare f0 f1
  | W_int_int(i0, j0), W_int_int(_, j1) -> begin
      let c = Stdlib.compare i0 i0 in
      if c = 0 then
        Stdlib.compare j0 j1
      else
        c
  end
  | _ -> failwith "Compare.weight_compare"


[%%capture_path
class ['node_t, 'tree_t] c
    options
    ?(has_elaborate_edits=false)
    (tree1 : 'tree_t)
    (tree2 : 'tree_t)
    = object (self)

  val mutable use_adjacency_cache = true
  val mutable use_similarity_cache = true
  val mutable use_mapping_comparison_cache = true

  method _is_incompatible nd11 nd12 nd21 nd22 =
    Node_mapping._is_incompatible tree1 tree2 nd11 nd12 nd21 nd22

  method is_incompatible nd11 nd12 nd21 nd22 =
    not (is_crossing nd11 nd12 nd21 nd22) && (self#_is_incompatible nd11 nd12 nd21 nd22)


  method is_crossing_or_incompatible nd11 nd12 nd21 nd22 =
    is_crossing nd11 nd12 nd21 nd22 || self#_is_incompatible nd11 nd12 nd21 nd22

  method select_p_pairs
      (p : 'node_t -> 'node_t -> 'node_t -> 'node_t -> bool)
      (pair_weight_list : ('node_t * 'node_t * weight_t) list)
      =
    (* returns p pairs and not p pairs *)

    let pair_weight_list =
      List.fast_sort
        (fun (n11, n12, _) (n21, n22, _) ->
          let c = Stdlib.compare n11#gindex n21#gindex in
          if c = 0 then
            Stdlib.compare n12#gindex n22#gindex
          else
            c
        ) pair_weight_list
    in

    begin %debug_block
      [%debug_log "select_p_pairs:"];
      List.iter (fun (n1, n2, w) -> [%debug_log "%a-%a %a" nups n1 nups n2 wps w]) pair_weight_list;
    end;

    let len = List.length pair_weight_list in

    if len > 1 then begin
      let a = Array.of_list pair_weight_list in
      let mat = Array.make_matrix len len false in
      for i = 0 to len - 2 do
        let nd11, nd12, _ = a.(i) in
        for j = i + 1 to len - 1 do
	  let nd21, nd22, _ = a.(j) in
	  let b =
	    if (nd11 == nd21 || nd12 == nd22) then
	      false
	    else
	      p nd11 nd12 nd21 nd22
	  in
	  mat.(i).(j) <- b;
	  mat.(j).(i) <- b
        done
      done;

      let nfriends_a = Array.make len 0 in
      for i = 0 to len - 1 do
        let c = ref 0 in
        for j = 0 to len - 1 do
	  if mat.(i).(j) then
	    incr c
        done;
        nfriends_a.(i) <- !c
      done;

      let sorted_idxs =
        List.fast_sort
	  (fun i j ->
	    let _, _, wi = a.(i) in
	    let _, _, wj = a.(j) in
	    let x = weight_compare wj wi in
	    if x = 0 then begin
	      let fi = nfriends_a.(i) in
	      let fj = nfriends_a.(j) in
	      weight_compare (weight_of_int fj) (weight_of_int fi)
	    end
	    else
	      x
	  ) (Xlist.range len)
      in

      let compat_idxs =
        List.fold_left
	  (fun l idx ->
	    if List.for_all (fun i -> mat.(i).(idx)) l then
	      idx :: l
	    else
	      l
	  ) [] sorted_idxs
      in

      let incompat_idxs =
        List.filter (fun i -> not (List.mem i compat_idxs)) (Xlist.range len)
      in

      let compat = List.map (fun i -> a.(i)) compat_idxs in
      let incompat = List.map (fun i -> a.(i)) incompat_idxs in

      begin %debug_block
        [%debug_log "select_p_pairs: p pairs:"];
        List.iter (fun (n1, n2, _) -> [%debug_log "%a-%a" nups n1 nups n2]) compat;
        [%debug_log "select_p_pairs: not p pairs:"];
        List.iter (fun (n1, n2, _) -> [%debug_log "%a-%a" nups n1 nups n2]) incompat;
      end;

      compat, incompat
    end
    else
      pair_weight_list, []

  method select_compatible_pairs (pair_weight_list : ('node_t * 'node_t * weight_t) list) =
    (* returns compat. pairs and incompat. pairs *)
    self#select_p_pairs
      (fun n11 n12 n21 n22 ->
        let b = not (self#is_incompatible n11 n12 n21 n22) in

        [%debug_log "%a-%a - %a-%a --> compatible:%B"
	  UID.ps n11#uid UID.ps n12#uid UID.ps n21#uid UID.ps n22#uid b];

        b
      ) pair_weight_list

  method select_compatible_and_not_crossing_pairs (pair_weight_list : ('node_t * 'node_t * weight_t) list) =
    self#select_p_pairs
      (fun n11 n12 n21 n22 ->
        let b =
	  not (is_crossing n11 n12 n21 n22) && not (self#is_incompatible n11 n12 n21 n22)
        in

        [%debug_log "%a-%a - %a-%a --> compatible_and_not_crossing:%B"
	  UID.ps n11#uid UID.ps n12#uid UID.ps n21#uid UID.ps n22#uid b];

        b
      ) pair_weight_list


  method get_boundary_key n1 n2 =
    if is_def n1 && is_def n2 then
      get_bn_opt n1, get_bn_opt n2
    else
      let get_def_bn_opt tree n =
        try
          let def = get_def_node tree n in
          get_bn_opt def
        with
          _ -> get_bn_opt n
      in
      get_def_bn_opt tree1 n1, get_def_bn_opt tree2 n2

  val mutable has_use_rename_opt = None

  val adjacency_cache =
    (Tbl3.create() : (('node_t * 'node_t) option, 'node_t, 'node_t,
                      float * ('node_t * 'node_t) list) Tbl3.t)

  method set_has_use_rename f =
    has_use_rename_opt <- Some f;
    Tbl3.clear adjacency_cache

  method _has_use_rename n1 n2 =
    match has_use_rename_opt with
    | Some f -> f n1 n2
    | None -> raise Not_found

  method has_use_rename x1 x2 =
    try
      self#_has_use_rename x1 x2
    with
      Not_found -> false

  method can_be_cached n1 n2 =
    let b =
      match has_use_rename_opt with
      | Some _ -> true
      | None ->
          try
            not (is_def n1 && is_def n2)
          with _ -> true
    in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b

  val mutable rename_pat_finalized_flag = false
  method finalize_rename_pat () =
    [%debug_log "rename patterns finalized"];
    rename_pat_finalized_flag <- true
  val rename_pat = (Xset.create 0 : (string * string) Xset.t)
  method add_rename_pat ((s1, s2) as sp) =
    let force = false in
    if force || s1 <> s2 then begin
      [%debug_log "\"%s\"-\"%s\"" s1 s2];
      Xset.add rename_pat sp
    end
  method is_rename_pat (s1, s2) =
    let b = Xset.mem rename_pat (s1, s2) in
    [%debug_log "\"%s\"-\"%s\" -> %B" s1 s2 b];
    b

  (*val mutable reliable_mappings_finalized_flag = false
  method finalize_reliable_mappings () =
    [%debug_log "reliable mappings finalized"];
    reliable_mappings_finalized_flag <- true
  val reliable_mappings = (Xset.create 0 : ('node_t * 'node_t) Xset.t)
  method add_reliable_mapping n1 n2 =
    [%debug_log "%a-%a" nups n1 nups n2];
    Xset.add reliable_mappings (n1, n2)
  method is_reliable_mapping n1 n2 =
    let b = Xset.mem reliable_mappings (n1, n2) in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b*)

  val ref_npairs = (new pairs : 'node_t pairs)
  method ref_npairs = ref_npairs

(* *)
  val permutation_hub_tbl = Hashtbl.create 0
  method add_permutation_hub_cand (n1 : 'node_t) (n2 : 'node_t) (lab : string) =
    [%debug_log "%a-%a %s" nugps n1 nugps n2 lab];
    let key = n1, n2, lab in
    try
      let c, lgi1, gi1, lgi2, gi2 = Hashtbl.find permutation_hub_tbl key in
      Hashtbl.replace permutation_hub_tbl key (c+1, lgi1, gi1, lgi2, gi2)
    with
      Not_found -> Hashtbl.add permutation_hub_tbl key (1, GI.dummy, GI.dummy, GI.dummy, GI.dummy)

  method finalize_permutation_hub_tbl() =
    let to_be_removed = ref [] in
    Hashtbl.iter
      (fun ((n1, n2, lab) as key) (c, _, _, _, _) ->
        let _ = lab in
        [%debug_log "%a-%a (%s): %d" nugps n1 nugps n2 lab c];
        if c < permutation_hub_count_thresh then begin
          to_be_removed := key :: !to_be_removed
        end
        else
          Hashtbl.replace permutation_hub_tbl key
            (c,
             (tree1#initial_leftmost n1)#gindex,
             n1#gindex,
             (tree2#initial_leftmost n2)#gindex,
             n2#gindex)
      ) permutation_hub_tbl;
    List.iter (Hashtbl.remove permutation_hub_tbl) !to_be_removed;

  method under_permutation_hub (n1 : 'node_t) (n2 : 'node_t) =
    let g1 = n1#gindex in
    let g2 = n2#gindex in
    let b =
    try
      Hashtbl.iter
        (fun (r1, r2, _) (_, lgi1, gi1, lgi2, gi2) ->
          let _ = r1 in
          let _ = r2 in
          if lgi1 <= g1 && g1 < gi1 && lgi2 <= g2 && g2 < gi2 then begin
            [%debug_log "found: %a-%a" nugps r1 nugps r2];
            raise Exit
          end
        ) permutation_hub_tbl;
      false
    with Exit -> true
    in
    [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
    b

  method under_permutation_hub1 (n1 : 'node_t) =
    let g1 = n1#gindex in
    let b =
    try
      Hashtbl.iter
        (fun (r1, r2, _) (_, lgi1, gi1, _, _) ->
          let _ = r1 in
          let _ = r2 in
          if lgi1 <= g1 && g1 < gi1 then begin
            [%debug_log "found: %a-%a" nps r1 nps r2];
            raise Exit
          end
        ) permutation_hub_tbl;
      false
    with Exit -> true
    in
    [%debug_log "%a -> %B" nps n1 b];
    b

  method under_permutation_hub2 (n2 : 'node_t) =
    let g2 = n2#gindex in
    let b =
    try
      Hashtbl.iter
        (fun (r1, r2, _) (_, _, _, lgi2, gi2) ->
          let _ = r1 in
          let _ = r2 in
          if lgi2 <= g2 && g2 < gi2 then begin
            [%debug_log "found: %a-%a" nps r1 nps r2];
            raise Exit
          end
        ) permutation_hub_tbl;
      false
    with Exit -> true
    in
    [%debug_log "%a -> %B" nps n2 b];
    b

  val mutable cache_path = ""

  val mutable is_possible_rename =
    ((fun ?(strict=false) _ _ -> ignore strict; true) : ?strict:bool -> 'node_t -> 'node_t -> bool)

  val is_possible_rename_cache = (Tbl3.create() : (bool, 'node_t, 'node_t, bool) Tbl3.t)

  method _is_possible_rename = is_possible_rename

  method is_possible_rename ?(strict=false) n1 n2 =
    try
      Tbl3.find is_possible_rename_cache strict n1 n2
    with
      Not_found ->
        let b = is_possible_rename ~strict n1 n2 in
        Tbl3.add is_possible_rename_cache strict n1 n2 b;
        b

  method set_is_possible_rename f =
    is_possible_rename <- f;
    Tbl3.clear is_possible_rename_cache

  val mutable def_bid_map1_set = false
  val mutable def_bid_map2_set = false
  method def_bid_maps_set = def_bid_map1_set && def_bid_map2_set

  val mutable def_bid_map1 = (Hashtbl.create 0 : (B.ID.t, B.ID.t) Hashtbl.t)
  val mutable def_bid_map2 = (Hashtbl.create 0 : (B.ID.t, B.ID.t) Hashtbl.t)
  method set_def_bid_map1 m = def_bid_map1 <- m; def_bid_map1_set <- true
  method set_def_bid_map2 m = def_bid_map2 <- m; def_bid_map2_set <- true

  val mutable def_use_tbl1_set = false
  val mutable def_use_tbl2_set = false
  method def_use_tbls_set = def_use_tbl1_set && def_use_tbl2_set

  val mutable def_use_tbl1 = Nodetbl.create 0
  val mutable def_use_tbl2 = Nodetbl.create 0
  method set_def_use_tbl1 tbl = def_use_tbl1 <- tbl; def_use_tbl1_set <- true
  method set_def_use_tbl2 tbl = def_use_tbl2 <- tbl; def_use_tbl2_set <- true

  method has_use_mapping nmapping n1 n2 =
    let b =
      let usel2 = try Nodetbl.find def_use_tbl2 n2 with _ -> [] in
      [%debug_log "uses2=[%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" usel2)];
      let uses2 = Xset.from_list usel2 in
      try
        List.iter
          (fun use1 ->
            [%debug_log "use1=%a" nups use1];
            try
              let use1' = nmapping#find use1 in
              [%debug_log "use1'=%a" nups use1'];
              if Xset.mem uses2 use1' then
                raise Found
            with
              Not_found -> ()
          ) (try Nodetbl.find def_use_tbl1 n1 with _ -> []);
        false
      with
        Found -> true
    in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b

  method scan_subtree_pair nd1 nd2 f =
    let xl1 = ref [] in
    let xl2 = ref [] in
    tree1#fast_scan_whole_initial_subtree nd1 (fun x1 -> xl1 := x1 :: !xl1);
    tree2#fast_scan_whole_initial_subtree nd2 (fun x2 -> xl2 := x2 :: !xl2);
    List.iter2 f !xl1 !xl2

  method is_scope_consistent_mapping
      ?(local=true)
      (nmapping : 'node_t Node_mapping.c)
      (nd1 : 'node_t)
      (nd2 : 'node_t)
      =
    is_use nd1 && is_use nd2 &&
    try
      let def1 = get_def_node tree1 nd1 in
      let def2 = get_def_node tree2 nd2 in
      let b =
        (not local || is_local_def def1 && is_local_def def2) &&
        nmapping#find def1 == def2
      in
      if b then begin
        [%debug_log "nd1=%a nd2=%a (%s)" nups nd1 nups nd2 nd1#data#to_string];
        [%debug_log "def1=%a def2=%a (%s)" nups def1 nups def2 def1#data#to_string];
      end;
      b
    with
      _ -> false

  method private _is_scope_breaking_mapping
      (nmapping : 'node_t Node_mapping.c)
      (n1 : 'node_t)
      (n2 : 'node_t)
      =
    [%debug_log "%a-%a" nups n1 nups n2];
    let b =
      try
        let b1 = n1#data#binding in
        let b2 = n2#data#binding in
        if B.is_use b1 && B.is_use b2 then begin
          [%debug_log "b1=%s b2=%s" (B.to_string b1) (B.to_string b2)];
          let xor a b = (a || b) && not (a && b) in
          if xor (B.has_loc b1) (B.has_loc b2) then begin
            [%debug_log "@"];
            false
          end
          else if self#def_bid_maps_set then begin
            let bi1 = B.get_bid b1 in
            let bi2 = B.get_bid b2 in
            [%debug_log "bi1=%a bi2=%a" B.ID.ps bi1 B.ID.ps bi2];
            (try
              let bi1' = Hashtbl.find def_bid_map1 bi1 in
              [%debug_log "%a -> %a" B.ID.ps bi1 B.ID.ps bi1'];
              bi1' <> bi2
            with
              Not_found -> false) ||
              (try
                let bi2' = Hashtbl.find def_bid_map2 bi2 in
                [%debug_log "%a <- %a" B.ID.ps bi2' B.ID.ps bi2];
                bi2' <> bi1
              with
                Not_found -> false)
          end
          else
            try
              let def_uid1 = B.get_uid b1 in
              let def_uid2 = B.get_uid b2 in
              let def1 = tree1#search_node_by_uid def_uid1 in
              let def2 = tree2#search_node_by_uid def_uid2 in
              [%debug_log "def1=%s" def1#data#to_string];
              [%debug_log "def2=%s" def2#data#to_string];
              let b =
                let def1_eq_def2 = def1#data#eq def2#data in
                not (def1_eq_def2 || def1#data#relabel_allowed def2#data) ||
                not def1_eq_def2 && is_local_def def1 && is_local_def def2 &&
                is_cross_boundary nmapping def1 def2 &&
                (
                 (
                  try
                    let def1' = nmapping#find def1 in
                    [%debug_log "def1'=%s" def1'#data#to_string];
                    def1' != def2 && def1'#data#eq def1#data &&
                    (
                     (
                      try
                        let bn1 = get_bn def1 in
                        not (nmapping#mem_dom bn1)
                      with _ -> true
                     ) ||
                     not (is_cross_boundary nmapping def1 def1')
                    )
                  with _ -> false
                 ) ||
                 (
                  try
                    let def2' = nmapping#inv_find def2 in
                    [%debug_log "def2'=%s" def2'#data#to_string];
                    def2' != def1 && def2'#data#eq def2#data &&
                    (
                     (
                      try
                        let bn2 = get_bn def2 in
                        not (nmapping#mem_cod bn2)
                      with _ -> true
                     ) ||
                     not (is_cross_boundary nmapping def2' def2)
                    )
                  with _ -> false
                 )
                )
              in
              [%debug_log "b=%B" b];
              b
            with _ ->
              failwith "Comparison.c#is_scope_breaking_mapping"
        end
        else if B.is_local_def b1 && B.is_local_def b2 then begin
          [%debug_log "@"];
          if self#def_use_tbls_set then
            not (self#has_use_mapping nmapping n1 n2)
          else
            failwith "Comparison.c#is_scope_breaking_mapping"
        end
        else
          raise Not_found
      with
        _ -> raise Not_found
    in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b

  method is_scope_breaking_mapping
      ?(subtree=false)
      (nmapping : 'node_t Node_mapping.c)
      (n1 : 'node_t)
      (n2 : 'node_t)
      =
    let b =
      try
        self#_is_scope_breaking_mapping nmapping n1 n2
      with
        _ -> begin
          [%debug_log "%a-%a: subtree=%B" nups n1 nups n2 subtree];
          if n1#data#is_primary && n2#data#is_primary then begin
            if subtree then begin
              try
                self#scan_subtree_pair n1 n2
                  (fun x1 x2 ->
                    try
                      if self#_is_scope_breaking_mapping nmapping x1 x2 then
                        raise Exit
                    with
                    | Failure _ | Not_found -> ()
                  );
                false
              with Exit -> true
            end
            else if
              n1#data#is_named_orig && n2#data#is_named_orig &&
              n1#data#anonymized_label <> n2#data#anonymized_label &&
              get_orig_name n1 = get_orig_name n2
            then begin
              [%debug_log "@"];
              false
            end
            else
            try
              tree1#fast_scan_whole_initial_subtree n1
                (fun x1 ->
                  try
                    let x2 = nmapping#find x1 in
                    if self#_is_scope_breaking_mapping nmapping x1 x2 then
                      raise Exit
                  with
                  | Failure _ | Not_found -> ()
                );
              false
            with Exit -> true
          end
          else begin
            n1#data#is_boundary && n2#data#is_boundary &&
            n1#data#is_named_orig && n2#data#is_named_orig &&
            try
              let bn1 = get_bn n1 in
              let bn2 = get_bn n2 in
              [%debug_log "bn1: %a" nps bn1];
              [%debug_log "bn2: %a" nps bn2];
              (
               try
                 nmapping#find bn1 != bn2
               with Not_found -> false
              ) ||
              (
               try
                 nmapping#inv_find bn2 != bn1
               with Not_found -> false
              )
            with
              _ -> false
          end
        end
    in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b

  val bad_pairs = (Xset.create 0 : ('node_t * 'node_t) Xset.t)
  method bad_pairs = bad_pairs
  method add_bad_pair n1 n2 =
    [%debug_log "%a-%a" nups n1 nups n2];
    Xset.add bad_pairs (n1, n2)
  method is_bad_pair n1 n2 = Xset.mem bad_pairs (n1, n2)

  val subtree_matches = (Xset.create 0 : ('node_t * 'node_t * int) Xset.t)
  method subtree_matches = subtree_matches

  method in_subtree_matches n1 n2 =
    let sz = tree1#fast_whole_initial_subtree_size n1 in
    Xset.mem subtree_matches (n1, n2, sz)

  method get_subtree_match_size n1 n2 =
    let sz = tree1#fast_whole_initial_subtree_size n1 in
    if Xset.mem subtree_matches (n1, n2, sz) then
      sz
    else
      raise Not_found

  method add_subtree_match ((nd, _, _) as elem) =
    let lgi = (tree1#initial_leftmost nd)#gindex in
    let gi = nd#gindex in
    try
      Xset.filter_inplace
        (fun (n0, _, _) ->
          let lgi0 = (tree1#initial_leftmost n0)#gindex in
          let gi0 = n0#gindex in
          if lgi0 <= lgi && gi < gi0 then
            raise Exit
          else if lgi <= lgi0 && gi0 < gi then
            false
          else
            true
        ) subtree_matches;
      Xset.add subtree_matches elem
    with
      Exit -> ()

  val mutable multiple_subtree_matches = (None : 'node_t multiple_subtree_matches option)
  method set_multiple_subtree_matches msm = multiple_subtree_matches <- Some msm
  method multiple_subtree_matches =
    match multiple_subtree_matches with
    | Some msm -> msm
    | None -> raise Not_found

  val mutable multiple_node_matches = (None : 'node_t multiple_node_matches option)
  method set_multiple_node_matches mnm = multiple_node_matches <- Some mnm
  method multiple_node_matches =
    match multiple_node_matches with
    | Some mnm -> mnm
    | None -> raise Not_found

  (*val adjacency_cache =
    (Tbl3.create() : (('node_t * 'node_t) option, 'node_t, 'node_t,
                      float * ('node_t * 'node_t) list) Tbl3.t)*)

  val mutable adjacency_cache_hit_count = 0

  val mapping_comparison_cache =
    (Tbl1.create() :
       (bool * bool * bool * bool
          * UID.t * UID.t * UID.t * UID.t,
        bool * int option * float option) Tbl1.t)

  val mutable mapping_comparison_cache_hit_count = 0

  val similarity_cache = (Tbl3.create() : ((bool * bool * bool(* * bool*)), UID.t, UID.t, float) Tbl3.t)
  val mutable similarity_cache_hit_count = 0

  val use_tbl1 = Hashtbl.create 0 (* bid -> node list *)
  val use_tbl2 = Hashtbl.create 0 (* bid -> node list *)

  val weak_node_eq_cache = (Tbl2.create() : ('node_t, 'node_t, bool) Tbl2.t)

  method private use_tbl_add tbl b n =
    try
      let l = Hashtbl.find tbl b in
      Hashtbl.replace tbl b (n::l)
    with
      Not_found -> Hashtbl.add tbl b [n]

  method get_use1 = Hashtbl.find use_tbl1
  method get_use2 = Hashtbl.find use_tbl2

  initializer
    if has_elaborate_edits then begin
      let scan tbl nd =
        let b = nd#data#binding in
        if B.is_use b then
          try
            let bid = B.get_bid b in
            self#use_tbl_add tbl bid nd
          with
            Not_found -> ()
      in
      tree1#scan_whole_initial (scan use_tbl1);
      tree2#scan_whole_initial (scan use_tbl2)
    end


  method tree1 = tree1
  method tree2 = tree2

  method use_adjacency_cache = use_adjacency_cache
  method size_of_adjacency_cache = Tbl3.length adjacency_cache

  method adjacency_cache_hit_count = adjacency_cache_hit_count

  method use_similarity_cache = use_similarity_cache
  method size_of_similarity_cache = Tbl3.length similarity_cache
  method similarity_cache_hit_count = similarity_cache_hit_count

  method use_mapping_comparison_cache = use_mapping_comparison_cache
  method set_use_mapping_comparison_cache = use_mapping_comparison_cache <- true
  method clear_use_mapping_comparison_cache = use_mapping_comparison_cache <- false

  method size_of_mapping_comparison_cache = Tbl1.length mapping_comparison_cache
  method mapping_comparison_cache_hit_count = mapping_comparison_cache_hit_count

  method cache_path = cache_path
  method set_cache_path p = cache_path <- p

  method has_non_trivial_value (nd : 'node_t) = nd#data#has_non_trivial_value
  method has_trivial_value (nd : 'node_t) = nd#data#has_value && not nd#data#has_non_trivial_value

  method weak_node_eq n1 n2 =
    (*let k = n1, n2 in*)
    try
      Tbl2.find weak_node_eq_cache n1 n2
    with Not_found ->
      let b =
        n1#data#eq n2#data ||
        n1#data#is_compatible_with ?weak:(Some false) n2#data
      in
      [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
      Tbl2.add weak_node_eq_cache n1 n2 b;
      b

  method has_weak_non_trivial_value =
    match multiple_node_matches with
    | Some mnm -> begin
        fun (nd : 'node_t) ->
          let b =
            nd#data#has_non_trivial_value ||
            nd#data#has_value &&
            try
              match mnm#find nd#data#_label with
              | [_], [_] -> true
              | _ -> false
            with
              Not_found -> false
          in
          [%debug_log "%a: %s -> %B" ups nd#uid (mnm#label_to_string nd#data#_label) b];
          (*if b then
            Printf.printf "! has_non_trivial_value: %s\n"
              (mnm#label_to_string nd#data#_label);*)
          b
    end
    | None -> fun nd -> nd#data#has_non_trivial_value

  method has_weak_non_trivial_tid =
    match multiple_node_matches with
    | Some mnm -> begin
        fun (nd : 'node_t) ->
          let b =
            nd#data#has_non_trivial_tid &&
            try
              match mnm#find nd#data#_label with
              | [_], [_] -> true
              | _ -> false
            with
              Not_found -> false
          in
          [%debug_log "%s -> %B" (mnm#label_to_string nd#data#_label) b];
          (*if b then
            Printf.printf "! has_non_trivial_tid: %s\n"
              (mnm#label_to_string nd#data#_label);*)
          b
    end
    | None -> fun nd -> nd#data#has_non_trivial_tid

  method has_weak_trivial_value =
    match multiple_node_matches with
    | Some mnm -> begin
        fun (nd : 'node_t) ->
          let b =
            nd#data#has_value && not nd#data#has_non_trivial_value ||
            try
              match mnm#find nd#data#_label with
              | _::_::_, _::_::_ -> true
              | _ -> false
            with
              _ -> false
          in
          [%debug_log "%s -> %B" (mnm#label_to_string nd#data#_label) b];
          (*if b then
            Printf.printf "! has_trivial_value: %s\n"
              (mnm#label_to_string nd#data#_label);*)
          b
    end
    | None -> fun nd -> nd#data#has_value && not nd#data#has_non_trivial_value

  method eval_label_match
      ?(bonus_named=false)
      ?(bonus_rename_pat=false)
      ?(check_uniq=false)
      ?(exact_only=false)
      nd1 nd2
      =
    let v =
      if nd1#data#eq nd2#data then begin

        let s =
          if bonus_named then
            if nd1#data#is_named_orig then
              get_label_match_eq_named_score nd1 (* 4 *)
            else
              label_match_eq_score (* 3 *)
          else
            label_match_eq_score (* 3 *)
        in
        if check_uniq then
          let extra =
            if nd1#data#is_op && self#has_uniq_subtree_match nd1 nd2 then begin
              let x = self#subtree_p_size tree1 (fun n -> n#data#is_named_orig) nd1 in
              [%debug_log "%a -> %d" nps nd1 x];
              x
            end
            else
              0
          in
          s + extra * 100
        (*else if self#is_reliable_mapping nd1 nd2 then
          s + 2*)
        else
          s

      end
      else if exact_only then
        0
      (*else if self#is_reliable_mapping nd1 nd2 then
        3 + 2*)
      else if nd1#data#_anonymized_label = nd2#data#_anonymized_label then
        if
          (*bonus_named && *)nd1#data#is_named && nd2#data#is_named &&
          (
           try
             self#is_rename_pat (get_orig_name nd1, get_orig_name nd2)
           with
             Not_found ->
               [%debug_log "%s -- %s" nd1#data#to_string nd2#data#to_string];
               false
          )
        (* || nd1#data#_stripped_label = nd2#data#_stripped_label*)
        then
          3 + if bonus_rename_pat then 2 else 0
        else if
          nd1#data#is_boundary && nd2#data#is_boundary &&
          nd1#data#is_named_orig && nd2#data#is_named_orig &&
          get_orig_name nd1 = get_orig_name nd2
        then begin
          [%debug_log "@"];
          3
        end
        else
          2
      else if nd1#data#_anonymized2_label = nd2#data#_anonymized2_label then begin
        try (* ADOPTED *)
          if (*get_orig_name nd1 = get_orig_name nd2*)nd1#data#get_name = nd2#data#get_name then
            2
          else
            1
        with
          Not_found -> 1
      end
      else
        0
    in
    [%debug_log "%a-%a --> %d" nps nd1 nps nd2 v];
(*
  begin %debug_block
  [%debug_log "%a-%a -> %d" nps nd1 nps nd2 v];
(*
  [%debug_log "anonymity level(0): (%s-%s)"
  nd1#data#label nd2#data#label];
  [%debug_log "anonymity level(1): (%s-%s)"
  nd1#data#anonymized_label nd2#data#anonymized_label];
  [%debug_log "anonymity level(2): (%s-%s)"
  nd1#data#anonymized2_label nd2#data#anonymized2_label];
 *)
  end;
 *)

    v

  method has_match1 (n1 : 'node_t) =
    let b =
      try
        match self#multiple_node_matches#find n1#data#_label with
        | _, [] | [], _ -> false
        | _ -> true
      with
        _ -> false
    in
    [%debug_log "%a -> %B" nps n1 b];
    b

  method has_match2 (n2 : 'node_t) =
    let b =
      try
        match self#multiple_node_matches#find n2#data#_label with
        | _, [] | [], _ -> false
        | _ -> true
      with
        _ -> false
    in
    [%debug_log "%a -> %B" nps n2 b];
    b

  method has_uniq_match n1 n2 =
    let b =
      n1#data#eq n2#data &&
      try
        match self#multiple_node_matches#find n1#data#_label with
        | _, [] | [], _ -> false
        | [x1], [x2] -> x1 == n1 && x2 == n2
        | _ -> false
      with
        _ -> false
    in
    (*[%debug_log "%a-%a -> %B" nps n1 nps n2 b];*)
    b

  method has_uniq_match1 n1 =
    let b =
      try
        match self#multiple_node_matches#find n1#data#_label with
        | _, [] | [], _ -> false
        | [x1], [_] -> x1 == n1
        | _ -> false
      with
        _ -> false
    in
    (*[%debug_log "%a -> %B" nps n1 b];*)
    b

  method has_uniq_match2 n2 =
    let b =
      try
        match self#multiple_node_matches#find n2#data#_label with
        | _, [] | [], _ -> false
        | [_], [x2] -> x2 == n2
        | _ -> false
      with
        _ -> false
    in
    (*[%debug_log "%a -> %B" nps n2 b];*)
    b

  val mutable num_to_be_notified1 = -1
  val mutable num_to_be_notified2 = -1

  method subtree_p_size tree pred rt =
    let c = ref 0 in
    tree#fast_scan_whole_initial_subtree rt
      (fun n ->
        if pred n then
          incr c
      );
    !c

  method get_num_to_be_notified1 () =
    if num_to_be_notified1 < 0 then begin
      let c = ref 0 in
      tree1#fast_scan_whole_initial
        (fun n ->
          if n#data#to_be_notified then
            incr c
        );
      num_to_be_notified1 <- !c;
      num_to_be_notified1
    end
    else
      num_to_be_notified1

  method get_num_to_be_notified2 () =
    if num_to_be_notified2 < 0 then begin
      let c = ref 0 in
      tree2#fast_scan_whole_initial
        (fun n ->
          if n#data#to_be_notified then
            incr c
        );
      num_to_be_notified2 <- !c;
      num_to_be_notified2
    end
    else
      num_to_be_notified2

  val many_matches_cache = Hashtbl.create 0

  method has_many_matches ?(thresh=0.6) (n : 'node_t) =
    let b =
      let lab = n#data#_label in
      try
        Hashtbl.find many_matches_cache lab
      with
        Not_found -> begin
          let b =
            try
              match self#multiple_node_matches#find lab with
              | _, [] | [], _ | [_], _ | _, [_] -> false
              | ns1, ns2 -> begin
                  let len1 = List.length ns1 in
                  let len2 = List.length ns2 in
                  let ntbn1 = self#get_num_to_be_notified1() in
                  let ntbn2 = self#get_num_to_be_notified2() in
                  [%debug_log "%a: %d(%d) %d(%d)" nps n len1 ntbn1 len2 ntbn2];
                  (float len1) > thresh *. (float ntbn1) ||
                  (float len2) > thresh *. (float ntbn2)
              end
            with
              _ -> false
          in
          [%debug_log "%a -> %B" nps n b];
          Hashtbl.add many_matches_cache lab b;
          b
        end
    in
    (*[%debug_log "%a -> %B" nps n b];*)
    b

  method has_uniq_match_within_boundary n1 n2 =
    let b =
      n1#data#eq n2#data &&
      try
        match self#multiple_node_matches#find n1#data#_label with
        | _, [] | [], _ -> false
        | [x1], [x2] -> x1 == n1 && x2 == n2
        | xl1, xl2 -> begin
            match self#get_boundary_key n1 n2 with
            | Some bn1, Some bn2 -> begin
                let filt bn = has_p_ancestor (fun x -> x == bn) in
                match List.filter (filt bn1) xl1, List.filter (filt bn2) xl2 with
                | [x1], [x2] -> x1 == n1 && x2 == n2
                | _ -> false
            end
            | _ -> false
        end
      with
        _ -> false
    in
    [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
    b

  method has_uniq_subtree_match n1 n2 =
    let b =
      self#in_subtree_matches n1 n2 ||
      n1#data#subtree_equals n2#data &&
      match n1#data#_digest with
      | Some d -> begin
          try
            match self#multiple_subtree_matches#find d with
            | [x1,_], [x2,_], _ -> x1 == n1 && x2 == n2
            | _ -> false
          with _ -> false
      end
      | None -> false
    in
    [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
    b

  method uniq_subtree_match_size n1 n2 =
    let sz =
      try
        self#get_subtree_match_size n1 n2
      with Not_found ->
        if n1#data#subtree_equals n2#data then
          match n1#data#_digest with
          | Some d -> begin
              try
                match self#multiple_subtree_matches#find d with
                | [x1,_], [x2,_], sz when x1 == n1 && x2 == n2 -> sz
                | _ -> 0
              with _ -> 0
          end
          | None -> 0
        else
          0
    in
    [%debug_log "%a-%a -> %d" nps n1 nps n2 sz];
    sz

  method has_uniq_subtree_match_within_boundary n1 n2 =
    let b =
      self#in_subtree_matches n1 n2 ||
      n1#data#subtree_equals n2#data &&
      match n1#data#_digest with
      | Some d -> begin
          try
            match self#multiple_subtree_matches#find d with
            | [x1,_], [x2,_], _ -> x1 == n1 && x2 == n2
            | xl1, xl2, _ -> begin
                match self#get_boundary_key n1 n2 with
                | Some bn1, Some bn2 -> begin
                    let filt bn (n, _) = has_p_ancestor (fun x -> x == bn) n in
                    match List.filter (filt bn1) xl1, List.filter (filt bn2) xl2 with
                    | [x1,_], [x2,_] -> x1 == n1 && x2 == n2
                    | _ -> false
                end
                | _ -> false
            end
          with _ -> false
      end
      | None -> false
    in
    [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
    b

  method get_child_having_use_rename n1 n2 =
    if n1#data#is_named && n2#data#is_named then
      let nm1 = n1#data#get_stripped_name in
      let nm2 = n2#data#get_stripped_name in
      [%debug_log "nm1=\"%s\" nm2=\"%s\"" nm1 nm2];
      let cl1 = ref [] in
      let cl2 = ref [] in
      Array.iter
        (fun c1 ->
          try
            let _ = B.get_bid c1#data#binding in
            let cnm1 = c1#data#get_stripped_name in
            [%debug_log "cnm1=\"%s\"" cnm1];
            if cnm1 = nm1 then
              cl1 := c1 :: !cl1
          with _ -> ()
        ) n1#initial_children;
      Array.iter
        (fun c2 ->
          try
            let _ = B.get_bid c2#data#binding in
            let cnm2 = c2#data#get_stripped_name in
            [%debug_log "cnm2=\"%s\"" cnm2];
            if cnm2 = nm2 then
              cl2 := c2 :: !cl2
          with _ -> ()
        ) n2#initial_children;
      match !cl1, !cl2 with
      | [c1], [c2] when self#has_use_rename c1 c2 -> c1, c2
      | _ -> raise Not_found
    else
      raise Not_found

  method child_has_use_rename n1 n2 =
    let b =
      try
        let _ = self#get_child_having_use_rename n1 n2 in
        true
      with Not_found -> false
    in
    [%debug_log "%s-%s --> %B" n1#data#to_string n2#data#to_string b];
    b

  method is_def_and_has_use_rename n1 n2 =
    let b =
      try
        is_def n1 && is_def n2 &&
        self#_has_use_rename n1 n2
      with _ -> false
    in
    if b then
      [%debug_log "%s-%s --> %B" n1#data#to_string n2#data#to_string b];
    b

  method eval_label_match_list
      ?(bonus_named=false)
      ?(bonus_rename_pat=false)
      ?(flat=false)
      ?(strip=false)
      ?(check_uniq=false)
      ?(exact_only=false)
      nds1 nds2
      =
    let getlab =
      if strip then
        fun n -> n#data#_stripped_label
      else
        fun n -> n#data#_label
    in
    let a1 = Array.of_list nds1 in
    let a2 = Array.of_list nds2 in

    let lab_a1 = Array.map getlab a1 in
    let lab_a2 = Array.map getlab a2 in

    begin %debug_block
      let to_str =
        Xarray.to_string
          (if strip then
            fun n -> n#data#stripped_label
          else
            fun n -> n#data#label) ";"
      in
      [%debug_log "a1: [%s]" (to_str a1)];
      [%debug_log "a2: [%s]" (to_str a2)];
    end;

    let mat, _, _, _ = Adiff.adiff lab_a1 lab_a2 in
    let mat1, mat2 = List.split mat in

    let anon_a1 =
      Array.mapi
        (fun i n -> if List.mem i mat1 then getlab n else n#data#_anonymized2_label)
        a1
    in
    let anon_a2 =
      Array.mapi
        (fun i n -> if List.mem i mat2 then getlab n else n#data#_anonymized2_label)
        a2
    in

    let mat, _, _, _ = Adiff.adiff anon_a1 anon_a2 in

    let score = ref 0.0 in
    let matches = ref [] in
    let nmcount = ref 0 in

    let has_uniq_match = self#has_uniq_match in

    List.iter
      (fun (i, j) ->
        let n1 = a1.(i) in
        let n2 = a2.(j) in
        let lm =
          if flat then begin
            let rename_pat_flag = ref false in
            (*if self#has_uniq_subtree_match n1 n2 then
              1.1
            else *)if n1#data#eq n2#data then
              if has_uniq_match n1 n2 then
                1.1
              else
                1.0
            else if
              not (Sourcecode.has_logical_pos n1) && not (Sourcecode.has_logical_pos n2) &&
              self#is_def_and_has_use_rename n1 n2
            then
              0.9
            else if
              n1#data#is_named && n2#data#is_named &&
              n1#data#_anonymized_label = n2#data#_anonymized_label &&
              try
                let p1 = n1#initial_parent in
                let p2 = n2#initial_parent in
                p1#data#is_named && p2#data#is_named &&
                let nm1 = get_orig_name n1 in
                let nm2 = get_orig_name n2 in
                (p1#data#eq p2#data || nm1 = get_orig_name p1 && nm2 = get_orig_name p2) &&
                (
                 rename_pat_flag := self#is_rename_pat (nm1, nm2);
                 !rename_pat_flag || n1#data#_stripped_label = n2#data#_stripped_label
                )
              with
                _ -> false
            then
              1.0 +.
              if
                bonus_rename_pat && !rename_pat_flag &&
                (self#has_use_rename n1 n2 || self#child_has_use_rename n1 n2)
              then
                0.5
              else
                0.0
            (*else if try get_orig_name n1 = get_orig_name n2 with _ -> false then
              0.8*)
            else
              0.7 (* subtree_similarity_thresh = 0.7 *)
          end
          else
            float (self#eval_label_match ~bonus_named ~bonus_rename_pat ~check_uniq ~exact_only n1 n2)
        in

        score := !score +. lm;

        if n1#data#is_named_orig && n1#data#eq n2#data then
          incr nmcount;
(* !!!
          nmcount := !nmcount + (try String.length n1#data#get_name with Not_found -> 0);
*)
        if options#use_adjacency_matches_flag then
          if n1#data#eq n2#data then
            matches := (n1, n2) :: !matches

      ) mat;
(*
      [%debug_log "eval_label_match_list[bonus_named:%B,flat:%B]: score=%f nmcount=%d"
        bonus_named flat !score !nmcount];
*)
    { lm_score=(!score);
      lm_matches=(!matches);
      lm_nmcount=(!nmcount);
    }

  method estimate_cost_of_move (nmapping : 'node_t Node_mapping.c) nd1 nd2 = (* cost = number of accompanying nodes *)
    estimate_cost_of_move tree1 tree2 nmapping nd1 nd2

  method find_ancestor_pairs_of_same_category rev_flag nd1 nd2 =
    let id x = x in
    let list_rev0 = if rev_flag then id else List.rev in
    let list_rev1 = if rev_flag then List.rev else id in

    let l1 = (tree1#initial_ancestor_nodeposs nd1) in
    let l2 = (tree2#initial_ancestor_nodeposs nd2) in

    let filt = List.filter (fun (n, p) -> not n#initial_children.(p)#data#is_order_insensitive) in
    let l1 = filt l1 in
    let l2 = filt l2 in

    let a1 = Array.of_list (list_rev0 l1) in
    let a2 = Array.of_list (list_rev0 l2) in

    let anon1 = Array.map (fun (n, _) -> n#data#_anonymized3_label) a1 in
    let anon2 = Array.map (fun (n, _) -> n#data#_anonymized3_label) a2 in

    [%debug_log "anon1: [%s]" (Xarray.to_string (fun (n, _) -> n#data#anonymized3_label) ";" a1)];
    [%debug_log "anon2: [%s]" (Xarray.to_string (fun (n, _) -> n#data#anonymized3_label) ";" a2)];

    let mat, _, _, _ = Adiff.adiff anon1 anon2 in

    let sorted =
      list_rev1
        (List.fast_sort (fun (i0, _) (i1, _) -> Stdlib.compare i0 i1) mat)
    in
(*
    let get_snd a i =
      try
        let n, _ = a.(i-1) in
        Some n
      with
        _ -> None
    in
*)
    List.map
      (fun (idx1, idx2) ->
        let nd1, pos1 = a1.(idx1) in
        let nd2, pos2 = a2.(idx2) in
(*
        let snd1 = get_snd a1 idx1 in
        let snd2 = get_snd a2 idx2 in
*)
        idx1, idx2, nd1, nd2, pos1, pos2
      ) sorted
(* end of method find_ancestor_pairs_of_same_category *)


  method get_ancestors_similarity
      ?(take_boundary=false)
      ?(strip=false)
      nd1 nd2
      =
    ignore strip;
    let _ancs1 = List.rev (tree1#initial_ancestor_nodes nd1) in
    let _ancs2 = List.rev (tree2#initial_ancestor_nodes nd2) in
    (*let flag =
      match _ancs1, _ancs2 with
      | a1::b1::_, a2::b2::_ ->
          a1#data#is_sequence && b1#data#is_boundary || a2#data#is_sequence && b2#data#is_boundary
      | _ -> false
    in*)
    let flag = take_boundary in
    let filt ancs =
      let _, l =
        List.fold_left
          (fun (skip, l) n ->
            if skip then
              (skip, l)
            else if n#data#is_boundary then
              (true, if flag then l @ [n] else l)
            else
              (skip, l @ [n])

          ) (false, []) ancs
      in
      l
    in
    let ancs1 = filt _ancs1 in
    let ancs2 = filt _ancs2 in
    if ancs1 = [] && ancs2 = [] then
      1.0
    else
      let res = self#eval_label_match_list ~flat:true(*!20240205! ~strip*) ancs1 ancs2 in
      let sim = (res.lm_score *. 2.0) /. (float ((List.length ancs1) + (List.length ancs2))) in
      sim



  method get_similarity_score
      ?(ignore_cache=false)
      ?(bonus_named=false)
      ?(flat=true)
      rt1 rt2 (* similarity [0.0,1.0] *)
      =
    let sim =
      try
        if not use_similarity_cache || ignore_cache then
          raise Not_found;

        let score =
          Tbl3.find similarity_cache
            (
             bonus_named,
             flat,
             rename_pat_finalized_flag
             (*,reliable_mappings_finalized_flag*)
            ) rt1#uid rt2#uid
        in

        similarity_cache_hit_count <- similarity_cache_hit_count + 1;

        score

      with
        Not_found ->

          if rt1#data#subtree_equals rt2#data then begin
(*
            let s =
              let c = ref 0 in
              let m = ref 0 in
              tree1#fast_scan_whole_initial_subtree rt1
                (fun n ->
                  incr c;
                  if n#data#is_named_orig then
                    m := !m + label_match_eq_named_score
                  else
                    m := !m + label_match_eq_score
                );
              (float !m) /. (float !c)
            in
*)
            let s = 1.0 in

            [%debug_log "[subtree match] %a-%a -> %f" nups rt1 nups rt2 s];

            if use_similarity_cache then
              Tbl3.add similarity_cache
                (
                 bonus_named,
                 flat,
                 rename_pat_finalized_flag
                 (*,reliable_mappings_finalized_flag*)
                ) rt1#uid rt2#uid s;
            s
          end
          else begin
            let nds1 = ref [] in
            let nds2 = ref [] in
            tree1#fast_scan_whole_initial_subtree rt1 (fun n -> nds1 := n :: !nds1);
            tree2#fast_scan_whole_initial_subtree rt2 (fun n -> nds2 := n :: !nds2);

            match !nds1, !nds2 with
            | [], _ | _, [] -> 0.0
            | _ ->
                let lmres =
                  self#eval_label_match_list
                    ~bonus_named ~bonus_rename_pat:true ~flat
                    !nds1 !nds2
                in
                let s =
                  (lmres.lm_score *. 2.0) /. (float ((List.length !nds1) + (List.length !nds2)))
                in

                [%debug_log "%a-%a -> %f" nups rt1 nups rt2 s];

                if use_similarity_cache then
                  Tbl3.add similarity_cache
                    (
                     bonus_named,
                     flat,
                     rename_pat_finalized_flag
                     (*,reliable_mappings_finalized_flag*)
                    ) rt1#uid rt2#uid s;
                s
          end
    in
    sim

  (* adjacency : similarity of the context *)
  method _get_adjacency_score ?(anchor=None) nd1 nd2 =

    [%debug_log "evaluating %a-%a..." nups nd1 nups nd2];

    try
      if not use_adjacency_cache then
        raise Not_found;

      let score, ref_npairs = Tbl3.find adjacency_cache anchor nd1 nd2 in

      adjacency_cache_hit_count <- adjacency_cache_hit_count + 1;

      [%debug_log "score: %a-%a -> %f" nups nd1 nups nd2 score];

      score, ref_npairs

    with
      Not_found ->

        let score = ref 0.0 in

        let ref_npairs = ref [] in

        let _incr_score
            ?(weight=1.0)
            ?(extra_denom=0)
            ?(bonus_named=false)
            ?(bonus_named_more=false)
            ?(check_uniq=false)
            ?(exact_only=false)
            nds1 nds2
            =

          [%debug_log "weight=%f extra_denom=%d bonus_named=%B bonus_named_more=%B"
            weight extra_denom bonus_named bonus_named_more];

          let len1 = List.length nds1 in
          let len2 = List.length nds2 in

          [%debug_log "nds1=[%s] (%d)" (Xlist.to_string (fun n -> n#data#label) ";" nds1) len1];
          [%debug_log "nds2=[%s] (%d)" (Xlist.to_string (fun n -> n#data#label) ";" nds2) len2];

          let lmres = self#eval_label_match_list ~bonus_named ~check_uniq ~exact_only nds1 nds2 in

          [%debug_log "score=%f nmcount=%d" lmres.lm_score lmres.lm_nmcount];
          begin %debug_block
            if lmres.lm_matches <> [] then begin
              [%debug_log "matches:"];
              List.iter
                (fun (n1, n2) ->
                  [%debug_log "  %a -- %a (%a-%a)" labps n1 labps n2 nups n1 nups n2]
                ) lmres.lm_matches
            end
          end;

          ref_npairs := lmres.lm_matches @ !ref_npairs;
          let s =
            let denom = float (len1 + len2 + extra_denom) in
            (lmres.lm_score *. 2.0) /. denom
          in
          let s' =
            if bonus_named_more then
              s +. (float lmres.lm_nmcount)
            else
              s
          in
          s' *. weight
        in

        let incr_score
            ?(weight=1.0)
            ?(extra_denom=0)
            ?(bonus_named=false)
            ?(bonus_named_more=false)
            nds1 nds2
            =
          let s = _incr_score ~weight ~extra_denom ~bonus_named ~bonus_named_more nds1 nds2 in
          score := !score +. s
        in

        let get_rightmost_descendants nd =
          let chk =
            (*if nd#data#is_boundary then
              fun n -> n#data#is_statement
            else*)
              fun _ -> true
          in
          let res = ref [] in
          let rec doit n =
            try
              let next = n#initial_children.(n#initial_nchildren - 1) in
              if chk next then
                res := next::!res;
              doit next
            with
              Invalid_argument _ -> ()
          in
          doit nd;

          [%debug_log "get_rightmost_descendants: %a -> [%a]" nups nd nsps !res];

          !res
        in

        let get_leftmost_descendants nd =
          let chk =
            (*if nd#data#is_boundary then
              fun n -> n#data#is_statement
            else*)
              fun _ -> true
          in
          let res = ref [] in
          let rec doit n =
            try
              let next = n#initial_children.(0) in
              if chk next then
                res := next::!res;
              doit next
            with
              Invalid_argument _ -> ()
          in
          doit nd;

          [%debug_log "get_leftmost_descendants: %a -> [%a]" nups nd nsps !res];

          !res
        in

        let get_descendants offset nd =
          [%debug_log "offset=%d nd=%a" offset nups nd];
          if offset < 0 then
            get_leftmost_descendants nd
          else if offset > 0 then
            get_rightmost_descendants nd
          else
            []
        in

        let rt1, rt2 = tree1#root, tree2#root in

(*
  let weq nd1 nd2 = nd1#data#anonymized2_label = nd2#data#anonymized2_label in (* to be tuned? *)
 *)
        let weq _ _ = true in

(*
        let get_n_skipped tree snd nd =
          match snd with
          | None -> 0
          | Some rt ->
              tree1#fast_size_of_initial_cluster (rt, [nd])
        in
*)
        let find_anchor nd1 nd2 =
          let rev_flag =
            try
              let pnd1 = nd1#initial_parent in
              let pnd2 = nd2#initial_parent in
              nd1#initial_nchildren = 0 && nd2#initial_nchildren = 0 &&
              not (nd1#data#eq nd2#data) &&
              pnd1#data#is_named && pnd2#data#is_named &&
              pnd1#initial_nchildren == 1 && pnd2#initial_nchildren == 1 &&
              not pnd1#data#is_named_orig && not pnd2#data#is_named_orig &&
              not
                (
                 let ppnd1 = pnd1#initial_parent in
                 let ppnd2 = pnd2#initial_parent in
                 pnd1#data#eq pnd2#data &&
                 ppnd1#data#is_named_orig && ppnd2#data#is_named_orig &&
                 ppnd1#initial_nchildren == 1 && ppnd2#initial_nchildren == 1 &&
                 ppnd1#data#get_orig_name = ppnd2#data#get_orig_name
                )
            with
              _ -> false
          in
          if rev_flag then begin
            [%debug_log "%a-%a (%a-%a)" nups nd1 nups nd2 locps nd1 locps nd2];
            (*Printf.printf "! rev_flag: %s\n" nd1#to_string*)
          end;

          let finish idx1 idx2 anc1 anc2 ipos1 ipos2 =
            let d = idx1 + idx2
                    (*(get_n_skipped tree1 snd1 nd1) + (get_n_skipped tree2 snd2 nd2)*)
            in
            let ichildren1 = anc1#initial_children in
            let ichildren2 = anc2#initial_children in
            let len1 = Array.length ichildren1 in
            let len2 = Array.length ichildren2 in
            let left = ipos1 >= 1 (* && *) || ipos2 >= 1 in
            let right = ipos1 <= len1 - 2 (* && *) || ipos2 <= len2 - 2 in
            (*if
               (not left || not right) &&
               match rest with
               | (_, _, a1, a2, ip1, ip2)::_ -> begin
                   a1 != rt1 && a2 != rt2 &&
                   not a1#data#is_boundary && not a2#data#is_boundary &&
                   not a1#initial_children.(ip1)#data#is_order_insensitive &&
                   not a2#initial_children.(ip2)#data#is_order_insensitive
               end
               | _ -> false
            then
              doit (lv+1) rest
            else*)
            (left, right, anc1, anc2, ipos1, ipos2, d)
          in

          let filt1, filt2 =
            match anchor with
            | Some (anchor1, anchor2) -> begin
                [%debug_log "anchor1=%a anchor2=%a" nups anchor1 nups anchor2];
                (fun x -> x == anchor1 || tree1#is_initial_ancestor x anchor1),
                (fun x -> x == anchor2 || tree2#is_initial_ancestor x anchor2)
            end
            | None -> (fun _ -> true), (fun _ -> true)
          in

          let rec doit lv = function
            | [] -> raise Not_found
            | (idx1, idx2, anc1, anc2, ipos1, ipos2)::rest ->
                [%debug_log "lv=%d anc1=%a anc2=%a" lv nups anc1 nups anc2];
                if anc1 == rt1 || anc2 == rt2 || anc1#data#is_boundary || anc2#data#is_boundary then
                  raise Not_found
                else begin
                  if rev_flag && anc1#initial_nchildren = 1 && anc2#initial_nchildren = 1 then
                    doit (lv+1) rest
                  else if not (filt1 anc1 && filt2 anc2) then
                    doit (lv+1) rest
                  else if weq anc1 anc2 then
                    finish idx1 idx2 anc1 anc2 ipos1 ipos2
                  else
                    doit (lv+1) rest

                end (* if not (anc1 == rt1... *)
          in
          doit 1 (self#find_ancestor_pairs_of_same_category rev_flag nd1 nd2)
        in (* find_anchor *)


        let _comp_score
            ?(weight=1.0)
            ?(bonus_named=false)
            ?(bonus_named_more=false)
            ?(extra_denom=0)
            n1 n2
            =
          if n1#data#subtree_equals n2#data then begin
            let sz = tree1#fast_whole_initial_subtree_size n1 in
            let nmcount = ref 0 in
            let s =
              if bonus_named then
                let m = ref 0 in
                tree1#fast_scan_whole_initial_subtree n1
                  (fun n ->
                    if n#data#is_named_orig then begin
                      m := !m + (get_label_match_eq_named_score n);
                      incr nmcount
                    end
                    else
                      m := !m + label_match_eq_score
                  );
                (float (2 * !m)) /. (float (2 * sz + extra_denom))

              else
                (float label_match_eq_score) *. ((float (2 * sz)) /. (float (2 * sz + extra_denom)))
            in
            let s' =
              if bonus_named_more then
                s +. (float !nmcount)
              else
                s
            in
            s' *. weight
          end
          else
            raise Not_found
        in

        let comp_score ?(weight=1.0) ?(bonus_named=false) ?(extra_denom=0) n1 n2 f =
          try
            let s = _comp_score ~weight ~bonus_named ~extra_denom n1 n2 in
            score := !score +. s
          with
            Not_found ->
              f ()
        in

        let score_lr ?(both=false) ?(extra=true) offset anc1 anc2 ipos1 ipos2 d =
          (* offset: 1 or -1 *)
          [%debug_log "offset=%d, ipos1=%d, ipos2=%d, d=%d" offset ipos1 ipos2 d];
          let ichildren1 = anc1#initial_children in
          let ichildren2 = anc2#initial_children in
          let offset' = -offset in

          begin
            try
              let lr1 = ichildren1.(ipos1 + offset) in
              let lr2 = ichildren2.(ipos2 + offset) in
              [%debug_log "lr1=%a lr2=%a" nups lr1 nups lr2];
              comp_score ~extra_denom:d ~bonus_named:true lr1 lr2
                (fun () ->
                  let lr_list1 = (get_descendants offset' lr1) @ [lr1] in
                  [%debug_log "lr_list1=[%s]"
                    (Xlist.to_string (fun n -> n#data#label) ";" lr_list1)];
                  let lr_list2 = (get_descendants offset' lr2) @ [lr2] in
                  [%debug_log "lr_list2=[%s]"
                    (Xlist.to_string (fun n -> n#data#label) ";" lr_list2)];
                  incr_score ~extra_denom:d ~bonus_named:true lr_list1 lr_list2;
                  if both then begin
                    let lr_list1' = (get_descendants offset lr1) in
                    let lr_list2' = (get_descendants offset lr2) in
                    incr_score ~extra_denom:d ~bonus_named:true lr_list1' lr_list2'
                  end
                )
            with
              Invalid_argument _ -> ()
          end;
          if extra then begin
            try (* extra addition *)
              let n1 = ichildren1.(ipos1 + offset * 2) in
              let n2 = ichildren2.(ipos2 + offset * 2) in

              comp_score ~extra_denom:d ~bonus_named:true n1 n2
                (fun () ->
                  let lst1 = (get_descendants offset' n1) @ [n1] in
                  let lst2 = (get_descendants offset' n2) @ [n2] in
                  incr_score ~extra_denom:d ~bonus_named:true lst1 lst2;
                  if both then begin
                    let lst1' = (get_descendants offset n1) in
                    let lst2' = (get_descendants offset n2) in
                    incr_score ~extra_denom:d ~bonus_named:true lst1' lst2'
                  end
                )
            with
              Invalid_argument _ -> ()
          end

        in (* end of func score_lr *)


        begin (* for left and right descendants *)
          try
            let left, right, anc1, anc2, pos1, pos2, d = find_anchor nd1 nd2 in

            [%debug_log "anchor for %a-%a: %a-%a (left=%B, right=%B, d=%d)"
              nups nd1 nups nd2 nups anc1 nups anc2 left right d];

(*
            if left && right then begin
              score_lr (-1) anc1 anc2 pos1 pos2 d;
              score_lr 1 anc1 anc2 pos1 pos2 d
            end
            else if left then
              score_lr ~both:true (-1) anc1 anc2 pos1 pos2 d
            else if right then
              score_lr ~both:true 1 anc1 anc2 pos1 pos2 d
*)
            if left then begin
              score_lr (-1) anc1 anc2 pos1 pos2 d;
              (*score_lr (-2) anc1 anc2 pos1 pos2 d*)
            end;
            if right then begin
              score_lr 1 anc1 anc2 pos1 pos2 d;
              (*score_lr 2 anc1 anc2 pos1 pos2 d*)
            end

          with
            Not_found -> ()
        end;
        [%debug_log "score for left and right descendants: %f" !score];

        (* for ancestors *)
        let ancs1 = List.rev (tree1#initial_ancestor_nodes nd1) in
        let ancs2 = List.rev (tree2#initial_ancestor_nodes nd2) in

        let score_anc = _incr_score ~weight:0.5 ~bonus_named:true ancs1 ancs2 in

        [%debug_log "score for ancestors: %f" score_anc];

        (* for descendants *)
        let score_desc =
          try
            _comp_score ~bonus_named:true ~bonus_named_more:true nd1 nd2
          with
            Not_found ->
              let desc1 = ref [] in
              let desc2 = ref [] in

              let target_cond tree x =
                let sz = tree#fast_whole_initial_subtree_size x in
                sz > 512
              in
              let is_target1 x =
                let b =
                  x#data#is_statement(* ||
                  x#data#has_non_trivial_value ||
                  self#has_uniq_match1 x*)
                in
                (*[%debug_log "%a -> %B" nups x b];*)
                b
              in
              let is_target2 x =
                let b =
                  x#data#is_statement(* ||
                  x#data#has_non_trivial_value ||
                  self#has_uniq_match2 x*)
                in
                (*[%debug_log "%a -> %B" nups x b];*)
                b
              in
              let filt1, filt2 =
                if
                  nd1#data#is_boundary && nd2#data#is_boundary &&
                  target_cond tree1 nd1 && target_cond tree2 nd2
                then
                  (fun nd n -> n != nd && is_target1 n),
                  (fun nd n -> n != nd && is_target2 n)
                else
                  let f = fun nd n -> n != nd in
                  f, f
              in
              tree1#fast_scan_whole_initial_subtree nd1
                (fun n ->
                  if filt1 nd1 n then
                    desc1 := n :: !desc1
                );
              tree2#fast_scan_whole_initial_subtree nd2
                (fun n ->
                  if filt2 nd2 n then
                    desc2 := n :: !desc2
                );
              match !desc1, !desc2 with
              | [], [] -> 0.0
              | [], _ | _, [] -> 0.0
              | _ ->
                  let check_uniq = nd1#data#is_boundary && nd2#data#is_boundary in
                  _incr_score ~bonus_named:true ~bonus_named_more:true ~check_uniq !desc1 !desc2
        in

        let score_siblings, score_parent =
          if
            nd1#initial_nchildren = 0 && nd2#initial_nchildren = 0 &&
            (self#under_permutation_hub nd1 nd2 ||
             nd1#data#eq nd2#data && self#has_trivial_value nd1)
          then begin
            [%debug_log "@"];
            (try
              let nds1 =
                List.filter (fun x -> x != nd1) (Array.to_list nd1#initial_parent#initial_children)
              in
              let nds2 =
                List.filter (fun x -> x != nd2) (Array.to_list nd2#initial_parent#initial_children)
              in
              _incr_score ~bonus_named:true ~bonus_named_more:true nds1 nds2
            with _ -> 0.0),
            (try
              self#get_adjacency_score nd1#initial_parent nd2#initial_parent
            with _ -> 0.0)
          end
          else if
             try
               not nd1#data#is_boundary && not nd2#data#is_boundary &&
               not (self#_has_use_rename nd1 nd2)
             with Not_found -> false
          then begin
            [%debug_log "@"];
            let rec get_sibl n =
              let pn = n#initial_parent in
              let siba = pn#initial_children in
              if Array.length siba > 1 then
                List.filter (fun x -> x != n) (Array.to_list siba)
              else
                get_sibl pn
            in
            (try
              let nds1 = get_sibl nd1 in
              let nds2 = get_sibl nd2 in
              let s = _incr_score ~bonus_named:true ~bonus_named_more:true nds1 nds2 in
              if s >= 0.0 then
                s
              else
                0.0
            with _ -> 0.0),
            0.0
          end
          else
            0.0, 0.0
        in (* score_siblings, score_parent *)

        (* for ancestor statement *)
        let score_stmt =
          let get_stmt = get_p_ancestor (fun x -> x#data#is_statement) in
          let filt1 n1 =
            (n1#data#is_named_orig || n1#data#has_non_trivial_value) &&
            self#has_uniq_match1 n1
          in
          let filt2 n2 =
            (n2#data#is_named_orig || n2#data#has_non_trivial_value) &&
            self#has_uniq_match2 n2
          in
          if
            nd1#data#is_statement || nd2#data#is_statement ||
            try
              not (is_use nd1) || not (is_use nd2)
            with _ -> true
          then
            0.0
          else
            try
              let stmt1 = get_stmt nd1 in
              let stmt2 = get_stmt nd2 in
              (*if not stmt1#data#is_named || not stmt2#data#is_named then
                raise Abort;*)
              let desc1 = ref [] in
              let desc2 = ref [] in
              tree1#preorder_scan_whole_initial_subtree stmt1
                (fun n1 ->
                  if filt1 n1 then
                    desc1 := n1 :: !desc1
                );
              tree2#preorder_scan_whole_initial_subtree stmt2
                (fun n2 ->
                  if filt2 n2 then
                    desc2 := n2 :: !desc2
                );
              [%debug_log "nd1: %a" nps nd1];
              [%debug_log "nd2: %a" nps nd2];
              [%debug_log "stmt1: %a" nps stmt1];
              [%debug_log "stmt2: %a" nps stmt2];
              match !desc1, !desc2 with
              | [], [] -> 0.0
              | [], _ | _, [] -> 0.0
              | _ -> _incr_score ~exact_only:true !desc1 !desc2
            with
              _ -> 0.0
        in

        let total_score =
          !score +. score_anc +. score_desc +. score_siblings +. score_parent +. score_stmt
        in

        begin %debug_block
          [%debug_log "score for descendants: %f" score_desc];
          [%debug_log "score=%f" !score];
          [%debug_log "score_anc=%f" score_anc];
          [%debug_log "score_desc=%f" score_desc];
          [%debug_log "score_siblings=%f" score_siblings];
          [%debug_log "score_parent=%f" score_parent];
          let head = if score_stmt > 0.0 then "!" else "" in
          [%debug_log "score_stmt=%s%f" head score_stmt];
          [%debug_log "total score: %a-%a -> %f" nups nd1 nups nd2 total_score];
          [%debug_log "ref_npairs: [%s]"
            (Xlist.to_string
               (fun (n1, n2) -> Printf.sprintf "%a-%a" nups n1 nups n2)
               ";" !ref_npairs)]
        end;

        if
          use_adjacency_cache &&
          self#can_be_cached nd1 nd2
        then begin
          (*let key = uid1, uid2 in*)
          (*let prev_score, _ = try Hashtbl.find adjacency_cache key with _ -> 0.0, [] in
          if total_score > prev_score then*)
          Tbl3.add adjacency_cache anchor nd1 nd2 (total_score, !ref_npairs)
        end;

        total_score, !ref_npairs
(* end of method _get_adjacency_score *)


  method get_adjacency_score ?(anchor=None) nd1 nd2 =
    let s, _ = self#_get_adjacency_score ~anchor nd1 nd2 in
    s



  method find_nearest_mapped_ancestor_pair
      (nmap : 'node_t -> 'node_t)
      (nd1 : 'node_t)
      (nd2 : 'node_t)
      =
    let rec doit nd =
      try
        let pnd = nd#initial_parent in
        try
          let pnd' = nmap pnd in
          if tree2#is_initial_ancestor pnd' nd2 then
            (pnd, pnd')
          else
            doit pnd
        with
          Not_found -> doit pnd
      with
        Otree.Parent_not_found _ -> raise Not_found
    in
    doit nd1

  method find_mapped_ancestor_pairs
      (nmap : 'node_t -> 'node_t)
      (nd1 : 'node_t)
      (nd2 : 'node_t)
      =
    let rec doit acc n1 n2 =
      try
        let pn1, pn2 = self#find_nearest_mapped_ancestor_pair nmap n1 n2 in
        doit ((pn1, pn2) :: acc) pn1 pn2
      with
        Not_found -> acc
    in
    doit [] nd1 nd2

(*
  method get_proximity (nd1 : node_t) (nd2 : node_t) =
    let ancs1 = Array.of_list nd1#initial_ancestor_nodes in
    let ancs2 = Array.of_list nd2#initial_ancestor_nodes in
    let lai1 = (Array.length ancs1) - 1 in
    let lai2 = (Array.length ancs2) - 1 in

    let _cands = ref [] in
    for i = lai1 downto 0 do
      let ni = ancs1.(i) in
      let labi = ni#data#_label in
      for j = lai2 downto 0 do
        let nj = ancs2.(j) in
        if labi = nj#data#_label then
          _cands := (ni, nj, i + j) :: !_cands
      done
    done;
    let cands =
      List.fast_sort
        (fun (_, _, p0) (_, _, p1) -> Stdlib.compare p1 p0)
        !_cands
    in
    let prox =
      match cands with
      | (n1, n2, p)::_ ->

            [%debug_log "c#get_proximity: (%a,%a) -> %d (pivot=%a-%a)"
              nups nd1 nups nd2 p nups n1 nups n2];

          p

      | [] -> 0
    in
    prox
(* end of method get_proximity *)
*)



  method check_parents ?(exact=true) (nmapping : 'node_t Node_mapping.c) nd1 nd2 =

    [%debug_log "checking: %a-%a" nups nd1 nups nd2];

    begin
      try
        let pnd1 = nd1#initial_parent in
        let pnd2 = nd2#initial_parent in

        [%debug_log "  parents: %a-%a" nups pnd1 nups pnd2];

        let cond_exact = exact && pnd1#data#eq pnd2#data in
        let cond_inexact =
          not exact && pnd1#data#relabel_allowed pnd2#data
        in

        if cond_exact || cond_inexact then begin

          let to_be_removed = ref [] in
          let add_ok = ref true in

          begin
            try
              let pnd1' = nmapping#find pnd1 in
              if pnd1' != pnd2 then
                if
                  not (next_to_each_other pnd2 pnd1') &&
                  self#get_adjacency_score pnd1 pnd2 > self#get_adjacency_score pnd1 pnd1'
                then
                  to_be_removed := (pnd1, pnd1') :: !to_be_removed
                else
                  add_ok := false
            with
              Not_found -> ()
          end;
          begin
            try
              let pnd2' = nmapping#inv_find pnd2 in
              if pnd2' != pnd1 then
                if
                  not (next_to_each_other pnd2' pnd2) &&
                  self#get_adjacency_score pnd1 pnd2 > self#get_adjacency_score pnd2' pnd2
                then
                  to_be_removed := (pnd2', pnd2) :: !to_be_removed
                else
                  add_ok := false
            with
              Not_found -> ()
          end;

          if !add_ok then begin
            if !to_be_removed <> [] then begin
              List.iter
                (fun (n1, n2) ->
                  [%debug_log "  removing %a-%a" nups n1 nups n2];
                  ignore (nmapping#remove n1 n2)
                ) !to_be_removed
            end;

            [%debug_log "  adding %a-%a" nups pnd1 nups pnd2];

            ignore (nmapping#add_unsettled pnd1 pnd2)
          end;

          self#check_parents ~exact nmapping pnd1 pnd2

        end (* of if pnd1#data#eq pnd2#data *)

      with
        Otree.Parent_not_found _ -> ()
    end


  method is_matched_subtree nmapping r1 r2 x =
    [%debug_log "%a %a: %a" nps r1 nps r2 nps x];
    let b =
      match x#data#_digest with
      | None -> false
      | Some d ->
          try
            match self#multiple_subtree_matches#find d with
            | [], _, _ | _, [], _ -> false
            | nml1, nml2, _ ->
                List.exists (fun (n1, _) -> tree1#is_initial_ancestor r1 n1) nml1 &&
                List.exists (fun (n2, _) -> tree2#is_initial_ancestor r2 n2) nml2
          with
            Not_found -> false
    in
    let b =
      b ||
      try
        match self#multiple_node_matches#find x#data#_label with
        | [], _ | _, [] -> false
        | nl1, nl2 ->
            let nl1_ = List.filter (tree1#is_initial_ancestor r1) nl1 in
            let nl2_ = List.filter (tree2#is_initial_ancestor r2) nl2 in
            match nl1_, nl2_ with
            | [], _ | _, [] -> false
            | [n1], [n2] -> begin
                let _ = n1 in
                let _ = n2 in
                [%debug_log "found: %a - %a" nps n1 nps n2];
                true
            end
            | _ -> begin
                List.exists
                  (fun n1 ->
                    try
                      let n1' = nmapping#find n1 in
                      let b = List.memq n1' nl2_ in
                      if b then
                        [%debug_log "found: %a - %a" nps n1 nps n1'];
                      b
                    with
                      Not_found -> false
                  ) nl1_
            end
      with
        Not_found -> false
    in
    if b then
      [%debug_log "%a -> %B" nps x b];
    b


  method has_matched_subtree nmapping r1 r2 ?(excluded=[]) n =
    let moveon x = not (List.memq x excluded) in
    has_p_descendant ~moveon (self#is_matched_subtree nmapping r1 r2) n


  method check_op_mappings_m nmapping _nd1 _nd2 nd1 nd2 =
    let b =
    _nd1 == nd1 &&
    (try not nd1#initial_parent#data#is_op with _ -> true) &&
    (try not _nd2#initial_parent#data#is_op with _ -> true) &&
    tree2#is_initial_ancestor _nd2 nd2 &&
    self#has_matched_subtree nmapping _nd1 _nd2 ~excluded:[nd2] _nd2 &&
    (tree2#fast_whole_initial_subtree_size nd2) * 2 < tree2#fast_whole_initial_subtree_size _nd2 &&
    Array.exists
      (fun x ->
        x#data#has_non_trivial_value &&
        Array.exists (fun y -> x#data#eq y#data) nd1#initial_children
      ) nd2#initial_children
  ||
    _nd2 == nd2 &&
    (try not nd2#initial_parent#data#is_op with _ -> true) &&
    (try not _nd1#initial_parent#data#is_op with _ -> true) &&
    tree1#is_initial_ancestor _nd1 nd1 &&
    self#has_matched_subtree nmapping _nd1 _nd2 ~excluded:[nd1] _nd1 &&
    (tree1#fast_whole_initial_subtree_size nd1) * 2 < tree1#fast_whole_initial_subtree_size _nd1 &&
    Array.exists
      (fun x ->
        x#data#has_non_trivial_value &&
        Array.exists (fun y -> x#data#eq y#data) nd2#initial_children
      ) nd1#initial_children
    in
    b && self#get_similarity_score _nd1 _nd2 > subtree_similarity_thresh


  method check_op_mappings nmapping size_nd1 size_nd2 _nd1 _nd2 nd1 nd2 =
    nd1 == _nd1 &&
    tree2#is_initial_ancestor _nd2 nd2 &&
    (try
      let n1 = nmapping#inv_find _nd2 in
      tree1#is_initial_ancestor nd1 n1 &&
      let sz_n1 = tree1#fast_whole_initial_subtree_size n1 in
      [%debug_log "sz_n1:%d size_nd2:%d" sz_n1 size_nd2];
      sz_n1 < size_nd2
    with
      _ -> false
    ) &&
    self#has_matched_subtree nmapping nd1 nd2 ~excluded:[_nd2] nd2
  ||
    nd2 == _nd2 &&
    tree1#is_initial_ancestor _nd1 nd1 &&
    (try
      let n2 = nmapping#find _nd1 in
      tree2#is_initial_ancestor nd2 n2 &&
      let sz_n2 = tree2#fast_whole_initial_subtree_size n2 in
      [%debug_log "sz_n2:%d size_nd1:%d" sz_n2 size_nd1];
      sz_n2 < size_nd1
    with
      _ -> false
    ) &&
    self#has_matched_subtree nmapping nd1 nd2 ~excluded:[_nd1] nd1


  method compare_mappings
      (nmapping : 'node_t Node_mapping.c)
      ?(override=false)
      ?(bonus_self=false)
      ?(bonus_parent=false)
      ?(force_prefer_crossing_count=false)
      nd1old nd2old ?(ncrossing_old=ref (-1)) ?(adjacency_old=ref (-1.0))
      (action_old :
         int option (* difference of ncrossing *) -> float option -> bool (*force*) -> unit)
      nd1new nd2new ?(ncrossing_new=ref (-1)) ?(adjacency_new=ref (-1.0))
      (action_new :
         int option (* difference of ncrossing *) -> float option -> bool (*force*) -> unit)
      =

    [%debug_log "[override:%B] %a-%a vs %a-%a" override
      nups nd1old nups nd2old nups nd1new nups nd2new];

    let add_cache ncross_used b ncd ncsim =
      if use_mapping_comparison_cache then
        if
          not ncross_used &&
          self#can_be_cached nd1old nd2old &&
          self#can_be_cached nd1new nd2new
        then
          Tbl1.add mapping_comparison_cache
            (override, bonus_self, bonus_parent, force_prefer_crossing_count,
             nd1old#uid, nd2old#uid, nd1new#uid, nd2new#uid)
            (b, ncd, ncsim)
    in

    begin
      try
        if not use_mapping_comparison_cache then
          raise Not_found;

        let b, ncross_diff, ncross_sim =
          Tbl1.find mapping_comparison_cache
            (override, bonus_self, bonus_parent, force_prefer_crossing_count,
             nd1old#uid, nd2old#uid, nd1new#uid, nd2new#uid)
        in

        [%debug_log "  cache hit! --> %B%s%s"
          b
          (match ncross_diff with Some i -> Printf.sprintf ", %d" i | None -> "")
          (match ncross_sim with Some x -> Printf.sprintf ", %f" x | None -> "")];

        if b then
          action_new ncross_diff ncross_sim false
        else
          action_old ncross_diff ncross_sim false;

        mapping_comparison_cache_hit_count <- mapping_comparison_cache_hit_count + 1;

      with
        Not_found ->

          let check_label_match ~ncross_used =
            let lmatch_old = self#eval_label_match nd1old nd2old in
            let lmatch_new = self#eval_label_match nd1new nd2new in

            [%debug_log "  label match: %d --> %d" lmatch_old lmatch_new];

            let b =
              if override then
                if lmatch_new >= lmatch_old then begin
                  action_new None None false;
                  true
                end
                else begin
                  action_old None None false;
                  false
                end
              else
                if lmatch_new > lmatch_old then begin
                  action_new None None false;
                  true
                end
                else begin
                  action_old None None false;
                  false
                end
            in
            add_cache ncross_used b None None
          in

          let check_adjacency ?(bonus_self=false) ?(bonus_parent=false) ~ncross_used () =
            let adj_old =
              if !adjacency_old < 0.0 then begin
                let bonus =
                  if nd1old#initial_nchildren = 0 && nd2old#initial_nchildren = 0 then begin
                    (if bonus_self then
                      float (self#eval_label_match ~bonus_named:true nd1old nd2old)
                    else
                      0.0) +.
                    (if bonus_parent && nd1old#data#is_named_orig && nd2old#data#is_named_orig then
                      try
                        let pnd1old = nd1old#initial_parent in
                        let pnd2old = nd2old#initial_parent in
                        if
                          pnd1old#data#is_named_orig && pnd1old#data#eq pnd2old#data &&
                          pnd1old#initial_nchildren = 1 && pnd2old#initial_nchildren = 1
                        then
                          let f = float (self#eval_label_match ~bonus_named:true pnd1old pnd2old) in
                          [%debug_log "bonus_parent: %f (%a-%a)" f nups nd1old nups nd2old];
                          f
                        else
                          0.0
                      with
                        _ -> 0.0
                    else
                      0.0)
                  end
                  else
                    0.0
                in
                adjacency_old := (self#get_adjacency_score nd1old nd2old) +. bonus;

                if bonus_self || bonus_parent then
                  [%debug_log "bonus=%f" bonus];

              end;
              !adjacency_old
            in
            let adj_new =
              if !adjacency_new < 0.0 then begin
                let bonus =
                  if nd1new#initial_nchildren = 0 && nd2new#initial_nchildren = 0 then begin
                    (if bonus_self then
                      float (self#eval_label_match ~bonus_named:true nd1new nd2new)
                    else
                      0.0) +.
                    (if bonus_parent && nd1new#data#is_named_orig && nd2new#data#is_named_orig then
                      try
                        let pnd1new = nd1new#initial_parent in
                        let pnd2new = nd2new#initial_parent in
                        if
                          pnd1new#data#is_named_orig && pnd1new#data#eq pnd2new#data &&
                          pnd1new#initial_nchildren = 1 && pnd2new#initial_nchildren = 1
                        then
                          let f = float (self#eval_label_match ~bonus_named:true pnd1new pnd2new) in
                          [%debug_log "bonus_parent: %f (%a-%a)" f nups nd1new nups nd2new];
                          f
                        else
                          0.0
                      with
                        _ -> 0.0
                    else
                      0.0)
                  end
                  else
                    0.0
                in
                adjacency_new := (self#get_adjacency_score nd1new nd2new) +. bonus;

                if bonus_self || bonus_parent then
                  [%debug_log "bonus=%f" bonus];

              end;
              !adjacency_new
            in

            [%debug_log " adjacency: %f --> %f" adj_old adj_new];

            if adj_old = adj_new then begin (* label match score is used *)

              check_label_match ~ncross_used

            end
            else begin (* adj_old <> adj_new *)
              let b =
                if adj_new > adj_old then begin
                  action_new None None false;
                  true
                end
                else begin
                  action_old None None false;
                  false
                end
              in
              add_cache ncross_used b None None
            end
          in (* check_adjacency *)

          let ancsim_old = self#get_ancestors_similarity nd1old nd2old in
          let ancsim_new = self#get_ancestors_similarity nd1new nd2new in

          (*!20240205!let ancsim_old, ancsim_new =
            if ancsim_old = ancsim_new then
              let take_boundary = true in
              let strip = true in
              self#get_ancestors_similarity ~take_boundary ~strip nd1old nd2old,
              self#get_ancestors_similarity ~take_boundary ~strip nd1new nd2new
            else
              ancsim_old, ancsim_new
          in*)

          [%debug_log "ancestors similarity: %f --> %f" ancsim_old ancsim_new];

          let has_matched_subtree = self#has_matched_subtree nmapping in

          let get_names nd =
            let _nl =
              List.map
                (fun x -> x#data#get_orig_name)
                (get_p_descendants (fun x -> x#data#is_named_orig) nd)
            in
            let nl =
              if nd#data#is_named_orig then
                nd#data#get_orig_name :: _nl
              else
                _nl
            in
            [%debug_log "%a -> [%s]" nups nd (Xlist.to_string Fun.id "," nl)];
            nl
          in
          let parent_check pivot pnd nd =
            let b =
              nd#initial_pos = 1 &&
              nd#initial_nchildren > 0 &&
              nd#data#is_named_orig &&
              pnd#initial_nchildren = 2 &&
              not pnd#data#is_op &&
              not pnd#data#is_named &&
              pivot#data#is_named_orig &&
              pivot#initial_nchildren > 0 &&
              let sib = pnd#initial_children.(0) in
              sib#initial_nchildren < 2 &&
              sib#data#_anonymized3_label <> pivot#data#_anonymized3_label &&
              pnd#data#_anonymized3_label <> pivot#data#_anonymized3_label &&
              nd#data#_anonymized3_label <> pivot#data#_anonymized3_label &&
              Xlist.intersection (get_names sib) (get_names pivot) = []
            in
            begin %debug_block
              if b then begin
                [%debug_log "!!!!!!! pivot=%a:%a[%a]" nups pivot labps pivot locps pivot];
                [%debug_log "parent=%a:%a[%a]" nups pnd labps pnd locps pnd];
                [%debug_log "nd=%a:%a[%a]" nups nd labps nd locps nd];
                let sib = pnd#initial_children.(0) in
                [%debug_log "sib=%a:%a[%a]" nups sib labps sib locps sib];
              end
            end;
            b
          in
          let anc_check pivot anc nd =
            let b =
              not pivot#data#is_op &&
              pivot#data#eq nd#data &&
              not (nd#data#eq anc#data) &&
              nd#data#_anonymized2_label <> anc#data#_anonymized2_label &&
              nd#data#_anonymized3_label <> anc#data#_anonymized3_label
            in
            [%debug_log "pivot=%a, anc=%a: %a -> %B" nugps pivot nugps anc nugps nd b];
            b
          in

          let ancsim_old, ancsim_new, prefer_sim =
            if nd1old == nd1new then
              if
                nd2old#initial_parent == nd2new &&
                (nd2new#initial_nchildren = 1 || parent_check nd1old nd2new nd2old)
              then
                ancsim_new, ancsim_new, true
              else if
                nd2old == nd2new#initial_parent &&
                (nd2old#initial_nchildren = 1 || parent_check nd1old nd2old nd2new)
              then
                ancsim_old, ancsim_old, true

              else if
                nd2old == nd2new#initial_parent &&
                nd2old#data#is_op &&
                nd2new#data#is_named_orig && nd1new#data#is_named_orig &&
                nd2new#data#_anonymized_label = nd1new#data#_anonymized_label
              then
                ancsim_new, ancsim_new, true
              else if
                nd2old#initial_parent == nd2new &&
                nd2new#data#is_op &&
                nd2old#data#is_named_orig && nd1old#data#is_named_orig &&
                nd2old#data#_anonymized_label = nd1old#data#_anonymized_label
              then
                ancsim_old, ancsim_old, true

              else if
                nd2old#initial_parent != nd2new &&
                anc_check nd1old nd2new nd2old &&
                tree2#is_initial_ancestor nd2new nd2old &&
                not (has_matched_subtree nd1new nd2new ~excluded:[nd2old] nd2new)
              then begin
                [%debug_log "!!!!! nd1old=%a -> nd2old=%a < nd2new=%a"
                  nugps nd1old nugps nd2old nugps nd2new];
                [%debug_log "nd1: %a" ndps nd1old];
                [%debug_log "nd2: %a < %a" ndps nd1old ndps nd1new];
                ancsim_new, ancsim_new, true
              end

              else if
                nd2old != nd2new#initial_parent &&
                anc_check nd1old nd2old nd2new &&
                tree2#is_initial_ancestor nd2old nd2new &&
                not (has_matched_subtree nd1old nd2old ~excluded:[nd2new] nd2old)
              then begin
                [%debug_log "!!!!! nd1old=%a -> nd2old=%a > nd2new=%a"
                  nugps nd1old nugps nd2old nugps nd2new];
                [%debug_log "nd1: %a" ndps nd1old];
                [%debug_log "nd2: %a > %a" ndps nd1old ndps nd1new];
                ancsim_old, ancsim_old, true
              end

              else if
                nd2old#initial_parent == nd2new#initial_parent &&
                nd1old#data#is_boundary && nd2old#data#is_boundary &&
                                           nd2new#data#is_boundary &&
                nd1old#data#is_named_orig && nd2old#data#is_named_orig &&
                                             nd2new#data#is_named_orig &&
                get_orig_name nd1old = get_orig_name nd2old &&
                get_orig_name nd1new = get_orig_name nd2new
              then begin
                [%debug_log "@"];
                ancsim_old, ancsim_new, true
              end

              else
                ancsim_old, ancsim_new, false

            else if nd2old == nd2new then
              if
                nd1old#initial_parent == nd1new &&
                (nd1new#initial_nchildren = 1 || parent_check nd2old nd1new nd1old)
              then
                ancsim_new, ancsim_new, true
              else if
                nd1old == nd1new#initial_parent &&
                (nd1old#initial_nchildren = 1 || parent_check nd2old nd1old nd1new)
              then
                ancsim_old, ancsim_old, true

              else if
                nd1old == nd1new#initial_parent &&
                nd1old#data#is_op &&
                nd1new#data#is_named_orig && nd2new#data#is_named_orig &&
                nd1new#data#_anonymized_label = nd2new#data#_anonymized_label
              then
                ancsim_new, ancsim_new, true
              else if
                nd1old#initial_parent == nd1new &&
                nd1new#data#is_op &&
                nd1old#data#is_named_orig && nd2old#data#is_named_orig &&
                nd1old#data#_anonymized_label = nd2old#data#_anonymized_label
              then
                ancsim_old, ancsim_old, true

              else if
                nd1old#initial_parent != nd1new &&
                anc_check nd2old nd1new nd1old &&
                tree1#is_initial_ancestor nd1new nd1old &&
                not (has_matched_subtree nd1new nd2new ~excluded:[nd1old] nd1new)
              then begin
                [%debug_log "!!!!! nd1old=%a < nd1new=%a <- nd2old=%a"
                  nugps nd1old nugps nd1new nugps nd2old];
                [%debug_log "nd2: %a" ndps nd2old];
                [%debug_log "nd1: %a < %a" ndps nd1old ndps nd1new];
                ancsim_new, ancsim_new, true
              end
              else if
                nd1old != nd1new#initial_parent &&
                anc_check nd2old nd1old nd1new &&
                tree1#is_initial_ancestor nd1old nd1new &&
                not (has_matched_subtree nd1old nd2old ~excluded:[nd1new] nd1old)
              then begin
                [%debug_log "!!!!! nd1old=%a > nd1new=%a <- nd2old=%a"
                  nugps nd1old nugps nd1new nugps nd2old];
                [%debug_log "nd2: %a" ndps nd2old];
                [%debug_log "nd1: %a > %a" ndps nd1old ndps nd1new];
                ancsim_old, ancsim_old, true
              end

              else if
                nd1old#initial_parent == nd1new#initial_parent &&
                nd1old#data#is_boundary && nd2old#data#is_boundary &&
                nd1new#data#is_boundary &&
                nd1old#data#is_named_orig && nd2old#data#is_named_orig &&
                nd1new#data#is_named_orig &&
                get_orig_name nd1old = get_orig_name nd2old &&
                get_orig_name nd1new = get_orig_name nd2new
              then begin
                [%debug_log "@"];
                ancsim_old, ancsim_new, true
              end

              else
                ancsim_old, ancsim_new, false
            else
              ancsim_old, ancsim_new, false
          in

          let anc_each_other1 n1 n2 =
            let b =
              tree1#is_initial_ancestor n1 n2
            ||
              tree1#is_initial_ancestor n2 n1
            in
            [%debug_log "%a %a --> %B" nups n1 nups n2 b];
            b
          in
          let anc_each_other2 n1 n2 =
            let b =
              tree2#is_initial_ancestor n1 n2
            ||
              tree2#is_initial_ancestor n2 n1
            in
            [%debug_log "%a %a --> %B" nups n1 nups n2 b];
            b
          in

          let prefer_sim =
            if
              prefer_sim &&
              nd1old == nd1new && anc_each_other2 nd2old nd2new ||
              nd2old == nd2new && anc_each_other1 nd1old nd1new
            then
              false
            else
              prefer_sim
          in

          [%debug_log "ancestors similarity: %f --> %f" ancsim_old ancsim_new];

          let anc_sim_ratio = min ancsim_old ancsim_new /. max ancsim_old ancsim_new in

          [%debug_log "ancestors similarity ratio: %f" anc_sim_ratio];

          [%debug_log "prefer_sim: %B" prefer_sim];

          let subtree_sim_old = self#get_similarity_score nd1old nd2old in
          let subtree_sim_new = self#get_similarity_score nd1new nd2new in

          [%debug_log "subtree similarity: %f --> %f" subtree_sim_old subtree_sim_new];

          let subtree_sim_ratio =
            min subtree_sim_old subtree_sim_new /. max subtree_sim_old subtree_sim_new
          in

          [%debug_log "subtree similarity ratio: %f" subtree_sim_ratio];

          let size_old1 = tree1#fast_whole_initial_subtree_size nd1old in
          let size_old2 = tree2#fast_whole_initial_subtree_size nd2old in
          let size_new1 = tree1#fast_whole_initial_subtree_size nd1new in
          let size_new2 = tree2#fast_whole_initial_subtree_size nd2new in

          let size_old = size_old1 + size_old2 in
          let size_new = size_new1 + size_new2 in

          [%debug_log "subtree size: %d --> %d" size_old size_new];

          let anc_sim_almost_same = anc_sim_ratio >= ancestors_similarity_ratio_thresh in
          let all_single = size_old = 2 && size_new = 2 in
          let all_double = size_old1 = 2 && size_old2 = 2 && size_new1 = 2 && size_new2 = 2 in
          let all_single_or_double = all_single || all_double in
          let chk_for_old () =
            all_single_or_double ||
            (nd1old == nd1new && tree2#is_initial_ancestor nd2new nd2old ||
            nd2old == nd2new && tree1#is_initial_ancestor nd1new nd1old)
          in
          let chk_for_new () =
            all_single_or_double ||
            (nd1old == nd1new && tree2#is_initial_ancestor nd2old nd2new ||
            nd2old == nd2new && tree1#is_initial_ancestor nd1old nd1new)
          in

          begin %debug_block
            [%debug_log "anc_sim_almost_same: %B (thresh=%f)"
              anc_sim_almost_same ancestors_similarity_ratio_thresh];
            [%debug_log "all_single: %B" all_single];
            [%debug_log "all_double: %B" all_double];
          end;

          let _is_plausible nd1 nd2 =
            let b =
             (nd2#data#is_named_orig &&
              not nd2#data#is_string_literal &&
              self#has_weak_non_trivial_value nd1 &&
              let v = nd1#data#get_value in
              let nm = nd2#data#get_name in
              [%debug_log "v=%s nm=%s" v nm];
              let count = ref 0 in
              try
                nmapping#iter
                  (fun n1 n2 ->
                    if try n1#data#get_value = v && n2#data#get_name = nm with _ -> false then begin
                      incr count;
                      if !count > 1 then
                        raise Exit
                    end
                  );
                false
              with
                Exit -> true) ||
            (nd1#data#is_named_orig &&
             not nd1#data#is_string_literal &&
             self#has_weak_non_trivial_value nd2 &&
             let nm = nd1#data#get_name in
             let v = nd2#data#get_value in
             [%debug_log "nm=%s v=%s" nm v];
             let count = ref 0 in
             try
               nmapping#iter
                 (fun n1 n2 ->
                   if try n1#data#get_name = nm && n2#data#get_value = v with _ -> false then begin
                     incr count;
                     if !count > 1 then
                       raise Exit
                   end
                 );
               false
             with
               Exit -> true)
            in
            [%debug_log "%a-%a -> %B" nups nd1 nups nd2 b];
            b
          in
          let is_plausible nd1 nd2 =
            try
              _is_plausible nd1 nd2
            with _ -> false
          in
          let tid_eq nd1 nd2 =
            [%debug_log "%a-%a" nups nd1 nups nd2];
            let b =
              self#has_weak_non_trivial_tid nd1 &&
              self#has_weak_non_trivial_tid nd2 &&
              nd1#data#eq nd2#data
            in
            [%debug_log "%a-%a -> %B" nups nd1 nups nd2 b];
            b
          in
          let has_same_subtree nd1 nd2 =
            [%debug_log "%a-%a" nups nd1 nups nd2];
            let b =
              let nc = nd1#initial_nchildren in
              nc = 2 &&
              nd2#initial_nchildren = nc &&
              try
                for i = nc - 1 downto 0 do
                  let cnd1 = nd1#initial_children.(i) in
                  let cnd2 = nd2#initial_children.(i) in
                  if cnd1#data#subtree_equals cnd2#data then
                    raise Exit
                done;
                false
              with
                Exit -> true
            in
            [%debug_log "%a-%a -> %B" nups nd1 nups nd2 b];
            b
          in
          let in_similar_context nd1 nd2 =
            let b =
              try
                nd1#initial_parent#data#is_sequence &&
                nd2#initial_parent#data#is_sequence &&
                let pos1 = nd1#initial_pos in
                let pos2 = nd2#initial_pos in
                [%debug_log "pos1=%d pos2=%d" pos1 pos2];
                let siblings1 = nd1#initial_parent#initial_children in
                let siblings2 = nd2#initial_parent#initial_children in
                let left1 = siblings1.(pos1-1) in
                let left2 = siblings2.(pos2-1) in
                [%debug_log "left1=%a left2=%a" nups left1 nups left2];
                let right1 = siblings1.(pos1+1) in
                let right2 = siblings2.(pos2+1) in
                [%debug_log "right1=%a right2=%a" nups right1 nups right2];
                left1#data#eq left2#data && right1#data#eq right2#data &&
                (left1#data#subtree_equals left2#data ||
                right1#data#subtree_equals right2#data)
              with
                _ -> false
            in
            [%debug_log "%a-%a -> %B" nups nd1 nups nd2 b];
            b
          in

          let in_no_seq n =
            let seq_flag = ref false in
            try
              let _ =
                get_p_ancestor
                  (fun x ->
                    if not !seq_flag && x#data#is_sequence then
                      seq_flag := true;
                    x#data#is_boundary
                  ) n
              in
              not !seq_flag
            with
              _ -> false
          in
          let all_in_no_seq () =
            let b =
              List.for_all in_no_seq [nd1old;nd2old;nd1new;nd2new]
            in
            [%debug_log "%B" b];
            b
          in
          let is_stable_ntuple n1 n2 =
            let b =
              n1#data#is_ntuple && n2#data#is_ntuple &&
              n1#data#is_named && n2#data#is_named &&
              try
                let pn1 = n1#initial_parent in
                let pn2 = n2#initial_parent in
                pn1#data#is_named && pn2#data#is_named &&
                pn1#data#get_name = n1#data#get_name &&
                pn2#data#get_name = n2#data#get_name
              with _ -> false
            in
            [%debug_log "%B" b];
            b
          in

          let anc_each_other_opt_ref = ref None in
          let anc_each_other () =
            match !anc_each_other_opt_ref with
            | Some b -> b
            | _ ->
                let b =
                  let b0 = nd1old == nd1new && anc_each_other2 nd2old nd2new in
                  [%debug_log "b0=%B" b0];
                  b0
                ||
                  let b1 = nd2old == nd2new && anc_each_other1 nd1old nd1new in
                  [%debug_log "b1=%B" b1];
                  b1
                in
                anc_each_other_opt_ref := Some b;
                b
          in

          let has_common_subtree n1 n2 =
            let b =
              Array.exists
                (fun c1 ->
                  Array.exists
                    (fun c2 ->
                      c1#data#subtree_equals c2#data
                    ) n2#initial_children
                ) n1#initial_children
            in
            [%debug_log "%a %a --> %B" nups n1 nups n2 b];
            b
          in
          (*let has_reliable_rename n1 n2 =
            let b =
              let b0 =
                n1#data#is_named && n2#data#is_named &&
                is_use n1 && is_use n2 &&
                try
                  let def1 = get_def_node tree1 n1 in
                  let def2 = get_def_node tree2 n2 in
                  nmapping#find def1 == def2
                with _ -> false
              in
              b0 ||
              Array.exists
                (fun c1 ->
                  Array.exists
                    (fun c2 ->
                      c1#data#is_named && c2#data#is_named &&
                      is_use c1 && is_use c2 &&
                      try
                        let def1 = get_def_node tree1 c1 in
                        let def2 = get_def_node tree2 c2 in
                        nmapping#find def1 == def2
                      with _ -> false
                    ) n2#initial_children
                ) n1#initial_children
            in
            [%debug_log "%a %a --> %B" nups n1 nups n2 b];
            b
          in*)

          [%debug_log "@"];

          if
            try
              let pnd1old = nd1old#initial_parent in
              let pnd2old = nd2old#initial_parent in
              let pnd1new = nd1new#initial_parent in
              let pnd2new = nd2new#initial_parent in
              pnd1old#data#is_boundary && pnd2old#data#is_boundary &&
              pnd1old#data#is_named_orig && pnd2old#data#is_named_orig &&
              pnd1new#data#is_boundary && pnd2new#data#is_boundary &&
              pnd1new#data#is_named_orig && pnd2new#data#is_named_orig &&
              get_orig_name pnd1old = get_orig_name pnd2old &&
              nmapping#find pnd1old == pnd2old
            with _ -> false
          then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_old None None false;
              false, None, None
            in
            add_cache false b ncd ncsim
          end
          else if
            try
              let pnd1old = nd1old#initial_parent in
              let pnd2old = nd2old#initial_parent in
              let pnd1new = nd1new#initial_parent in
              let pnd2new = nd2new#initial_parent in
              pnd1old#data#is_boundary && pnd2old#data#is_boundary &&
              pnd1old#data#is_named_orig && pnd2old#data#is_named_orig &&
              pnd1new#data#is_boundary && pnd2new#data#is_boundary &&
              pnd1new#data#is_named_orig && pnd2new#data#is_named_orig &&
              get_orig_name pnd1new = get_orig_name pnd2new &&
              nmapping#find pnd1new == pnd2new
             with _ -> false
          then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_new None None false;
              true, None, None
            in
            add_cache false b ncd ncsim
          end
          else if
            (
             nd1old#data#is_common && nd2old#data#is_common &&
             nd1new#data#is_common && nd2new#data#is_common
           (*||
             nd1old#data#is_statement && not nd1old#data#is_named &&
             nd2old#data#is_statement && not nd2old#data#is_named &&
             nd1new#data#is_statement && not nd1new#data#is_named &&
             nd2new#data#is_statement && not nd2new#data#is_named*)
           (*||
             not nd1old#data#is_named_orig && not nd2old#data#is_named_orig &&
             not nd1new#data#is_named_orig && not nd2new#data#is_named_orig &&
             nd1old#data#_anonymized_label = nd2old#data#_anonymized_label*)
            ) &&
            not (is_cross_boundary nmapping nd1old nd2old) &&
            is_cross_boundary nmapping nd1new nd2new
          then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_old None None false;
              false, None, None
            in
            add_cache false b ncd ncsim
          end
          else if
            (
             nd1old#data#is_common && nd2old#data#is_common &&
             nd1new#data#is_common && nd2new#data#is_common
           (*||
             nd1old#data#is_statement && not nd1old#data#is_named &&
             nd2old#data#is_statement && not nd2old#data#is_named &&
             nd1new#data#is_statement && not nd1new#data#is_named &&
             nd2new#data#is_statement && not nd2new#data#is_named*)
           (*||
             not nd1old#data#is_named_orig && not nd2old#data#is_named_orig &&
             not nd1new#data#is_named_orig && not nd2new#data#is_named_orig &&
             nd1new#data#_anonymized_label = nd2new#data#_anonymized_label*)
            ) &&
            is_cross_boundary nmapping nd1old nd2old &&
            not (is_cross_boundary nmapping nd1new nd2new)
          then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_new None None false;
              true, None, None
            in
            add_cache false b ncd ncsim
          end
          else if
            ancsim_old > 1.0 && ancsim_new < 1.0 && subtree_sim_new = 1.0
              && all_in_no_seq() && boundary_mapped nmapping#find nd1old nd2old
          ||
            ancsim_old = 1.0 && subtree_sim_old = 1.0 && ancsim_new < 1.0 && subtree_sim_new < 1.0
          (*||
            size_old > 4 && size_new > 4 &&
            subtree_sim_old = 1.0 && not (is_cross_boundary nmapping nd1old nd2old) &&
            subtree_sim_new < 1.0 && is_cross_boundary nmapping nd1new nd2new
          ||
            self#is_scope_consistent_mapping nmapping nd1old nd2old &&
            not (self#is_scope_consistent_mapping nmapping nd1new nd2new)*)
          ||
            anc_sim_almost_same && subtree_sim_old = 1.0 && subtree_sim_new < 1.0 && chk_for_old()
          ||
            is_plausible nd1old nd2old && not (is_plausible nd1new nd2new)
          ||
            tid_eq nd1old nd2old && not (tid_eq nd1new nd2new)
          ||
            not (anc_each_other()) &&
            has_same_subtree nd1old nd2old && not (has_same_subtree nd1new nd2new)
          ||
            in_similar_context nd1old nd2old && not (in_similar_context nd1new nd2new)
          ||
            nmapping#is_stable_pair nd1old nd2old && not (nmapping#is_stable_pair nd1new nd2new)
          ||
            prefer_sim && subtree_sim_old > subtree_sim_new
          ||
            is_stable_ntuple nd1old nd2old && not (is_stable_ntuple nd1new nd2new)
          ||
            anc_each_other() &&
            nd1old#data#is_named &&
            nd1old#data#is_named_orig = nd2old#data#is_named_orig &&
            (
             nd1old#data#eq nd2old#data && not (nd1new#data#eq nd2new#data) ||
             try
               get_orig_name nd1old = get_orig_name nd2old &&
               not (get_orig_name nd1new = get_orig_name nd2new)
             with _ -> false
            )
          ||
            nd1old == nd1new && nd1old#data#is_named &&
            nd1old#data#eq nd2old#data && not (nd1old#data#eq nd2new#data) &&
            (try
              let pnd1old = nd1old#initial_parent in
              let pnd2old = nd2old#initial_parent in
              let pnd2new = nd2new#initial_parent in
              anc_each_other2 pnd2old pnd2new &&
              pnd1old#data#eq pnd2old#data && not (pnd1old#data#eq pnd2new#data)
            with _ -> false)
          ||
            nd2old == nd2new && nd2old#data#is_named &&
            nd2old#data#eq nd1old#data && not (nd2old#data#eq nd1new#data) &&
            (try
              let pnd2old = nd2old#initial_parent in
              let pnd1old = nd1old#initial_parent in
              let pnd1new = nd1new#initial_parent in
              anc_each_other1 pnd1old pnd1new &&
              pnd2old#data#eq pnd1old#data && not (pnd2old#data#eq pnd1new#data)
            with _ -> false)
          ||
            nd1old == nd1new && nd1old#data#is_named &&
            nd1old#data#eq nd2old#data && nd1old#data#eq nd2new#data &&
            (
             let _ = [%debug_log "@@@ %a--[%a,%a]" nups nd1old nups nd2old nups nd2new] in
             has_common_subtree nd1old nd2old && not (has_common_subtree nd1new nd2new)
           (*||
             has_reliable_rename nd1old nd2old && not (has_reliable_rename nd1new nd2new)*)
           (*||
             try
              let pnd1old = nd1old#initial_parent in
              let pnd2old = nd2old#initial_parent in
              let pnd1new = nd1new#initial_parent in
              let pnd2new = nd2new#initial_parent in
              pnd1old#data#is_statement &&
              pnd1old#data#eq pnd2old#data && not (pnd1new#data#eq pnd2new#data)
             with _ -> false*)
            )
          ||
            nd2old == nd2new && nd2old#data#is_named &&
            nd2old#data#eq nd1old#data && nd2old#data#eq nd1new#data &&
            (
             let _ = [%debug_log "@@@ [%a,%a]--%a" nups nd1old nups nd2old nups nd2new] in
             has_common_subtree nd1old nd2old && not (has_common_subtree nd1new nd2new)
           (*||
             has_reliable_rename nd1old nd2old && not (has_reliable_rename nd1new nd2new)*)
           (*||
             try
              let pnd1old = nd1old#initial_parent in
              let pnd2old = nd2old#initial_parent in
              let pnd1new = nd1new#initial_parent in
              let pnd2new = nd2new#initial_parent in
              pnd1old#data#is_statement &&
              pnd1old#data#eq pnd2old#data && not (pnd1new#data#eq pnd2new#data)
             with _ -> false*)
            )
        (*||
        (subtree_sim_old > subtree_sim_new && subtree_sim_ratio < subtree_similarity_ratio_cutoff)*)
          then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_old None None false;
              false, None, None
            in
            add_cache false b ncd ncsim
          end
          else if
            ancsim_new > 1.0 && ancsim_old < 1.0 && subtree_sim_old = 1.0
              && all_in_no_seq() && boundary_mapped nmapping#find nd1new nd2new
          ||
            ancsim_new = 1.0 && subtree_sim_new = 1.0 && ancsim_old < 1.0 && subtree_sim_old < 1.0
          (*||
            size_old > 4 && size_new > 4 &&
            subtree_sim_new = 1.0 && not (is_cross_boundary nmapping nd1new nd2new) &&
            subtree_sim_old < 1.0 && is_cross_boundary nmapping nd1old nd2old
          ||
            self#is_scope_consistent_mapping nmapping nd1new nd2new &&
            not (self#is_scope_consistent_mapping nmapping nd1old nd2old)*)
          ||
            anc_sim_almost_same && subtree_sim_new = 1.0 && subtree_sim_old < 1.0 && chk_for_new()
          ||
            is_plausible nd1new nd2new && not (is_plausible nd1old nd2old)
          ||
            tid_eq nd1new nd2new && not (tid_eq nd1old nd2old)
          ||
            not (anc_each_other()) &&
            has_same_subtree nd1new nd2new && not (has_same_subtree nd1old nd2old)
          ||
            in_similar_context nd1new nd2new && not (in_similar_context nd1old nd2old)
          ||
            nmapping#is_stable_pair nd1new nd2new && not (nmapping#is_stable_pair nd1old nd2old)
          ||
            prefer_sim && subtree_sim_new > subtree_sim_old
          ||
            is_stable_ntuple nd1new nd2new && not (is_stable_ntuple nd1old nd2old)
          ||
            anc_each_other() &&
            nd1new#data#is_named &&
            nd1new#data#is_named_orig = nd2new#data#is_named_orig &&
            (
             nd1new#data#eq nd2new#data && not (nd1old#data#eq nd2old#data) ||
             try
               get_orig_name nd1new = get_orig_name nd2new &&
               not (get_orig_name nd1old = get_orig_name nd2old)
             with _ -> false
            )
          ||
            nd1old == nd1new && nd1old#data#is_named &&
            nd1new#data#eq nd2new#data && not (nd1new#data#eq nd2old#data) &&
            (try
              let pnd1new = nd1new#initial_parent in
              let pnd2new = nd2new#initial_parent in
              let pnd2old = nd2old#initial_parent in
              anc_each_other2 pnd2old pnd2new &&
              pnd1new#data#eq pnd2new#data && not (pnd1new#data#eq pnd2old#data)
            with _ -> false)
          ||
            nd2old == nd2new && nd2old#data#is_named &&
            nd2new#data#eq nd1new#data && not (nd2new#data#eq nd1old#data) &&
            (try
              let pnd2new = nd2new#initial_parent in
              let pnd1new = nd1new#initial_parent in
              let pnd1old = nd1old#initial_parent in
              anc_each_other1 pnd1old pnd1new &&
              pnd2new#data#eq pnd1new#data && not (pnd2new#data#eq pnd1old#data)
            with _ -> false)
          ||
            nd1old == nd1new && nd1old#data#is_named &&
            nd1old#data#eq nd2old#data && nd1old#data#eq nd2new#data &&
            (
             let _ = [%debug_log "@@@ %a--[%a,%a]" nups nd1old nups nd2old nups nd2new] in
             has_common_subtree nd1new nd2new && not (has_common_subtree nd1old nd2old)
           (*||
             has_reliable_rename nd1new nd2new && not (has_reliable_rename nd1old nd2old)*)
           (*||
             try
              let pnd1old = nd1old#initial_parent in
              let pnd2old = nd2old#initial_parent in
              let pnd1new = nd1new#initial_parent in
              let pnd2new = nd2new#initial_parent in
              pnd1new#data#is_statement &&
              pnd1new#data#eq pnd2new#data && not (pnd1old#data#eq pnd2old#data)
             with _ -> false*)
            )
          ||
            nd2old == nd2new && nd2old#data#is_named &&
            nd2old#data#eq nd1old#data && nd2old#data#eq nd1new#data &&
            (
             let _ = [%debug_log "@@@ [%a,%a]--%a" nups nd1old nups nd2old nups nd2new] in
             has_common_subtree nd1new nd2new && not (has_common_subtree nd1old nd2old)
           (*||
             has_reliable_rename nd1new nd2new && not (has_reliable_rename nd1old nd2old)*)
           (*||
             try
              let pnd1old = nd1old#initial_parent in
              let pnd2old = nd2old#initial_parent in
              let pnd1new = nd1new#initial_parent in
              let pnd2new = nd2new#initial_parent in
              pnd1new#data#is_statement &&
              pnd1new#data#eq pnd2new#data && not (pnd1old#data#eq pnd2old#data)
             with _ -> false*)
            )
        (*||
        (subtree_sim_new > subtree_sim_old && subtree_sim_ratio < subtree_similarity_ratio_cutoff)*)
          then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_new None None false;
              true, None, None
            in
            add_cache false b ncd ncsim
          end
          else if ancsim_new = 0.0 && ancsim_old > 0.5 then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_old None None false;
              false, None, None
            in
            add_cache false b ncd ncsim
          end
          else if ancsim_old = 0.0 && ancsim_new > 0.5 then begin
            [%debug_log "@"];
            let b, ncd, ncsim =
              action_new None None false;
              true, None, None
            in
            add_cache false b ncd ncsim
          end
          else begin
            [%debug_log "@"];

            let both_are_def_old = List.for_all is_def [nd1old; nd2old] in
            let both_are_def_new = List.for_all is_def [nd1new; nd2new] in
            let old_has_use_rename =
              self#has_use_rename nd1old nd2old(* || self#child_has_use_rename nd1old nd2old*)
            in
            let new_has_use_rename =
              self#has_use_rename nd1new nd2new(* || self#child_has_use_rename nd1new nd2new*)
            in
            [%debug_log "both_are_def_old=%B both_are_def_new=%B" both_are_def_old both_are_def_new];
            [%debug_log "old_has_use_rename=%B new_has_use_rename=%B"
              old_has_use_rename new_has_use_rename];

            let bn_mapped n1 n2 =
              [%debug_log "%s-%s" n1#data#to_string n2#data#to_string];
              let b =
                try
                  let bn1 = get_bn n1 in
                  let bn2 = get_bn n2 in
                  [%debug_log "bn: %s-%s" bn1#data#to_string bn2#data#to_string];
                  try
                    let bn1' = nmapping#find bn1 in
                    bn1' == bn2 ||
                    let _ = [%debug_log "-> %s" bn1'#data#to_string] in
                    bn1'#data#get_name = bn1#data#get_name &&
                    let bn2' = nmapping#inv_find bn2 in
                    [%debug_log "%s <-" bn2'#data#to_string];
                    bn2'#data#get_name = bn2#data#get_name
                  with
                    Not_found -> false
                with
                  _ -> raise Abort
              in
              [%debug_log "%B" b];
              b
            in
            if
              both_are_def_old && not both_are_def_new
            ||
              both_are_def_old && old_has_use_rename && not new_has_use_rename &&
              try not (bn_mapped nd1old nd2old && bn_mapped nd1new nd2new) with Abort -> false
            then begin
              let b, ncd, ncsim =
                action_old None None false;
                false, None, None
              in
              add_cache false b ncd ncsim
            end
            else if
              both_are_def_new && not both_are_def_old
            ||
              both_are_def_new && new_has_use_rename && not old_has_use_rename &&
              try not (bn_mapped nd1old nd2old && bn_mapped nd1new nd2new) with Abort -> false
            then begin
              let b, ncd, ncsim =
                action_new None None false;
                true, None, None
              in
              add_cache false b ncd ncsim
            end
            else

            let has_same_children nd1 nd2 =
              let cs1 = nd1#initial_children in
              let cs2 = nd2#initial_children in
              let len1 = Array.length cs1 in
              let len2 = Array.length cs2 in

              if len1 = len2 && len1 > 0 then
                try
                  let b = ref false in
                  Array.iteri
                    (fun i n1 ->
                      let n2 = cs2.(i) in
                      if n1#data#_label = n2#data#_label then
                        b := true;

                      if n1#data#_anonymized_label <> n2#data#_anonymized_label then
                        raise Found
                    ) cs1;
                  !b
                with
                  Found -> false
              else
                false
            in

            let _prefer_crossing_count () =
              force_prefer_crossing_count ||
              let size_cond =
                size_old > 2 && size_new > 2
              ||
                (all_single &&
                 nd1old#data#eq nd2old#data &&
                 nd2old#data#eq nd1new#data &&
                 nd1new#data#eq nd2new#data)
              in
              [%debug_log "size_cond: %B" size_cond];

              if size_cond then begin

                let anc_cond =
                  (ancsim_old >= ancestors_similarity_thresh &&
                   ancsim_new >= ancestors_similarity_thresh)
                ||
                  (
                   anc_sim_almost_same &&
                   (ancsim_old >= ancestors_similarity_thresh ||
                   ancsim_new >= ancestors_similarity_thresh)
                  )
                in
                [%debug_log "anc_cond: %B" anc_cond];

                if anc_cond then begin

                  let neighbour_cond =
                    let pairs_old = self#find_mapped_ancestor_pairs nmapping#find nd1old nd2old in
                    let pairs_new = self#find_mapped_ancestor_pairs nmapping#find nd1new nd2new in

                    begin %debug_block
                      let f =
                        Xlist.to_string
                          (fun (n1, n2) -> Printf.sprintf "%a-%a" nups n1 nups n2) ";"
                      in
                      [%debug_log "pairs_old: %s" (f pairs_old)];
                      [%debug_log "pairs_new: %s" (f pairs_new)]
                    end;

                    let rec get_uniq_pairs p =
                      match p with
                      | _, [] | [], _ -> p
                      | (a11, a12)::t1, (a21, a22)::t2 ->
                          if a11 == a21 && a12 == a22 then
                            get_uniq_pairs (t1, t2)
                          else
                            p
                    in
                    try
                      let uniq_pairs_old, uniq_pairs_new = get_uniq_pairs (pairs_old, pairs_new) in

                      begin %debug_block
                        let f =
                          Xlist.to_string
                            (fun (n1, n2) -> Printf.sprintf "%a-%a" nups n1 nups n2) ";"
                        in
                        [%debug_log "uniq_pairs_old: %s" (f uniq_pairs_old)];
                        [%debug_log "uniq_pairs_new: %s" (f uniq_pairs_new)]
                      end;

                      let get_n_mapped = function
                        | [] -> 0
                        | (pn1, pn2)::_ -> self#estimate_cost_of_move nmapping pn1 pn2
                      in
                      let n_mapped_old = get_n_mapped uniq_pairs_old in
                      let n_mapped_new = get_n_mapped uniq_pairs_new in

                      [%debug_log "n_mapped_old: %d n_mapped_new: %d" n_mapped_old n_mapped_new];

                      (*n_mapped_old > 0 && n_mapped_new > 0 &&*)

                      let get_sz = function
                        | [] -> 0
                        | (pn1, pn2)::_ ->
                            (tree1#fast_whole_initial_subtree_size pn1)
                              + (tree2#fast_whole_initial_subtree_size pn2)
                      in

                      let sz_old = get_sz uniq_pairs_old in
                      let sz_new = get_sz uniq_pairs_new in

                      [%debug_log "sz_old: %d sz_new: %d" sz_old sz_new];

                      (
                       nd1old#data#is_ntuple && nd2old#data#is_ntuple &&
                       nd1new#data#is_ntuple && nd2new#data#is_ntuple &&
                       match uniq_pairs_old, uniq_pairs_new with
                       | [], [(n1, n2)]
                       | [(n1, n2)], [] -> begin
                           let b =
                             (n_mapped_old > 0 || n_mapped_new > 0) &&
                             n1#data#is_boundary && n2#data#is_boundary &&
                             n1#data#is_named_orig && n2#data#is_named_orig &&
                             get_orig_name n1 = get_orig_name n2
                           in
                           [%debug_log "b=%B" b];
                           b
                       end
                       | _ -> false
                      ) ||

                      let denom = sz_old + sz_new in
                      let r =
                        if denom = 0 then
                          0.0
                        else
                          (float (2 * (abs (n_mapped_old - n_mapped_new)))) /. (float denom)
                      in
                      [%debug_log "difference: %f (thresh=%f)"
                        r options#mapped_neighbours_difference_threshold];

                      r < options#mapped_neighbours_difference_threshold

                    with
                      Not_found -> true
                  in
                  [%debug_log "neighbour_cond: %B" neighbour_cond];

                  if neighbour_cond then begin

                    let sim_cond =
                      (
                       subtree_sim_old >= subtree_similarity_thresh &&
                       subtree_sim_new >= subtree_similarity_thresh
                      ) ||
                      (has_same_children nd1old nd2old && has_same_children nd1new nd2new)
                    in
                    [%debug_log "sim_cond: %B" sim_cond];
                    (
                     sim_cond ||
                     (anc_cond && subtree_sim_ratio > subtree_similarity_ratio_thresh
(* subtree_sim_old <= subtree_similarity_cutoff && subtree_sim_new <= subtree_similarity_cutoff *))
                    ) &&
                    (
                     (ancsim_old < 1.0 && ancsim_new < 1.0) ||
                     (ancsim_old = 1.0 && ancsim_new = 1.0)
                    )
                  end
                  else
                    false
                end
                else
                  false
              end
              else
                false
            in (* _prefer_crossing_count *)

            let is_rename_pat n1 n2 =
              try
                n1#data#is_named && n2#data#is_named &&
                self#is_rename_pat (get_stripped_name n1, get_stripped_name n2)
              with _ -> false
            in

            let is_rename_pat_ n1 n2 =
              let b =
                is_rename_pat n1 n2 ||
                n1#data#is_named_orig && (n1#data#eq n2#data || stripped_orig_eq n1 n2) &&
                try
                  let pn1 = n1#initial_parent in
                  let pn2 = n2#initial_parent in
                  pn1#data#_anonymized_label = pn2#data#_anonymized_label && is_rename_pat pn1 pn2
                with _ -> false
              in
              [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
              b
            in

            let names_eq n1 n2 =
              let b =
                n1#data#is_named && (n1#data#eq n2#data) &&
                Array.exists (fun c -> c#data#is_order_insensitive) n1#initial_children &&
                Array.exists (fun c -> c#data#is_order_insensitive) n2#initial_children &&
                try
                  let pn1 = n1#initial_parent in
                  let pn2 = n2#initial_parent in
                  pn1#data#is_boundary && pn2#data#is_boundary &&
                  get_stripped_name n1 = get_stripped_name pn1 &&
                  get_stripped_name n2 = get_stripped_name pn2 &&
                  stripped_orig_eq pn1 pn2
                with _ -> false
              in
              [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
              b
            in

            let prefer_crossing_count () =
              let is_rename_pat_old = is_rename_pat_ nd1old nd2old in
              let is_rename_pat_new = is_rename_pat_ nd1new nd2new in
              [%debug_log "is_rename_pat_old=%B is_rename_pat_new=%B"
                is_rename_pat_old is_rename_pat_new];
              let b = is_rename_pat_old = is_rename_pat_new && _prefer_crossing_count() in
              [%debug_log "%B" b];
              b
            in

            (*let prefer_crossing_count =
              prefer_crossing_count ||
              is_cross_boundary nmapping nd1old nd2old || is_cross_boundary nmapping nd1new nd2new
            in!!!NG!!!*)

            let is_map = _is_map nmapping in

            let has_op_sibling pn n =
              Array.exists (fun c -> c != n && c#data#is_op) pn#initial_children
            in
            let parent_is_op n =
              try
                n#initial_parent#data#is_op
              with _ -> false
            in

            if
              subtree_sim_old = 1.0 && subtree_sim_new = 1.0 &&
              (nd1new#data#has_non_trivial_value || nd1new#data#is_named_orig) &&
              try
                let pnd1new = nd1new#initial_parent in
                let pnd2new = nd2new#initial_parent in
                [%debug_log "pnd1new: %a" nps pnd1new];
                [%debug_log "pnd2new: %a" nps pnd2new];
                (
                 (
                  pnd2new#data#is_op && not pnd1new#data#is_op &&
                  (has_op_sibling pnd2new nd2new || parent_is_op pnd2new) &&
                  let pnd1new' = nmapping#find pnd1new in
                  [%debug_log "pnd1new': %a" nps pnd1new'];
                  pnd1new#data#_anonymized_label = pnd1new'#data#_anonymized_label &&
                  tree2#is_initial_ancestor pnd1new' pnd2new
                 ) ||
                 (
                  pnd1new#data#is_op && not pnd2new#data#is_op &&
                  (has_op_sibling pnd1new nd2new || parent_is_op pnd1new) &&
                  let pnd2new' = nmapping#inv_find pnd2new in
                  [%debug_log "pnd2new': %a" nps pnd2new'];
                  pnd2new'#data#_anonymized_label = pnd2new#data#_anonymized_label &&
                  tree1#is_initial_ancestor pnd2new' pnd1new
                 )
                ) &&
                let stmt1 = get_stmt nd1new in
                let stmt2 = get_stmt nd2new in
                stmt1#data#eq stmt2#data && is_map stmt1 stmt2
              with
                _ -> false
            then begin
              [%debug_log "!!!!!!!!! selecting %a - %a" nps nd1new nps nd2new];
              (*nmapping#lock_mapping nd1new nd2new;*)
              action_new None None true
            end
            else if
              subtree_sim_old = 1.0 && subtree_sim_new = 1.0 &&
              (nd1old#data#has_non_trivial_value || nd1old#data#is_named_orig) &&
              try
                let pnd1old = nd1old#initial_parent in
                let pnd2old = nd2old#initial_parent in
                [%debug_log "pnd1old: %a" nps pnd1old];
                [%debug_log "pnd2old: %a" nps pnd2old];
                (
                 (
                  pnd2old#data#is_op && not pnd1old#data#is_op &&
                  (has_op_sibling pnd2old nd2old || parent_is_op pnd2old) &&
                  let pnd1old' = nmapping#find pnd1old in
                  [%debug_log "pnd1old': %a" nps pnd1old'];
                  pnd1old#data#_anonymized_label = pnd1old'#data#_anonymized_label &&
                  tree2#is_initial_ancestor pnd1old' pnd2old
                 ) ||
                 (
                  pnd1old#data#is_op && not pnd2old#data#is_op &&
                  (has_op_sibling pnd1old nd1old || parent_is_op pnd1old) &&
                  let pnd2old' = nmapping#inv_find pnd2old in
                  [%debug_log "pnd2old': %a" nps pnd2old'];
                  pnd2old'#data#_anonymized_label = pnd2old#data#_anonymized_label &&
                  tree1#is_initial_ancestor pnd2old' pnd1old
                 )
                ) &&
                let stmt1 = get_stmt nd1old in
                let stmt2 = get_stmt nd2old in
                stmt1#data#eq stmt2#data && is_map stmt1 stmt2
              with
                _ -> false
            then begin
              [%debug_log "!!!!!!!!! keeping %a - %a" nps nd1old nps nd2old];
              (*nmapping#lock_mapping nd1old nd2old;*)
              action_old None None true
            end
            else

            if
              (* (nd1old#data#eq nd2old#data || nd1new#data#eq nd2new#data) && *)
              prefer_crossing_count() ||
              ancsim_old = ancsim_new && size_old = 2 && size_new = 2 &&
              try
                is_rename_pat_ nd1old nd2old && is_rename_pat_ nd1new nd2new
              with _ -> false
            then begin (* crossing count preferred *)
              let ncross_old =
                if !ncrossing_old < 0 then
                  ncrossing_old := nmapping#count_crossing_or_incompatible_matches nd1old nd2old;
                !ncrossing_old
              in
              let ncross_new =
                if !ncrossing_new < 0 then
                  ncrossing_new := nmapping#count_crossing_or_incompatible_matches nd1new nd2new;
                !ncrossing_new
              in

              [%debug_log " num of incompatible or crossing matches: %d --> %d" ncross_old ncross_new];

(*
  let similar_ncross =
  let sim =
  ((float (min ncross_old ncross_new)) /. (float (max ncross_old ncross_new)))
  in
  [%debug_log "similarity of ncross: %f" sim];

  sim > ncross_sim_ratio_thresh
  in
 *)
              if ncross_old = ncross_new (* similar_ncross *) then begin

                (*let sibling_cond =
                  if nd2old == nd2new then
                    next_to_each_other nd1old nd1new
                  else if nd1old == nd2new then
                    next_to_each_other nd2old nd2new
                  else
                    false
                in
                [%debug_log "sibling_cond=%B" sibling_cond];
                if sibling_cond then
                  check_label_match ~ncross_used:true
                else!!!NG!!!*)
                  check_adjacency ~bonus_self:true ~ncross_used:true ()

              end
              else begin (* ncross_old <> ncross_new *)
                let ncross_sim =
                  ((float (min ncross_old ncross_new)) /. (float (max ncross_old ncross_new)))
                in
                [%debug_log "similarity of ncross: %f" ncross_sim];

                let b, ncd, ncsim =
                  if ncross_new < ncross_old then
                    let d = Some (ncross_old - ncross_new) in
                    let s = Some ncross_sim in
                    action_new d s false;
                    true, d, s
                  else
                    let d = Some (ncross_new - ncross_old) in
                    let s = Some ncross_sim in
                    action_old d s false;
                    false, d, s
                in
                add_cache true b ncd ncsim
              end
            end
            else if (* adjacency is useless for siblings *)
              nd1old#initial_parent == nd1new#initial_parent &&
              nd2old#initial_parent == nd2new#initial_parent &&
              abs (nd1old#initial_pos - nd1new#initial_pos) <= 1 &&
              abs (nd2old#initial_pos - nd2new#initial_pos) <= 1
            then
              check_label_match ~ncross_used:false

            else if
              try
                get_orig_name nd1old <> get_orig_name nd2old &&
                not (is_rename_pat_ nd1old nd2old) && is_rename_pat_ nd1new nd2new
              with _ -> false
            then begin
              [%debug_log "!!!!!!!! selecting %a - %a" nps nd1new nps nd2new];
              nmapping#lock_mapping nd1new nd2new;
              action_new None None true
            end
            else if
              try
                get_orig_name nd1new <> get_orig_name nd2new &&
                is_rename_pat_ nd1old nd2old && not (is_rename_pat_ nd1new nd2new)
              with _ -> false
            then begin
              [%debug_log "!!!!!!!! keeping %a - %a" nps nd1old nps nd2old];
              nmapping#lock_mapping nd1old nd2old;
              action_old None None true
            end

            else if
              try
                not (names_eq nd1old nd2old) && names_eq nd1new nd2new
              with _ -> false
            then begin
              [%debug_log "!!!!!!!! selecting %a - %a" nps nd1new nps nd2new];
              nmapping#lock_mapping nd1new nd2new;
              action_new None None true
            end
            else if
              try
                names_eq nd1old nd2old && not (names_eq nd1new nd2new)
              with _ -> false
            then begin
              [%debug_log "!!!!!!!! keeping %a - %a" nps nd1old nps nd2old];
              nmapping#lock_mapping nd1old nd2old;
              action_old None None true
            end

            else if
              ancsim_old = 1.0 && ancsim_new < 1.0 &&
              nd1old#data#is_op && nd2old#data#is_op && nd1new#data#is_op && nd2new#data#is_op &&
              subtree_sim_ratio < subtree_similarity_ratio_thresh &&
              self#check_op_mappings_m nmapping nd1old nd2old nd1new nd2new
            then begin
              [%debug_log "!!!!!!!! selecting %a - %a" nps nd1new nps nd2new];
              nmapping#lock_mapping nd1new nd2new;
              action_new None None true
            end
            else if
              ancsim_old < 1.0 && ancsim_new = 1.0 &&
              nd1old#data#is_op && nd2old#data#is_op && nd1new#data#is_op && nd2new#data#is_op &&
              subtree_sim_ratio < subtree_similarity_ratio_thresh &&
              self#check_op_mappings_m nmapping nd1new nd2new nd1old nd2old
            then begin
              [%debug_log "!!!!!!!! keeping %a - %a" nps nd1old nps nd2old];
              nmapping#lock_mapping nd1old nd2old;
              action_old None None true
            end
            else if
              ancsim_old = 1.0 && ancsim_new < 1.0 &&
              nd1old#data#is_op && nd2old#data#is_op && nd1new#data#is_op && nd2new#data#is_op &&
              subtree_sim_ratio > subtree_similarity_ratio_thresh &&
              self#check_op_mappings nmapping size_new1 size_new2 nd1old nd2old nd1new nd2new
            then begin
              [%debug_log "!!!!!!!! selecting %a - %a" nps nd1new nps nd2new];
              nmapping#lock_mapping nd1new nd2new;
              action_new None None true
            end
            else if
              ancsim_old < 1.0 && ancsim_new = 1.0 &&
              nd1old#data#is_op && nd2old#data#is_op && nd1new#data#is_op && nd2new#data#is_op &&
              subtree_sim_ratio > subtree_similarity_ratio_thresh &&
              self#check_op_mappings nmapping size_old1 size_old2 nd1new nd2new nd1old nd2old
            then begin
              [%debug_log "!!!!!!!! keeping %a - %a" nps nd1old nps nd2old];
              nmapping#lock_mapping nd1old nd2old;
              action_old None None true
            end

            else begin (* adjacency is used *)

              check_adjacency ~bonus_self ~bonus_parent ~ncross_used:false ()

            end

          end

    end (* of method compare_mappings *)


  method elaborate_nmapping
      ?(multi=false)
      ?(multi_node=false)
      (nmapping : 'node_t Node_mapping.c)
      =
    begin %debug_block
      [%debug_log "nmapping:\n%s\n" nmapping#to_string];
      (*[%debug_log "nmapping (gindex):\n%s\n" nmapping#to_string_gid];*)
      [%debug_log "multi=%B multi_node=%B" multi multi_node]
    end;

    let multiple_subtree_matches =
      try
        self#multiple_subtree_matches
      with
        Not_found -> raise Elaboration_impossible
    in
    let multiple_node_matches =
      try
        self#multiple_node_matches
      with
        Not_found -> raise Elaboration_impossible
    in

    Xprint.verbose options#verbose_flag
      "    elaborating nmapping (multi:%B,multi_node:%B)..." multi multi_node;

    if multi_node then
      nmapping#setup_partitions;

    let added_pairs =
      if multi then
        ref (multiple_subtree_matches#align nmapping)
      else
        ref []
    in
    let removed_pairs = ref [] in

    let check n1 n2 =
      begin
        try
          let n1' = nmapping#find n1 in
          if n1' != n2 then begin
            if nmapping#remove n1 n1' then
              removed_pairs := (n1, n1') :: !removed_pairs
          end
        with
          Not_found -> ()
      end;
      begin
        try
          let n2' = nmapping#inv_find n2 in
          if n2' != n1 then begin
            if nmapping#remove n2' n2 then
              removed_pairs := (n2', n2) :: !removed_pairs
          end
        with
          Not_found -> ()
      end
    in

    let count = ref 0 in

    multiple_subtree_matches#iter
      (fun (d, ndmems1, ndmems2, sz) ->
        let _ = d in
        [%debug_log "checking subtrees of digest %s" (try Digest.to_hex d with _ -> d)];

        let unmapped1, mapped1 =
          List.partition
            (fun (_, nds) ->
              List.for_all (fun n -> not (nmapping#mem_dom n)) nds
            ) ndmems1
        in
        let unmapped2, mapped2 =
          List.partition
            (fun (_, nds) ->
              List.for_all (fun n -> not (nmapping#mem_cod n)) nds
            ) ndmems2
        in

        let getroots ndmems = List.map (fun (n, _) -> n) ndmems in

        let nmapped1 = List.length mapped1 in
        let nmapped2 = List.length mapped2 in
        (*let nunmapped1 = List.length unmapped1 in
        let nunmapped2 = List.length unmapped2 in*)

        begin %debug_block
          let ndmem_to_str (n, _) =
            Printf.sprintf "%a" nups n
            (*Printf.sprintf "%a[%a]" nups n nsps ns *)
          in
          let ndmems_to_str ndmems =
            Xlist.to_string ndmem_to_str "; " ndmems
          in
          [%debug_log "mapped1(%d): %s" nmapped1 (ndmems_to_str mapped1)];
          [%debug_log "mapped2(%d): %s" nmapped2 (ndmems_to_str mapped2)];
          [%debug_log "unmapped1: %s" (ndmems_to_str unmapped1)];
          [%debug_log "unmapped2: %s" (ndmems_to_str unmapped2)];
        end;

        if
          nmapped1 > options#prematch_subtree_cands_threshold &&
          nmapped2 > options#prematch_subtree_cands_threshold
        then begin
          [%debug_log "too many subtrees: %d:%d" nmapped1 nmapped2];
        end
        else

        let add_map n1 n2 =
          [%debug_log "%a-%a" nups n1 nups n2];
          begin
            try
              let n1' = nmapping#find n1 in
              if n1' != n2 then begin
                if nmapping#remove n1 n1' then
                  removed_pairs := (n1, n1') :: !removed_pairs
              end
            with
              Not_found -> ()
          end;
          begin
            try
              let n2' = nmapping#inv_find n2 in
              if n2' != n1 then begin
                if nmapping#remove n2' n2 then
                  removed_pairs := (n2', n2) :: !removed_pairs
              end
            with
              Not_found -> ()
          end;
          let _ = nmapping#add_settled ~stable:false (* EXPERIMENTAL *) n1 n2 in
          if not (List.mem (n1, n2) !added_pairs) then
            added_pairs := (n1, n2) :: !added_pairs
        in

        let overwrite rt1 rt2 mem_pairs =
          [%debug_log "%a-%a: %d mem pairs" nups rt1 nups rt2 (List.length mem_pairs)];
          incr count;
          List.iter
            (fun (n1, n2) ->
              add_map n1 n2
            ) mem_pairs;

          nmapping#add_settled_roots rt1 rt2
        in

        let combi ns1 ns2 =
          List.fold_left (fun l n1 -> l @ (List.map (fun n -> (n1, n)) ns2)) [] ns1
        in

        let unmapped_extra1 = ref [] in
        let unmapped_extra2 = ref [] in

        let mapped_nds1 = List.map (fun (n, _) -> n) mapped1 in
        let mapped_nds2 = List.map (fun (n, _) -> n) mapped2 in

        let all_mapped_nds1 =
          List.fold_left (fun l (_, ns) -> l @ ns) [] mapped1
        in
        let all_mapped_nds2 =
          List.fold_left (fun l (_, ns) -> l @ ns) [] mapped2
        in

        let conflicting_pairs_tbl = Hashtbl.create 0 in
        let add_conflicting_pair (n1, n2, ns1, ns2, mps, f) =
          Hashtbl.replace conflicting_pairs_tbl (n1, n2) (ns1, ns2, mps, f)
        in

        let atbl1 = Nodetbl.create 0 in
        let atbl2 = Nodetbl.create 0 in
        let mtbl = Nodetbl.create 0 in
        let atbl_add atbl is_mapped n nl =
          try
            let an = Sourcecode.find_nearest_mapped_ancestor_node is_mapped n in
            Nodetbl.add mtbl n nl;
            try
              let nl = Nodetbl.find atbl an in
              Nodetbl.replace atbl an (n::nl)
            with
              Not_found -> Nodetbl.add atbl an [n]
          with
            _ -> ()
        in
        List.iter (fun (n1, nl1) ->  atbl_add atbl1 nmapping#mem_dom n1 nl1) mapped1;
        List.iter (fun (n2, nl2) ->  atbl_add atbl2 nmapping#mem_cod n2 nl2) mapped2;

        List.iter
          (fun (nd1, nds1) ->

            List.iter
              (fun (nd2, nds2) ->

                let is_settled =
                  nmapping#is_settled_root_pair nd1 nd2 ||
                  nmapping#has_settled_mapping nd1 nd2 (* nmapping#mem_settled nd1 *)
                in

                [%debug_log " %a-%a --> settled:%B" nups nd1 nups nd2 is_settled];


                if is_settled then
                  () (* overwrite uid1 uid2 (List.combine nds1 nds2) *)

                else begin
                  let c = ref 0 in
                  let cands = ref [] in

                  List.iter2
                    (fun n1 n2 ->
                      (*[%debug_log " checking %a-%a" ups u1 ups u2];*)
                      try
                        let n1' = nmapping#find n1 in
                        (*[%debug_log " found: %a -> %a" ups u1 ups u1'];*)
                        if n1' == n2 then
                          incr c
                        else
                          cands := (n1, n2) :: !cands
                      with
                        Not_found -> cands := (n1, n2) :: !cands
                    ) nds1 nds2;

                  match !cands with
                  | [] -> ()
                  | _ -> begin
                      let match_ratio = (float !c) /. (float sz) in

                      [%debug_log "subtree pair %a-%a: %d nodes mapped (ratio=%f)"
                        nups nd1 nups nd2 !c match_ratio];

                      if match_ratio > options#subtree_match_ratio_threshold then begin
                        overwrite nd1 nd2 !cands
                      end
                      else begin
                        begin
                          try
                            let nd1' = nmapping#find nd1 in
                            if not (List.memq nd1' mapped_nds2) && nd1' != nd2 then begin
                              let mem_pairs =
                                List.fold_left
                                  (fun l n1 ->
                                    if n1 != nd1 then
                                      try
                                        let n1' = nmapping#find n1 in
                                        if not (List.memq n1' all_mapped_nds2) then
                                          (n1, n1')::l
                                        else
                                          l
                                      with
                                        Not_found -> l
                                    else
                                      l
                                  ) [] nds1
                              in
                              add_conflicting_pair
                                (nd1, nd1', [nd1], getroots unmapped2, mem_pairs,
                                 (fun () ->
                                   unmapped_extra1 := (nd1, nds1) :: !unmapped_extra1;
                                   raise Exit)
                                )
                            end
                          with
                            Not_found -> ()
                        end;

                        begin
                          try
                            let nd2' = nmapping#inv_find nd2 in
                            if not (List.memq nd2' mapped_nds1) && nd2' != nd1 then begin
                              let mem_pairs =
                                List.fold_left
                                  (fun l n2 ->
                                    if n2 != nd2 then
                                      try
                                        let n2' = nmapping#inv_find n2 in
                                        if not (List.memq n2' all_mapped_nds1) then
                                          (n2', n2)::l
                                        else
                                          l
                                      with
                                        Not_found -> l
                                    else
                                      l
                                  ) [] nds2
                              in
                              add_conflicting_pair
                                (nd2', nd2, getroots unmapped1, [nd2], mem_pairs,
                                 (fun () ->
                                   unmapped_extra2 := (nd2, nds2) :: !unmapped_extra2;
                                   raise Exit)
                                )
                            end
                          with
                            Not_found -> ()
                        end

                      end
                  end
                end
              ) mapped2

          ) mapped1;

        Nodetbl.iter
          (fun an1 nl1 ->
            [%debug_log "%a -> [%a]" nups an1 nsps nl1];
            match nl1 with
            | [n1] -> begin
                try
                  let an1' = nmapping#find an1 in
                  let nl2 = Nodetbl.find atbl2 an1' in
                  [%debug_log "%a -> %a -> [%a]" nups an1 nups an1' nsps nl2];
                  match nl2 with
                  | [n2] -> begin
                      add_map n1 n2;
                      try
                        let mnl1 = Nodetbl.find mtbl n1 in
                        let mnl2 = Nodetbl.find mtbl n2 in
                        if List.length mnl1 = List.length mnl2 then
                          List.iter2 (fun mn1 mn2 -> add_map mn1 mn2) mnl1 mnl2
                      with
                        _ -> ()
                  end
                  | _ -> ()
                with
                  _ -> ()
            end
            | _ -> ()
          ) atbl1;

        let to_be_removed = Xset.create 0 in

        Hashtbl.iter
          (fun (cn1, cn2) (ns1, ns2, mem_pairs, act) ->

            [%debug_log "conflicting pair: %a-%a [%a]-[%a] %a" nups cn1 nups cn2 locps cn1 locps cn2 labps cn1];
            [%debug_log "mem_pairs: [%s]"
              (Xlist.to_string (fun (n1, n2) -> Printf.sprintf "%a-%a" nups n1 nups n2) ";" mem_pairs)];

            let pairs = combi ns1 ns2 in

            if List.length pairs < options#conflicting_pairs_threshold then begin

              begin %debug_block
                List.iter
                  (fun (n1, n2) ->
                    [%debug_log "  vs %a-%a" nups n1 nups n2]
                  ) pairs
              end;

              let ncross = ref (-1) in
              let adj = ref (-1.0) in
              try
                List.iter
                  (fun (n1, n2) ->
                    self#compare_mappings nmapping
                      ?override:None ?bonus_self:None
                      n1 n2 ?ncrossing_old:None ?adjacency_old:None
                      (fun _ _ _ ->
                        Xset.add to_be_removed (cn1, cn2);
                        List.iter (Xset.add to_be_removed) mem_pairs;
                        act()
                      )
                      cn1 cn2 ?ncrossing_new:(Some ncross) ?adjacency_new:(Some adj)
                      (fun _ _ _ -> ())
                  ) pairs
              with
                Exit -> ()

            end

          ) conflicting_pairs_tbl;


        begin %debug_block
          Xset.iter
          (fun (n1, n2) ->
            [%debug_log " to_be_removed: %a-%a" nups n1 nups n2];
          ) to_be_removed;
          let pr i ume =
            if ume <> [] then
              [%debug_log " unmapped_extra%d: [%s]" i
                (Xlist.to_string (fun (n, _) -> UID.to_string n#uid) ";" ume)]
          in
          pr 1 !unmapped_extra1;
          pr 2 !unmapped_extra2
        end;


        Xset.iter
          (fun (u1, u2) ->
            if nmapping#remove u1 u2 then
              removed_pairs := (u1, u2) :: !removed_pairs
          ) to_be_removed;

        begin %debug_block
          List.iter
            (fun (n1, ns1) ->
              if List.for_all (fun n -> not (nmapping#mem_dom n)) ns1 then
                [%debug_log "unmapped_extra1: %a -> OK" nups n1]
              else
                [%debug_log "unmapped_extra1: %a -> NG!" nups n1]
            ) !unmapped_extra1;

          List.iter
            (fun (n2, ns2) ->
              if List.for_all (fun n -> not (nmapping#mem_cod n)) ns2 then
                [%debug_log "unmapped_extra2: %a -> OK" nups n2]
              else
                [%debug_log "unmapped_extra2: %a -> NG!" nups n2]
            ) !unmapped_extra2
        end;

        let unmapped1 = unmapped1 @ !unmapped_extra1 in
        let unmapped2 = unmapped2 @ !unmapped_extra2 in

        match unmapped1, unmapped2 with
        | [(n1, ns1)], [(n2, ns2)] ->

            [%debug_log "adding: %a-%a (size=%d) (digest=%s) (%a-%a)"
              nups n1 nups n2 sz (try Digest.to_hex d with _ -> d) GI.ps n1#gindex GI.ps n2#gindex];

            incr count;
            List.iter2
              (fun n1 n2 ->
                check n1 n2;
                ignore (nmapping#add_settled ~stable:false (* EXPERIMENTAL *) n1 n2);
                added_pairs := (n1, n2) :: !added_pairs
              ) ns1 ns2;
            nmapping#add_settled_roots n1 n2;
(*        multiple_subtree_matches#remove d *)

        | [], ndmems | ndmems, [] ->
            if options#lock_matches_flag then begin (* lock residuals *)
              List.iter
                (fun (n, ns) ->
                  let _ = n in
                  [%debug_log "align: locking %a" nups n];

                  List.iter (fun n -> nmapping#lock_node n) ns
                ) ndmems
            end;

(*        multiple_subtree_matches#remove d *)

        | _ ->
            if multi then begin (* we are somewhat gambling if multi=true! *)

              let adj_score (n1, _) (n2, _) =
                let s = self#get_adjacency_score n1 n2 in

                [%debug_log "adj_score: %a-%a --> %f" nups n1 nups n2 s];

                s
              in

              let crossing_score (n1, _) (n2, _) =
                let s = -(nmapping#count_crossing_or_incompatible_matches n1 n2) in

                [%debug_log "crossing_score: %a-%a --> %d" nups n1 nups n2 s];

                s
              in

              let prox_score (n1, _) (n2, _) =
                let nprox = nmapping#get_proximity n1 n2 in
                let s = nprox#primary_prox in

                [%debug_log "prox_score: %a-%a --> %d" nups n1 nups n2 s];

                s
              in

              let a1 = Array.of_list unmapped1 in
              let a2 = Array.of_list unmapped2 in

              let selected =
                let score_f x y = (adj_score x y, crossing_score x y, prox_score x y) in
                let cmpr = new SMP.ComparatorFloatIntInt.c score_f a1 a2 in
                SMP.get_stable_matches cmpr a1 a2
              in

              begin %debug_block
                let ltos l =
                  String.concat ";" (List.map (fun (n, _) -> UID.to_string n#uid) l)
                in
                [%debug_log "  unmapped1=[%s]" (ltos unmapped1)];
                [%debug_log "  unmapped2=[%s]" (ltos unmapped2)];

                if selected <> [] then begin
                  [%debug_log "selected pairs:"];
                  List.iter
                    (fun ((n1, _), (n2, _)) ->
                      [%debug_log "%a-%a" nups n1 nups n2]
                    ) selected
                end
              end;

              List.iter
                (fun ((n1, ns1), (n2, ns2)) ->
                  let _ = n1 in
                  let _ = n2 in
                  [%debug_log "[MULTI] adding: %a-%a (size=%d) (digest=%s) (%a-%a)"
                    nups n1 nups n2 sz (try Digest.to_hex d with _ -> d)
                    GI.ps n1#gindex GI.ps n2#gindex];

                  List.iter2
                    (fun n1 n2 ->
                      incr count;

                      [%debug_log "adding: %a-%a (%a-%a)"
                        nups n1 nups n2 GI.ps n1#gindex GI.ps n2#gindex];

                      check n1 n2;
                      ignore (nmapping#add_unsettled n1 n2);
                      added_pairs := (n1, n2) :: !added_pairs

                    ) ns1 ns2;


                  (* lock residuals *)
                  if options#lock_matches_flag then begin
                    let _selected1, _selected2 = List.split selected in
                    let selected1 = List.map (fun (n, _) -> n) _selected1 in
                    let selected2 = List.map (fun (n, _) -> n) _selected2 in
                    List.iter
                      (fun (n, ns) ->
                        if not (List.memq n selected1) then begin

                          [%debug_log "align: locking %a" nups n];

                          List.iter (fun n -> nmapping#lock_node n) ns
                        end
                      ) unmapped1;
                    List.iter
                      (fun (n, ns) ->
                        if not (List.memq n selected2) then begin

                          [%debug_log "align: locking %a" nups n];

                          List.iter (fun n -> nmapping#lock_node n) ns
                        end
                      ) unmapped2
                  end;

(*              multiple_subtree_matches#remove d *)

                ) selected

            end
      );

    multiple_subtree_matches#iter
      (fun (d, ndmems1, ndmems2, _) ->
        let cnt =
          List.fold_left
            (fun c (nd1, _) ->
              if nmapping#mem_settled nd1 then
                c + 1
              else
                c
            ) 0 ndmems1
        in
        if cnt = min (List.length ndmems1) (List.length ndmems2) then
          multiple_subtree_matches#remove d
      );

    [%debug_log "%d pairs added by multiple subtree matches." !count];

    if options#multi_node_match_flag then begin

      count := 0;

      multiple_node_matches#iter
        (fun (_lab, nds1, nds2) ->
          let l1 =
            List.filter
              (fun nd ->
                (*not nd#data#is_common &&*)
                not (nmapping#mem_dom nd)
              ) nds1
          in
          let l2 =
            List.filter
              (fun nd ->
                (*not nd#data#is_common &&*)
                not (nmapping#mem_cod nd)
              ) nds2
          in
          match l1, l2 with
          | [], _ | _, [] -> ()
                (* multiple_node_matches#remove _lab *)

          | [nd1], [nd2] -> begin
              [%debug_log "node match (%s): |nds1|=1 |nds2|=1"
                (multiple_node_matches#label_to_string _lab)];

              (*if
                (try not (nmapping#mem_dom (get_bn nd1)) with _ -> false) ||
                (try not (nmapping#mem_cod (get_bn nd2)) with _ -> false)
              then
                [%debug_log "canceled"]
              else *)begin
                [%debug_log "adding: %a-%a (%a-%a)"
                  nups nd1 nups nd2 GI.ps nd1#gindex GI.ps nd2#gindex];

                incr count;
                check nd1 nd2;
                ignore (nmapping#add_unsettled nd1 nd2);
                added_pairs := (nd1, nd2) :: !added_pairs;
                multiple_node_matches#add_uniq_match nd1 nd2
                (* multiple_node_matches#remove _lab *)
              end
          end
          | nd1::_, _::_ -> begin
              let len1 = List.length l1 in
              let len2 = List.length l2 in

              [%debug_log "node match (%s): |nds1|=%d |nds2|=%d"
                (multiple_node_matches#label_to_string (Obj.obj _lab)) len1 len2];

              (*if nd1#data#is_op then begin
                if multi_node then begin
                  List.iter
                    (fun (nl1, nl2) ->
                      match nl1, nl2 with
                      | [nd1], [nd2] -> begin
                          [%debug_log "node match (%s): |nds1|=1 |nds2|=1"
                            (multiple_node_matches#label_to_string _lab)];
                          [%debug_log "adding: %a-%a (%a-%a)"
                            nups n1 nups n2 GI.ps nd1#gindex GI.ps nd2#gindex];

                          incr count;
                          check n1 n2;
                          ignore (nmapping#add_unsettled n1 n2);
                          added_pairs := (n1, n2) :: !added_pairs;

                      end
                      | _ -> ()
                    ) (group_node_matches l1 l2)
                end
              end
              else *)if nd1#data#is_named then begin

                if multi_node then begin

                  let thresh = options#prematch_cands_threshold in

                  if len1 <= thresh && len2 <= thresh then begin

                    [%debug_log "nds1=[%s] nds2=[%s]"
                      (Xlist.to_string (fun n -> UID.to_string n#uid) ";" l1)
                      (Xlist.to_string (fun n -> UID.to_string n#uid) ";" l2)];

                    let a1 = Array.of_list l1 in
                    let a2 = Array.of_list l2 in

                    let under_permutation_hub =
                      Array.for_all self#under_permutation_hub1 a1 &&
                      Array.for_all self#under_permutation_hub2 a2
                    in
                    [%debug_log "under_permutation_hub=%B" under_permutation_hub];

                    let crossing_score n1 n2 =
                      let s = -(nmapping#count_crossing_or_incompatible_matches n1 n2) in
                      [%debug_log "crossing_score: %a-%a --> %d" nups n1 nups n2 s];
                      s
                    in

                    let selected =
                      if under_permutation_hub then
                        let score_f x y = (self#get_adjacency_score x y, crossing_score x y) in
                        let cmpr = new SMP.ComparatorFloatInt.c score_f a1 a2 in
                        SMP.get_stable_matches cmpr a1 a2
                      else
                        let score_f x y = (crossing_score x y, self#get_adjacency_score x y) in
                        let cmpr = new SMP.ComparatorIntFloat.c score_f a1 a2 in
                        SMP.get_stable_matches cmpr a1 a2
                    in
                    List.iter
                      (fun (n1, n2) ->
                        [%debug_log "adding: %a-%a (%a-%a)"
                          nups n1 nups n2 GI.ps n1#gindex GI.ps n2#gindex];
                        incr count;
                        check n1 n2;
                        ignore (nmapping#add_unsettled n1 n2);
                        added_pairs := (n1, n2) :: !added_pairs
                      ) selected
                  end
                  else begin
                    try
                      let pa1 = nmapping#partition_nodes1 l1 in
                      [%debug_log "---"];
                      let pa2 = nmapping#partition_nodes2 l2 in

                      Array.iteri
                        (fun i ns1 ->
                          match ns1, pa2.(i) with
                          | [n1], [n2] ->
                              [%debug_log "adding: %a-%a (%a-%a)"
                                nups n1 nups n2 GI.ps n1#gindex GI.ps n2#gindex];

                              incr count;
                              check n1 n2;
                              ignore (nmapping#add_unsettled n1 n2);
                              nmapping#add_stable_pair n1 n2;
                              added_pairs := (n1, n2) :: !added_pairs

                          | _ -> ()
                        ) pa1
                    with
                      Invalid_argument _ -> ()

                  end

                end (* of if multi_node *)
              end (* of nd1#data#is_named *)
          end
        );

      [%debug_log "%d pairs added by multiple node matches." !count]

    end; (* if options#multi_node_match_flag *)

    let added_then_removed_pairs = Xlist.intersection !removed_pairs !added_pairs in
    begin %debug_block
      List.iter
      (fun (n1, n2) ->
        [%debug_log "added then removed pair: %a-%a" nups n1 nups n2]
      ) added_then_removed_pairs
    end;
    if added_then_removed_pairs <> [] then begin
      (*removed_pairs := Xlist.subtract !removed_pairs added_then_removed_pairs;*)
      added_pairs := Xlist.subtract !added_pairs added_then_removed_pairs
    end;

    begin %debug_block
      List.iter
        (fun (n1, n2) ->
          [%debug_log "removed_pair: %a-%a (%a-%a)" nups n1 nups n2 GI.ps n1#gindex GI.ps n2#gindex];
        ) !removed_pairs;
      List.iter
        (fun (n1, n2) ->
          [%debug_log "added_pair: %a-%a (%a-%a)" nups n1 nups n2 GI.ps n1#gindex GI.ps n2#gindex];
        ) !added_pairs
    end;

    Xprint.verbose options#verbose_flag "    elaborating completed.";

    !removed_pairs, !added_pairs

    (* end of method elaborate_nmapping *)

end (* of class Comparison.c *)
]
