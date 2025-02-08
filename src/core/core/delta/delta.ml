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
(* delta.ml *)

[%%prepare_logger]

module Xarray = Diffast_misc.Xarray
module Compression = Diffast_misc.Compression
module Binding = Diffast_misc.Binding
module Loc = Diffast_misc.Loc

module UID = Diffast_misc.UID
module MID = Moveid
module CB = Change_base

open Delta_base
open Delta_common

let node_opt_to_string = function
  | Some nd -> UID.to_string nd#uid
  | None -> ""

[%%capture_path
let get_p_siblings pred' x' =
  let l_opt = ref None in
  let r_opt = ref None in
  let px' = x'#initial_parent in
  let ca' = px'#initial_children in
  begin
    try
      for i = x'#initial_pos + 1 to px'#initial_nchildren - 1 do
        let c' = ca'.(i) in
        [%debug_log "i=%d c'=%a" i nps c'];
        if pred' c' then begin
          r_opt := Some c';
          raise Exit
        end
      done
    with
      Exit -> ()
  end;
  begin
    try
      for i = x'#initial_pos - 1 downto 0 do
        let c' = ca'.(i) in
        [%debug_log "i=%d c'=%a" i nps c'];
        if pred' c' then begin
          l_opt := Some c';
          raise Exit
        end
      done
    with
      Exit -> ()
  end;
  [%debug_log "%a -> %s, %s" nps x' (node_opt_to_string !l_opt) (node_opt_to_string !r_opt)];
  !l_opt, !r_opt
]

let overlaps a b x y = (* assumes a <= b && x <= y *)
  y >= a && b >= x

let rev_array_exists f a =
  try
    for i = (Array.length a) - 1 downto 0 do
      if f a.(i) then
        raise Exit
    done;
    false
  with
    Exit -> true

exception Defer
exception Abort


[%%capture_path
module Edit = struct

  type move_id = Editop.move_id
  type move_kind = Editop.move_kind

  type 'data t =
    | Delete  of 'data node_t * 'data node_t list
    | Insert  of 'data node_t * 'data node_t list
    | Relabel of 'data node_t * 'data node_t list * 'data node_t * 'data node_t list

    | Move of move_id * move_kind *
          'data node_t * 'data node_t list * 'data node_t * 'data node_t list

    | MoveInsert of move_id * move_kind * 'data node_t * 'data node_t list

  let nodes_to_paths path nds =
    List.map
      (fun (nd : 'data node_t) ->
        new boundary_path (get_rel_path path#path nd#apath)
      ) nds

  let move_id_to_string = Editop.move_id_to_string

  let move_kind_to_string = Editop.move_kind_to_string

  let to_string = function
    | Delete(nd, excluded) ->
        sprintf "DELETE(\n%s,[\n%s\n])"
          nd#initial_to_string (nodes_to_string excluded)

    | Insert(nd, excluded) ->
        sprintf "INSERT(\n%s,[\n%s\n])"
          nd#initial_to_string (nodes_to_string excluded)

    | Relabel(nd1, excluded1, nd2, excluded2) ->
        sprintf "RELABEL(\n%s,[\n%s\n] -> %s,[\n%s\n])"
          nd1#initial_to_string (nodes_to_string excluded1)
          nd2#initial_to_string (nodes_to_string excluded2)

    | Move(mid, k, nd1, excluded1, nd2, excluded2) ->
        sprintf "MOVE[%a][%s](\n%s,[\n%s\n] -> %s,[\n%s\n])"
          MID.ps mid (move_kind_to_string k)
          nd1#initial_to_string (nodes_to_string excluded1)
          nd2#initial_to_string (nodes_to_string excluded2)

    | MoveInsert(mid, k, nd2, excluded2) ->
        sprintf "MOVE_INSERT[%a][%s](\n%s,[\n%s\n])"
          MID.ps mid (move_kind_to_string k)
          nd2#initial_to_string (nodes_to_string excluded2)

  let is_permutation = function
    | Move(_, k, _, _, _, _) ->
        k = Editop.Mpermutation

    | _ -> false


  exception Parent_not_stable

  let flatten_remote_stable_tbl tbl =
    List.concat_map (fun (_, ns) -> ns) tbl

  let rec _get_anc_in mem n =
    if mem n then
      n
    else
      try
        _get_anc_in mem n#initial_parent
      with
        _ -> raise Not_found

  let get_anc_in xs = _get_anc_in (fun x -> List.memq x xs)


  type 'data eop_t = (#SB.node_data_t_shared as 'data) node_t Editop.t


  let opl_of_editop (eop : 'data eop_t) =
    let opl =
      match eop with
      | Editop.Delete(_, info, excluded) ->
          [Delete(Info.get_node info, Info.excluded_to_nodes !excluded)]

      | Editop.Insert(_, info, excluded) ->
          [Insert(Info.get_node info, Info.excluded_to_nodes !excluded)]

      | Editop.Relabel(_, (info1, excluded1), (info2, excluded2)) ->
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          let exc1 = Info.excluded_to_nodes !excluded1 in
          let exc2 = Info.excluded_to_nodes !excluded2 in
          [Relabel(nd1, exc1, nd2, exc2)]

      | Editop.Move(mid, k, (info1, excluded1), (info2, excluded2)) ->
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          let exc1 = Info.excluded_to_nodes !excluded1 in
          let exc2 = Info.excluded_to_nodes !excluded2 in
          [ Move(!mid, !k, nd1, exc1, nd2, exc2);
            MoveInsert(!mid, !k, nd2, exc2);
          ]
    in
    opl
(*
  let op_of_editop_filt ?(more=false) uidmapping edit_seq tree (eop : 'data eop_t) =
    let op =
      match eop with
      | Editop.Delete(_, _, info, excluded) ->
          Some (Delete(Info.get_node info, Info.excluded_to_nodes !excluded))

      | Editop.Insert(_, _, info, excluded) ->
          Some (Insert(Info.get_node info, Info.excluded_to_nodes !excluded))

      | Editop.Relabel(_, (_, info1, excluded1), (_, info2, excluded2)) ->
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          let exc1 = Info.excluded_to_nodes !excluded1 in
          let exc2 = Info.excluded_to_nodes !excluded2 in
          if
            (not nd1#data#is_named_orig) && (not nd1#data#has_value) &&
            (not nd2#data#is_named_orig) && (not nd2#data#has_value) &&
            nd1#data#elem_name_for_delta = nd2#data#elem_name_for_delta
          then begin
            [%debug_log "filtered: %s" (Editop.to_string eop)];
            None
          end
          else if begin
            match nd1#data#orig_lab_opt, nd2#data#orig_lab_opt with
            | Some o1, Some o2 -> o1 = o2
            | _ -> false
          end then begin
            [%debug_log "filtered: %s" (Editop.to_string eop)];
            None
          end
          else if more && nd1#data#is_compatible_with nd2#data then begin
            [%debug_log "filtered: %s" (Editop.to_string eop)];
            None
          end
          else
            Some (Relabel(nd1, exc1, nd2, exc2))

      | Editop.Move(mid, k, (_, info1, excluded1), (_, info2, excluded2)) ->
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          let exc1 = Info.excluded_to_nodes !excluded1 in
          let exc2 = Info.excluded_to_nodes !excluded2 in
          if
            more &&
            nd1#data#is_order_insensitive && nd2#data#is_order_insensitive &&
            !excluded1 = [] && !excluded2 = [] &&
            let pnd1 = nd1#initial_parent in
            let pnd2 = nd2#initial_parent in
            (try (uidmapping#find pnd1#uid) = pnd2#uid with _ -> false) &&
            (try
              edit_seq#iter_moves
                (function
                  | Editop.Move(_, _, (_, _, e1), (_, _, _)) -> begin
                      List.iter
                        (fun inf ->
                          if Info.get_node inf == nd1 then
                            raise Exit
                        ) !e1
                  end
                  | _ -> assert false
                );
              true
            with
              Exit -> false) &&
            match edit_seq#find12 pnd1#uid pnd2#uid with
            | [] -> true
            | [Editop.Relabel _] -> pnd1#data#elem_name_for_delta = pnd2#data#elem_name_for_delta
            | _ -> false
          then begin
            [%debug_log "filtered: %s" (Editop.to_string eop)];
            None
          end
          else
            Some (Move(!mid, !k, nd1, exc1, nd2, exc2))
    in
    op
*)
  let align_maps pmap fmap =
    let ith map i = if i < 0 then -1 else map.(i) in
    let pi = ith pmap in
    let fi = ith fmap in
    let overlap (a0, b0) (a1, b1) =
      [%debug_log "%d-%d vs %d-%d" a0 b0 a1 b1];
      let a = max a0 a1 in
      let b = min b0 b1 in
      let n = b - a + 1 in
      if n <= 0 then begin
        [%debug_log " -> 0 []"];
        0, []
      end
      else begin
        [%debug_log " -> %d [(%d,%d)]" n a b];
        n, [(a, b)]
      end
    in
    let plen = Array.length pmap in
    let flen = Array.length fmap in

    let idx = ref 0 in
    let ranges = ref [] in

    for i = 0 to plen - 1 do
      [%debug_log "i=%d" i];
      let ovl = ref 0 in
      let rs = ref [] in
      let cur = ref 0 in
      for j = !cur to flen - 1 do
        [%debug_log " j=%d" j];
        let (pa, pb) = ((pi (i-1))+1, (pi i)) in
        let (fa, fb) = ((fi (j-1))+1, (fi j)) in
        let x, r = overlap (pa, pb) (fa, fb) in
        if x > 0 then begin
          if
            x >= !ovl &&
            (flen = 1 || (fb - pb) <= x || fa <= pa && pb <= fb) then begin
            cur := j;
            ovl := x;
            rs := r
          end
        end
      done;
      ranges := !ranges @ !rs;
      idx := i
    done;
    !idx, !ranges

  let paths_to_string paths = String.concat ";" (List.map (fun p -> p#to_string) paths)

  let filter_paths_i shift i paths =
    [%debug_log "shift=%d i=%d paths=[%s]" shift i
      (String.concat ";" (List.map (fun p -> p#to_string) paths))];
    let ps = ref paths in
    if shift > 0 then
      for _ = 0 to shift - 1 do
        ps := List.tl !ps
      done;
    let c = ref 0 in
    let paths_ =
      List.filter
        (fun p ->
          if not p#has_frac_ofs then
            incr c;
          !c <= i
        ) (*paths*)!ps
    in
    [%debug_log " -> [%s]" (paths_to_string paths_)];
    paths_

  let tbl_keys tbl = Hashtbl.fold (fun k _ l -> k::l) tbl []
  let tbl_add_uniq tbl k v =
    try
      let l = Hashtbl.find tbl k in
      if not (List.mem v l) then
        Hashtbl.replace tbl k (v::l)
    with
      Not_found -> Hashtbl.add tbl k [v]


  class ['node, 'tree] seq
      options
      ?(irreversible_flag=false)
      (tree1 : 'tree tree_t)
      (tree2 : 'tree tree_t)
      nmapping
      edits_copy
      edit_seq
      (*(edit_seq : ('data node_t, 'tree tree_t) Edit_base.seq_base)*)
      =
    let is_indivisible_move = edits_copy#is_indivisible_move in
    let edit_list =
      (*if options#minimize_delta_flag then
        List.filter_map (op_of_editop_filt ~more nmapping edit_seq tree1) edit_seq#content
      else*)
        List.concat_map opl_of_editop edit_seq#content
    in
    object (self)

      val mutable edits = edit_list

      val mutable _filter = fun _ -> true
      val filt_blacklist = Xset.create 0 (* node set *)

      val staying_moves = Xset.create 0
      val remote_stable_tbl = Hashtbl.create 0

      val edit_tbl1 = Hashtbl.create 0 (* uid -> edit list *)
      val edit_tbl2 = Hashtbl.create 0 (* uid -> edit list *)

      val mutable stid_count = 0
      val stid_tbl = Hashtbl.create 0 (* uid -> stid *)
      val excluded_nodes = Xset.create 0 (* node set *)
      val st_tbl = Hashtbl.create 0 (* stid -> root node * excluded node list * size *)
      val mid_tbl = Hashtbl.create 0 (* stid -> mid *)
      val rev_mid_tbl1 = Hashtbl.create 0 (* mid -> stid *)
      val rev_mid_tbl2 = Hashtbl.create 0 (* mid -> stid *)

      val pos_cache = Hashtbl.create 0 (* node -> pos *)

      val lift_tbl1 = Hashtbl.create 0 (* Path.t * Path.t -> Path.t * subtree_key * upstream count *)
      val lift_tbl2 = Hashtbl.create 0 (* Path.t * Path.t -> Path.t * subtree_key * upstream count *)

      val edit_parent_tbl1 = Hashtbl.create 0
      val edit_parent_tbl2 = Hashtbl.create 0

      val lifted_nodes1 = Xset.create 0
      val lifted_nodes2 = Xset.create 0

      val mem_pos_tbl = Hashtbl.create 0 (* node -> pos *)

      val intermediate_pos_tbl1 = Hashtbl.create 0 (* node -> pos *)
      val intermediate_ofs_tbl1 = Hashtbl.create 0 (* node -> ofs *)

      val intermediate_pos_tbl2 = Hashtbl.create 0 (* node -> pos *)
      val intermediate_ofs_tbl2 = Hashtbl.create 0 (* node -> ofs *)

      val intermediate_parent_tbl1 = Hashtbl.create 0 (* node -> node *)
      val intermediate_parent_tbl2 = Hashtbl.create 0 (* node -> node *)

      val key_opt_cache = Hashtbl.create 0

      val is_upward_staying_move_cache = Hashtbl.create 0 (* tree * mid -> bool *)

      val parent_staying_move_tbl1 = Hashtbl.create 0 (* child -> parent *)
      val parent_staying_move_tbl2 = Hashtbl.create 0 (* child -> parent *)

      val common_ancestor_tbl = Hashtbl.create 0 (* uid list -> node * tbl *)

      val keys_with_changed_sub_path = Xset.create 0

      val nodes_to_be_lifted_tbl = Hashtbl.create 0

      val upstream_keys1 = Xset.create 0
      val upstream_keys2 = Xset.create 0

      val canceled_stable_nodes1 = Xset.create 0
      val canceled_stable_nodes2 = Xset.create 0

      val pre_canceled_stable_nodes1 = Xset.create 0
      val pre_canceled_stable_nodes2 = Xset.create 0

      val locked_stable_nodes1 = Xset.create 0
      val locked_stable_nodes2 = Xset.create 0

      val comp_cand_tbl = Hashtbl.create 0

      val walls = Hashtbl.create 0
      val quasi_walls = Hashtbl.create 0

      val simple_ins_roots1 = Xset.create 0
      val simple_ins_roots2 = Xset.create 0

      val pre_anc1to_tbl = Hashtbl.create 0 (* key -> insertion target node *)
      val pre_anc2to_tbl = Hashtbl.create 0 (* key -> insertion target node *)

      val anc1to_tbl = Hashtbl.create 0 (* key -> insertion target node * path * boundary *)
      val anc2to_tbl = Hashtbl.create 0 (* key -> insertion target node * path * boundary *)

      val rev_anc1to_tbl = Hashtbl.create 0 (* insertion target node * pos -> key list *)
      val rev_anc2to_tbl = Hashtbl.create 0 (* insertion target node * pos -> key list *)

      val parent_key_tbl1 = Hashtbl.create 0
      val parent_key_tbl2 = Hashtbl.create 0

      val parent_spec_tbl = Hashtbl.create 0 (* node -> (key option * upc * path option) *)

      val mutable deferred_checks = []

      val forced_upstream_nodes = Xset.create 0

      val movins_tbl = Hashtbl.create 0

      val group_tbl = Hashtbl.create 0

      initializer
        List.iter
          (fun ed ->
            match ed with
            | Delete(nd1, excluded1) -> begin
                scan_initial_cluster nd1 excluded1
                  (fun n -> tbl_add edit_tbl1 n#uid ed)
            end
            | Insert(nd2, excluded2) -> begin
                scan_initial_cluster nd2 excluded2
                  (fun n -> tbl_add edit_tbl2 n#uid ed)
            end
            | Relabel(nd1, excluded1, nd2, excluded2) -> begin
                scan_initial_cluster nd1 excluded1
                  (fun n -> tbl_add edit_tbl1 n#uid ed);
                scan_initial_cluster nd2 excluded2
                  (fun n -> tbl_add edit_tbl2 n#uid ed)
            end
            | Move(_, _, nd1, excluded1, nd2, excluded2) -> begin
                scan_initial_cluster nd1 excluded1
                  (fun n -> tbl_add edit_tbl1 n#uid ed);
                scan_initial_cluster nd2 excluded2
                  (fun n -> tbl_add edit_tbl2 n#uid ed)
            end
            | MoveInsert _ -> ()
          ) edit_list;

        if options#minimize_delta_flag then
          [%debug_log "filtering edits..."];
          _filter <-
            (fun ed ->
              match ed with
              | Relabel(nd1, _, nd2, _) -> begin
                  if
                    options#ignore_non_orig_relabel_flag &&
                    (not nd1#data#is_named_orig) && (not nd1#data#has_value) &&
                    (not nd2#data#is_named_orig) && (not nd2#data#has_value) &&
                    nd1#data#_anonymized_label = nd2#data#_anonymized_label &&
                    nd1#data#elem_name_for_delta = nd2#data#elem_name_for_delta
                  then begin
                    [%debug_log "filtered: %s" (to_string ed)];
                    false
                  end
                  else if begin
                    options#ignore_non_orig_relabel_flag &&
                    match nd1#data#orig_lab_opt, nd2#data#orig_lab_opt with
                    | Some o1, Some o2 ->
                        o1 = o2 || nd1#data#orig_to_elem_data_for_eq = nd2#data#orig_to_elem_data_for_eq
                    | _ -> false
                  end then begin
                    [%debug_log "filtered: %s" (to_string ed)];
                    false
                  end
                  else if options#weak_eq_flag && nd1#data#is_compatible_with nd2#data then begin
                    [%debug_log "filtered: %s" (to_string ed)];
                    false
                  end
                  else
                    true
              end
              | Move(_, _, nd1, exc1, nd2, exc2) when not (Xset.mem filt_blacklist nd1) -> begin
                  if
                    options#ignore_move_of_unordered_flag(* && not options#recover_orig_ast_flag*) &&
                    nd1#data#is_order_insensitive && nd2#data#is_order_insensitive &&
                    exc1 = [] && exc2 = [] &&
                    let pnd1 = nd1#initial_parent in
                    let pnd2 = nd2#initial_parent in
                    (try nmapping#find pnd1 == pnd2 with _ -> false) &&
                    (try
                      edit_seq#iter_moves
                        (function
                          | Editop.Move(_, _, (_, e1), _) -> begin
                              List.iter
                                (fun inf ->
                                  if Info.get_node inf == nd1 then
                                    raise Exit
                                ) !e1
                          end
                          | _ -> assert false
                        );
                      true
                    with
                      Exit -> false) &&
                    match edit_seq#find12 pnd1 pnd2 with
                    | [] -> true
                    | [Editop.Relabel _] -> pnd1#data#elem_name_for_delta = pnd2#data#elem_name_for_delta
                    | _ -> false
                  then begin
                    [%debug_log "filtered: %s" (to_string ed)];
                    false
                  end
                  else
                    true
              end
              | _ -> true);


      method fail : 'a. string -> 'a = fun mes ->
        failwith ("Delta.Edit.seq#"^mes)

      method private filter ed = _filter ed

      method private is_node_to_be_lifted = Hashtbl.mem nodes_to_be_lifted_tbl
      method private get_key_of_node_to_be_lifted k =
        match Hashtbl.find nodes_to_be_lifted_tbl k with
        | Some v -> v
        | None -> raise Not_found
      method private add_node_to_be_lifted ?key x = Hashtbl.replace nodes_to_be_lifted_tbl x key

      method private get_parent_spec nd =
        Hashtbl.find parent_spec_tbl nd

      method private is_quasi_upstream nd =
        try
          let k_opt, upc, _ = Hashtbl.find parent_spec_tbl nd in
          k_opt <> None && upc > 0
        with
          Not_found -> false

      method private has_parent_path nd =
        try
          let k_opt, _, _ = Hashtbl.find parent_spec_tbl nd in
          k_opt <> None
        with
          Not_found -> false

      method private reg_deferred_check f =
        deferred_checks <- f :: deferred_checks

      method private do_deferred_checks () =
        List.iter
          (fun f ->
            try
              f()
            with
              _ -> ()
          ) deferred_checks

      method private tree_of_node nd =
        try
          if nd == (tree1#search_node_by_uid nd#uid) then
            tree1
          else
            tree2
        with
          Not_found -> tree2

      method private canceled_stable_node_list tree =
        let s =
          if tree == tree2 then
            canceled_stable_nodes1
          else
            canceled_stable_nodes2
        in
        Xset.to_list s

      method private pre_cancel_stable_node nd =
        let tree = self#tree_of_node nd in
        let c, l =
          if tree == tree2 then
            pre_canceled_stable_nodes1, locked_stable_nodes1
          else
            pre_canceled_stable_nodes2, locked_stable_nodes2
        in
        if not (Xset.mem l nd) then begin
          if not (Xset.mem c nd) then begin
            [%debug_log "%a canceled" nps nd];
            Xset.add c nd
          end
        end

      method private cancel_stable_node nd =
        let tree = self#tree_of_node nd in
        let s =
          if tree == tree2 then
            canceled_stable_nodes1
          else
            canceled_stable_nodes2
        in
        if not (Xset.mem s nd) then begin
          [%debug_log "%a canceled" nps nd];
          Xset.add s nd
        end

      method private is_canceled_stable_node nd =
        let tree = self#tree_of_node nd in
        let s =
          if tree == tree2 then
            canceled_stable_nodes1
          else
            canceled_stable_nodes2
        in
        Xset.mem s nd

      method private is_pre_canceled_stable_node nd =
        let tree = self#tree_of_node nd in
        let s =
          if tree == tree2 then
            pre_canceled_stable_nodes1
          else
            pre_canceled_stable_nodes2
        in
        Xset.mem s nd

      method private lock_stable_node nd =
        let tree = self#tree_of_node nd in
        let s =
          if tree == tree2 then
            locked_stable_nodes1
          else
            locked_stable_nodes2
        in
        if not (Xset.mem s nd) then begin
          [%debug_log "%a locked" nps nd];
          Xset.add s nd
        end

      method private filter_canceled_stable_nodes tree nmap' nds =
        let s =
          if tree == tree2 then
            canceled_stable_nodes1
          else
            canceled_stable_nodes2
        in
        List.filter
          (fun x ->
            not (Xset.mem s x) &&
            try
              not (Xset.mem s (nmap' x))
            with
              Not_found -> true
          ) nds

      method private iter_canceled_stable_nodes tree f =
        let s =
          if tree == tree2 then
            canceled_stable_nodes1
          else
            canceled_stable_nodes2
        in
        Xset.iter f s

      method private restore_canceled_stable_node nd =
        let tree = self#tree_of_node nd in
        let s =
          if tree == tree2 then
            canceled_stable_nodes1
          else
            canceled_stable_nodes2
        in
        [%debug_log "removing %a" nps nd];
        Xset.remove s nd

      method get_parent_staying_move1 mid =
        let m = Hashtbl.find parent_staying_move_tbl1 mid in
        [%debug_log "%a -> %a" MID.ps mid MID.ps m];
        m

      method has_parent_staying_move1 mid =
        let b = Hashtbl.mem parent_staying_move_tbl1 mid in
        [%debug_log "%a -> %B" MID.ps mid b];
        b

      method get_parent_staying_move2 mid =
        let m = Hashtbl.find parent_staying_move_tbl2 mid in
        [%debug_log "%a -> %a" MID.ps mid MID.ps m];
        m

      method has_parent_staying_move2 mid =
        let b = Hashtbl.mem parent_staying_move_tbl2 mid in
        [%debug_log "%a -> %B" MID.ps mid b];
        b

      method is_deleted nd =
        try
          List.exists
            (function
              | Delete _ -> true
              | _ -> false)
            (Hashtbl.find edit_tbl1 nd#uid)
        with
          Not_found -> false

      method is_moved nd =
        try
          List.exists
            (function
              | Move _ -> true
              | _ -> false)
            (Hashtbl.find edit_tbl1 nd#uid)
        with
          Not_found -> false

      method private _reg_parent_key parent_key_tbl paths key =
        List.iter
          (fun p ->
            match p#key_opt with
            | Some k -> begin
                let path = p#path in
                [%debug_log "%s -> %s (%s)" (key_to_string k) (key_to_string key) (Path.to_string path)];
                let tbl =
                  try
                    Hashtbl.find parent_key_tbl k
                  with
                    Not_found -> begin
                      let t = Hashtbl.create 0 in
                      Hashtbl.add parent_key_tbl k t;
                      t
                    end
                in
                tbl_add_uniq tbl key path
            end
            | None -> ()
          ) paths

      method private reg_parent_key1 = self#_reg_parent_key parent_key_tbl1
      method private reg_parent_key2 = self#_reg_parent_key parent_key_tbl2

      method private reg_intermediate_parent1 n p =
        [%debug_log "%a -> %a" nps n nps p];
        Hashtbl.add intermediate_parent_tbl1 n p

      method private reg_intermediate_parent2 n p =
        [%debug_log "%a -> %a" nps n nps p];
        Hashtbl.add intermediate_parent_tbl2 n p

      method private find_intermediate_parent1 n =
        [%debug_log "%a" nps n];
        let p = Hashtbl.find intermediate_parent_tbl1 n in
        [%debug_log " -> %a" nps p];
        p

      method private find_intermediate_parent2 n =
        [%debug_log "%a" nps n];
        let p = Hashtbl.find intermediate_parent_tbl2 n in
        [%debug_log " -> %a" nps p];
        p

      method private reg_intermediate_ofs1 n ofs =
        [%debug_log "%a -> %d" nps n ofs];
        Hashtbl.add intermediate_ofs_tbl1 n ofs

      method private reg_intermediate_ofs2 n ofs =
        [%debug_log "%a -> %d" nps n ofs];
        Hashtbl.add intermediate_ofs_tbl2 n ofs

      method private find_intermediate_ofs1 n =
        [%debug_log "%a" nps n];
        let ofs = Hashtbl.find intermediate_ofs_tbl1 n in
        [%debug_log " -> %d" ofs];
        ofs

      method private find_intermediate_ofs2 n =
        [%debug_log "%a" nps n];
        let ofs = Hashtbl.find intermediate_ofs_tbl2 n in
        [%debug_log " -> %d" ofs];
        ofs

      method private has_intermediate_ofs1 n = Hashtbl.mem intermediate_ofs_tbl1 n

      method private has_intermediate_ofs2 n = Hashtbl.mem intermediate_ofs_tbl2 n

      method private reg_intermediate_pos1 n pos =
        if not (Hashtbl.mem intermediate_pos_tbl1 n) then begin
          [%debug_log "%a -> %d" nps n pos];
          Hashtbl.add intermediate_pos_tbl1 n pos
        end

      method private reg_intermediate_pos2 n pos =
        if not (Hashtbl.mem intermediate_pos_tbl2 n) then begin
          [%debug_log "%a -> %d" nps n pos];
          Hashtbl.add intermediate_pos_tbl2 n pos
        end

      method private find_intermediate_pos1 n =
        [%debug_log "%a" nps n];
        let pos = Hashtbl.find intermediate_pos_tbl1 n in
        [%debug_log " -> %d" pos];
        pos

      method private find_intermediate_pos2 n =
        [%debug_log "%a" nps n];
        let pos = Hashtbl.find intermediate_pos_tbl2 n in
        [%debug_log " -> %d" pos];
        pos

      method private add_mem_pos n i =
        [%debug_log "%a -> %d" nps n i];
        Hashtbl.add mem_pos_tbl n i

      method private get_mem_pos n = Hashtbl.find mem_pos_tbl n

      method private gen_stid() =
        let i = stid_count in
        stid_count <- stid_count + 1;
        i

      method private reg_subtree (*tree*)_ root excluded =
        (*Xset.add excluded_nodes root;!!!*)
        List.iter (Xset.add excluded_nodes) excluded;
        let id = self#gen_stid() in

        [%debug_log "stid=%s root=%a excluded=[%a]"
          (stid_to_str id) nps root nsps excluded];

        let sz = ref 0 in

        scan_initial_cluster root excluded
          (fun nd ->
            incr sz;
            Hashtbl.add stid_tbl nd#uid id
          );
        Hashtbl.add st_tbl id (root, excluded, !sz);
        id

      method private find_stid uid = Hashtbl.find stid_tbl uid

      method private has_stid uid = Hashtbl.mem stid_tbl uid

      method private is_excluded x =
        let b = Xset.mem excluded_nodes x in
        [%debug_log "%a: b=%B" nps x b];
        b

      method get_anc_in_excluded n =
        if self#is_excluded n then
          n
        else
          self#get_anc_in_excluded n#initial_parent

      method private get_pos_shift is_stable stid nd =
        [%debug_log "stid=%s nd=%a" (stid_to_str stid) nps nd];
        try
          let root, excluded, _ = self#get_subtree_spec stid in
          let _ = root in
          [%debug_log "root=%a excluded=[%a]" nps root nsps excluded];
          let gi = nd#gindex in
          let p = nd#initial_parent in
          let adj =
            List.fold_left
              (fun a n ->
                if n#initial_parent == p && n#gindex < gi && is_stable n then
                  a + 1
                else
                  a
              ) 0 excluded
          in
          [%debug_log "adj=%d" adj];
          if adj = 0 then
            None
          else
            Some adj
        with
          Not_found -> None

      method private get_subtree_spec stid =
        Hashtbl.find st_tbl stid

      method private get_subtree_root stid =
        let root, _, _ = self#get_subtree_spec stid in
        root

      method private get_subtree_size stid =
        let _, _, sz = self#get_subtree_spec stid in
        sz

      method private _reg_mid rev_mid_tbl stid mid =
        [%debug_log "%d -> %a" stid MID.ps mid];
        Hashtbl.add mid_tbl stid mid;
        Hashtbl.add rev_mid_tbl mid stid;

      method private reg_mid1 = self#_reg_mid rev_mid_tbl1
      method private reg_mid2 = self#_reg_mid rev_mid_tbl2

      method private find_mid = Hashtbl.find mid_tbl
      method private has_mid = Hashtbl.mem mid_tbl

      method private stid_of_mid1 = Hashtbl.find rev_mid_tbl1
      method private stid_of_mid2 = Hashtbl.find rev_mid_tbl2

      method private _stid_of_key stid_of_mid = function
        | K_stid stid -> stid
        | K_mid mid -> stid_of_mid mid
        | _ -> raise Not_found

      method private stid_of_key1 = self#_stid_of_key self#stid_of_mid1
      method private stid_of_key2 = self#_stid_of_key self#stid_of_mid2

      method private _get_subtree_root_by_key stid_of_key key =
        self#get_subtree_root (stid_of_key key)

      method private get_subtree_root_by_key1 =
        self#_get_subtree_root_by_key self#stid_of_key1

      method private get_subtree_root_by_key2 =
        self#_get_subtree_root_by_key self#stid_of_key2


      method private find_key_opt uid =
        try
          Hashtbl.find key_opt_cache uid
        with
          Not_found -> begin
            let key_opt =
              try
                let stid = self#find_stid uid in
                try
                  Some (key_of_mid (self#find_mid stid))
                with
                  Not_found -> Some (key_of_stid stid)
              with
                Not_found -> None
            in
            [%debug_log "%a -> %s" UID.ps uid (key_opt_to_string key_opt)];
            Hashtbl.add key_opt_cache uid key_opt;
            key_opt
          end

      method private find_key uid =
        match self#find_key_opt uid with
        | Some k -> k
        | None -> raise Not_found

      (*method map f = List.map f edits*)

      method map_for_delta f =
        let sort =
          List.fast_sort
            (fun ed1 ed2 ->
              match ed1, ed2 with
              | Insert(nd1, _), Insert(nd2, _)
              | MoveInsert(_, _, nd1, _), MoveInsert(_, _, nd2, _)
              | Insert(nd1, _), MoveInsert(_, _, nd2, _)
              | MoveInsert(_, _, nd1, _), Insert(nd2, _)
              | Move(_, _, _, _, nd1, _), Move(_, _, _, _, nd2, _)
              | Insert(nd1, _), Move(_, _, _, _, nd2, _)
              | Move(_, _, _, _, nd1, _), Insert(nd2, _) ->
                  Stdlib.compare nd2#gindex nd1#gindex
              | _ ->
                  self#fail
                    (sprintf "map_for_delta: sort: illegal edit: %s, %s"
                       (to_string ed1) (to_string ed2))
            )
        in
        let sorted_edits =
          let dels, inss, movs, rels = ref [], ref [], ref [], ref [] in
          self#iter
            (fun edit ->
              match edit with
              | Relabel _ -> rels := edit::!rels
              | Delete _  -> dels := edit::!dels
              | Insert _ -> inss := edit::!inss
              | MoveInsert _ -> inss := edit::!inss
              | Move _ -> movs := edit::!movs
            );
          !rels @ (sort !inss) @ !movs @ !dels
        in
        List.map f sorted_edits

      method iter f = List.iter f edits

      method dump = self#iter (fun e -> Printf.fprintf stdout "%s\n" (to_string e))

      method find1 uid =
        try
          Hashtbl.find edit_tbl1 uid
        with
          Not_found -> []

      method find2 uid =
        try
          Hashtbl.find edit_tbl2 uid
        with
          Not_found -> []

      method find_mov1 uid =
        let l =
          List.filter
            (function
              | Move _ -> true
              | _ -> false
            ) (Hashtbl.find edit_tbl1 uid)
        in
        match l with
        | [] -> raise Not_found
        | m::_ -> m

      method find_mov2 uid =
        let l =
          List.filter
            (function
              | Move _ -> true
              | _ -> false
            ) (Hashtbl.find edit_tbl2 uid)
        in
        match l with
        | [] -> raise Not_found
        | m::_ -> m

      method mem_mov1 uid =
        try
          let _ = self#find_mov1 uid in
          true
        with
          Not_found -> false

      method mem_mov2 uid =
        try
          let _ = self#find_mov2 uid in
          true
        with
          Not_found -> false

      method is_stable1 nd =
        match self#find1 nd#uid with
        | []
        | [Relabel _] -> true
        | _ -> false

      method is_stable2 nd =
        match self#find2 nd#uid with
        | []
        | [Relabel _] -> true
        | _ -> false

      method get_remote_stable_tbl mid =
        try
          Hashtbl.find remote_stable_tbl mid
        with
          Not_found -> [], []

      method is_staying_move = Xset.mem staying_moves

      (*method sort =
        let sort1 =
          List.fast_sort
            (fun ed1 ed2 ->
              match ed1, ed2 with
              | Delete(nd1, _), Delete(nd2, _)
              | Move(_, _, nd1, _, _, _), Move(_, _, nd2, _, _, _)
              | Delete(nd1, _), Move(_, _, nd2, _, _, _)
              | Move(_, _, nd2, _, _, _), Delete(nd1, _) ->
                  Stdlib.compare nd1#gindex nd2#gindex
              | _ ->
                  self#fail
                    (sprintf "sort: sort1: illegal edit: %s, %s"
                       (to_string ed1) (to_string ed2))
            )
        in
        let sort2 =
          List.fast_sort
            (fun ed1 ed2 ->
              match ed1, ed2 with
              | Insert(nd1, _), Insert(nd2, _)
              | Move(_, _, _, _, nd1, _), Move(_, _, _, _, nd2, _)
              | Insert(nd1, _), Move(_, _, _, _, nd2, _)
              | Move(_, _, _, _, nd2, _), Insert(nd1, _) ->
                  Stdlib.compare nd1#gindex nd2#gindex
              | _ ->
                  self#fail
                    (sprintf "sort: sort2: illegal edit: %s, %s"
                       (to_string ed1) (to_string ed2))

            )
        in
        let dels, inss, rels = ref [], ref [], ref [] in
        let movs = ref [] in
        self#iter
          (fun edit ->
            match edit with
            | Delete _  -> dels := edit::!dels
            | Insert _  -> inss := edit::!inss
            | Relabel _ -> rels := edit::!rels
            | Move _    -> movs := edit::!movs
          );
        edits <-
          (List.rev !rels) @ (sort1 !dels) @ (sort2 !inss) @ (sort1 !movs)*)

      (* experimental *)
      method private _is_simple_ins tree is_stable' is_stable_' nmap' ?(exact=true) ?(top_nodes=[]) x' =
        [%debug_log "x'=%a top_nodes=[%a]" nps x' nsps top_nodes];
        let ancto_tbl =
          if tree == tree1 then
            anc1to_tbl
          else
            anc2to_tbl
        in
        let get_ins_target = self#get_ins_target tree nmap' is_stable' in
        let lr = ref [] in
        let b =
          (*Xset.mem simple_ins_roots x' ||*)
          not (is_stable' x') &&
          let moveon x' = not (is_stable' x') in
          let ss' = get_p_descendants ~moveon is_stable_' x' in
          [%debug_log "ss'=[%a]" nsps ss'];
          (match ss' with
          | [] -> true
          | [_] when not exact -> true
          | [s'] -> begin
              List.exists
                (fun tn ->
                  is_ancestor tn (nmap' s')
                ) top_nodes
          end
          | ss' when List.exists (fun tn -> List.for_all (is_ancestor tn) (List.map nmap' ss')) top_nodes -> true
          | _ -> false) &&
          (*let parent_is_staying_move =
            try
              let stid = self#find_stid x'#initial_parent#uid in
              let mid = self#find_mid stid in
              self#is_staying_move mid
            with
              _ -> false
          in
          [%debug_log "parent_is_staying_move=%B" parent_is_staying_move];
          parent_is_staying_move ||*)
          let xa_opt = ref None in
          (match self#find_key_opt x'#uid with
          | Some xk when top_nodes <> [] && Hashtbl.mem ancto_tbl xk -> begin
              [%debug_log "xk=%s" (key_to_string xk)];
              let xa, (xpt, xps) = Hashtbl.find ancto_tbl xk in
              let _ = xpt in
              let _ = xps in
              xa_opt := Some xa;
              let a0 = (List.hd top_nodes)#initial_parent in
              [%debug_log "a0=%a xa=%a xpt=%s xps=[%s]" nps a0 nps xa xpt#to_string (paths_to_string xps)];
              let b =
                not
                  (Array.exists
                     (fun y' ->
                       [%debug_log "y'=%a" nps y'];
                       y'#initial_pos < x'#initial_pos &&
                       match self#find_key_opt y'#uid with
                       | None -> false
                       | Some yk ->
                           try
                             let ya =
                               try
                                 let a, _ =  Hashtbl.find ancto_tbl yk in
                                 a
                               with
                                 Not_found ->
                                   let a, _, _, _ = get_ins_target y' in
                                   a
                             in
                             [%debug_log "ya=%a" nps ya];
                             let b = ya != a0 && is_ancestor ya xa in
                             if b then [%debug_log "found"];
                             b
                           with _ -> false
                     ) x'#initial_parent#initial_children)
              in
              [%debug_log "b=%B" b];
              b
          end
          | _ -> true) &&
          let lr_opts' = get_p_siblings is_stable_' x' in
          let sss' =
            match lr_opts' with
            | Some l', Some r' -> [l'; r']
            | Some y', None | None, Some y' -> [y']
            | _ -> []
          in
          [%debug_log "sss'=[%a]" nsps sss'];
          match sss' with
          | [] -> true
          | [_] when begin
              match !xa_opt with
              | Some xa -> List.exists (fun t -> is_ancestor t xa) top_nodes
              | None -> false
          end -> false
          | [_] -> true
          | _ ->
              let sss = List.map nmap' sss' in
              lr := sss;
              [%debug_log "sss=[%a]" nsps sss];
              if List.exists self#has_parent_path sss then begin
                [%debug_log "!!!!!"];
                true
              end
              else
              let a, _ = self#get_latest_common_ancestor tree sss in
              let b =
                top_nodes <> [] && (List.hd top_nodes)#initial_parent == a ||
                List.exists (fun ss -> ss#initial_parent == a) sss ||
                List.exists (fun s -> s#initial_parent == a) (List.map nmap' ss')
              in
              [%debug_log "b=%B" b];
              b &&
              match top_nodes with
              | [] -> true
              | _ ->
                  not
                    (List.exists
                       (fun tn ->
                         List.for_all (fun ss -> is_ancestor tn ss) sss
                       ) top_nodes)
        in
        [%debug_log "%a -> %B (exact=%B)" nps x' b exact];
        if b then begin (* check if not simple *)
          match !lr with
          | [lsn; rsn] -> begin
              match self#find_key_opt x'#initial_parent#uid with
              | Some pk -> begin
                  [%debug_log "pk=%s" (key_to_string pk)];
                  try
                    let a, (pt, ps) = Hashtbl.find ancto_tbl pk in
                    let _ = pt in
                    let _ = ps in
                    [%debug_log "a=%a pos=%d nb=%d" nps a pt#position (List.length ps)];
                    let anc, _ = self#get_latest_common_ancestor tree [lsn;rsn] in
                    [%debug_log "anc=%a" nps anc];
                    if self#has_parent_path lsn && self#has_parent_path rsn then begin
                      b
                    end
                    else if is_ancestor a anc then begin
                      [%debug_log "%a -> false (exact=%B)" nps x' exact];
                      false
                    end
                    else
                      b
                  with _ -> b
              end
              | None -> b
          end
          | _ -> b
        end
        else
          b

      method private paths_to_have_frac_ofs paths_to =
        List.exists
          (fun path -> path#has_frac_ofs) paths_to

      method private get_top_nodes rt' bn' anc_to path_to paths_to =
        [%debug_log "rt'=%a bn'=%a" nps rt' nps bn'];
        [%debug_log "anc_to=%a path_to=%s paths_to=%s"
          nps anc_to path_to#to_string (boundary_to_string paths_to)];
        let pos = path_to#position in
        let npaths = List.length paths_to in
        [%debug_log "pos=%d npaths=%d" pos npaths];
        let cl = ref [] in
        for i = pos + npaths - 1 downto pos do
          let ci = anc_to#initial_children.(i) in
          cl := ci :: !cl
        done;
        [%debug_log "cl=[%a]" nsps !cl];
        let top_nodes = ref [] in
        List.iter2
          (fun c rp ->
            [%debug_log "c=%a rp=%s" nps c rp#to_string];
            if not rp#has_frac_ofs then
            match rp#key_opt with
            | Some _ -> ()
            | None ->
                let prp = Path.get_parent rp#path in
                [%debug_log "prp=%s" (Path.to_string prp)];
                try
                  let p' = self#acc rt' prp in
                  [%debug_log "p'=%a" nps p'];
                  if p' == bn'#initial_parent then begin
                    top_nodes := c :: !top_nodes
                  end
                with
                  Not_found -> ()
          ) !cl paths_to;
        [%debug_log "top_nodes=[%a]" nsps !top_nodes];
        !top_nodes

      method private is_excluded_tn is_stable nmap rt x bn anc_to path_to paths_to =
        [%debug_log "x=%a bn=%a anc_to=%a path_to=%s paths_to=%s"
          nps x nps bn nps anc_to path_to#to_string (boundary_to_string paths_to)];
        let b =
          x == bn ||
          let px = x#initial_parent in
          bn#initial_parent != px ||
          (*let base_pos = bn#initial_pos in*)
          let _ = [%debug_log "base_pos=%d" bn#initial_pos] in
          (*x#initial_pos >= base_pos ||*)(*!!!!!*)
          let top_nodes = self#get_top_nodes rt x anc_to path_to paths_to in
          let check_prev tn =
            let b =
              try
                for i = x#initial_pos - 1 downto 0 do
                  let prev = px#initial_children.(i) in
                  if is_stable prev then begin
                    if is_ancestor tn (nmap prev) then
                      raise Exit
                  end
                  else if
                    List.exists
                      (fun s ->
                        is_ancestor tn (nmap s)
                      ) (get_p_descendants is_stable prev)
                  then
                    raise Exit
                done;
                false
              with
                Exit -> true
            in
            [%debug_log "b=%B" b];
            b
          in
          self#is_canceled_stable_node x ||
          let ss =
            if is_stable x then
              [nmap x]
            else
              let is_stable_ x = is_stable x && not (self#is_canceled_stable_node x) in
              let moveon x = not (is_stable x) in
              List.map nmap (get_p_descendants ~moveon is_stable_ x)
          in
          [%debug_log "ss=[%a]" nsps ss];
          ss = [] ||
          List.exists
            (fun s ->
              [%debug_log "s=%a" nps s];
              List.for_all
                (fun tn ->
                  if tn == s || is_ancestor tn s then begin
                    [%debug_log "tn=%a is (an ancestor of) s=%a" nps tn nps s];
                    check_prev tn
                  end
                  else
                    true
                ) top_nodes
            ) ss
        in
        [%debug_log "b=%B x=%a bn=%a" b nps x nps bn];
        b

      method get_subpath tree (*tree'*)_ nmap' ?(ins_point_opt=None) k bn' =
        let lifted_nodes, is_stable, is_stable', get_ipos, get_iofs,
          stid_of_key, simple_ins_roots, ancto_tbl, is_ancestor_key,
          edit_parent_tbl, parent_key_tbl, rev_ancto_tbl =
          if tree == tree1 then
            lifted_nodes1,
            self#is_stable1,
            self#is_stable2,
            (fun _ -> raise Not_found),
            self#find_intermediate_ofs1,
            self#stid_of_key2,
            simple_ins_roots2,
            anc1to_tbl,
            self#is_ancestor_key1, edit_parent_tbl1, parent_key_tbl1,
            rev_anc1to_tbl
          else
            lifted_nodes2,
            self#is_stable2,
            self#is_stable1,
            (fun _ -> raise Not_found),
            self#find_intermediate_ofs2,
            self#stid_of_key1,
            simple_ins_roots1,
            anc2to_tbl,
            self#is_ancestor_key2, edit_parent_tbl2, parent_key_tbl2,
            rev_anc2to_tbl
        in
        let stid = stid_of_key k in
        let rt' = self#get_subtree_root stid in
        [%debug_log "rt'=%a k=%s bn'=%a" nps rt' (key_to_string k) nps bn'];
        let rp = get_rel_path rt'#apath bn'#apath in
        [%debug_log "rp=%s" (Path.to_string rp)];

        let is_stable_' x' = is_stable' x' && not (self#is_canceled_stable_node x') in
        let _is_simple_ins = self#_is_simple_ins tree is_stable' is_stable_' nmap' in

        let is_simple_ins x' =
          let b = Xset.mem simple_ins_roots x' in
          [%debug_log "%a -> %B" nps x' b];
          if b then begin
            [%debug_log "%a -> true" nps x'];
            Some true
          end
          else if self#find_key_opt x'#uid = None then begin
            [%debug_log "%a -> false" nps x'];
            Some false
          end
          else if
            try Hashtbl.mem ancto_tbl (self#find_key x'#uid) with _ -> false
          then begin
            [%debug_log "%a -> false" nps x'];
            Some false
          end
          else begin
            [%debug_log "%a -> unknown" nps x'];
            None
          end
        in

        let get_ins_target = self#get_ins_target tree nmap' is_stable' in

        let paths_opt = ref None in

        let anc_to, pos, nboundary =
          try
            let anc_to, (path_to, paths) = Hashtbl.find ancto_tbl k in
            let pos = path_to#position in
            let nb = List.length paths in
            paths_opt := Some paths;
            anc_to, pos, nb
          with
            Not_found ->
              match ins_point_opt with
              | Some ins_point -> ins_point
              | _ ->
                  let anc_to, pos, nb, _ = get_ins_target rt' in
                  anc_to, pos, nb
        in
        [%debug_log "anc_to=%a pos=%d nbondary=%d" nps anc_to pos nboundary];

        (*let top_nodes =
          try
            let anc_to, (path_to, paths) = Hashtbl.find ancto_tbl k in
            self#get_top_nodes rt' bn' anc_to path_to paths
          with
            _ -> []
        in*)
        let top_nodes =
          if nboundary > 0 then
            Array.to_list (Array.sub anc_to#initial_children pos nboundary)
          else
            []
        in
        [%debug_log "top_nodes=[%a]" nsps top_nodes];

        let unstable_top_nodes =
          List.filter (fun x -> not (is_stable x)) top_nodes
        in
        [%debug_log "unstable_top_nodes=[%a]" nsps unstable_top_nodes];
        let get_group x' =
          [%debug_log "x'=%a" nps x'];
          if self#is_canceled_stable_node x' then
            raise Not_found;
          let ss =
            if is_stable' x' then
              [nmap' x']
            else
              let moveon x' = not (is_stable' x') in
              List.map nmap' (get_p_descendants ~moveon is_stable_' x')
          in
          [%debug_log "ss=[%a]" nsps ss];
          let grps =
            List.filter
              (fun tn -> List.exists (fun s -> tn == s || is_ancestor tn s) ss)
              unstable_top_nodes
          in
          match grps with
          | [grp] -> [%debug_log "grp=%a" nps grp]; grp
          | _ -> raise Not_found
        in

        let is_excluded =
          begin %debug_block
          let all_excluded_stable =
            Array.for_all
              (fun x' -> is_stable' x' && self#is_excluded x')
              bn'#initial_parent#initial_children
          in
          [%debug_log "all_excluded_stable=%B" all_excluded_stable];
          end;

          let _is_excluded x = not (Hashtbl.mem comp_cand_tbl x) && self#is_excluded x in

          let moveon x' = not (is_stable' x') in
          let bnds =
            if is_stable' bn' then
              [nmap' bn']
            else
              List.map nmap' (get_p_descendants ~moveon is_stable_' bn')
          in
          [%debug_log "bnds=[%a]" nsps bnds];
          let top_nodes_ =
            List.filter (fun tn -> List.for_all (is_ancestor tn) bnds) top_nodes
          in
          [%debug_log "top_nodes_=[%a]" nsps top_nodes_];
          let get_grp x' =
            [%debug_log "x'=%a" nps x'];
            let ss =
              if is_stable' x' then
                [nmap' x']
              else
                List.map nmap' (get_p_descendants ~moveon is_stable_' x')
            in
            [%debug_log "ss=[%a]" nsps ss];
            let grp =
              List.filter
                (fun tn -> List.exists (fun s -> tn == s || is_ancestor tn s) ss)
                top_nodes
            in
            [%debug_log "grp=[%a]" nsps grp];
            grp
          in
          let in_base_group x' =
            [%debug_log "x'=%a" nps x'];
            let ss =
              if is_stable' x' then
                [nmap' x']
              else
                List.map nmap' (get_p_descendants ~moveon is_stable_' x')
            in
            [%debug_log "ss=[%a]" nsps ss];
            let b =
              ss <> [] &&
              List.for_all (fun s -> List.exists (fun tn -> is_ancestor tn s) top_nodes_) ss
            in
            [%debug_log "b=%B" b];
            b
          in
          let extra_base_cond x' =
            let b =
            self#is_excluded x' &&
            if
              self#is_excluded x' && not (is_stable' x') &&
              get_p_descendants is_stable' x' = [] &&
              try
                let xk = self#find_key x'#uid in
                [%debug_log "xk=%s" (key_to_string xk)];
                let a__pt_ps = Hashtbl.find ancto_tbl xk in
                let _ = a__pt_ps in
                begin %debug_block
                let a, (_, _) = a__pt_ps in
                [%debug_log "a=%a" nps a];
                end;
                let b = Hashtbl.mem edit_parent_tbl xk || Hashtbl.mem parent_key_tbl xk in
                [%debug_log "b=%B" b];
                b
              with _ -> false
            then
              false
            else
            (in_base_group x' &&
            let ca' = x'#initial_parent#initial_children in
            (*(x'#initial_pos > 0 &&
             array_range_exists
              (fun c' ->
                let cg = get_grp c' in
                [%debug_log "c'=%a cg=[%a]" nps c' nsps cg];
                Xlist.intersectionq cg top_nodes_ <> []
              ) ca' 0 (x'#initial_pos-1)) &&*)
            (match self#find_key_opt x'#initial_parent#uid with
            | Some k -> begin
                is_stable' x' &&
                try
                  let x = nmap' x' in
                  [%debug_log "x=%a" nps x];
                  let a, (pt, ps) =  Hashtbl.find ancto_tbl k in
                  let pos = pt#position in
                  let nb = List.length ps in
                  [%debug_log "a=%a pos=%d nb=%d" nps a pos nb];
                  let ca = a#initial_children in
                  for i = pos to pos + nb - 1 do
                    if is_ancestor ca.(i) x then begin
                      [%debug_log "i=%d: %a is an ancestor of %a" i nps ca.(i) nps x];
                      raise Exit
                    end
                  done;
                  true
                with
                | Exit -> false
                | _ -> true
            end
            | _ -> true
            ) &&
            array_range_exists
              (fun c' ->
                c' != x' &&
                match self#find_key_opt c'#uid with
                | Some ck when ck <> k -> begin
                    [%debug_log "ck=%s" (key_to_string ck)];
                    try
                      let a, (pt, ps) = Hashtbl.find ancto_tbl ck in
                      let _ = pt in
                      let _ = ps in
                      [%debug_log "c'=%a a=%a pos=%d nb=%d" nps c' nps a pt#position (List.length ps)];
                      List.exists (fun tn -> is_ancestor tn a) top_nodes_ &&
                      List.for_all (fun bn -> is_ancestor a bn) bnds
                    with _ -> false
                end
                | _ -> false
              ) ca' (bn'#initial_pos+1) ((Array.length ca')-1)) ||

              (self#is_excluded x' && not (is_stable' x') &&(* not simple ins*)
              get_p_descendants is_stable' x' = [] &&
              try
                let xk = self#find_key x'#uid in
                let _, (pt, _) =  Hashtbl.find ancto_tbl xk in
                pt#key_opt = None &&
                not (Hashtbl.mem edit_parent_tbl xk) &&
                not (Hashtbl.mem parent_key_tbl xk)
              with _ -> false) ||

              match !paths_opt with
              | Some paths -> begin
                  match get_grp x' with
                  | [g] -> begin
                      let path = List.nth paths (g#initial_pos - pos) in
                      [%debug_log "path=%s" path#to_string];
                      if path#key_opt = None then
                        let p' = self#acc rt' (Path.get_parent path#path) in
                        [%debug_log "p'=%a" nps p'];
                        x'#initial_parent != p'
                      else
                        false
                  end
                  | _ -> false
              end
              | _ -> false
            in
            [%debug_log "x'=%a b=%B" nps x' b];
            b
          in

          if true
            (*Array.exists
              (fun x' ->
                match self#find_key_opt x'#uid with
                | Some k0 -> k0 = k
                | None -> false
              ) bn'#initial_parent#initial_children ||
            self#is_canceled_stable_node bn' ||
            not (is_stable' bn') &&
            match get_p_descendants is_stable' bn' with
            | [s'] -> (*self#is_canceled_stable_node s'*)true
            | _ -> false*)
          then begin
            (*[%debug_log "%a is (has) a canceled_stable_node" nps bn'];*)
            fun lv x' ->
              [%debug_log "x'=%a lv=%d" nps x' lv];
              if lv > 0 then
                _is_excluded x'
              (*else if lv = 0 && all_excluded_stable then
                self#is_canceled_stable_node x' ||
                List.for_all
                  (fun y' ->
                    self#is_canceled_stable_node y'
                  ) (get_p_descendants is_stable' x')*)
              else if _is_excluded x' && x' == bn' then
                true
              else
                let base_cond = x' == bn' || extra_base_cond x' in
                [%debug_log "base_cond=%B" base_cond];
                let b =
                  _is_excluded x' &&
                  (base_cond ||
                    (is_stable' x' &&
                     (self#is_canceled_stable_node x' ||
                     Xset.mem lifted_nodes x' ||
                     (try (nmap' bn')#initial_parent == (nmap' x')#initial_parent with _ -> false) ||
                     let x = nmap' x' in
                     Array.exists
                       (fun y' ->
                         let b =
                           y'#initial_pos < x'#initial_pos &&
                           Hashtbl.mem walls y' &&
                           List.exists
                             (fun y ->
                               List.exists
                                 (fun tn ->
                                   is_ancestor tn y && is_ancestor tn x
                                 ) top_nodes
                             ) (List.map
                                  nmap'
                                  (if is_stable' y' then [y'] else get_p_descendants is_stable' y'))
                         in
                         if b then
                           [%debug_log "found: y'=%a" nps y'];
                         b
                       ) x'#initial_parent#initial_children
                     )
                    ) ||
                    (List.filter
                       (fun y' ->
                         not (self#is_canceled_stable_node y') &&
                         not (Xset.mem lifted_nodes y')
                       ) (x'::(get_p_descendants is_stable' x'))) = [] ||
                    List.exists
                         (fun tn ->
                           try
                             for i = x'#initial_pos-1 downto 0 do
                               let prev' = x'#initial_parent#initial_children.(i) in
                               let b =
                                 if is_stable' prev' then
                                   is_ancestor tn (nmap' prev')
                                 else
                                   List.exists
                                     (fun s' ->
                                       is_ancestor tn (nmap' s')
                                     ) (get_p_descendants is_stable' prev')
                               in
                               if b then
                                 raise Exit
                             done;
                             false
                           with
                             Exit -> true
                         ) top_nodes ||
                    Array.exists
                     (fun y' ->
                       [%debug_log "y'=%a" nps y'];
                       y' != x' &&
                       match self#find_key_opt y'#uid with
                       | Some k' -> begin
                           [%debug_log "k'=%s" (key_to_string k')];
                           if k' = k then
                             x'#initial_pos < y'#initial_pos && y'#initial_pos < bn'#initial_pos
                           else
                           (try
                             not (is_stable' x') &&
                             match self#find_key_opt x'#uid with
                             | None -> false
                             | Some xk' ->
                                 y'#initial_pos < x'#initial_pos &&
                                 let xa, xpos, xnb =
                                   try
                                     let a, (pt, ps) =  Hashtbl.find ancto_tbl xk' in
                                     a, pt#position, List.length ps
                                   with
                                     Not_found ->
                                       let a, pos, nb, _ = get_ins_target x' in
                                       a, pos, nb
                                 in
                                 let _ = xpos in
                                 let _ = xnb in
                                 [%debug_log "xa=%a xpos=%d xnb=%d x'=%a" nps xa xpos xnb nps x'];
                                 let ya, ypos, ynb =
                                   try
                                     let a, (pt, ps) =  Hashtbl.find ancto_tbl k' in
                                     a, pt#position, List.length ps
                                   with
                                     Not_found ->
                                       let a, pos, nb, _ = get_ins_target y' in
                                       a, pos, nb
                                 in
                                 [%debug_log "ya=%a ypos=%d ynb=%d y'=%a" nps ya ypos ynb nps y'];
                                 let b =
                                   ynb > 0 &&
                                   array_range_exists
                                     (fun x ->
                                       x == xa || is_ancestor x xa
                                     ) ya#initial_children ypos (ypos+ynb-1)
                                 in
                                 [%debug_log "b=%B" b];
                                 b
                           with _ -> false
                           ) ||
                           is_stable' x' &&
                           let x = nmap' x' in
                           (is_ancestor_key k k' &&
                           let a, pos, nb =
                             try
                               let a, (pt, ps) =  Hashtbl.find ancto_tbl k in
                               a, pt#position, List.length ps
                             with
                               Not_found ->
                                 let a, pos, nb, _ = get_ins_target y' in
                                 a, pos, nb
                           in
                           [%debug_log "a=%a pos=%d nb=%d x'=%a x=%a" nps a pos nb nps x' nps x];
                           try
                             for i = pos to pos + nb - 1 do
                               let ci = a#initial_children.(i) in
                               [%debug_log "ci=%a" nps ci];
                               if is_ancestor ci x then begin
                                 [%debug_log "found: ci=%a" nps ci];
                                 raise Exit
                               end
                             done;
                             false
                           with
                             Exit -> true
                           ) ||
                           y'#initial_pos < x'#initial_pos && not (Hashtbl.mem walls x') &&
                           has_p_descendant is_stable' y' &&
                           try
                             let a, p, nb =
                               try
                                 let a, (pt, ps) =  Hashtbl.find ancto_tbl k' in
                                 a, pt#position, List.length ps
                               with
                                 Not_found ->
                                   let a, p, nb, _ = get_ins_target y' in
                                   a, p, nb
                             in
                             let _ = p in
                             let _ = nb in
                             [%debug_log "a=%a p=%d nb=%d x'=%a x=%a" nps a p nb nps x' nps x];
                             let tn = get_ancestor_below a anc_to in
                             [%debug_log "tn=%a" nps tn];
                             let b =
                               pos <= tn#initial_pos && tn#initial_pos <= pos + nboundary - 1 &&
                               is_ancestor tn x
                             in
                             [%debug_log "b=%B" b];
                             b
                           with
                             _ -> false
                       end
                       | _ -> false
                     ) x'#initial_parent#initial_children
                  )
                in
                [%debug_log "x'=%a b=%B" nps x' b];
                let b =
                  if
                    b && not base_cond(*x' != bn'*) && is_stable_' x' &&
                    let prev_cond =
                      x'#initial_pos > 0 &&
                      try
                        let ca' = x'#initial_parent#initial_children in
                        let xpos' = x'#initial_pos in
                        let prev' = ca'.(xpos'-1) in
                        [%debug_log "prev'=%a" nps prev'];
                        (not (is_stable' prev') &&
                         (Xset.mem simple_ins_roots prev' ||
                         self#find_key_opt prev'#uid =
                         self#find_key_opt prev'#initial_parent#uid)
                        ) ||
                        self#is_canceled_stable_node prev'(* &&
                        ( (* NG????? *)
                         (try
                           [%debug_log "top_nodes=[%a]" nsps top_nodes];
                           let x = nmap' x' in
                           [%debug_log "x=%a" nps x];
                           List.memq x top_nodes
                         with _ -> false
                         )(* ||
                         (* NG????? *)
                         xpos' > 1 &&
                         array_range_exists
                           (fun x -> not (self#is_canceled_stable_node x)) ca' 0 (xpos'-2)*)
                        )*)
                      with
                      | _ -> true
                    in
                    [%debug_log "x'=%a prev_cond=%B" nps x' prev_cond];
                    prev_cond
                  then
                    false
                  else
                    b
                in
                [%debug_log "x'=%a b=%B" nps x' b];
                let b =
                  b &&
                  match self#find_key_opt x'#initial_parent#uid with
                  | Some (K_mid m) -> begin
                      not (self#is_staying_move m) ||
                      self#_is_upward_staying_move tree m ||
                      self#is_canceled_stable_node x'
                  end
                  | _ -> true
                in
                [%debug_log "x'=%a b=%B" nps x' b];
                let b =
                  b &&
                  (is_stable' x' ||
                  (*let exact =
                    try
                      let ca' = x'#initial_parent#initial_children in
                      for i = 0 to x'#initial_pos - 1 do
                        let c' = ca'.(i) in
                        if is_stable_' c' then
                          raise Exit
                      done;
                      false
                    with
                      Exit -> true
                  in*)
                  let moveon x' = not (is_stable' x') in
                  let ss' = get_p_descendants ~moveon is_stable_' x' in
                  [%debug_log "ss'=[%a]" nsps ss'];
                  match ss' with
                  | [] -> not (_is_simple_ins (*~exact *)~top_nodes x')
                  | [s'] -> begin
                      let s = nmap' s' in
                      let ca' = x'#initial_parent#initial_children in
                      [%debug_log "s=%a" nps s];
                      try
                        for i = x'#initial_pos-1 downto 0 do
                          let ci' = ca'.(i) in
                          [%debug_log "i=%d ci'=%a" i nps ci'];
                          if
                            is_stable' ci' &&
                            let ci = nmap' ci' in
                            [%debug_log "ci=%a" nps ci];
                            List.exists
                              (fun tn ->
                                is_ancestor tn ci && is_ancestor tn s &&
                                not (self#is_canceled_stable_node ci')
                                (*try
                                  let lmn = tree#initial_leftmost tn in
                                  for g = lmn#gindex to ci#gindex do
                                    if is_stable (tree#search_node_by_gindex g) then
                                      raise Exit
                                  done;
                                  false
                                with
                                  Exit -> true*)
                              ) top_nodes
                          then
                            raise Exit
                        done;
                        false
                      with
                        Exit -> true
                  end
                  | _ -> begin
                      let xpos = x'#initial_pos in
                      [%debug_log "x'=%a xpos=%d" nps x' xpos];
                      xpos > 0 &&
                      (*let ss = List.map nmap' ss' in*)
                      let _ = [%debug_log "ss=[%a]" nsps (List.map nmap' ss')] in
                      let xg = get_grp x' in
                      [%debug_log "xg=[%a]" nsps xg];

                      try
                        match xg with
                        | [g] -> begin
                            begin
                              let ca' = x'#initial_parent#initial_children in
                              let flag = ref false in
                              for i = xpos - 1 downto 0 do
                                if !flag && get_grp ca'.(i) = [g] then begin
                                  [%debug_log "%a belong to %a group" nps ca'.(i) nps g];
                                  raise Not_found
                                end;
                                if Xset.mem simple_ins_roots ca'.(i) then begin
                                  [%debug_log "%a is a simple ins root" nps ca'.(i)];
                                  flag := true
                                end
                              done
                            end;
                            let ks = Hashtbl.find rev_ancto_tbl (g#initial_parent, g#initial_pos) in
                            [%debug_log "g#initial_parent=%a pos=%d ks=[%s]"
                              nps g#initial_parent g#initial_pos (keys_to_string ks)];
                            match ks with
                            | [k] -> begin
                                let pk = self#find_key x'#initial_parent#uid in
                                [%debug_log "pk=%s" (key_to_string pk)];
                                if pk = k then
                                  false
                                else
                                  raise Not_found
                            end
                            | _ -> raise Not_found
                        end
                        | _ -> raise Not_found
                      with
                        Not_found ->

                      array_range_exists
                        (fun c' ->
                          let cg = get_grp c' in
                          [%debug_log "c'=%a cg=[%a]" nps c' nsps cg];
                          Xlist.intersectionq cg xg <> []
                        ) x'#initial_parent#initial_children 0 (xpos-1)
                  end)
                in
                [%debug_log "x'=%a b=%B" nps x' b];
                let b =
                  base_cond ||
                  not (is_stable' x') && b ||
                  (*b && ( (* NG????? *)
                  let xpos' = x'#initial_pos in
                  xpos' > 1 &&
                  try
                    let ca' = x'#initial_parent#initial_children in
                    try
                      for i = xpos' - 1 downto 0 do
                        let ci' = ca'.(i) in
                        [%debug_log "i=%d ci'=%a" i nps ci'];
                        if not (_is_excluded ci') && not (is_stable' ci') then
                          raise Exit;
                        if not (self#is_canceled_stable_node ci') then
                          raise Abort
                      done;
                      false
                    with
                    | Exit -> true
                    | Abort -> false
                  with _ -> false
                  ) ||*)
                  b &&
                  let check_prev tn =
                    try
                      for i = x'#initial_pos-1 downto 0 do
                        let prev' = x'#initial_parent#initial_children.(i) in
                        let b =
                          if is_stable' prev' then
                            is_ancestor tn (nmap' prev')
                          else
                            List.exists
                              (fun s' ->
                                is_ancestor tn (nmap' s')
                              ) (get_p_descendants is_stable' prev')
                        in
                        if b then
                          raise Exit
                      done;
                      false
                    with
                      Exit -> true
                  in
                  (*let check_prev =
                    try
                      let prev' = x'#initial_parent#initial_children.(x'#initial_pos-1) in
                      if is_stable' prev' then
                        fun tn -> is_ancestor tn (nmap' prev')
                      else
                        fun tn ->
                          List.exists
                            (fun s' ->
                              is_ancestor tn (nmap' s')
                            ) (get_p_descendants is_stable' prev')
                    with
                      _ -> fun _ -> false
                  in*)
                  self#is_canceled_stable_node x' ||
                  (*(try (* NG????? *)
                    let ca' = x'#initial_parent#initial_children in
                    array_range_forall self#is_canceled_stable_node ca' 0 (x'#initial_pos-1)
                  with
                    _ -> false)
                  ||*)
                  List.exists
                    (fun x ->
                      [%debug_log "x=%a" nps x];
                      List.for_all
                        (fun tn ->
                          [%debug_log "tn=%a" nps tn];
                          if tn == x || is_ancestor tn x then begin
                            [%debug_log "tn=%a is (an ancestor of) x=%a" nps tn nps x];
                            check_prev tn
                          end
                          else
                            true
                        ) top_nodes
                    )
                    (if is_stable' x' then
                      [nmap' x']
                    else
                      let moveon x' = not (is_stable' x') in
                      List.map nmap' (get_p_descendants ~moveon is_stable_' x'))
                in
                [%debug_log "x'=%a b=%B" nps x' b];
                b
          end
          else
            fun _ x' ->
              [%debug_log "x'=%a" nps x'];
              let b = _is_excluded x' in
              [%debug_log "x'=%a b=%B" nps x' b];
              b
        in
        let ap =
          self#get_adjusted_path ~get_group
            ~is_simple_ins ~is_excluded
            get_ipos get_iofs is_stable' rt' rp
        in
        [%debug_log "ap=%s" (Path.to_string ap)];
        ap

      method get_adjusted_path
          ?(get_group=fun _ -> raise Not_found)
          ?(group_heads=[])
          ?(is_simple_ins=fun _ -> None)
          ?(get_iparent_opt=None)
          ?(is_excluded=fun _ x -> self#is_excluded x)
          find_ipos
          find_iofs
          is_stable
          root
          rel_path
          =
        get_adjusted_path ~get_group ~group_heads ~get_iparent_opt
          find_ipos find_iofs self#get_mem_pos pos_cache
          is_simple_ins self#is_excluded is_excluded is_stable root rel_path

      method private get_uid_key nds =
        List.fast_sort UID.compare (List.map (fun n -> n#uid) nds)

      method private get_latest_common_ancestor tree nds =
        let ukey = self#get_uid_key nds in
        try
          let anc, top_nd_tbl = Hashtbl.find common_ancestor_tbl ukey in
          [%debug_log "ancestor (cached): %a" nps anc];
          [%debug_log "top_nd_tbl (cached): top_nd -> mems\n%s"
            (String.concat "\n"
               (List.map
                  (fun (n, ns) ->
                    sprintf "%a -> [%a]" nps n nsps ns
                  ) top_nd_tbl))];
          anc, top_nd_tbl
        with
          Not_found ->

        [%debug_log "nds=[\n%s]" (nodes_to_string nds)];
        let anc, top_nd_tbl =
          match nds with
          | [] -> invalid_arg "Delta.Edit.seq#get_latest_common_ancestor"
          | [nd] -> nd#initial_parent, [nd, [nd]]
          | _ -> begin
              let sorted = sort_nodes_by_gindex nds in
              let nd0, ndx = List.hd sorted, Xlist.last sorted in
              [%debug_log "nd0=%a ndx=%a" nps nd0 nps ndx];
              let last_gi = ndx#gindex in
              let cur = ref nd0#initial_parent in
              begin
                try
                  while (!cur)#gindex <= last_gi do
                    cur := (!cur)#initial_parent
                  done
                with
                  _ -> ()
              end;
              let anc = !cur in
              [%debug_log "anc=%a" nps anc];
              (*let st = ref (-1) in
              let ed = ref (-1) in*)
              let topa =
                Array.mapi
                  (fun (*i*)_ c ->
                    let lgi = (tree#initial_leftmost c)#gindex in
                    let mems =
                      List.filter
                        (fun n -> lgi <= n#gindex && n#gindex <= c#gindex)
                        nds
                    in
                    (*if mems <> [] then begin
                      if !st < 0 then
                        st := i;
                      ed := i
                    end;*)
                    c, mems
                  ) anc#initial_children
              in
              let topl =
                (*Array.to_list (Array.sub topa !st (!ed - !st + 1))*)
                List.filter (fun (_, ms) -> ms <> []) (Array.to_list topa)
              in
              anc, topl
          end
        in
        Hashtbl.add common_ancestor_tbl ukey (anc, top_nd_tbl);

        [%debug_log "ancestor: %s" anc#initial_to_string];
        [%debug_log "top_nd_tbl: top_nd -> mems\n%s"
          (String.concat "\n"
             (List.map
                (fun (n, ns) ->
                  sprintf "%a -> [%a]" nps n nsps ns
                ) top_nd_tbl))];

        anc, top_nd_tbl


      method private get_opposite_path_and_excepted_paths lift_tbl lifted_nodes
          is_stable is_stable' get_path' nmap nmap' tree tree'
          nd excluded _excepted_nds
          =
        [%debug_log "nd=%a excluded=[%a] _excepted_nds=[%a]"
          nps nd nsps excluded nsps _excepted_nds];

        let is_stable_ x =
          is_stable x && not (self#is_canceled_stable_node x) &&
          not (Xset.mem lifted_nodes x)
        in

        let excepted_nds =
          List.filter
            (fun x ->
              if is_stable x then
                not (self#is_canceled_stable_node x)
              else
                List.filter
                  (fun x -> not (self#is_canceled_stable_node x))
                  (get_p_descendants is_stable x) <> []
            ) _excepted_nds
        in
        [%debug_log "excepted_nds(filtered)=[%a]" nsps excepted_nds];

        let reg_ipos, reg_iofs, find_ipos, find_iofs,
          get_subtree_root_by_key, reg_iparent, find_iparent,
          reg_parent_key, (*is_ancestor_key*)_, rev_ancto_tbl
            =
          if tree == tree2 then
            self#reg_intermediate_pos1, self#reg_intermediate_ofs1,
            self#find_intermediate_pos1, self#find_intermediate_ofs1,
            self#get_subtree_root_by_key2,
            self#reg_intermediate_parent1, self#find_intermediate_parent1,
            self#reg_parent_key1, self#is_ancestor_key1, rev_anc1to_tbl
          else
            self#reg_intermediate_pos2, self#reg_intermediate_ofs2,
            self#find_intermediate_pos2, self#find_intermediate_ofs2,
            self#get_subtree_root_by_key1,
            self#reg_intermediate_parent2, self#find_intermediate_parent1,
            self#reg_parent_key1, self#is_ancestor_key2, rev_anc2to_tbl
        in
        let nmap n =
          [%debug_log "n=%a" nps n];
          let n' = nmap n in
          [%debug_log " -> %a" nps n'];
          n'
        in
        let nmap' n' =
          [%debug_log "n'=%a" nps n'];
          let n = nmap' n' in
          [%debug_log " -> %a" nps n];
          n
        in
        let to_be_canceled = Xset.create 0 in
        let check_occupancy anc' tnt =
          let keys = ref [] in
          let occupied = ref [] in
          let extra_lift_flag = ref false in
          let count = ref 0 in
          let shift = ref 0 in
          (*let flag = ref false in*)
          try
            List.iteri
              (fun i (tn', ss') ->
                let _ = i in
                [%debug_log "i=%d tn'=%a ss'=[%a]" i nps tn' nsps ss'];
                let b =
                  (*!flag ||*)
                  try
                    let ks = Hashtbl.find rev_ancto_tbl (anc', tn'#initial_pos) in
                    [%debug_log "anc'=%a pos=%d ks=[%s]"
                      nps anc' tn'#initial_pos (keys_to_string ks)];
                    if ks <> [] then begin
                      (*if
                        match self#find_key_opt nd#uid with
                        | Some k0 -> List.for_all (fun k -> not (is_ancestor_key k k0)) ks
                        | None -> true
                      then *)begin
                        [%debug_log "%a.(%d)=%a is occupied by [%s]"
                          nps anc' tn'#initial_pos nps tn' (keys_to_string ks)];
                        List.iter (fun k -> if not (List.mem k !keys) then keys := k :: !keys) ks;
                        occupied := tn' :: !occupied;
                        (*flag := true;*)
                        true
                      end
                      (*else
                        false*)
                    end
                    else
                      false
                  with
                    Not_found -> false
                in
                [%debug_log "b=%B count=%d" b !count];
                if b then begin
                  if !count = 0 then
                    incr shift;
                  (*if i = 0 then
                    raise Exit
                  else*)
                    List.iter
                      (fun s' ->
                        let s = nmap' s' in
                        [%debug_log "%a will be canceled" nps s];
                        Xset.add to_be_canceled s
                      ) ss'
                end
                else begin
                  begin
                    let ss'' =
                      match ss' with
                      | [] | [_] -> ss'
                      | s' :: rest' ->
                          let s = nmap' s' in
                          let rest = List.map nmap' rest' in
                          [%debug_log "s=%a rest=[%a]" nps s nsps rest];
                          let ca = s#initial_parent#initial_children in
                          let len = Array.length ca in
                          let not_to_be_reversed =
                            array_range_exists
                              (fun c ->
                                not (self#is_excluded c) &&
                                array_range_exists
                                  (fun c1 -> List.memq c1 rest) ca (c#initial_pos + 1) (len - 1)
                              ) ca (s#initial_pos + 1) (len - 1)
                          in
                          [%debug_log "not_to_be_reversed=%B" not_to_be_reversed];
                          if not_to_be_reversed then
                            ss'
                          else
                            List.rev ss'
                    in
                    match ss'' with
                    | [] | [_] -> ()
                    | s' :: rest ->
                        (*let a', _ = self#get_latest_common_ancestor tree' ss' in*)
                        let ps = (nmap' s')#initial_parent in
                        [%debug_log "ps=%a" nps ps];
                        List.iter
                          (fun s0' ->
                            [%debug_log "s0'=%a" nps s0'];
                            let ps0' = s0'#initial_parent in
                            if (*ps0' != a' && *)self#is_moved ps0' then begin
                              [%debug_log "ps0'=%a is moved" nps ps0'];
                              match self#find_key_opt (nmap' ps0')#uid with
                              | Some (K_mid m) when not (self#is_staying_move m) -> begin
                                  [%debug_log "%a is not a staying move" MID.ps m];
                                  let s0 = nmap' s0' in
                                  if not (is_ancestor ps s0) then begin
                                    [%debug_log "%a will be canceled" nps s0];
                                    extra_lift_flag := true;
                                    Xset.add to_be_canceled s0
                                  end
                                end
                              | _ -> ()
                            end
                          ) rest
                  end;
                  incr count
                end
              ) tnt;
            !shift, !count, !extra_lift_flag, !keys, !occupied
          with
            Exit -> !shift, !count, !extra_lift_flag, !keys, !occupied
        in
        let get_adjusted_path
            ?(get_group=fun _ -> raise Not_found)
            ?(group_heads=[])
            ?(is_simple_ins=fun _ -> None)
            ?(get_iparent_opt=None)
            ?(is_excluded=fun _ x -> self#is_excluded x) rp
            =
          self#get_adjusted_path
            ~get_group ~group_heads ~is_simple_ins ~get_iparent_opt ~is_excluded
            find_ipos find_iofs is_stable nd rp
        in
        let get_anc_in_excluded = get_anc_in excluded in
        let _get_anc_in_mem n =
          let x = get_anc_in_excluded n in
          x#initial_parent, x#initial_pos, n
        in
        let get_anc_in_mem n =
          (get_anc_in_excluded n)#initial_parent
        in

        let anc', path', paths, upstream, simple =
          match excepted_nds with
          | [] -> begin
              let anc', path', paths, upc, simple =
                let is_excluded _ = self#is_excluded in
                let get_group _ = raise Not_found in
                let group_heads = [] in
                let is_simple_ins = fun _ -> None in
                get_path'
                  (get_adjusted_path
                     ~get_group ~group_heads ~is_simple_ins ~get_iparent_opt:None ~is_excluded)
                  nd excluded
              in
              anc', path', paths, upc, simple
          end
          | [n] -> begin
              let n' = nmap n in
              [%debug_log "n'=%a" nps n'];
              let anc' = n'#initial_parent in
              let path' =
                Path.append anc'#apath (Elem.make n'#initial_pos)
              in
              [%debug_log "path'=%s" (Path.to_string path')];
              let nx = get_anc_in_excluded n in
              [%debug_log "nx=%a" nps nx];
              let rp = get_rel_path nd#apath nx#apath in
              let ca = nx#initial_parent#initial_children in
              let is_excluded lv x =
                let b =
                self#is_excluded x &&
                (lv > 0 ||
                x#initial_pos > 0 ||
                Array.exists (fun y -> not (self#is_excluded y)) ca ||
                is_stable x || has_p_descendant is_stable x ||
                Array.for_all (fun y -> not (is_stable y)) ca &&
                not (Hashtbl.mem walls x) && not (has_p_descendant is_stable x))
                in
                [%debug_log "x=%a b=%B" nps x b];
                b
              in
              let ap = get_adjusted_path ~is_excluded rp in
              let key_opt = self#find_key_opt nx#uid in
              anc', path', [new boundary_path ~key_opt ap], 0, false
          end
          | _ -> begin
              let added_walls = ref [] in
              let excepted_nds' = List.map nmap excepted_nds in
              [%debug_log "excepted_nds'=[%a]" nsps excepted_nds'];
              let anc', top_nd_tbl' =
                self#get_latest_common_ancestor tree' excepted_nds'
              in
              let top_nds' = List.map (fun (n', _) -> n') top_nd_tbl' in
              [%debug_log "anc'=%a top_nds'=[%a]" nps anc' nsps top_nds'];
              (*let pos_range =
                match top_nds' with
                | [] -> 0
                | [x] -> 1
                | hd :: tl -> (Xlist.last tl)#initial_pos - hd#initial_pos + 1
              in
              [%debug_log "pos_range=%d" pos_range];*)
              let pos_shift, paths_count, extra_lift_flag, keys, occupied =
                check_occupancy anc' top_nd_tbl'
              in
              let _ = occupied in
              [%debug_log "pos_shift=%d paths_count=%d" pos_shift paths_count];
              [%debug_log "extra_lift_flag=%B keys=[%s] occupied=[%a]"
                extra_lift_flag (keys_to_string keys) nsps occupied];
              let pos_shift, paths_count =
                if pos_shift > 0 then
                  match top_nds' with
                  | [tn0'; tn1'] when tn0'#initial_pos + 1 < tn1'#initial_pos ->
                      [%debug_log "pos0=%d pos1=%d" tn0'#initial_pos tn1'#initial_pos];
                      0, 2
                  | _ ->
                      let len' = List.length top_nds' in
                      if pos_shift >= len' then
                        0, 0
                      else
                        pos_shift, paths_count
                else
                  match top_nd_tbl' with
                  | [tn0', ss0'; tn1', ss1'] when tn0'#initial_pos + 1 < tn1'#initial_pos -> begin
                      let ss0 = List.map nmap' ss0' in
                      let ss1 = List.map nmap' ss1' in
                      let _, top_nd_tbl =
                        self#get_latest_common_ancestor tree excepted_nds
                      in
                      let grp_tbl = Hashtbl.create 0 in
                      List.iter
                        (fun (tn, ss) ->
                          List.iter (fun s -> Hashtbl.add grp_tbl s tn) ss
                        ) top_nd_tbl;
                      if
                        List.for_all
                          (function
                            | [] -> false
                            | h::tl -> begin
                                try
                                  let g = Hashtbl.find grp_tbl h in
                                  List.for_all (fun s -> Hashtbl.find grp_tbl s == g) tl
                                with _ -> false
                            end
                          ) [ss0; ss1]
                      then begin
                        [%debug_log "pos0=%d pos1=%d" tn0'#initial_pos tn1'#initial_pos];
                        List.iter
                          (fun k ->
                            let r = get_subtree_root_by_key k in
                            [%debug_log "r=%a is forced to be upstream" nps r];
                            Xset.add forced_upstream_nodes r
                          ) keys;
                        0, 2
                      end
                      else
                        pos_shift, paths_count
                  end
                  | _ -> pos_shift, paths_count
              in
              [%debug_log "pos_shift=%d paths_count=%d" pos_shift paths_count];

              let len' = List.length top_nd_tbl' in
              [%debug_log "len'=%d" len'];

              let group_tbl = Hashtbl.create 0 in
              let stable_node_group_tbl = Hashtbl.create 0 in

              let groups_ref = ref [] in

              let sole_stable_mem_list' =
                List.fold_left
                  (fun l (tn', ns') ->
                    match ns' with
                    | [x'] -> x' :: l
                    | _::_ -> begin
                        let sg_g =
                          List.filter_map
                            (fun n' ->
                              if n' != tn' then
                                let n = nmap' n' in
                                let x =
                                  try
                                    get_anc_in_excluded n
                                  with
                                    Not_found -> n
                                in
                                Some (n, x)
                              else
                                None
                            ) ns'
                        in
                        let sg, g = List.split sg_g in
                        List.iter
                          (fun x ->
                            let b =
                              try Hashtbl.find group_tbl x != tn' with _ -> true
                            in
                            if b then
                              Hashtbl.replace(*add*) group_tbl x tn'
                          ) g;
                        groups_ref := g :: !groups_ref;
                        List.iter
                          (fun x ->
                            [%debug_log "%a -> %a" nps x nps tn'];
                            Hashtbl.add stable_node_group_tbl x tn'
                          ) sg;
                        l
                    end
                    | [] -> l
                  ) [] top_nd_tbl'
              in
              [%debug_log "sole_stable_mem_list'=[%a]" nsps sole_stable_mem_list'];

              let get_group = Hashtbl.find group_tbl in

              let mem_group_tbl = Hashtbl.create 0 in
              (*Printf.printf "nd=%s excluded=[%s] _excepted_nds=[%s]\n"
                (UID.to_string nd#uid) (nodes_to_uids_string excluded)
                (nodes_to_uids_string _excepted_nds);*)
              Hashtbl.iter
                (fun sn g ->
                  [%debug_log "sn=%a" nps sn];
                  (*Printf.printf "sn=%s\n" sn#to_string;
                  scan_ancestors sn (fun a -> Printf.printf " %s\n" a#to_string);*)
                  try
                    let m = (get_anc_in_mem sn) in
                    if
                      try
                        (Hashtbl.find mem_group_tbl m) <> g
                      with _ -> true
                    then
                      Hashtbl.add mem_group_tbl m g
                  with
                    Not_found -> assert false
                ) stable_node_group_tbl;

              let allsameq = function
                | [] | [_] -> true
                | h::t -> List.for_all (fun x -> x == h) t
              in

              let same_stable_node_group ?(weak=false) ss =
                [%debug_log "weak=%B ss=[%a]" weak nsps ss];
                let b =
                  if weak then
                    allsameq
                      (List.map
                         (fun x ->
                           try
                             let g = Hashtbl.find stable_node_group_tbl x in
                             [%debug_log "%a -> %a" nps x nps g];
                             g
                           with
                             Not_found -> List.hd ss
                         ) ss)(*REGRESSION:thinkaurelius/titan 223 vs excilys/androidannotations 57*)
                  else
                    try
                      allsameq
                        (List.map
                           (fun s ->
                             [%debug_log "s=%a" nps s];
                             let g = Hashtbl.find stable_node_group_tbl s in
                             [%debug_log "g=%a" nps g];
                             g
                           ) ss)
                    with
                      Not_found -> false
                in
                [%debug_log "%B" b];
                b
              in

              begin %debug_block
                [%debug_log "group_tbl:"];
                Hashtbl.iter
                  (fun n tn ->
                    [%debug_log " %a -> %a" nps n nps tn]
                  ) group_tbl;
                [%debug_log "groups:"];
                List.iter
                  (fun g ->
                    [%debug_log " [%a]" nsps g]
                  ) !groups_ref;
                [%debug_log "stable_node_group_tbl:"];
                Hashtbl.iter
                  (fun n tn ->
                    [%debug_log " %a -> %a" nps n nps tn]
                  ) stable_node_group_tbl;
                [%debug_log "mem_group_tbl:"];
                Hashtbl.iter
                  (fun n tn ->
                    [%debug_log " %a -> %a" nps n nps tn]
                  ) mem_group_tbl;
              end;

              let gmap n = List.filter (fun x -> x != n) in
              let update_groups ?(f=fun () -> ()) n ax =
                let an =
                  try
                    get_anc_in_mem n
                  with
                    Not_found -> ax
                in
                if an != ax then begin
                  [%debug_log "removing %a..." nps n];
                  groups_ref := List.map (gmap n) !groups_ref;
                  f()
                end
              in

              let distinct_mems = ref [] in

              let mems =
                List.map
                  (fun x ->
                    let m = get_anc_in_mem x in
                    if not (List.memq m !distinct_mems) then
                      distinct_mems := m :: !distinct_mems;
                    m
                  ) excepted_nds
              in
              [%debug_log "mems=[%a]" nsps mems];

              let ngroups = List.length !distinct_mems in
              [%debug_log "ngroups=%d" ngroups];

              let find_mem_group m =
                try
                  Hashtbl.find mem_group_tbl m
                with
                  Not_found -> m
              in
              let grp_sep_opt = ref None in
              let no_grp_sep =
                List.length (Xlist.uniq mems) = ngroups &&
                match mems with
                | [] | [_] -> true
                | h::_ -> begin
                    try
                      let _ =
                        List.fold_left
                          (fun pv m ->
                            [%debug_log "m=%a" nps m];
                            let nx =
                              if pv == m then
                                pv
                              else begin
                                let gp = find_mem_group pv in
                                let gm = find_mem_group m in
                                [%debug_log "gp=%a, gm=%a" nps gp nps gm];
                                if gp == gm then begin
                                  grp_sep_opt := Some m;
                                  raise Exit
                                end;
                                m
                              end
                            in
                            [%debug_log "nx=%a" nps nx];
                            nx
                          ) h mems
                      in
                      true
                    with
                      Exit -> false
                end
              in
              [%debug_log "no_grp_sep=%B" no_grp_sep];
              [%debug_log "grp_sep=%s" (node_opt_to_string !grp_sep_opt)];

              [%debug_log "len'=%d" len'];
              let pmap = Array.make len' 0 in
              let cur = ref 0 in
              List.iteri
                (fun i (tn', ns') ->
                  let _ = tn' in
                  [%debug_log "i=%d tn'=%a ns'=[%a]" i nps tn' nsps ns'];
                  let nns' = List.length ns' in
                  cur := nns' + !cur;
                  pmap.(i) <- !cur - 1
                ) top_nd_tbl';

              [%debug_log "pmap=[%s]"
                (String.concat ";" (List.map string_of_int (Array.to_list pmap)))];

              let m_p_n_list = List.map _get_anc_in_mem excepted_nds in

              let fmap =
                match m_p_n_list with
                | [] -> assert false
                | (m0, _, _)::_ ->
                    let _, monotonic, _ =
                      List.fold_left
                        (fun (prev, b, seen) mem ->
                          if prev == mem then
                            (mem, b, seen)
                          else if List.memq mem seen then
                            (mem, false, seen)
                          else
                            (mem, b, mem::seen)
                        ) (m0, true, [m0]) mems
                    in
                    [%debug_log "monotonic=%B" monotonic];

                    let count, _, _, il =
                      List.fold_left
                        (fun (c, m0, p0, l) (m, p, n) ->
                          let _ = n in
                          [%debug_log "c=%d m0=%a p0=%d l=[%s] m=%a p=%d n=%a"
                            c nps m0 p0 (String.concat "," (List.map string_of_int l)) nps m p nps n];

                          let c' = c + 1 in
                          if m == m0 then begin
                            let key_cond =
                              try
                                let mk = self#find_key m#uid in
                                [%debug_log "mk=%s" (key_to_string mk)];
                                [%debug_log "for i = %d to %d" (p0+1) (p-1)];
                                for i = p0 + 1 to p - 1 do
                                  let ci = m#initial_children.(i) in
                                  [%debug_log "i=%d ci=%a" i nps ci];
                                  let k = self#find_key ci#uid in
                                  [%debug_log "i=%d k=%s" i (key_to_string k)];
                                  if k = mk then
                                    raise Exit
                                done;
                                false
                              with
                              | Not_found -> false
                              | Exit -> true
                            in
                            [%debug_log "key_cond=%B" key_cond];

                            if (ngroups = 1 || key_cond) && p0 >= 0 && p > p0 + 1 then begin
                              [%debug_log "p0=%d c=%d" p0 c];
                              c', m0, p, c::l
                            end
                            else
                              c', m0, p, l
                          end
                          else begin
                            let l' = try List.tl l with _ -> l in
                            if monotonic && is_ancestor m m0 &&
                              try pmap.(List.length l') = c with _ -> false
                            then begin
                              [%debug_log "%a is an ancestor of %a" nps m nps m0];
                              c', m, p, c::l'
                            end
                            else
                              c', m, p, c::l
                          end
                        ) (-1, m0, -1, []) m_p_n_list
                    in
                    Array.of_list (List.rev (count::il))
              in
              [%debug_log "fmap: [%s]"
                (String.concat ";" (List.map string_of_int (Array.to_list fmap)))];

              let lift_cands = ref [] in
              let _lift_cands = Xset.create 0 in

              let pmap' = Array.make len' 0 in
              let pmap'' = Array.make len' 0 in

              begin
                let idx, ranges = align_maps pmap fmap in
                let _ = idx in
                [%debug_log "idx=%d, ranges=[%s]" idx
                  (String.concat ", "
                     (List.map (fun (a, b) -> sprintf "%d-%d" a b) ranges))];
                List.iteri
                  (fun i (a, b) ->
                    pmap'.(i) <- a;
                    pmap''.(i) <- b
                  ) ranges;

                let sub_ins_opt = ref None in
                let sub_ins_idx_opt =
                  let count = ref (-1) in
                  try
                    let _ =
                      List.fold_left
                        (fun b (m, _, x) ->
                          let mk = self#find_key m#uid in
                          [%debug_log "x=%a mk=%s" nps x (key_to_string mk)];
                          incr count;
                          let px = x#initial_parent in
                          let has_sub_ins =
                            try
                              let pxk = self#find_key px#uid in
                              [%debug_log "pxk=%s" (key_to_string pxk)];
                              if mk <> pxk then begin
                                let ins = get_subtree_root_by_key pxk in
                                [%debug_log "ins=%a" nps ins];
                                sub_ins_opt := Some ins;
                                true
                              end
                              else
                                false
                            with
                              Not_found -> false
                          in
                          [%debug_log "has_sub_ins=%B" has_sub_ins];
                          if
                            b &&
                            not has_sub_ins &&
                            try
                              let c0 = !count - 1 in
                              Array.iteri
                                (fun j st ->
                                  let ed = pmap''.(j) in
                                  [%debug_log "count=%d c0=%d st=%d ed=%d" !count c0 st ed];
                                  if
                                    st <= c0 &&(* st <= !count &&*)
                                    (*c0 <= ed && *)!count = ed &&
                                    fmap = [|ed|] &&
                                    match !sub_ins_opt with
                                    | Some ins -> begin
                                        let moveon x = not (is_stable x) in
                                        match get_p_descendants ~moveon is_stable_ ins with
                                        | [] | [_] -> false
                                        | _ -> true
                                    end
                                    | _ -> false
                                  then
                                    raise Exit
                                ) pmap';
                              false
                            with
                            | Exit -> true
                            | _ -> false
                          then
                            raise Exit
                          else
                            has_sub_ins
                        ) false m_p_n_list
                    in
                    None
                  with
                  | Not_found -> None
                  | Exit -> Some !count
                in
                [%debug_log "sub_ins_idx_opt=%s" (int_opt_to_string sub_ins_idx_opt)];
                [%debug_log "sub_ins_opt=%s" (node_opt_to_string !sub_ins_opt)];

                let key_opt = self#find_key_opt nd#uid in
                [%debug_log "nd=%a key_opt=%s" nps nd (key_opt_to_string key_opt)];
                List.iteri
                  (fun i sn ->
                    [%debug_log "i=%d sn=%a" i nps sn];
                    let canceled = self#is_pre_canceled_stable_node sn in
                    [%debug_log "canceled: %a -> %B" nps sn canceled];
                    let pk_opt = self#find_key_opt sn#initial_parent#uid in
                    [%debug_log "pk_opt=%s" (key_opt_to_string pk_opt)];
                    let cond0 () =
                      let b = canceled && key_opt = pk_opt in
                      [%debug_log "%B" b];
                      b
                    in
                    let cond1 () =
                      let b = List.for_all (fun (a, b) -> i < a || b < i) ranges in
                      [%debug_log "%B" b];
                      b
                    in
                    let cond2 () =
                      let b = match sub_ins_idx_opt with Some j -> j = i | _ -> false in
                      [%debug_log "%B" b];
                      b
                    in
                    let cond3 () =
                      let b =
                        Xset.mem to_be_canceled sn && (not extra_lift_flag || !sub_ins_opt = None)
                      in
                      [%debug_log "%B" b];
                      b
                    in
                    if cond0() || cond1() || cond2() || cond3() then begin
                      let mem = get_anc_in_mem sn in
                      [%debug_log "lift cand: i=%d (%a) mem=%a" i nps sn nps mem];
                      lift_cands := (i, mem, true) :: !lift_cands;
                      Xset.add _lift_cands sn;
                      update_groups sn mem;
                      [%debug_log "stability of %a will be ignored" nps sn];
                      self#cancel_stable_node sn
                    end
                  ) excepted_nds
              end;

              let wtbl = Hashtbl.create 0 in
              let qwtbl = Hashtbl.create 0 in
              let is_stable__ x = is_stable_ x && not (Xset.mem _lift_cands x) in
              begin
                match m_p_n_list with
                | [] -> assert false
                | (m0, _, _)::_ -> begin
                    ignore (
                    List.fold_left
                      (fun (c, m0) (m, _, _) ->
                        [%debug_log "c=%d, m=%a" c nps m];
                        let c' = c + 1 in
                        if c = -1 || m0 != m then begin
                          let all_cond =
                            Array.for_all self#is_excluded m#initial_children
                          in
                          [%debug_log "all_cond=%B" all_cond];
                          if all_cond then begin
                            Array.iter
                              (fun w ->
                                [%debug_log "w=%a" nps w];
                                (*let moveon x = not (is_stable x) in*)
                                let moveon x =
                                  not (self#is_canceled_stable_node x && x#initial_pos = 0) &&
                                  not (Xset.mem _lift_cands x)
                                in
                                let context_cond =
                                  ((not (is_stable w) ||
                                  not (Xset.mem _lift_cands w) &&
                                  let w' = nmap w in
                                  List.exists (fun t' -> t' == w' || is_ancestor t' w') top_nds')) &&
                                  (is_stable w && List.memq (nmap w) top_nds' ||
                                  let lss = get_p_left_nodes ~moveon is_stable__ w nd in
                                  [%debug_log "lss=[%a]" nsps lss];
                                  if lss <> [] then begin
                                    let rss = get_p_right_nodes ~moveon is_stable__ w nd in
                                    [%debug_log "rss=[%a]" nsps rss];
                                    if rss <> [] then begin
                                      let get_grp sn =
                                        try
                                          Some (Hashtbl.find stable_node_group_tbl sn)
                                        with
                                          Not_found ->
                                            if try List.memq (nmap sn) top_nds' with _ -> false then
                                              Some (nmap sn)
                                            else
                                              List.fold_left
                                                (fun acc t' ->
                                                  if try is_ancestor t' (nmap sn) with _ -> false then
                                                    Some t'
                                                  else
                                                    acc
                                                ) None top_nds'
                                      in
                                      let map = List.filter_map get_grp in
                                      let lsg = Xlist.uniq (map lss) in
                                      [%debug_log "lsg=[%a]" nsps lsg];
                                      if lsg <> [] then begin
                                        let rsg = Xlist.uniq (map rss) in
                                        [%debug_log "rsg=[%a]" nsps rsg];
                                        match lsg, rsg with
                                        | [ln'], [rn'] when ln' == rn' -> begin
                                            let filt x =
                                              if Hashtbl.mem stable_node_group_tbl x then
                                                Some x#initial_parent
                                              else if is_stable x && List.memq (nmap x) top_nds' then
                                                Some x#initial_parent
                                              else if List.exists (fun t' -> is_ancestor t' (nmap x)) top_nds' then
                                                Some x#initial_parent
                                              else
                                                None
                                            in
                                            let lps = List.filter_map filt lss in
                                            [%debug_log "lps=[%a]" nsps lps];
                                            let rps = List.filter_map filt rss in
                                            [%debug_log "rps=[%a]" nsps rps];
                                            Xlist.intersectionq lps rps = []
                                        end
                                        | [ln'], rn'::_ when begin
                                            ln'#initial_parent == rn'#initial_parent &&
                                            ln'#initial_parent != anc' &&
                                            rn'#initial_pos - ln'#initial_pos = 1
                                        end -> false
                                        | [ln'], [] when List.memq ln' top_nds' -> false
                                        | _ -> begin
                                            match Xlist.intersectionq lsg rsg with
                                            | [] -> begin
                                                match get_grp w with
                                                | None -> true
                                                | Some g when w#initial_pos = 0 ->
                                                    not (List.memq g lsg) && not (List.memq g rsg)
                                                | _ -> true
                                            end
                                            | [n'] when w#initial_pos = 0 && List.memq n' top_nds' -> begin
                                                List.for_all
                                                  (fun s ->
                                                    match get_grp s with
                                                    | Some g -> g == n'
                                                    | None -> true
                                                  ) lss &&
                                                match get_grp w with
                                                | None -> false
                                                | Some g -> g == n'
                                            end
                                            | _ -> false
                                        end
                                      end
                                      else
                                        true
                                    end
                                    else
                                      true
                                  end
                                  else
                                    true)
                                in
                                [%debug_log "context_cond=%B" context_cond];
                                let b =
                                  context_cond &&
                                  (not (is_stable w) &&
                                   (match get_p_descendants is_stable w with
                                   | [] | [_] -> true
                                   | _ -> false) ||
                                  is_stable w &&
                                  (* && self#is_canceled_stable_node w*)
                                  (w#initial_pos > 0 || not (self#is_canceled_stable_node w))
                                  )
                                in
                                if b then begin
                                  if Hashtbl.mem wtbl m then begin
                                    [%debug_log "%a -> quasi-wall" nps w];
                                    tbl_add qwtbl m w;
                                    Hashtbl.add quasi_walls w (try Some (Hashtbl.find group_tbl w) with _ -> None);
                                    added_walls := w :: !added_walls
                                  end
                                  else begin
                                    [%debug_log "%a -> wall" nps w];
                                    Hashtbl.add wtbl m w;
                                    Hashtbl.add walls w (try Some (Hashtbl.find group_tbl w) with _ -> None);
                                    added_walls := w :: !added_walls
                                  end
                                end
                              ) m#initial_children
                          end
                        end;
                        c', m
                      ) (-1, m0) m_p_n_list
                   )
                end
              end;

              let sub_canceled_stable_node_tbl = Hashtbl.create 0 in
              let has_no_stable_desc x = get_p_descendants is_stable x = [] in
              List.iter
                (fun n ->
                  [%debug_log "n=%a" nps n];
                  if not (is_stable n) then begin
                    let ss = get_p_descendants is_stable n in
                    [%debug_log "stable descendants of %a: [%a]" nps n nsps ss];

                    let ss =
                      List.filter (fun x -> not (self#is_canceled_stable_node x)) ss
                    in
                    [%debug_log "ss(filtered)=[%a]" nsps ss];

                    match ss with
                    | [] | [_] -> ()
                    | _ -> begin
                      let ss' = List.map nmap ss in
                      let a', tns' = self#get_latest_common_ancestor tree' ss' in
                      [%debug_log "a'=%a" nps a'];

                      if a' == anc' then begin
                        if
                          no_grp_sep ||
                          (match !grp_sep_opt with
                          | Some sep -> sep#gindex > n#gindex
                          | None -> false) ||
                          same_stable_node_group ~weak:true ss
                        then begin
                          let range = List.map (fun (tn', _) -> tn') tns' in
                          [%debug_log "comp_cand: %a -> [%a]" nps n nsps range];
                          Hashtbl.add comp_cand_tbl n range
                        end
                        else begin
                          let lcond() =
                            let b =
                              match get_left_sibling_opt n with
                              | Some x -> begin
                                  [%debug_log "left sibling of %a: %a" nps n nps x];
                                  not (List.memq x excluded) || has_no_stable_desc x
                              end
                              | _ -> false
                            in
                            [%debug_log "b=%B" b];
                            b
                          in
                          let rcond() =
                            let b =
                              match get_right_sibling_opt n with
                              | Some x -> begin
                                  [%debug_log "right sibling of %a: %a" nps n nps x];
                                  not (List.memq x excluded) || has_no_stable_desc x
                              end
                              | _ -> false
                            in
                            [%debug_log "b=%B" b];
                            b
                          in
                          [%debug_log "n#initial_parent=%a nd=%a" nps n#initial_parent nps nd];
                          if n#initial_parent != nd || lcond() || rcond() then begin
                            let len = List.length ss in
                            let count = ref 0 in
                            let r = ref [] in
                            let c = ref [] in
                            List.iter
                              (fun (tn', ns') ->
                                count := !count + (List.length ns');
                                if !count <= len then
                                  r := !r @ [tn']
                                else
                                  c := !c @ ns'
                              ) tns';
                            [%debug_log "comp_cand: %a -> [%a]" nps n nsps !r];
                            Hashtbl.add comp_cand_tbl n !r;

                            [%debug_log "c=[%a]" nsps !c];
                            List.iter self#cancel_stable_node (List.map nmap' !c);
                          end
                          else begin
                            List.iter self#cancel_stable_node ss;
                            Hashtbl.add sub_canceled_stable_node_tbl n ss
                          end
                        end
                      end
                    end
                  end
                ) excluded;

              List.iter2
                (fun n n' ->
                  [%debug_log "n=%a n'=%a" nps n nps n'];
                  let p' = n'#initial_parent in
                  if p' == anc' then begin
                    [%debug_log "n=%a n'=%a p'=%a: p' == anc'" nps n nps n' nps p'];
                    let ax = get_anc_in_excluded n in
                    [%debug_log "ax=%a" nps ax];
                    if not (is_stable ax) && not (Hashtbl.mem comp_cand_tbl ax) then begin
                      [%debug_log "comp_cand: %a -> [%a]" nps ax nps n'];
                      Hashtbl.add comp_cand_tbl ax [n'];
                      self#restore_canceled_stable_node n
                    end
                  end
                  else if p'#initial_parent == anc' then begin
                    [%debug_log "n=%a n'=%a p'=%a: p'#initial_parent=%a == anc'"
                      nps n nps n' nps p' nps anc'];
                    reg_iparent n p'
                  end
                ) _excepted_nds (List.map nmap _excepted_nds);

              if not (is_stable' anc') then begin
                let sns' = get_p_descendants is_stable' anc' in
                [%debug_log "sns'=[%a]" nsps sns'];
                let sns0' = List.filter (fun x' -> not (List.memq x' excepted_nds')) sns' in
                [%debug_log "sns0'=[%a]" nsps sns0'];
                if sns0' <> [] then begin
                  let a0, _ = self#get_latest_common_ancestor tree (List.map nmap' sns0') in
                  let a, _ = self#get_latest_common_ancestor tree excepted_nds in
                  if not (is_ancestor a0 a) && not (is_ancestor a a0) then begin
                    List.iter
                      (fun (tn', ns') ->
                        List.iter
                          (fun sn0' ->
                            [%debug_log "tn'=%a sn0'=%a" nps tn' nps sn0'];
                            if is_ancestor tn' sn0' then begin
                              let sns_to_be_locked' =
                                List.filter
                                  (fun x' -> not (self#is_canceled_stable_node x'))
                                  ns'
                              in
                              [%debug_log "sns_to_be_locked'=[%a]" nsps sns_to_be_locked'];
                              if sns_to_be_locked' <> [] then begin
                                let sn0 = nmap' sn0' in
                                let cond =
                                  (List.length sns_to_be_locked') > 1 &&
                                  try
                                    let sr =
                                      get_subtree_root_by_key
                                        (self#find_key sn0#initial_parent#uid)
                                    in
                                    [%debug_log "sr=%a" nps sr];
                                    (get_p_descendants is_stable sr) <> [sn0]
                                  with
                                    _ -> true
                                in
                                [%debug_log "cond=%B" cond];
                                if cond then begin
                                  self#pre_cancel_stable_node sn0;
                                  let sns_to_be_locked = List.map nmap' sns_to_be_locked' in
                                  List.iter self#lock_stable_node sns_to_be_locked
                                end
                              end
                            end
                          ) sns0'
                  ) top_nd_tbl'
                  end
                end
              end;

              begin %debug_block
                [%debug_log "canceled_stable_nodes=[%a]"
                  nsps (self#canceled_stable_node_list tree)];
                [%debug_log "composition candidates:"];
                Hashtbl.iter
                  (fun n ns ->
                    [%debug_log "  %a -> [%a]" nps n nsps ns]
                  ) comp_cand_tbl;
              end;

              (*let top_nd_tbl' =
                List.fold_left
                  (fun l (tn', ns') ->
                    let ns0' =
                      List.filter (fun n' -> not (self#is_canceled_stable_node (nmap' n'))) ns'
                    in
                    if ns0' = [] then
                      l
                    else
                      l @ [(tn', ns0')]
                  ) [] top_nd_tbl'
              in
              [%debug_log "top_nd_tbl': top_nd' -> mems'\n%s"
                (String.concat "\n"
                   (List.map
                      (fun (n', ns') ->
                        sprintf "%a -> [%a]" nps n' nsps ns'
                      ) top_nd_tbl'))];*)

              let st_nd', _ = (*List.hd top_nd_tbl'*)List.nth top_nd_tbl' pos_shift in
              let st_pos' = st_nd'#initial_pos in

              [%debug_log "anc'=%a, st_nd'=%a, st_pos'=%d" nps anc' nps st_nd' st_pos'];

              let path' = Path.append anc'#apath (Elem.make st_pos') in
              [%debug_log "path'=%s" (Path.to_string path')];

              let a' = Array.of_list (fst (List.split top_nd_tbl')) in
              let children' = anc'#initial_children in

              let emap = Array.make (len' - 1) 0 in

              [%debug_log "len'=%d" len'];
              [%debug_log "a'=[%a]" nsps (Array.to_list a')];
              [%debug_log "children'=[%a]" nsps (Array.to_list children')];

              let npaths = ref len' in

              for i = 0 to len' - 2 do
                let count = ref 0 in
                let st = (a'.(i))#initial_pos + 1 in
                let ed = (a'.(i+1))#initial_pos - 1 in
                [%debug_log "[i=%d] st=%d ed=%d" i st ed];
                for j = st to ed do
                  let cj' = children'.(j) in
                  if
                    not (self#is_excluded cj') ||
                    (get_p_descendants is_stable' cj') = []
                  then begin
                    [%debug_log "%a is not excluded or does't have stable descendants"
                      nps children'.(j)];
                    incr count;
                    incr npaths
                  end
                done;
                emap.(i) <- !count
              done;

              [%debug_log "emap: [%s]"
                (String.concat ";" (List.map string_of_int (Array.to_list emap)))];

              [%debug_log "npaths=%d" !npaths];

              let group_heads =
                let rec f = function
                  | h0::h1::_ when h0#initial_parent == h1#initial_parent -> [h0]
                  | h0::(_::_ as t) -> h0 :: (f t)
                  | [h] -> [h]
                  | [] -> []
                in
                List.concat_map f !groups_ref
              in
              [%debug_log "group_heads: [%a]" nsps group_heads];

              (* adjusting group_tbl *)
              if Hashtbl.length group_tbl > 0 then begin
                [%debug_log "adjusting group_tbl..."];
                let l = ref [] in
                Hashtbl.iter
                  (fun n gn ->
                    let _ = gn in
                    try
                      Xset.iter
                        (fun x ->
                          if n == x || is_ancestor n x then begin
                            [%debug_log "to be removed: %a -> %a" nps n nps gn];
                            l := n :: !l;
                            raise Exit
                          end
                        ) _lift_cands
                    with
                      Exit -> ()
                  ) group_tbl;
                List.iter (Hashtbl.remove group_tbl) !l;
                [%debug_log "done."];
                begin %debug_block
                  if !l <> [] then begin
                    [%debug_log "group_tbl:"];
                    Hashtbl.iter
                      (fun n tn ->
                        [%debug_log " %a -> %a" nps n nps tn]
                      ) group_tbl
                  end;
                end
              end;

              let node_tbl = Hashtbl.create 0 in (* path -> node * pos * range * node *)

              let orig_path_tbl = Hashtbl.create 0 in (* boundary_path -> boundary_path *)

              let mkpath_cache = Hashtbl.create 0 in

              let mkpath ?(skip_parent_key_check=true) n sn =
                [%debug_log "n=%a, sn=%a" nps n nps sn];
                try
                  Hashtbl.find mkpath_cache (n, sn)
                with
                  Not_found ->

                let path, pos, range =
                  let key_opt, range =
                    try
                      let range = Hashtbl.find comp_cand_tbl n in
                      (self#find_key_opt n#uid), range
                    with
                      Not_found -> None, []
                  in
                  let rp = get_rel_path nd#apath n#apath in
                  [%debug_log "rp=%s" (Path.to_string rp)];
                  let pos = (Path.tail rp).Elem.pos in
                  let path =
                    let _is_simple_ins x =
                      let b =
                        not (is_stable x) &&
                        Hashtbl.mem quasi_walls x &&
                        not (has_p_descendant is_stable__ x)
                      in
                      [%debug_log "%a -> %B" nps x b];
                      b
                    in
                    let is_excluded lv x =
                      let b =
                        self#is_excluded x &&
                        (lv > 0 || not (Hashtbl.mem walls x) || _is_simple_ins x)
                      in
                      [%debug_log "x=%a b=%B" nps x b];
                      b
                    in
                    let ap = get_adjusted_path ~get_group ~group_heads ~is_excluded rp in
                    let e = Path.tail ap in
                    let p = e.Elem.pos in
                    let o = e.Elem.ofs in
                    let cs = n#initial_parent#initial_children in
                    if pos > 0 && p = 0 && Hashtbl.mem walls cs.(0) && o = float pos then begin
                      let c = ref 0 in
                      let right_added = ref false in
                      Array.iteri
                        (fun i x ->
                          [%debug_log "i=%d x=%a" i nps x];
                          if
                            i < pos &&
                            (Hashtbl.mem walls x || Hashtbl.mem quasi_walls x ||
                            not skip_parent_key_check && self#find_key_opt x#uid != None)
                          then begin
                            [%debug_log "wall or quasi_wall or has key"];
                            incr c
                          end
                          else if i >= pos && not !right_added then begin
                            right_added := true;
                            [%debug_log "right added"];
                            incr c
                          end
                        ) cs;
                      if !c > 1 then
                        let c_ = float !c in
                        if c_ < o then begin
                          [%debug_log "%f -> %f" o c_];
                          Path.set_ofs ap c_
                        end
                    end;
                    new boundary_path ~key_opt ap
                  in
                  path, pos, range
                in
                Hashtbl.add node_tbl path (n, pos, range, sn);

                [%debug_log "%s -> (%a, %d, [%s])" path#to_string nps n pos
                  (String.concat ";" (List.map node_to_uid_string range))];

                Hashtbl.add mkpath_cache (n, sn) path;
                path
              in (* mkpath *)

              let a = Array.of_list excepted_nds in

              [%debug_log "a=[%a]" nsps excepted_nds];

              let lifted_nds = Xset.create 0  in
              (*let lift_targets = Xset.create 0 in*)

              let lift n =
                [%debug_log "n=%a" nps n];
                if (Xset.mem lifted_nds n) || (Xset.mem lifted_nodes n) then begin
                  [%debug_log "already lifted"]
                end
                else begin
                Xset.add lifted_nds n;
                Xset.add lifted_nodes n;
                [%debug_log "lifting %a" nps n];
                let x =
                  if self#is_canceled_stable_node n then begin
                    [%debug_log "%a is a canceled node" nps n];
                    let rec find_parent n0 =
                      let p = n0#initial_parent in
                      let pk = self#find_key p#uid in
                      let sr = get_subtree_root_by_key pk in
                      let ss = get_p_descendants is_stable sr in
                      [%debug_log "n0=%a ss=[%a]" nps n0 nsps ss];
                      if ss = [n0] then
                        if try self#find_key nd#uid <> pk with _ -> false then begin
                          if n0 == n then begin
                            [%debug_log "different parent key found: %s (n0=%a)"
                              (key_to_string pk) nps n0];
                            n0
                          end
                          else
                            raise Exit
                        end
                        else
                          find_parent sr
                      else
                        n0
                    in
                    try
                      find_parent n
                    with
                      Not_found -> get_anc_in_excluded n
                  end
                  else
                    get_anc_in_excluded n
                in
                [%debug_log "x=%a" nps x];
                let _an = x#initial_parent in
                [%debug_log "_an=%a" nps _an];
                let key = self#find_key _an#uid in
                [%debug_log "key=%s" (key_to_string key)];

                let an =
                  if try self#find_key nd#uid <> key with _ -> false then
                    get_subtree_root_by_key key
                  else
                    _an
                in
                [%debug_log "an=%a" nps an];

                let rp = get_rel_path nd#apath x#apath in

                (*let has_lifted_descendant x =
                  try
                    preorder_scan_whole_initial_subtree x
                      (fun y ->
                        if Xset.mem lifted_nds y || Xset.mem lifted_nodes y then
                          raise Exit
                      );
                    false
                  with
                    Exit -> true
                in*)

                let is_excluded lv n0 =
                  [%debug_log "lv=%d n0=%a x=%a" lv nps n0 nps x];
                  let b =
                  if lv = 0 then
                    if self#is_excluded n0 then
                      if n0 == x || self#is_canceled_stable_node n0 then
                        true
                      else
                        let b0 =
                          if is_stable n0 then
                            not (List.memq n0 group_heads) &&
                            let b =
                              try
                                let prev = n0#initial_parent#initial_children.(n0#initial_pos-1) in
                                is_stable prev && same_stable_node_group [prev; n0]
                              with _ -> false
                            in
                            b ||
                            let b00 = not (List.memq (nmap n0) sole_stable_mem_list') in
                            [%debug_log "b00=%B" b00];
                            let b00_and_b01 =
                              if b00 then
                                let b01 =
                                  let p0 = n0#initial_parent in
                                  if p0 == nd then
                                    true
                                  else
                                    let ss' = List.map nmap (get_p_descendants is_stable p0) in
                                    let a', _ = self#get_latest_common_ancestor tree' ss' in
                                    not
                                      (List.exists
                                         (fun (t', ms') ->
                                           let len_ms' = List.length ms' in
                                           t' == a' &&
                                           List.length (Xlist.intersectionq ms' ss')
                                             = len_ms' &&
                                           List.length ss' = len_ms'
                                         ) top_nd_tbl')
                                in
                                [%debug_log "b01=%B" b01];
                                b01
                              else
                                false
                            in
                            b00_and_b01
                          else
                            false
                        in (* b0 *)
                        [%debug_log "%a: b0=%B" nps n0 b0];
                        let ss0 =
                          if b0 then
                            []
                          else
                            let moveon x =
                              not (is_stable x)(* || not (self#is_canceled_stable_node x) ||
                              not (Xset.mem lifted_nodes x)*)
                            in
                            let ss0 = get_p_descendants ~moveon is_stable_ n0 in
                            [%debug_log "n0=%a ss0=[%a]" nps n0 nsps ss0];
                            ss0
                        in
                        let b1 () =
                          let b1 =
                            List.exists
                              (fun x -> not (is_stable' (nmap x)#initial_parent))
                              ss0
                          in
                          let b1 =
                            if b1 then begin
                              [%debug_log "n0=%a" nps n0];
                              let ss1 = get_p_descendants is_stable n0 in
                              [%debug_log "ss1=[%a]" nsps ss1];
                              let ss1 =
                                List.filter (fun x -> not (self#is_canceled_stable_node x)) ss1
                              in
                              [%debug_log "ss1=[%a] (filtered)" nsps ss1];
                              match ss1 with
                              | [] | [_] -> false(*b1*)
                              | _ ->
                                  let ss1' = List.map nmap ss1 in
                                  let a1', _ = self#get_latest_common_ancestor tree' ss1' in
                                  [%debug_log "a1'=%a" nps a1'];

                                  let pk = self#find_key n0#initial_parent#uid in
                                  [%debug_log "pk=%s" (key_to_string pk)];
                                  let sr0 = get_subtree_root_by_key pk in
                                  [%debug_log "sr0=%a" nps sr0];
                                  let xnds =
                                    List.filter (fun x -> not (self#is_canceled_stable_node x))
                                      (get_p_descendants is_stable sr0)
                                  in
                                  [%debug_log "xnds=[%a]" nsps xnds];
                                  let anc1', _ =
                                    self#get_latest_common_ancestor tree' (List.map nmap xnds)
                                  in
                                  [%debug_log "anc1'=%a" nps anc1'];
                                  if a1' == anc1' then begin
                                    if
                                      same_stable_node_group ss1 ||
                                      let distinct_mems = ref [] in
                                      let mems =
                                        List.map
                                          (fun x ->
                                            let m = get_anc_in_mem x in
                                            if not (List.memq m !distinct_mems) then
                                              distinct_mems := m :: !distinct_mems;
                                            m
                                          ) xnds
                                      in
                                      [%debug_log "mems=[%a]" nsps mems];
                                      let ngroups = List.length !distinct_mems in
                                      [%debug_log "ngroups=%d" ngroups];
                                      let find_mem_group m =
                                        try
                                          Hashtbl.find mem_group_tbl m
                                        with
                                          Not_found -> m
                                      in
                                      let no_grp_sep =
                                        List.length (Xlist.uniq mems) = ngroups &&
                                        match mems with
                                        | [] | [_] -> true
                                        | h::_ -> begin
                                            try
                                              let _ =
                                                List.fold_left
                                                  (fun pv m ->
                                                    [%debug_log "m=%a" nps m];
                                                    let nx =
                                                      if pv == m then
                                                        pv
                                                      else begin
                                                        let gp = find_mem_group pv in
                                                        let gm = find_mem_group m in
                                                        [%debug_log "gp=%a, gm=%a" nps gp nps gm];
                                                        if gp == gm then
                                                          raise Exit;
                                                        m
                                                      end
                                                    in
                                                    [%debug_log "nx=%a" nps nx];
                                                    nx
                                                  ) h mems
                                              in
                                              true
                                            with
                                              Exit -> false
                                        end
                                      in
                                      [%debug_log "no_grp_sep=%B" no_grp_sep];
                                      no_grp_sep
                                    then
                                      false
                                    else
                                      b1
                                  end
                                  else
                                    b1
                            end
                            else
                              b1
                          in
                          [%debug_log "%a: b1=%B" nps n0 b1];
                          b1
                        in
                        (*let b2 () =
                          let b2 =
                            has_lifted_descendant n0
                          in
                          let b2 = not b2 in
                          [%debug_log "%a: b2=%B" nps n0 b2];
                          b2
                        in
                        let b3 () =
                          let b3 =
                            ss0 = [] &&
                            not (is_stable n0) &&
                            not (Array.for_all
                                   self#is_excluded n0#initial_parent#initial_children)
                          in
                          let b3 = not b3 in
                          [%debug_log "%a: b3=%B" nps n0 b3];
                          b3
                        in*)
                        let b3 () =
                          let b3 =
                            not (is_stable n0) &&
                            match ss0 with
                            | [] | [_] -> begin
                                let pred y =
                                  y != x &&
                                  (is_stable y || has_p_descendant is_stable_ y) &&
                                  (not (is_stable y) || is_stable_ y)
                                in
                                match get_p_siblings pred n0 with
                                | Some l, Some r -> begin
                                    try
                                      (Hashtbl.find group_tbl l) = (Hashtbl.find group_tbl r)
                                    with
                                      Not_found -> false
                                end
                                | _ -> false
                            end
                            | _ -> false
                          in
                          [%debug_log "%a: b3=%B" nps n0 b3];
                          b3
                        in
                        (*[%debug_log "%a: b0=%B, b1=%B, b2=%B, b3=%B" nps n0 b0 b1 b2 b3];*)
                        b0 || b1()(* || b2()*) || b3()
                    else
                      false
                  else
                    self#is_excluded n0
                  in
                  (*[%debug_log "lv=%d %a -> %B" lv nps n0 b];*)
                  b
                in (* is_excluded *)

                let ap =
                  let find_iparent x =
                    let p = find_iparent x in
                    if p == anc' && x#initial_pos <= st_pos' then
                      raise Not_found
                    else
                      p
                  in
                  let get_iparent_opt = Some find_iparent in
                  let ap0 = get_adjusted_path ~get_iparent_opt ~is_excluded rp in
                  [%debug_log "rp=%s" (Path.to_string rp)];
                  [%debug_log "ap0=%s" (Path.to_string ap0)];
                  let k = self#find_key nd#uid in
                  [%debug_log "nd=%a k=%s (key=%s)" nps nd (key_to_string k) (key_to_string key)];
                  if k <> key then
                    self#get_adjusted_path ~is_excluded
                      find_ipos find_iofs is_stable an (get_rel_path an#apath x#apath)
                    (*let h =
                      get_adjusted_path ~is_excluded (get_rel_path nd#apath an#apath)
                    in
                    [%debug_log "h=%s" (Path.to_string h)];
                    Path.remove_head h ap0*)
                  else
                    ap0
                in
                [%debug_log "n=%a ap=%s" nps n (Path.to_string ap)];
                let x' = self#get_anc_in_excluded (nmap n) in
                [%debug_log "x'=%a" nps x'];
                let r' =
                  self#get_subtree_root
                    (self#find_stid x'#initial_parent#uid)
                in
                [%debug_log "r'=%a" nps r'];
                let rp' = get_rel_path r'#apath x'#apath in

                let upc =
                  let x = get_anc_in_excluded n in
                  [%debug_log "x=%a" nps x];
                  match self#find_key_opt x#uid with
                  | Some k when x != n -> begin
                      [%debug_log "k=%s" (key_to_string k)];
                      let is_ancestor_key =
                        if tree == tree2 then
                          self#is_ancestor_key1
                        else
                          self#is_ancestor_key2
                      in
                      if
                        k <> key && not (is_ancestor_key key k) &&
                        try self#find_key n#initial_parent#uid <> key with _ -> false
                      then
                        1
                      else
                        0
                  end
                  | _ -> 0
                in
                [%debug_log "%a: (%s,%s) -> (%s,%s,%d)" nps n
                  (Path.to_string r'#apath) (Path.to_string rp')
                  (Path.to_string ap) (key_to_string key) upc];

                (*let ap_key = ap, key in
                if Xset.mem lift_targets ap_key then begin
                  [%debug_log "already targeted: (%s,%s)"
                    (Path.to_string ap) (key_to_string key)];
                end
                else *)begin
                  Hashtbl.add lift_tbl (r'#apath, rp') (ap, key, upc);
                  (*Xset.add lift_targets ap_key*)
                end
                end
              in (* lift *)

              let lift_list = ref [] in

              let sub_path_map = Array.make (len'-1) None in

              begin
                try
                  let lifti ?(force=false) i ax =
                    let n = a.(i) in
                    [%debug_log "i=%d n=%a ax=%a force=%B" i nps n nps ax force];

                    let an = get_anc_in_mem n in
                    [%debug_log "an=%a" nps an];

                    if force || an != ax then begin
                      try
                        lift n
                      with
                        _ -> ()
                    end
                    else
                      [%debug_log "not lifted: an == ax"]
                  in

                  List.iter
                    (fun (i, mem, force) ->
                      lift_list := (fun () -> lifti ~force i mem)::!lift_list;
                    ) !lift_cands;

                  [%debug_log "pmap'=[%s]"
                    (String.concat ";" (List.map string_of_int (Array.to_list pmap')))];

                  [%debug_log "pmap''=[%s]"
                    (String.concat ";" (List.map string_of_int (Array.to_list pmap'')))];

                  if len' > 1 then begin
                    for i = 0 to len'-2 do
                      let p = pmap'.(i) in
                      if pmap.(i) <> p then begin
                        let n0 = a.(p) in
                        let x0 = get_anc_in_excluded n0 in
                        [%debug_log "x0=%a n0=%a" nps x0 nps n0];
                        let ks = ref [] in
                        let moveon n = n != nd in
                        scan_ancestors ~moveon x0#initial_parent
                          (fun n ->
                            match self#find_key_opt n#uid with
                            | Some k -> ks := k :: !ks
                            | None -> ()
                          );
                        [%debug_log "ks=[%s]" (keys_to_string !ks)];
                        match !ks with
                        | [k] -> begin
                            let _spath =
                              let _n0 = a.(pmap.(i)) in
                              [%debug_log "_n0=%a" nps _n0];
                              let _x0 = get_anc_in_excluded _n0 in
                              [%debug_log "_x0=%a" nps _x0];
                              mkpath _x0 _n0
                            in
                            let spath = mkpath x0 n0 in
                            [%debug_log "_spath=%s spath=%s" _spath#to_string spath#to_string];
                            if _spath <> spath then begin
                              [%debug_log "a'.(i)=%a" nps a'.(i)];
                              let ss0' = List.assq a'.(i) top_nd_tbl' in
                              [%debug_log "ss0'=[%a]" nsps ss0'];
                              [%debug_log "p=%d" p];
                              let r = pmap.(i) - p in
                              [%debug_log "r=%d" r];
                              let li = (List.length ss0') - r - 1 in
                              [%debug_log "li=%d" li];
                              let lifted_idxs = List.map (fun (i, _, _) -> i) !lift_cands in
                              [%debug_log "lifted_idxs=[%s]"
                                (String.concat "," (List.map string_of_int lifted_idxs))];
                              let key_opt = self#find_key_opt nd#uid in
                              [%debug_log "nd=%a key_opt=%s" nps nd (key_opt_to_string key_opt)];
                              try
                                List.iteri
                                  (fun i0 s0' ->
                                    if
                                      i0 <= li &&
                                      match self#find_key_opt (nmap' s0')#initial_parent#uid with
                                      | Some _ as k_opt -> k_opt = key_opt
                                      | _ -> false
                                    then begin
                                      [%debug_log "[%d] parent key of %a: %s spath=%s"
                                        i nps s0' (key_to_string k) spath#to_string];
                                      match sub_path_map.(i) with
                                      | None ->
                                          Xset.add keys_with_changed_sub_path k;
                                          let b =
                                            not (List.mem (pmap.(i)) lifted_idxs) &&
                                            not (List.mem (li+i+1) lifted_idxs) &&
                                            _spath#key_opt = None
                                          in
                                          [%debug_log "b=%B" b];
                                          let sp = if b then _spath else spath in
                                          sub_path_map.(i) <- Some sp;
                                          raise Exit
                                      | _ -> ()
                                    end
                                  ) ss0'
                              with
                                Exit -> ()
                            end
                        end
                        | _ -> ()
                      end
                    done
                  end;
                with
                  Not_found -> ()
              end;

              let excluded_ = ref [] in

              let top_nds' = fst (List.split top_nd_tbl') in
              [%debug_log "top_nds': [%a]" nsps top_nds'];
              let get_top_nd' sn =
                get_anc_in top_nds' (nmap sn)
              in
              let _top_nds' = ref [] in
              let finished_paths = ref [] in

              let st_cond =
                let tn' = Xlist.last top_nds' in
                let ss' =
                  if is_stable' tn' then
                    [tn']
                  else
                    get_p_descendants is_stable' tn'
                in
                [%debug_log "ss'=[%a]" nsps ss'];
                let rs' = List.assq tn' top_nd_tbl' in
                [%debug_log "rs'=[%a]" nsps rs'];
                ss' = rs'
              in
              [%debug_log "st_cond=%B" st_cond];

              let not_added_count = ref 0 in

              for i = 0 to len' - 2 do
                [%debug_log "[i=%d] not_added_count=%d" i !not_added_count];
                let added_flag = ref false in

                let pos = pmap''.(i) in
                let nd0 = a.(pos) in
                [%debug_log "[i=%d] pos=%d nd0=%a" i pos nps nd0];

                let tnd' = get_top_nd' nd0 in
                [%debug_log "tnd'=%a" nps tnd'];

                let st_path =
                  match sub_path_map.(i) with
                  | Some sp ->
                      [%debug_log "st_path: %s" sp#to_string];
                      sp
                  | None ->
                      let stn = get_anc_in_excluded nd0 in
                      let st_path = mkpath stn nd0 in
                      [%debug_log "stn=%a nd0=%a st_path: %s"
                        nps stn nps nd0 st_path#to_string];
                      st_path
                in
                [%debug_log "_top_nds'=[%a]" nsps !_top_nds'];
                begin
                  match !excluded_ with
                  | [] -> begin
                      [%debug_log "added: i=%d st_path=%s" i st_path#to_string];
                      excluded_ := [st_path];
                      added_flag := true
                  end
                  | h :: _ -> begin
                      [%debug_log "h=%s" h#to_string];
                      if h#path <> st_path#path then begin
                        [%debug_log "added: i=%d h=%s" i h#to_string];
                        excluded_ := st_path :: !excluded_;
                        added_flag := true
                      end
                      else if st_cond && not (List.mem st_path !finished_paths) then begin
                        match !_top_nds' with
                        | [] -> ()
                        | h :: _ ->
                            [%debug_log "h=%a" nps h];
                            if h != tnd' then begin
                              [%debug_log "added: i=%d h=%a" i nps h];
                              excluded_ := st_path :: !excluded_;
                              added_flag := true
                            end
                      end
                  end
                end;

                begin
                  match !_top_nds' with
                  | [] -> _top_nds' := [tnd']
                  | h :: _ ->
                      if h != tnd' then
                        _top_nds' := tnd' :: !_top_nds'
                end;

                [%debug_log "_top_nds'=[%a]" nsps !_top_nds'];

                let pos1 = pmap'.(i+1) in
                let nd1 = a.(pos1) in
                [%debug_log "[i=%d] pos1=%d nd1=%a" i pos1 nps nd1];

                if emap.(i) > 0 then begin
                  let _, top_nd_tbl =
                    self#get_latest_common_ancestor tree [nd0; nd1]
                  in
                  [%debug_log "top_nds: [%a]" nsps (fst (List.split top_nd_tbl))];
                  let st_nd, _ = List.hd top_nd_tbl in
                  let rp = get_rel_path nd#apath (Path.get_parent st_nd#apath) in
                  let ap = get_adjusted_path rp in
                  let st_pos = st_nd#initial_pos in

                  if i > 2 && !not_added_count > 0 then begin
                    let pos_i = pmap'.(i-1) in
                    let pos_i_ = pmap''.(i-1) in
                    let posi = pmap'.(i) in
                    let posi_ = pmap''.(i) in
                    [%debug_log "pos_i=%d pos_i_=%d" pos_i pos_i_];
                    [%debug_log "posi=%d posi_=%d" posi posi_];
                    let b = pos_i > 0 && pos_i < pos_i_ && posi = posi_ && posi > 0 in
                    let nx = List.length !excluded_ in
                    [%debug_log "i=%d len'=%d b=%B nx=%d" i len' b nx];
                    if i = (len'-2) && b && nx + emap.(i) < !npaths - 1 then begin
                      let ndi = a.(posi) in
                      let n = get_anc_in_excluded ndi in

                      let skip_parent_key_check =
                        match !excluded_ with
                        | bp::_ when bp#has_frac_ofs -> true
                        | _ -> false
                      in
                      [%debug_log "skip_parent_key_check=%B" skip_parent_key_check];

                      let i_path = mkpath ~skip_parent_key_check n ndi in
                      [%debug_log "n=%a ndi=%a i_path: %s" nps n nps ndi i_path#to_string];
                      [%debug_log "added: i=%d i_path=%s" i i_path#to_string];
                      excluded_ := i_path :: !excluded_;
                      added_flag := true
                    end
                  end;

                  let ndigits = String.length (string_of_int emap.(i)) in
                  for j = 1 to emap.(i) do
                    let ofs =
                      float_of_string
                        (sprintf
                           (Scanf.format_from_string
                              (sprintf "%%d.%%0%dd" ndigits) "%d%d") st_pos j)
                    in
                    let p =
                      Path.append
                        ap (Elem.make ~ofs (Path.tail st_path#path).Elem.pos(*st_pos*))
                    in
                    [%debug_log "p=%s" (Path.to_string p)];
                    match !excluded_ with
                    | [] -> begin
                        [%debug_log "added: i=%d p=%s" i (Path.to_string p)];
                        excluded_ := [new boundary_path p];
                        added_flag := true
                    end
                    | h :: _ ->
                        [%debug_log "h=%s" h#to_string];
                        if h#path <> p then begin
                          [%debug_log "added: i=%d p=%s" i (Path.to_string p)];
                          excluded_ := (new boundary_path p) :: !excluded_;
                          added_flag := true
                        end
                  done
                end;

                [%debug_log "pos1=%d, i=%d, len'=%d" pos1 i len'];

                if pos1 = pmap.(i+1) || i = (len'-2) then begin
                  let edn = get_anc_in_excluded nd1 in
                  let skip_parent_key_check =
                    match !excluded_ with
                    | bp::_ when bp#has_frac_ofs -> true
                    | _ -> false
                  in
                  [%debug_log "skip_parent_key_check=%B" skip_parent_key_check];
                  let ed_path = mkpath ~skip_parent_key_check edn nd1 in
                  [%debug_log "edn=%a nd1=%a ed_path: %s" nps edn nps nd1 ed_path#to_string];

                  match !excluded_ with
                  | [] -> assert false
                  | h :: _ ->
                      [%debug_log "h=%s" h#to_string];
                      if h#path <> ed_path#path || edn != nd1 then begin
                        [%debug_log "added: i=%d ed_path=%s" i ed_path#to_string];
                        excluded_ := ed_path :: !excluded_;
                        finished_paths := ed_path :: !finished_paths;
                        added_flag := true;
                        if not (is_stable edn) && ed_path#key_opt = st_path#key_opt then begin
                          try
                            List.iter
                              self#restore_canceled_stable_node
                              (Hashtbl.find sub_canceled_stable_node_tbl edn)
                          with
                            _ -> ()
                        end
                      end
                end;

                [%debug_log "i=%d excluded_=[%s]"
                  i (String.concat ";" (List.map (fun x -> x#to_string) !excluded_))];

                if not !added_flag then
                  incr not_added_count

              done; (* for i = 0 to len' - 2 do *)

              let paths =
                List.fold_left
                  (fun l p ->
                    [%debug_log "p=%s" p#to_string];
                    match l with
                    | [] -> [p]
                    | h::_ ->
                        try
                          let pn, _, _, _ = Hashtbl.find node_tbl p in
                          let hn, _, _, _ = Hashtbl.find node_tbl h in
                          if not (is_stable pn) || not (is_stable hn) then
                            raise Not_found;
                          let anc0', _ =
                            self#get_latest_common_ancestor tree' [nmap pn; nmap hn]
                          in
                          [%debug_log "pn=%a hn=%a anc0'=%a (anc'=%a)"
                            nps pn nps hn nps anc0' nps anc'];

                          if anc0' != anc' then
                            l
                          else
                            p :: l
                        with
                          Not_found -> p :: l
                  ) [] !excluded_
              in
              let paths =
                List.map
                  (fun p ->
                    try
                      Hashtbl.find orig_path_tbl p
                    with
                      Not_found -> p
                  ) paths
              in
              [%debug_log "paths=%s" (boundary_to_string paths)];
              [%debug_log "anc'=%a children'=[%a] st_pos'=%d"
                nps anc' nsps (Array.to_list children') st_pos'];

              begin
                match self#find_key_opt nd#uid with
                | Some k -> reg_parent_key paths k
                | _ -> ()
              end;

              let implicit_frac_begin_opt = ref None in
              let check_path p =
                [%debug_log "p=%s" p#to_string];
                match !implicit_frac_begin_opt with
                | Some p0 -> begin
                    [%debug_log "p0=%s" p0#to_string];
                    let parent, elem = Path.split p#path in
                    let parent0, elem0 = Path.split p0#path in
                    if parent = parent0 && elem.Elem.pos = elem0.Elem.pos then begin
                      elem.Elem.ofs <- elem0.Elem.ofs +. 1.
                    end
                end
                | None -> ()
              in
              let rec scan = function
                | [] -> ()
                | [p] -> begin
                    if p#key_opt <> None then
                      check_path p
                end
                | p0::(p1::_ as tl) -> begin
                    [%debug_log "p0=%s p1=%s" p0#to_string p1#to_string];
                    if p0#key_opt = None then begin
                      if
                        (Path.tail p0#path).Elem.ofs = 0. && p1#has_frac_ofs
                      then begin
                        [%debug_log "%s has frac ofs" p1#to_string];
                        implicit_frac_begin_opt := Some p0
                      end
                    end
                    else begin
                      check_path p0;
                      implicit_frac_begin_opt := None
                    end;
                    scan tl
                end
              in
              scan paths;
              [%debug_log "paths=%s" (boundary_to_string paths)];

              let intermediate_tbl = Hashtbl.create 0 in
              List.iteri
                (fun i p ->
                  let _ = i in
                  let fe = Path.tail p#path in
                  [%debug_log "i=%d p=%s fe=%s" i p#to_string (Elem.to_string fe)];

                  let child_insert_root_opt =
                    match p#key_opt with
                    | Some k -> begin
                        try
                          Some (get_subtree_root_by_key k)
                        with
                          Not_found -> None
                    end
                    | None -> None
                  in
                  [%debug_log "child_insert_root_opt=%s"
                    (match child_insert_root_opt with
                    | Some x -> node_to_uid_string x
                    | None -> "")];
                  try
                    let n, _, range, _ = Hashtbl.find node_tbl p in
                    let fn = n#initial_parent in
                    [%debug_log "n=%a range=[%a] fn=%a" nps n nsps range nps fn];
                    List.iter
                      (fun n' ->
                        [%debug_log "n'=%a" nps n'];
                        match child_insert_root_opt with
                        | Some x when not (Hashtbl.mem comp_cand_tbl x) ->
                            [%debug_log "%a -> (%s, %a, %a)"
                              nps fn (Elem.to_string fe) nps n' nps x];
                            tbl_add intermediate_tbl fn (fe, n', child_insert_root_opt)
                        | _ -> ()
                      ) range
                  with
                    Not_found -> ()
                ) paths;
              let vec_tbl = Hashtbl.create 0 in
              Hashtbl.iter
                (fun fn l ->
                  let children = Array.to_list fn#initial_children in
                  let mems =
                    List.filter (fun x -> not (self#is_excluded x)) children
                  in
                  let all_excluded = mems = [] in
                  [%debug_log "fn=%a mems=[%a] all_excluded=%B"
                    nps fn nsps mems all_excluded];

                  if all_excluded then begin
                    if not (Hashtbl.mem vec_tbl fn) then begin
                      let atbl = Hashtbl.create 0 in
                      let aatbl = Hashtbl.create 0 in
                      List.iter
                        (fun (_, n', ci_opt) ->
                          [%debug_log "n'=%a ci_opt=%s" nps n'
                            (match ci_opt with
                            | Some x -> node_to_uid_string x
                            | None -> "")];

                          List.iter
                            (fun x' ->
                              match ci_opt with
                              | Some ci ->
                                  [%debug_log "atbl: add %a -> %a" nps x' nps ci];
                                  Hashtbl.add atbl x' ci
                              | None ->
                                  [%debug_log "atbl: add %a -> %a" nps x' nps n'];
                                  Hashtbl.add atbl x' n'
                            ) (get_p_descendants is_stable' n')
                        ) l;
                      let ancs_with_stable_descs = Xset.create 0 in
                      let _vec =
                        List.concat_map
                          (fun x ->
                            [%debug_log "x=%a" nps x];
                            if is_stable x then begin
                              [%debug_log "%a is stable" nps x];
                              let x' = nmap x in
                              try
                                let a' = Hashtbl.find atbl x' in
                                [%debug_log "atbl: x'=%a -> a'=%a"
                                  nps x' nps a'];
                                Xset.add ancs_with_stable_descs a';
                                [a']
                              with
                                Not_found ->
                                  Xset.add ancs_with_stable_descs x';
                                  [x']
                            end
                            else begin
                              let ss = get_p_descendants is_stable x in
                              [%debug_log "ss=[%a]" nsps ss];
                              if ss = [] then
                                [x]
                              else
                                let ss' = List.map nmap ss in
                                [%debug_log "ss'=[%a]" nsps ss'];
                                List.rev
                                  (List.fold_left
                                     (fun l x' ->
                                       try
                                         let a' = Hashtbl.find atbl x' in
                                         [%debug_log "atbl: x'=%a -> a'=%a"
                                           nps x' nps a'];
                                         Xset.add ancs_with_stable_descs a';
                                         a' :: l
                                       with
                                         Not_found ->
                                           Xset.add ancs_with_stable_descs x;
                                           if
                                             Xarray.exists ((==) x') children'
                                           then
                                             List.iter
                                               (fun y ->
                                                 [%debug_log "aatbl: %a -> %a" nps y nps x];
                                                 Hashtbl.add aatbl y x
                                               ) l;
                                           x :: l
                                     ) [] ss')
                            end
                          ) children
                      in
                      [%debug_log "_vec=[%a]" nsps _vec];
                      [%debug_log "canceled_stable_nodes=[%a]"
                        nsps (self#canceled_stable_node_list tree)];
                      let vec =
                        Array.of_list
                          (self#filter_canceled_stable_nodes tree nmap'
                          (Xlist.uniqq
                             (List.map
                                (fun x ->
                                  try
                                    Hashtbl.find aatbl x
                                  with
                                    Not_found -> x
                                ) _vec)))
                      in
                      let ofs = ref 0 in
                      begin
                        try
                          Array.iteri
                            (fun i x ->
                              if
                                Xset.mem ancs_with_stable_descs x ||
                                Hashtbl.mem walls x
                              then begin
                                ofs := i;
                                raise Exit
                              end
                            ) vec
                        with
                          Exit -> ()
                      end;
                      [%debug_log "vec=[%a] ofs=%d" nsps (Array.to_list vec) !ofs];
                      Hashtbl.add vec_tbl fn (vec, !ofs)
                    end
                  end
                  else begin (* mems <> [] *)
                    let ns =
                      List.flatten
                        (List.mapi
                           (fun i mem ->
                             let left, right =
                               List.fold_left
                                 (fun (left, right) (fe, n', (*ci_opt*)_) ->
                                   if fe.Elem.pos = i then
                                     let ofs = fe.Elem.ofs in
                                     if ofs > 0. then
                                       left, (n' :: right)
                                     else if ofs < 0. then
                                       (n' :: left), right
                                     else
                                       left, right
                                   else
                                     left, right
                                 ) ([], []) l
                             in
                             left @ (mem :: right)
                           ) mems)
                    in
                    [%debug_log "ns=[%a]" nsps ns];
                    List.iteri
                      (fun i n ->
                        if List.memq n mems then begin
                          self#add_mem_pos n i
                        end
                      ) ns
                  end
                ) intermediate_tbl;

              let vec_mems = Xset.create 0 in

              Hashtbl.iter
                (fun _ (vec, ofs) ->
                  let nvec = Array.length vec in
                  for i = 0 to nvec - 1 do
                    let ni = vec.(i) in
                    Xset.add vec_mems ni;
                    reg_ipos ni i;
                    reg_iofs ni (i-ofs)
                  done
                ) vec_tbl;

              let fnl = ref [] in
              List.iter
                (fun p ->
                  [%debug_log "p=%s" p#to_string];
                  try
                    let n, _, _, _ = Hashtbl.find node_tbl p in
                    let fn = n#initial_parent in
                    [%debug_log "n=%a fn=%a" nps n nps fn];

                    if Xset.mem vec_mems n then begin
                      try
                        (Path.tail p#path).Elem.ofs <- float (find_iofs n)
                      with
                        Not_found -> ()
                    end;

                    if not (List.memq fn !fnl) && Hashtbl.mem vec_tbl fn then begin
                      List.iter
                        (fun (fe, n', (*ci_opt*)_) ->
                          [%debug_log "fe=%s n'=%a" (Elem.to_string fe) nps n'];
                          try
                            let ofs' = float (find_iofs n') in

                            if fe.Elem.ofs <> ofs' then begin
                              [%debug_log "ofs: %s -> %s"
                                (Elem.ofs_to_str fe.Elem.ofs) (Elem.ofs_to_str ofs')];

                              fe.Elem.ofs <- ofs'
                            end
                          with
                            Not_found -> ()

                        ) (Hashtbl.find intermediate_tbl fn);

                      fnl := fn :: !fnl
                    end
                  with
                    Not_found -> ()
                ) paths;


              List.iter (fun f -> f()) !lift_list;

              let is_upward =
                try
                  tree'#is_initial_ancestor anc' (nmap nd)
                with
                  Not_found -> false
              in
              [%debug_log "is_upward=%B" is_upward];

              let should_be_lifted =
                if is_upward then
                  []
                else
                let mem_tbl = Hashtbl.create 0 in (* parent path -> parent node *)
                let pos_tbl = Hashtbl.create 0 in (* parent path -> pos list *)
                let pps =
                  Xlist.uniq
                    (List.map
                       (fun p ->
                         [%debug_log "p=%s" p#to_string];
                         let pp = Path.get_parent p#path in
                         [%debug_log "pp=%s" (Path.to_string pp)];
                         begin
                           try
                             let pn, pos, _, _ = Hashtbl.find node_tbl p in
                             [%debug_log "pn=%a pos=%d" nps pn pos];
                             [%debug_log "pos_tbl: add %s -> %d"
                               (Path.to_string pp) pos];

                             tbl_add pos_tbl pp pos;
                             let mem = pn#initial_parent in
                             let mps =
                               List.filter_map
                                 (fun x ->
                                   if List.memq x excluded then
                                     None
                                   else
                                     Some x#initial_pos
                                 ) (Array.to_list mem#initial_children)
                             in
                             [%debug_log "mem_tbl: add \"%s\" -> (%a,[%s])"
                               (Path.to_string pp) nps mem
                               (String.concat ";" (List.map string_of_int mps))];

                             Hashtbl.add mem_tbl pp (mem, mps);
                           with
                             Not_found -> ()
                         end;
                         pp, p#key_opt
                       ) paths)
                in (* pps *)
                [%debug_log "pps=[%s]"
                  (String.concat ";"
                     (List.map
                        (fun (p, k_opt) ->
                          sprintf "\"%s\"%s" (Path.to_string p)
                            (match k_opt with
                            | Some k -> ":"^(key_to_string k)
                            | None -> "")
                        ) pps
                     ))];

                List.filter
                  (fun n ->
                    [%debug_log "n=%a" nps n];
                    if Xset.mem lifted_nds n then begin
                      [%debug_log "already lifted"];
                      false
                    end
                    else begin
                      let x = get_anc_in_excluded n in
                      let pos = x#initial_pos in
                      let rp = get_rel_path nd#apath x#initial_parent#apath in
                      let ap = get_adjusted_path rp in
                      [%debug_log "x=%a pos=%d ap=%s" nps x pos (Path.to_string ap)];

                      List.for_all
                        (fun (pp, k_opt) ->
                          let is_eq = Path.eq pp ap in

                          [%debug_log "pp=%s is_eq=%B" (Path.to_string pp) is_eq];

                          let path_change =
                            if is_eq then begin
                              match k_opt with
                              | Some _ -> x == n
                              | None ->
                              try
                                let ps = Hashtbl.find pos_tbl pp in
                                let mem, mps = Hashtbl.find mem_tbl pp in
                                [%debug_log "mem=%a pos=%d mps=[%s] ps=[%s]"
                                  nps mem pos
                                  (String.concat ";" (List.map string_of_int mps))
                                  (String.concat ";" (List.map string_of_int ps))];

                                match mps with
                                | [] -> false
                                | _ -> begin
                                    let rangel =
                                      Xlist.uniq (0::(mps@[mem#initial_nchildren-1]))
                                    in
                                    [%debug_log "rangel=[%s]"
                                      (String.concat ";" (List.map string_of_int rangel))];
                                    let rangea = Array.of_list rangel in
                                    try
                                      for i = 0 to (Array.length rangea) - 2 do
                                        (*[%debug_log "i=%d" i];*)
                                        let st, ed = rangea.(i), rangea.(i+1) in
                                        (*[%debug_log "st=%d, ed=%d" st ed];*)
                                        if st <= pos && pos <= ed then begin
                                          if
                                            List.for_all
                                              (fun p -> p < st || ed < p) ps
                                          then
                                            raise Exit
                                        end
                                      done;
                                      false
                                    with
                                      Exit ->
                                        [%debug_log "transposition detected"];
                                        true
                                end
                              with
                                Not_found -> false
                            end
                            else (* ap <> pp *)
                              true
                          in (* path_change *)
                          [%debug_log "path_change=%B" path_change];
                          path_change

                        ) pps
                    end

                  ) excepted_nds
              in (* should_be_lifted *)
              [%debug_log "should_be_lifted=[%a]" nsps should_be_lifted];
              List.iter self#cancel_stable_node should_be_lifted;
              List.iter
                (fun n ->
                  try
                    lift n
                  with
                    _ -> ()
                ) should_be_lifted;

              let paths = filter_paths_i pos_shift paths_count paths in

              if paths = [] then begin
                let anc', path', paths, upc, simple =
                  let is_excluded _ = self#is_excluded in
                  let get_group _ = raise Not_found in
                  let group_heads = [] in
                  let is_simple_ins = fun _ -> None in
                  get_path'
                    (get_adjusted_path
                       ~get_group ~group_heads ~is_simple_ins ~get_iparent_opt:None ~is_excluded)
                    nd excluded
                in
                [%debug_log "anc'=%a path'=%s upc=%d simple=%B"
                  nps anc' (Path.to_string path') upc simple];
                anc', path', paths, upc, simple
              end
              else begin
              begin
                let to_be_invalidated = ref [] in
                let top_nds' = Xset.create 0 in
                List.iter
                  (fun w ->
                    [%debug_log "w=%a" nps w];
                    try
                      if not (is_stable w) then
                        raise Not_found;
                      let w' = nmap w in
                      let t' = get_ancestor_below w' anc' in
                      let i = t'#initial_pos - Path.get_position path' in
                      [%debug_log "w'=%a t'=%a path'=%s i=%d" nps w' nps t' (Path.to_string path') i];
                      let bpath = List.nth paths i in
                      [%debug_log "bpath=%s" bpath#to_string];
                      if bpath#offset <> 0. then begin
                        let pp = Path.get_parent bpath#path in
                        let pn = self#acc nd pp in
                        let pw = w#initial_parent in
                        [%debug_log "pp=%s pn=%a pw=%a" (Path.to_string pp) nps pn nps pw];
                        if
                          pn != pw &&
                          try
                            for i = w#initial_pos + 1 to pw#initial_nchildren - 1 do
                              let ci = pw#initial_children.(i) in
                              [%debug_log "i=%d ci=%a" i nps ci];
                              if not (is_stable ci) && not (has_p_descendant is_stable ci) then
                                raise Exit
                            done;
                            false
                          with
                            Exit -> true
                        then begin
                          [%debug_log "to be invalidated: w=%a" nps w];
                          to_be_invalidated := w :: !to_be_invalidated;
                          Hashtbl.remove walls w
                        end
                        else if Hashtbl.mem walls w && Xset.mem top_nds' t' then begin
                          [%debug_log "to be invalidated: w=%a" nps w];
                          to_be_invalidated := w :: !to_be_invalidated;
                          Hashtbl.remove walls w
                        end
                        else
                          Xset.add top_nds' t'
                      end
                    with
                      _ -> ()

                  ) (List.rev !added_walls);

                Hashtbl.iter
                  (fun m w0 ->
                    if List.memq w0 !to_be_invalidated then begin
                      try
                        let w =
                          List.hd
                            (List.rev
                               (List.filter
                                  (fun x -> not (List.memq x !to_be_invalidated))
                                  (Hashtbl.find qwtbl m)))
                        in
                        [%debug_log "%a -> wall" nps w];
                        Hashtbl.add walls w (try Some (Hashtbl.find group_tbl w) with _ -> None);
                        (*let ca = w#initial_parent#initial_children in
                        for i = 0 to w#initial_pos - 1 do
                          let ci = ca.(i) in
                          if Xset.mem walls ci then
                            Xset.remove walls ci;
                          if Xset.mem quasi_walls ci then
                            Xset.remove quasi_walls ci
                        done;
                        Xset.remove quasi_walls w*)
                      with
                        _ -> ()
                    end
                  ) wtbl
              end;
              anc', path', paths, 0, false
              end
          end
        in (* anc', path', paths, upstream, simple *)
        [%debug_log "anc'=%a path'=%s upstream=%d simple=%B"
          nps anc' (Path.to_string path') upstream simple];
        [%debug_log "excepted paths: %s" (boundary_to_string paths)];

        anc', (new path_c ~upstream path'), paths, simple

      method private acc ?(simple=false) root path =
        [%debug_log "root=%a path=%s simple=%B" nps root (Path.to_string path) simple];
        let is_excluded =
          if simple then
            fun _ -> false
          else
            self#is_excluded
        in
        let cur = ref root in
        List.iter
          (fun elem ->
            [%debug_log "%s" (Elem.to_string elem)];
            if elem.Elem.ofs <> 0. then
              raise Not_found;
            let pos = elem.Elem.pos in
            (*[%debug_log "pos=%d" pos];*)
            let i = ref (-1) in
            try
              Array.iter
                (fun x ->
                  (*[%debug_log "x=%a" nps x];*)
                  if not (is_excluded x) then
                    incr i;
                  (*[%debug_log "i=%d" !i];*)
                  if !i = pos then begin
                    [%debug_log "cur=%a" nps x];
                    cur := x;
                    raise Exit
                  end;
                ) (!cur)#initial_children;
              raise Not_found
            with
              Exit -> ()

          ) (Path.get_elems path);
        [%debug_log " -> %a" nps !cur];
        !cur

      method private rev_ancto_tbl_add mem_mov tbl k anc path paths rt =
        let chk_mov_filt p anc i =
          if p#has_frac_ofs then begin
            let c = anc#initial_children.(i) in
            if mem_mov c then begin
              [%debug_log "%a should not be filtered" nps c];
              Xset.add filt_blacklist c
            end
          end
        in
        let pos = path#position in
        [%debug_log "k=%s anc=%a pos=%d npaths=%d rt=%a"
          (key_to_string k) nps anc pos (List.length paths) nps rt];
        List.iteri
          (fun i p ->
            [%debug_log "i=%d p=%s" i p#to_string];
            match p#key_opt with
            | Some k0 -> let _ = k0 in [%debug_log "not added: i=%d p=%s k0=%s" i p#to_string (key_to_string k0)]
            | None when
                (try
                  let pn = self#acc ~simple:false rt (Path.get_parent p#path) in
                  let pk = self#find_key pn#uid in
                  [%debug_log "pn=%a pk=%s" nps pn (key_to_string pk)];
                  pk <> k
                with
                  _ -> true) -> [%debug_log "not added: i=%d p=%s" i p#to_string]
            | _ ->
                let i = i + pos in
                let anc_i = anc, i in
                try
                  let kl = Hashtbl.find tbl anc_i in
                  if not (List.mem k kl) then begin
                    let kl' = k::kl in
                    [%debug_log "(%a,%d) -> [%s]" nps anc i (keys_to_string kl')];
                    chk_mov_filt p anc i;
                    Hashtbl.replace tbl anc_i kl'
                  end
                with
                  Not_found ->
                    [%debug_log "(%a,%d) -> [%s]" nps anc i (key_to_string k)];
                    chk_mov_filt p anc i;
                    Hashtbl.add tbl anc_i [k]
          ) paths

      method is_upward_staying_move mid rt remote_stable_tbl' nmap' tree =
        [%debug_log "mid=%a rt=%a" MID.ps mid nps rt];
        let (_, _, b) as res =
          try
            Hashtbl.find is_upward_staying_move_cache (tree, mid)
          with
            Not_found ->
              let rss' = flatten_remote_stable_tbl remote_stable_tbl' in
              [%debug_log "rss'=[%a]" nsps rss'];
              if rss' = [] then
                ([], [], false)
              else
                let rss = List.map nmap' rss' in
                [%debug_log "rss=[%a]" nsps rss];
                let ra, _ = self#get_latest_common_ancestor tree rss in
                let b = ra == rt || tree#is_initial_ancestor ra rt in
                let res = (rss, rss', b) in
                Hashtbl.add is_upward_staying_move_cache (tree, mid) res;
                res
        in
        let _ = b in
        [%debug_log "%a -> %B" MID.ps mid b];
        res

      method _is_upward_staying_move tree mid =
        try
          let _, _, b =
            Hashtbl.find is_upward_staying_move_cache (tree, mid)
          in
          b
        with
          Not_found -> false

      method private make_chg_inst tag node1 node2 =
        let ln1 = Triple._make_entity options tree1 node1 in
        let ln2 = Triple._make_entity options tree2 node2 in
        let ln = String.concat Entity.sep [ln1; ln2; Editop.tag_to_string tag] in
        Triple.mkchginst ln

      method private find_from_or_into ?(mid_opt=None) tree' map_find node =
        CB.find_from_or_into tree1 tree2 edits_copy ~mid_opt tree' map_find node

      method private are_contiguous_children nds =
        match nds with
        | [] | [_] -> true
        | h::_ -> begin
            let pnd = h#initial_parent in
            let p0 = h#initial_pos in
            try
              List.iteri
                (fun i x ->
                  if x#initial_parent != pnd || x#initial_pos <> i + p0 then
                    raise Exit
                ) nds;
              true
            with
              Exit -> false
        end

      method private get_conflicts ?(ancto_opt=None) ?(parent_ins_point_opt=None)
          is_stable is_stable' tree tree' nmap nmap'
          nd nd'
          =
        let stid_of_key, ancto_tbl, is_ancestor_key, get_subtree_root_by_key', simple_ins_roots =
          if tree == tree1 then
            self#stid_of_key2, anc1to_tbl, self#is_ancestor_key1, self#get_subtree_root_by_key2, simple_ins_roots2
          else
            self#stid_of_key1, anc2to_tbl, self#is_ancestor_key2, self#get_subtree_root_by_key1, simple_ins_roots1
        in
        let has_stable_descendant n =
          is_stable n || has_p_descendant is_stable n
        in

        [%debug_log "nd=%a nd'=%a" nps nd nps nd'];

        begin %debug_block
          match ancto_opt with
          | Some x -> [%debug_log "ancto=%a" nps x]
          | None -> [%debug_log "ancto="]
        end;
        begin %debug_block
          match parent_ins_point_opt with
          | Some (k, x, pos, nb) -> [%debug_log "parent_ins_target=(%s,%a,%d,%d)" (key_to_string k) nps x pos nb]
          | None -> [%debug_log "parent_ins_target="]
        end;

        let parent_ins_point_opt =
          match parent_ins_point_opt with
          | Some _ -> parent_ins_point_opt
          | None ->
              match self#find_key_opt nd'#initial_parent#uid with
              | Some k' -> begin
                  [%debug_log "k'=%s" (key_to_string k')];
                  try
                    let t', (pt', ps') = Hashtbl.find ancto_tbl k' in
                    let pos' = pt'#position in
                    let nb' = List.length ps' in
                    [%debug_log "t'=%a pos'=%d nb'=%d" nps t' pos' nb'];
                    Some (k', t', pos', nb')
                  with _ -> None
              end
              | None -> None
        in
        let parent_parent_ins_key_opt =
          match parent_ins_point_opt with
          | Some (k, _, _, _) -> begin
              try
                let r = get_subtree_root_by_key' k in
                [%debug_log "r=%a" nps r];
                let k' = self#find_key r#initial_parent#uid in
                [%debug_log "%s -> %s" (key_to_string k) (key_to_string k')];
                Some k'
              with _ -> None
          end
          | _ -> None
        in
        let parent_parent_ins_target_opt =
          match parent_parent_ins_key_opt with
          | Some k' -> begin
              try
                let a', _ = Hashtbl.find ancto_tbl k' in
                [%debug_log "parent_parent_ins_target: %a" nps a'];
                Some a'
              with _ -> None
          end
          | _ -> None
        in

        (*let s_anc = get_p_ancestor is_stable nd in
        let s_anc' = nmap s_anc in*)
        let s_anc, s_anc' =
          let last_k = ref K_stable in
          let pred x' =
            [%debug_log "last_k=%s x'=%a" (key_to_string !last_k) nps x'];
            match self#find_key_opt x'#uid with
            | Some k -> begin
                [%debug_log "k=%s" (key_to_string k)];
                let r' = get_subtree_root_by_key' k in
                let b =
                  !last_k <> K_stable &&
                  r' == x' &&
                  k <> !last_k && not (is_ancestor_key k !last_k) &&
                  Hashtbl.mem ancto_tbl k &&
                  let px' = x'#initial_parent in
                  is_stable' px' || not (is_ancestor_key (self#find_key px'#uid) k)
                in
                if k <> !last_k then
                  last_k := k;
                [%debug_log "b=%B" b];
                b
            end
            | None -> true
          in
          let anc' = get_p_ancestor pred nd' in
          [%debug_log "anc'=%a last_k=%s" nps anc' (key_to_string !last_k)];
          if is_stable' anc' then
            let anc = nmap' anc' in
            anc, anc'
          else
            let anc, _ = Hashtbl.find ancto_tbl !last_k in
            anc, (*anc'#initial_parent*)get_p_ancestor is_stable' anc'
        in (* s_anc, s_anc' *)
        [%debug_log "ancestor of %a: %a -> %a" nps nd nps s_anc nps s_anc'];

        let key_nodes' =
          let is_ini_anc' = tree'#is_initial_ancestor in
          let moveon x' = x' == s_anc' || not (is_stable' x') in
          get_p_descendants
            ~keep_going:true(*REGRESSION:k9mail/k-9 99 vs Rajawali/Rajawali 62, atlasapi/atlas 211*)
            ~moveon
            (fun n' ->
              [%debug_log "n'=%a" nps n'];
              let b =
              n' != nd' &&
              try
                let stid = self#find_stid n'#uid in
                let sr' = self#get_subtree_root stid in
                if n' == sr'(* || is_ini_anc' sr' n'*)(*!!!!!!*) then
                  not (is_ini_anc' (*sr'*)n' nd') && not (is_ini_anc' nd' (*sr'*)n')
                else
                  false
              with
                Not_found -> false
              in
              [%debug_log "n'=%a b=%B" nps n' b];
              b
            ) s_anc'
        in
        [%debug_log "key_nodes': [%s]" (nodes_to_uids_string key_nodes')];

        let staying_move_only = ref true in
        let conflicting_staying_moves = ref [] in

        let gi = nd#gindex in

        let ins_target_tbl = Hashtbl.create 0 in

        let pnd_stable' = is_stable' nd'#initial_parent in

        let top_nda =
          match parent_ins_point_opt with
          | Some (_, t, p, bn) when bn > 0 -> Array.sub t#initial_children p bn
          | _ -> [||]
        in
        [%debug_log "top_nda=[%a]" nsps (Array.to_list top_nda)];

        let has_conflicts' n' =
          [%debug_log "n'=%a" nps n'];
          let is_simple_ins = Xset.mem simple_ins_roots n' in
          [%debug_log "is_simple_ins=%B" is_simple_ins];
          try
            if not (is_stable' n'#initial_parent) then begin
              if
                is_simple_ins ||
                top_nda <> [||] &&
                let ss' = get_p_descendants ~moveon:(fun x' -> not (is_stable' x')) is_stable' n' in
                let ss = List.map nmap' ss' in
                [%debug_log "ss=[%a]" nsps ss];
                not (List.exists (fun s -> Array.exists (fun t -> is_ancestor t s) top_nda) ss)
              then begin
                [%debug_log "nd'=%a n'=%a" nps nd' nps n'];
                raise Not_found
              end
            end;
            match self#find_key_opt n'#uid with
            | Some k -> begin
                [%debug_log "k=%s" (key_to_string k)];
                let a, (pt, ps) = Hashtbl.find ancto_tbl k in
                let pos = pt#position in
                let nb = List.length ps in
                [%debug_log "a=%a pos=%d nb=%d" nps a pos nb];
                let a_children = a#initial_children in
                try
                  if array_range_exists (fun x -> is_ancestor x nd) a_children pos (pos+nb-1) then begin
                    begin
                      match parent_parent_ins_target_opt with
                      | Some a' ->
                          if is_ancestor a' a then
                            raise Exit
                      | _ -> ()
                    end;
                  (*for i = pos to pos + nb - 1 do
                    let ci = a_children.(i) in
                    [%debug_log "i=%d ci=%a" i nps ci];
                    if
                      is_ancestor ci nd &&
                      not
                        (match parent_ins_target_opt with
                        | Some (_, x) -> (*x == ci || *)is_ancestor ci x
                        | None -> false)
                    then
                      raise Exit
                  done;*)
                  if
                    (pnd_stable' ||
                    match parent_ins_point_opt with
                    | Some (_, x, xp, xnb) ->
                        is_ancestor x a || x == a && xnb > 0 && nb > 0 && overlaps xp (xp+xnb-1) pos (pos+nb-1)
                    | None -> false)
                  then
                    raise Exit
                  end;
                  false
                with
                  Exit ->
                    [%debug_log "conflict found: key_node'=%a" nps n'];
                    begin
                      match k with
                      | K_mid m -> begin
                          let is_staying = self#is_staying_move m in
                          [%debug_log "%a: staying_move=%B" MID.ps m is_staying];

                          staying_move_only := !staying_move_only && is_staying;
                          if is_staying then
                            if not (List.mem m !conflicting_staying_moves) then
                              conflicting_staying_moves := m :: !conflicting_staying_moves
                      end
                      | _ -> staying_move_only := false
                    end;
                    Hashtbl.add ins_target_tbl n' a;
                    [%debug_log "ins_target_tbl: %a -> %a" nps n' nps a];
                    true
            end
            | None -> raise Not_found
          with Not_found ->
          let ss' =
            self#filter_canceled_stable_nodes tree' nmap
              (get_p_descendants is_stable' n')
          in
          [%debug_log "ss'=[%a]" nsps ss'];
          let ss = List.map nmap' ss' in
          [%debug_log "ss=[%a]" nsps ss];
          (*let ss =
            List.filter
              (fun s ->
                try
                  let k_opt, upc, _ = Hashtbl.find parent_spec_tbl s in
                  k_opt = None && upc = 0
                with
                  Not_found -> true
              ) ss
          in
          [%debug_log "ss=[%a] (filtered)" nsps ss];*)
          if (List.length ss) > 1 then
            let a, tnt = self#get_latest_common_ancestor tree ss in
            [%debug_log "a=%a" nps a];

            let safe_nds =
              let sa' =
                if is_stable' n'#initial_parent then
                  n'
                else
                  get_p_ancestor (fun x -> is_stable' x#initial_parent) n'
              in
              match self#find_key_opt sa'#uid with
              | Some k ->
                  [%debug_log "k=%s" (key_to_string k)];
                  let stid = stid_of_key k in
                  let _, xs, _ = self#get_subtree_spec stid in
                  [%debug_log "xs=[%a]" nsps xs];
                  let sxs = List.filter has_stable_descendant xs in
                  [%debug_log "sxs=[%a]" nsps sxs];
                  if (List.length sxs) > 1 then
                    List.flatten
                      (List.mapi
                         (fun i _ ->
                           try
                             let _, ms = List.nth tnt i in
                             ms
                           with
                             _ -> []
                         ) xs)
                  else
                    ss
              | None -> ss
            in
            [%debug_log "safe_nds=[%a]" nsps safe_nds];

            let k_opt = self#find_key_opt n'#uid in
            [%debug_log "n'=%a k_opt=%s" nps n' (key_opt_to_string k_opt)];

            let b =
              (match ancto_opt with
              | Some ancto -> not (is_ancestor ancto a)
              | None -> true) &&
              (*(is_stable' nd'#initial_parent ||
               match k_opt with
              | Some k -> Hashtbl.mem ancto_tbl k
              | None -> true) &&*)
              (tree#is_initial_ancestor s_anc a || a == s_anc) &&
              (tree#is_initial_ancestor a nd) &&

              (List.exists (tree#is_initial_ancestor nd) ss ||
              (let _, closest =
                List.fold_left
                  (fun (d, nx) n0 ->
                    let d' = abs (n0#gindex - gi) in
                    if List.memq n0 safe_nds && (d = 0 || d' < d) then
                      (d', n0)
                    else
                      (d, nx)
                  ) (0, nd) ss
              in
              [%debug_log "closest=%a" nps closest];
              if closest == nd then
                false
              else
                let a0, _ =
                  self#get_latest_common_ancestor tree [nd;closest]
                in
                [%debug_log "a0=%a" nps a0];
                a0 == a &&
                let get_ins_target = self#get_ins_target tree nmap' is_stable' in
                try
                  let a1, p1, nb1 =
                    try
                      let a1, (pt1, ps1) =  Hashtbl.find ancto_tbl (self#find_key n'#uid) in
                      a1, pt1#position, List.length ps1
                    with
                      Not_found ->
                        let a1, p1, nb1, _ = get_ins_target n' in
                        a1, p1, nb1
                  in
                  [%debug_log "a1=%a p1=%d nb1=%d n'=%a nd=%a" nps a1 p1 nb1 nps n' nps nd];
                  array_range_exists (fun x -> is_ancestor x nd) a1#initial_children p1 (p1+nb1-1)
                with
                  _ -> false
              ))
            in
            [%debug_log "b=%B" b];
            if b then begin
              Hashtbl.add ins_target_tbl n' a;
              [%debug_log "ins_target_tbl: %a -> %a" nps n' nps a];

              [%debug_log "conflict found: key_node'=%a ss'=[%a] ss=[%a]"
                nps n' nsps ss' nsps ss];
              match k_opt with
              | Some (K_mid m) -> begin
                  let is_staying = self#is_staying_move m in
                  [%debug_log "%a: staying_move=%B" MID.ps m is_staying];

                  staying_move_only := !staying_move_only && is_staying;
                  if is_staying then
                    if not (List.mem m !conflicting_staying_moves) then
                      conflicting_staying_moves := m :: !conflicting_staying_moves
              end
              | _ -> staying_move_only := false
            end;
            b
          else
            false
        in (* has_conflicts' *)

        let conflicts' = List.filter has_conflicts' key_nodes' in

        [%debug_log "nd=%a nd'=%a conflicts'=[%a] staying_move_only=%B"
          nps nd nps nd' nsps conflicts' !staying_move_only];
        [%debug_log "conflicting_staying_moves=[%s]"
          (mids_to_string !conflicting_staying_moves)];

        conflicts', !staying_move_only, !conflicting_staying_moves, ins_target_tbl

      method private is_quasi_upstream_impossible tree' is_stable is_stable' rt' =
        [%debug_log "rt'=%a" nps rt'];
        not (is_stable' rt') &&
        let ancto_tbl =
          if tree' == tree2 then anc1to_tbl else anc2to_tbl
        in
        let b =
          try
            let pred x' =
              [%debug_log "x'=%a" nps x'];
              is_stable' x'#initial_parent
            in
            let tn' = get_p_ancestor pred rt' in
            let tk = self#find_key tn'#uid in
            let it, _ = Hashtbl.find ancto_tbl tk in
            [%debug_log "tn'=%a tk=%s it=%a"
              nps tn' (key_to_string tk) nps it];
            is_stable it
          with
            _ -> false
        in
        [%debug_log "b=%B" b];
        b

      method private get_ins_target tree nmap' is_stable' r' =
        [%debug_log "r'=%a" nps r'];
        let ss' = get_p_descendants is_stable' r' in
        (*[%debug_log "ss'=[%a]" nsps ss'];*)
        let ss = List.map nmap' ss' in
        (*[%debug_log "ss=[%a]" nsps ss];*)
        let a, tnt = self#get_latest_common_ancestor tree ss in
        (*[%debug_log "a=%a" nps a];*)
        let pos, nb =
          match tnt with
          | [] -> assert false
          | (tn, _)::tl -> begin
              let pos = tn#initial_pos in
              match tl with
              | [] -> pos, 1
              | _ ->
                  let (tn_last, _) = Xlist.last tl in
                  pos, tn_last#initial_pos - pos + 1
          end
        in
        [%debug_log "%a -> %a (pos=%d, nb=%d)" nps r' nps a pos nb];
        a, pos, nb, tnt

      method private has_destined_upstream tree' get_ins_target nmap nd nd' =
        [%debug_log "nd=%a nd'=%a" nps nd nps nd'];
        let stid_of_key, is_stable', ancto_tbl, is_ancestor_key =
          if tree' == tree2 then
            self#stid_of_key2, self#is_stable2, anc1to_tbl, self#is_ancestor_key1
          else
            self#stid_of_key1, self#is_stable1, anc2to_tbl, self#is_ancestor_key2
        in
        let key_opt = ref None in
        let cond =
          let moveon x' = not (is_stable' x') in
          let keys = Xset.create 0 in
          let prev_target = ref nd in
          let targets = Xset.create 0 in
          let pred x' =
            [%debug_log "x'=%a" nps x'];
            match self#find_key_opt x'#uid with
            | Some k -> begin
                let stid = stid_of_key k in
                let r' = self#get_subtree_root stid in
                [%debug_log "k=%s r'=%a" (key_to_string k) nps r'];
                (*not (is_stable' r'#initial_parent) && *)r' == x' &&
                let _ = Xset.add keys k in
                let occupied_posl = ref [] in
                let t, pos, nb =
                  try
                    let t, (pt, ps) = Hashtbl.find ancto_tbl k in
                    let pos = pt#position in
                    let nb = List.length ps in
                    List.iteri
                      (fun i p ->
                        match p#key_opt with
                        | Some k0 -> begin
                            let _ = k0 in
                            [%debug_log "p=%s k0=%s" p#to_string (key_to_string k0)];
                            let posi = pos + i in
                            let cp = t#initial_children.(posi) in
                            if is_ancestor cp nd then begin
                              [%debug_log "posi=%d: %a is an ancestor of %a" posi nps cp nps nd];
                              raise Exit
                            end;
                            occupied_posl := posi :: !occupied_posl
                        end
                        | _ -> ()
                      ) ps;
                    t, pos, nb
                  with
                    Not_found ->
                      let t, pos, nb, tnt = get_ins_target (self#get_subtree_root (stid_of_key k)) in
                      for i = pos to pos + nb - 1 do
                        let ci = t#initial_children.(i) in
                        let ss = try List.assq ci tnt with Not_found -> [] in
                        let ss' = List.map nmap ss in
                        [%debug_log "i=%d ci=%a ss=[%a] ss'=[%a]" i nps ci nsps ss nsps ss'];
                        let gi' = nd'#gindex in
                        let has_child_ins =
                          List.exists
                            (fun s' ->
                              s' != nd' && s'#gindex > gi' &&
                              try
                                let _ =
                                  get_p_ancestor ~moveon:(fun y' -> y' != r' && not (is_stable' y'))
                                    (fun y' ->
                                      match self#find_key_opt y'#uid with
                                      | Some k0 ->
                                          [%debug_log "y'=%a k0=%s" nps y' (key_to_string k0)];
                                          k0 <> k
                                      | _ -> false
                                    ) s'
                                in
                                true
                              with
                                Not_found -> false
                            ) ss'
                        in
                        [%debug_log "has_child_ins=%B" has_child_ins];
                        if has_child_ins then begin
                          if is_ancestor ci nd then begin
                            [%debug_log "i=%d: %a is an ancestor of %a" i nps ci nps nd];
                            raise Not_found
                          end;
                          occupied_posl := i :: !occupied_posl
                        end
                      done;
                      t, pos, nb
                in
                [%debug_log "t=%a pos=%d nb=%d" nps t pos nb];
                [%debug_log "occupied_posl=[%s]" (String.concat ";" (List.map string_of_int !occupied_posl))];
                begin
                  if
                    try
                      for i = pos to pos + nb - 1 do
                        if is_ancestor t#initial_children.(i) nd then
                          raise Exit
                      done;
                      true
                    with
                      Exit -> false
                  then
                    raise Not_found
                end;
                let _ = Xset.add targets t in
                let b =
                Xset.length keys > 1 &&
                let px' = x'#initial_parent in
                [%debug_log "px'=%a keys=[%s]" nps px' (keys_to_string (Xset.to_list keys))];
                Array.exists
                  (fun n' ->
                    [%debug_log "n'=%a" nps n'];
                    let b =
                      n' != r' && not (is_stable' n') &&
                      try
                        let k0 = self#find_key n'#uid in
                        [%debug_log "k0=%s" (key_to_string k0)];
                        if k0 = k || is_ancestor_key k0 k then
                          raise Not_found;
                        let t0, (pt0, ps0) = Hashtbl.find ancto_tbl k0 in
                        let pos0 = pt0#position in
                        let nb0 = List.length ps0 in
                        (*let t0, pos0, nb0 = get_ins_target n' in*)
                        [%debug_log "t0=%a pos0=%d nb0=%d" nps t0 pos0 nb0];
                        (*pt == t0*)
                        (*t == t0 || is_ancestor t t0*)
                        t == t0 && overlaps pos (pos+nb-1) pos0 (pos0+nb0-1) ||
                        try
                          for i = pos to pos + nb - 1 do
                            let ci = t#initial_children.(i) in
                            [%debug_log "i=%d ci=%a prev_target=%a" i nps ci nps !prev_target];
                            if
                              t != !prev_target && ci == t0 ||
                              t0 != !prev_target && is_ancestor ci t0 && is_ancestor t0 !prev_target
                            then
                              raise Exit
                          done;
                          false
                        with
                          Exit -> true
                      with _ -> false
                    in
                    [%debug_log "%a -> %B" nps n' b];
                    if b then
                      key_opt := Some k;
                    b
                  ) px'#initial_children
                in
                prev_target := t;
                b
            end
            | None -> false
          in
          try
            let u' = get_p_ancestor ~moveon pred nd' in
            [%debug_log "u'=%a" nps u'];
            Xset.length targets > 1 && u' != nd'#initial_parent
          with
            _ -> false
        in
        [%debug_log "nd'=%a cond=%B key_opt=%s" nps nd' cond (key_opt_to_string !key_opt)];
        cond, !key_opt

      method private really_has_conflict tree' conflicts' insttbl get_ins_target nmap' is_stable' nd' =
        [%debug_log "nd'=%a" nps nd'];
        let stid_of_key, ancto_tbl, pre_ancto_tbl =
          if tree' == tree2 then
            self#stid_of_key2, anc1to_tbl, pre_anc1to_tbl
          else
            self#stid_of_key1, anc2to_tbl, pre_anc2to_tbl
        in
        let b =
        match self#find_key_opt nd'#initial_parent#uid with
        | Some k -> begin
            [%debug_log "k=%s" (key_to_string k)];
            let stid = stid_of_key k in
            let r' = self#get_subtree_root stid in
            let it, pos, nb, _ = get_ins_target r' in
            let _ = pos in
            let _ = nb in
            [%debug_log "r'=%a it=%a pos=%d" nps r' nps it pos];
            List.exists
              (fun c' ->
                try
                  let ct = Hashtbl.find insttbl c' in
                  [%debug_log "c'=%a ct=%a" nps c' nps ct];
                  let b =
                    it == ct || is_ancestor it ct ||
                    is_ancestor ct it &&
                    try
                      let a =
                        try
                          if is_stable' r'#initial_parent then
                            let a = nmap' r'#initial_parent in
                            [%debug_log "a=%a" nps a];
                            a
                          else
                            raise Not_found
                        with
                          Not_found ->
                            let pk = self#find_key r'#initial_parent#uid in
                            [%debug_log "pk=%s" (key_to_string pk)];
                            try
                              let a, (_, _) = Hashtbl.find ancto_tbl pk in
                              [%debug_log "a=%a" nps a];
                              a
                            with
                              Not_found ->
                                let a = Hashtbl.find pre_ancto_tbl pk in
                                [%debug_log "a=%a" nps a];
                                a
                      in
                      is_ancestor ct a ||
                      a == ct || is_ancestor a ct ||
                      let sa' = get_p_ancestor is_stable' r' in
                      [%debug_log "sa'=%a" nps sa'];
                      nmap' sa' == ct
                    with
                      Not_found -> false
                  in
                  [%debug_log "b=%B" b];
                  b
                with _ -> true
              ) conflicts'
        end
        | _ -> true
        in
        [%debug_log "nd'=%a b=%B" nps nd' b];
        b

      method private get_parent_key_opt
          ?(force_lift=false)
          ?(parent_ins_point_opt=None)
          ?(anc_to_opt=None)
          is_stable is_stable' tree tree' nmap nmap'
          nd
          =
        [%debug_log "force_lift=%B, nd=%a" force_lift nps nd];

        (*let parent_ins_target_opt =
          match parent_ins_point_opt with
          | Some (k, x, _, _) -> Some (k, x)
          | None -> None
        in*)

        begin %debug_block
          match parent_ins_point_opt with
          | Some (_, x, p, n) -> [%debug_log "parent_ins_point=(%a,%d,%d)" nps x p n]
          | None -> [%debug_log "parent_ins_point="]
        end;

        let stid_of_mid, stid_of_key, get_ipos, get_iofs,
          is_upstream_key, (*lifted_nodes*)_, ancto_tbl, rev_ancto_tbl, simple_ins_roots,is_ancestor_key,
          get_subtree_root_by_key' =
          if tree == tree1 then
            self#stid_of_mid1,
            self#stid_of_key2,
            self#find_intermediate_pos1,
            self#find_intermediate_ofs1,
            (Xset.mem upstream_keys1),
            lifted_nodes1,
            anc1to_tbl,
            rev_anc1to_tbl,
            simple_ins_roots2,
            self#is_ancestor_key1,
            self#get_subtree_root_by_key2
          else
            self#stid_of_mid2,
            self#stid_of_key1,
            self#find_intermediate_pos2,
            self#find_intermediate_ofs2,
            (Xset.mem upstream_keys2),
            lifted_nodes2,
            anc2to_tbl,
            rev_anc2to_tbl,
            simple_ins_roots1,
            self#is_ancestor_key2,
            self#get_subtree_root_by_key1
        in
        let has_stable_descendant' n' =
          is_stable' n' || has_p_descendant is_stable' n'
        in

        let result =
          if is_stable nd then begin

            let nd' = nmap nd in

            let conflicts', staying_move_only, (*conflicting_staying_moves*)_, insttbl =
              self#get_conflicts ~parent_ins_point_opt is_stable is_stable' tree tree' nmap nmap' nd nd'
            in
            let has_conflict = conflicts' <> [] in
            [%debug_log "has_conflict: %a -> %B" nps nd has_conflict];

            let is_preceded_by_conflict key =
              try
                let stid = stid_of_key key in
                let sr' = self#get_subtree_root stid in
                let psr' = sr'#initial_parent in
                [%debug_log "stid=%d, sr'=%a, psr'=%a" stid nps sr' nps psr'];
                let pnd = nd#initial_parent in
                let get_cond0 () =
                  let b0 =
                    List.exists
                      (fun c' ->
                        try
                          psr'#initial_children.(sr'#initial_pos+1) == c' &&
                          List.exists
                            (fun sn' ->
                              (nmap' sn')#initial_parent == pnd
                            ) (get_p_descendants is_stable' c')
                        with _ -> false
                      ) conflicts'
                  in
                  [%debug_log "%s: b0=%B" (key_to_string key) b0];
                  b0
                in
                let get_cond1 () =
                  let b1 =
                    let ss' = get_p_descendants is_stable' sr' in
                    let ss = List.map nmap' ss' in
                    let a, _ = self#get_latest_common_ancestor tree ss in
                    List.exists
                      (fun c' ->
                        let ss0' = get_p_descendants is_stable' c' in
                        let ss0 = List.map nmap' ss0' in
                        let a0, _ = self#get_latest_common_ancestor tree ss0 in
                        is_ancestor a a0
                      ) conflicts'
                  in
                  [%debug_log "%s: b1=%B" (key_to_string key) b1];
                  b1
                in
                get_cond0() || get_cond1()
              with
                _ -> false
            in

            let off_staying() =
              let b =
                List.for_all
                  (fun x' ->
                    try
                      not (tree#is_initial_ancestor (nmap' x') nd)
                    with
                      Not_found -> true
                  ) conflicts'
              in
              [%debug_log "off_staying=%B" b];
              b
            in

            let has_upward_staying_move() =
              not (is_stable nd#initial_parent) &&
              let res =
                try
                  let _ =
                    get_p_ancestor
                      (fun x ->
                        match self#find_key_opt x#uid with
                        | Some (K_mid m) ->
                            if self#is_staying_move m then begin
                              [%debug_log "%a is a staying move" MID.ps m];
                              let stid = stid_of_mid m in
                              let rt, _, _ = self#get_subtree_spec stid in
                              let remote_stable_tbl1, remote_stable_tbl2 =
                                self#get_remote_stable_tbl m
                              in
                              let remote_stable_tbl' =
                                if tree == tree1 then
                                  remote_stable_tbl2
                                else
                                  remote_stable_tbl1
                              in
                              let _, _, b =
                                self#is_upward_staying_move m rt
                                  remote_stable_tbl' nmap' tree
                              in
                              if b then
                                [%debug_log "found: m=%a" MID.ps m];
                              b
                            end
                            else
                              false
                        | _ -> false
                      ) nd
                  in
                  true
                with
                  Not_found -> false
              in
              [%debug_log "has_upward_staying_move=%B" res];
              res
            in

            let to_be_lifted = self#is_node_to_be_lifted nd in
            [%debug_log "nd=%a to_be_lifted=%B" nps nd to_be_lifted];

            let get_ins_target = self#get_ins_target tree nmap' is_stable' in
            let has_destined_upstream, dk_opt =
              if has_conflict && not (self#is_canceled_stable_node nd') then
                self#has_destined_upstream tree' get_ins_target nmap nd nd'
              else
                false, None
            in
            let really_has_conflict () =
              has_conflict &&
              (*not (self#is_quasi_upstream_impossible tree' is_stable is_stable' nd'#initial_parent) &&*)
              self#really_has_conflict tree' conflicts' insttbl get_ins_target nmap' is_stable' nd'
            in
            let quasi_upstream_target_key = ref None in
            let force_lift =
              force_lift ||
              let is_dangling =
                let ks = ref [] in
                let prev = ref [] in
                let pred' x' =
                  [%debug_log "x'=%a" nps x'];
                  match self#find_key_opt x'#uid with
                  | Some k -> begin
                      [%debug_log "k=%s" (key_to_string k)];
                      if List.mem k !ks then
                        false
                      else begin
                        prev := !ks;
                        ks := k :: !ks;
                        try
                          let a, (pt, ps) = Hashtbl.find ancto_tbl k in
                          let p = pt#position in
                          let nb = List.length ps in
                          [%debug_log "a=%a p=%d nb=%d ps=%s" nps a p nb (paths_to_string ps)];

                          let x_opt = ref None in

                          let to_be_lifted0 () =
                            let b =
                              try
                                not
                                  (array_range_exists
                                     (fun x ->
                                       (x == nd || is_ancestor x nd) &&
                                       let xpos = x#initial_pos in
                                       let rp = xpos - p in
                                       [%debug_log "x=%a xpos=%d rp=%d" nps x xpos rp];
                                       let xpath = List.nth ps rp in
                                       [%debug_log "xpath=%s" xpath#to_string];
                                       let sr' = self#get_subtree_root (stid_of_key k) in
                                       [%debug_log "sr'=%a" nps sr'];
                                       let y' = self#acc sr' (Path.get_parent xpath#path) in
                                       [%debug_log "y'=%a nd'=%a" nps y' nps nd'];
                                       if is_ancestor y' nd' then begin
                                         x_opt := Some x;
                                         true
                                       end
                                       else
                                         false
                                     ) a#initial_children p (p+nb-1))
                              with _
                                -> false
                            in
                            [%debug_log "%B" b];
                            b
                          in
                          let to_be_lifted1 () =
                            let b =
                              match !x_opt with
                              | None -> false
                              | Some x -> begin
                                  [%debug_log "x=%a" nps x];
                                  try
                                    List.iter
                                      (fun (y, p) ->
                                        [%debug_log "y=%a p=%d" nps y p];
                                        let ks0 = Hashtbl.find rev_ancto_tbl (y, p) in
                                        [%debug_log "ks0=[%s]" (keys_to_string ks0)];
                                        if
                                          List.exists
                                            (fun k0 ->
                                              not (List.mem k0 !ks)
                                            ) ks0
                                        then
                                          raise Found
                                      ) (get_ancestors ~limit:(Some x) nd);
                                    false
                                  with
                                  | Found -> true
                                  | _ -> false
                              end
                            in
                            [%debug_log "%B" b];
                            b
                          in
                          let b =
                          (try not (is_ancestor_key k (List.hd !prev)) with _ -> true) &&
                          not
                            (array_range_exists
                               (fun x -> x == nd || is_ancestor x nd)
                               a#initial_children p (p+nb-1)
                            ) ||

                          array_range_exists
                            (fun x ->
                              is_ancestor x nd &&
                              (List.nth ps (x#initial_pos - p))#has_frac_ofs
                            ) a#initial_children p (p+nb-1)
                          in
                          [%debug_log "%B" b];
                          b || to_be_lifted0() || to_be_lifted1()
                        with
                          _ -> false
                      end
                  end
                  | None -> false
                in
                try
                  let a' = get_p_ancestor ~moveon:(fun x' -> not (is_stable' x')) pred' nd' in
                  let _ = a' in
                  [%debug_log "a'=%a" nps a'];
                  if List.length !ks > 1 then
                    quasi_upstream_target_key := Some (List.hd !ks);
                  true
                with
                  Not_found -> false
              in
              [%debug_log "is_dangling=%B" is_dangling];
              is_dangling
            in
            [%debug_log "nd=%a force_lift=%B" nps nd force_lift];
            [%debug_log "quasi_upstream_target_key=%s" (key_opt_to_string !quasi_upstream_target_key)];
            let key_opt, upc, sp_opt =
              if has_destined_upstream then
                dk_opt, 1, None
              else if
                force_lift ||
                ((really_has_conflict() || to_be_lifted) &&
                (
                 not staying_move_only ||
                 off_staying() ||
                 has_upward_staying_move() ||
                 is_stable' nd'#initial_parent
                ))
              then begin
                [%debug_log "nd'=%a" nps nd'];
                let res = ref ((Some K_stable), 0, None) in
                let prev' = ref nd' in
                let cur' = ref nd'#initial_parent in
                let base' = ref nd' in
                let k_opts = ref [] in
                let key_cand = ref None in
                let base_cand' = ref nd' in
                let get_subpath = self#get_subpath tree tree' nmap' in
                let keys_to_be_skipped = Xset.create 0 in
                begin
                  [%debug_log "cur'=%a" nps !cur'];

                  let pnd = nd#initial_parent in
                  [%debug_log "pnd=%a" nps pnd];

                  let move_cond() =
                    let b =
                      match self#find_key_opt pnd#uid with
                      | Some xk when is_move_key xk -> true
                      | _ -> false
                    in
                    [%debug_log "b=%B" b];
                    b
                  in

                  let single_ins() =
                    let b =
                      match self#find_key_opt nd'#initial_parent#uid with
                      | Some k -> is_stable' (get_subtree_root_by_key' k)#initial_parent
                      | _ -> false
                    in
                    [%debug_log "b=%B" b];
                    b
                  in

                  try
                    while not (is_stable' !cur') do
                      [%debug_log "cur'=%a is not stable" nps !cur'];
                      let k_opt = self#find_key_opt (!cur')#uid in
                      if k_opt <> None && not (List.mem_assoc k_opt !k_opts) then
                        base' := !prev';
                      k_opts := !k_opts @ [(k_opt, !cur')];
                      if !quasi_upstream_target_key <> None && !quasi_upstream_target_key <> k_opt then
                        ()
                      else
                      begin
                        match k_opt with
                        | Some k -> begin
                            [%debug_log "k=%s" (key_to_string k)];

                            let force_to_be_lifted = ref false in

                            if not force_lift && not (single_ins()) then begin
                              try
                                let a, (pt, ps) = Hashtbl.find ancto_tbl k in
                                let _ = pt in
                                let _ = ps in
                                [%debug_log "a=%a p=%d nb=%d" nps a pt#position (List.length ps)];
                                let confl_targets =
                                  List.map (fun c' -> let x, _, _, _ = get_ins_target c' in x) conflicts'
                                in
                                [%debug_log "confl_targets=[%a]" nsps confl_targets];
                                if
                                  is_ancestor a pnd &&
                                  confl_targets <> [] &&
                                  not (List.exists (fun ct -> is_ancestor a ct || a == ct) confl_targets)
                                then begin
                                  if
                                    try
                                      let x = pnd in
                                      [%debug_log "x=%a" nps x];
                                      move_cond() &&
                                      match anc_to_opt with
                                      | Some anc_to -> begin
                                          [%debug_log "anc_to=%a" nps anc_to];
                                          if is_ancestor x anc_to then begin
                                            let x' = nmap x in
                                            [%debug_log "x'=%a" nps x'];
                                            match self#find_key_opt x'#initial_parent#uid with
                                            | Some xk' -> begin
                                                [%debug_log "xk'=%s" (key_to_string xk')];
                                                let a1, (pt1, ps1) = Hashtbl.find ancto_tbl xk' in
                                                let _ = pt1 in
                                                let _ = ps1 in
                                                [%debug_log "a1=%a p1=%d nb1=%d"
                                                  nps a1 pt1#position (List.length ps1)];
                                                if a1 == x#initial_parent then begin
                                                  let r' = get_subtree_root_by_key' xk' in
                                                  [%debug_log "r'=%a" nps r'];
                                                  has_p_descendant ~moveon:(fun x' -> not (is_stable' x'))
                                                    (fun x' ->
                                                      is_stable' x' && self#is_quasi_upstream (nmap' x')
                                                    ) r'
                                                end
                                                else
                                                  false
                                            end
                                            | _ -> false
                                          end
                                          else
                                            false
                                      end
                                      | _ -> false

                                    with _ -> false
                                  then begin
                                    [%debug_log "force_to_be_lifted -> true"];
                                    force_to_be_lifted := true
                                  end
                                  else begin
                                    [%debug_log "!"];
                                    res := (None, 0, None);
                                    raise Exit
                                  end
                                end
                              with Not_found -> ()
                            end;

                            let key_with_changed_sub_path =
                              Xset.mem keys_with_changed_sub_path k
                            in
                            [%debug_log "key_with_changed_sub_path=%B"
                              key_with_changed_sub_path];

                            let xs' =
                              get_p_descendants
                                (fun n' -> List.memq n' conflicts') !cur'
                            in
                            [%debug_log "xs'=[%a]" nsps xs'];

                            let to_be_skipped, simple_ins =
                              try
                                let sr' = self#get_subtree_root (stid_of_key k) in
                                Xset.mem keys_to_be_skipped k ||
                                (get_p_descendants is_stable' sr') = [nd'],
                                Xset.mem simple_ins_roots sr'
                              with
                                _ -> false, false
                            in
                            if to_be_skipped then
                              Xset.add keys_to_be_skipped k;

                            [%debug_log "simple_ins: %s -> %B" (key_to_string k) simple_ins];
                            let to_be_skipped = not simple_ins && to_be_skipped in
                            [%debug_log "to_be_skipped: %s -> %B" (key_to_string k) to_be_skipped];

                            let should_be_lifted () =
                              let to_be_lifted =
                                !force_to_be_lifted ||
                                is_preceded_by_conflict k ||
                                (has_upward_staying_move() &&
                                 let a =
                                   let ss' = get_p_descendants is_stable' !cur' in
                                   let ss = List.map nmap' ss' in
                                   [%debug_log "ss=[%a]" nsps ss];
                                   let a, _ = self#get_latest_common_ancestor tree ss in
                                   [%debug_log "a=%a" nps a];
                                   a
                                 in
                                 List.exists
                                   (fun n' ->
                                     [%debug_log "n'=%a" nps n'];
                                     let ss0' = get_p_descendants is_stable' n' in
                                     let ss0 = List.map nmap' ss0' in
                                     [%debug_log "ss0=[%a]" nsps ss0];
                                     let a0, _ = self#get_latest_common_ancestor tree ss0 in
                                     let b = is_ancestor a a0 in
                                     [%debug_log "b=%B" b];
                                     b
                                   ) conflicts')(* ||
                                   try
                                     let a, (pt, ps) = Hashtbl.find ancto_tbl k in
                                     let pos = pt#position in
                                     let np = List.length ps in
                                     [%debug_log "a=%a pos=%d np=%d nd=%a" nps a pos np nps nd];
                                     try
                                       for i = pos to pos + np - 1 do
                                         let ci = a#initial_children.(i) in
                                         [%debug_log "i=%d ci=%a" i nps ci];
                                         let ks = Hashtbl.find rev_ancto_tbl (a, i) in
                                         if ks = [k] && is_ancestor ci nd then
                                           raise Exit
                                       done;
                                       true
                                     with
                                       Exit -> false
                                   with
                                     _ -> false*)
                              in
                              [%debug_log "%a: should_be_lifted=%B" nps nd to_be_lifted];
                              to_be_lifted
                            in (* should_be_lifted *)

                            if not to_be_skipped && (force_lift || xs' <> [] || should_be_lifted()) then begin
                              (*let a' = List.assoc k_opt !k_opts in*)
                              [%debug_log "a'=%a base'=%a" nps (List.assoc k_opt !k_opts) nps !base'];
                              let sp_opt =
                                let not_deferred =
                                  match parent_ins_point_opt with
                                  | None -> false
                                  | Some (mkey, ancto, pos, nb) -> begin
                                      [%debug_log "mkey=%s ancto=%a pos=%d nb=%d" (key_to_string mkey) nps ancto pos nb];
                                      if mkey <> k && not (is_ancestor_key mkey k) then
                                        false
                                      else
                                        let b =
                                          not (is_ancestor ancto nd) ||
                                          try
                                            let p = (get_ancestor_below nd ancto)#initial_pos in
                                            [%debug_log "p=%d" p];
                                            nb > 1 && pos <= p && p <= pos + nb - 1 &&
                                            let r' = self#get_subtree_root (stid_of_key k) in
                                            let pk = self#find_key nd#initial_parent#uid in
                                            let pk' = self#find_key r'#initial_parent#uid in
                                            [%debug_log "r'=%a pk=%s pk'=%s" nps r' (key_to_string pk) (key_to_string pk')];
                                            pk = pk' &&
                                            let pr' = self#get_subtree_root (stid_of_key pk) in
                                            [%debug_log "pr'=%a" nps pr'];
                                            let ss' =
                                              get_p_descendants
                                                (fun x' ->
                                                  is_stable' x' && not (self#is_canceled_stable_node x') &&
                                                  not (is_ancestor r' x')) pr'
                                            in
                                            [%debug_log "ss'=[%a]" nsps ss'];
                                            let pl =
                                              List.fold_left
                                                (fun l s' ->
                                                  let s = nmap' s' in
                                                  let p0 = (get_ancestor_below s ancto)#initial_pos in
                                                  [%debug_log "s=%a s'=%a p0=%d" nps s nps s' p0];
                                                  if List.mem p0 l then
                                                    l
                                                  else
                                                    p0::l
                                                ) [] ss'
                                            in
                                            [%debug_log "pl=[%s]" (String.concat ";" (List.map string_of_int pl))];
                                            pl = [p]
                                          with
                                            Not_found -> false
                                        in
                                        [%debug_log "b=%B" b];
                                        b
                                  end
                                in
                                [%debug_log "not_deferred=%B" not_deferred];
                                if not (Hashtbl.mem ancto_tbl k) && not not_deferred then (* defer *)
                                  None
                                else if
                                  try
                                    let a0, (pt0, ps0) = Hashtbl.find ancto_tbl k in
                                    let pos0, nb0 = pt0#position, List.length ps0 in
                                    let _ = nb0 in
                                    [%debug_log "a0=%a pos0=%d nb0=%d" nps a0 pos0 nb0];
                                    let p = (get_ancestor_below nd a0)#initial_pos in
                                    let i = p - pos0 in
                                    [%debug_log "p=%d i=%d" p i];
                                    let pathi = List.nth ps0 i in
                                    let b =
                                      match pathi#key_opt with
                                      | Some k0 ->
                                          [%debug_log "k0=%s" (key_to_string k0)];
                                          List.exists
                                            (fun c' ->
                                              try
                                                let ck = self#find_key c'#uid in
                                                [%debug_log "ck=%s" (key_to_string ck)];
                                                ck = k0
                                              with
                                                Not_found -> false
                                            ) conflicts'
                                      | None ->
                                          List.exists
                                            (fun c' ->
                                              try
                                                let ck = self#find_key c'#uid in
                                                [%debug_log "ck=%s" (key_to_string ck)];
                                                let a1, pos1, nb1 =
                                                  try
                                                    let a1, (pt1, ps1) = Hashtbl.find ancto_tbl ck in
                                                    a1, pt1#position, List.length ps1
                                                  with
                                                    Not_found ->
                                                      let a1, pos1, nb1, _ = get_ins_target c' in
                                                      a1, pos1, nb1
                                                in
                                                [%debug_log "a1=%a pos1=%d nb1=%d" nps a1 pos1 nb1];
                                                array_range_exists
                                                  (fun x -> is_ancestor x a0)
                                                  a1#initial_children pos1 (pos1+nb1-1)
                                              with
                                                Not_found -> false
                                            ) conflicts'
                                    in
                                    [%debug_log "b=%B" b];
                                    b
                                  with
                                    _ -> false
                                then
                                  None
                                else if
                                  force_lift ||
                                  to_be_lifted ||
                                  key_with_changed_sub_path ||
                                  (*List.for_all
                                    (fun c' ->
                                      [%debug_log "c'=%a" nps c'];
                                      let b = not (tree'#is_initial_ancestor a' c') in
                                      [%debug_log "a' is%s an ancestor of c'"
                                        (if b then " not" else "")];
                                      b
                                    ) conflicts' ||*)
                                  List.exists (*!!!!!!*)
                                    (fun c' ->
                                      [%debug_log "c'=%a" nps c'];
                                      let ck_opt = self#find_key_opt c'#uid in
                                      [%debug_log "key of c': %s" (key_opt_to_string ck_opt)];
                                      let b0 = ck_opt = k_opt in
                                      let b1 = not (tree'#is_initial_ancestor c' !base') in
                                      [%debug_log "c' is%s an ancestor of base'"
                                        (if b1 then " not" else "")];
                                      (b0 || has_upward_staying_move()) && b1
                                    ) conflicts'
                                then
                                  let ins_point_opt =
                                    match parent_ins_point_opt with
                                    | Some (_, ancto, pos, nb) -> Some (ancto, pos, nb)
                                    | None -> None
                                  in
                                  Some (get_subpath ~ins_point_opt k !base')
                                else if
                                  List.exists
                                    (fun c' ->
                                      try
                                        let _ = get_ipos c' in
                                        true
                                      with
                                        Not_found -> false
                                    ) conflicts'
                                then
                                  let stid = stid_of_key k in
                                  let rt' = self#get_subtree_root stid in
                                  [%debug_log "rt'=%a bn'=%a" nps rt' nps !base'];
                                  let rp = get_rel_path rt'#apath (!base')#apath in
                                  [%debug_log "rp=%s" (Path.to_string rp)];
                                  let is_excluded _ x' =
                                    let xs' =
                                      List.filter
                                        (fun c' ->
                                          try
                                            let _ = get_ipos c' in
                                            true
                                          with
                                            Not_found -> false
                                        ) conflicts'
                                    in
                                    if List.memq x' xs' then
                                      false
                                    else
                                      self#is_excluded x'(* &&
                                      let a, (pt, ps) = Hashtbl.find ancto_tbl k in
                                      let pos = pt#position in
                                      let np = List.length ps in
                                      [%debug_log "k=%s a=%a pos=%d np=%d x'=%a" (key_to_string k) nps a pos np nps x'];
                                      let ss =
                                        if is_stable x' then
                                          [nmap' x']
                                        else
                                          List.map nmap' (get_p_descendants is_stable' x')
                                      in
                                      [%debug_log "ss=[%a]" nsps ss];
                                      try
                                        for i = pos to pos + np - 1 do
                                         let ci = a#initial_children.(i) in
                                         [%debug_log "i=%d ci=%a" i nps ci];
                                         let ks = Hashtbl.find rev_ancto_tbl (a, i) in
                                         if ks = [k] then
                                           if List.for_all (is_ancestor ci) ss then begin
                                             [%debug_log "found: ci=%a" nps ci];
                                             raise Exit
                                           end
                                        done;
                                        true
                                      with
                                        Exit -> false*)
                                  in
                                  let ap =
                                    self#get_adjusted_path
                                      ~is_excluded get_ipos get_iofs is_stable' rt' rp
                                  in
                                  [%debug_log "ap=%s" (Path.to_string ap)];
                                  Some ap
                                else
                                  None
                              in (* sp_opt *)
                              [%debug_log "k=%s" (key_to_string k)];
                              let upc =
                                match self#find_key_opt nd'#initial_parent#uid with
                                | Some ((K_stid _ | K_mid _) as pk) when pk <> k(* && sp_opt = None*) -> 1
                                | _ -> 0
                              in
                              res := ((Some k), upc, sp_opt);
                              raise Exit
                            end
                            else begin (* xs' = [] *)
                              let has_parent =
                                let ss' = get_p_descendants is_stable' !cur' in
                                [%debug_log "ss'=[%a]" nsps ss'];
                                if List.length ss' > 1 then begin
                                  let ss = List.map nmap' ss' in
                                  [%debug_log "ss=[%a]" nsps ss];
                                  let a, tnt =
                                    self#get_latest_common_ancestor tree ss
                                  in
                                  let is_simple_ins =
                                    a == nd#initial_parent &&
                                    self#are_contiguous_children ss
                                  in
                                  [%debug_log "is_simple_ins=%B" is_simple_ins];

                                  let has_ins_conflict =
                                    List.exists
                                      (fun c' ->
                                        let css' = get_p_descendants is_stable' c' in
                                        [%debug_log "css'=[%a]" nsps css'];
                                        if css' = [] then
                                          false
                                        else
                                          let css = List.map nmap' css' in
                                          [%debug_log "css=[%a]" nsps css];
                                          let ca, _ =
                                            self#get_latest_common_ancestor tree css
                                          in
                                          (List.hd css)#gindex < (List.hd ss)#gindex &&
                                          ca == a
                                      ) conflicts'
                                  in
                                  [%debug_log "has_ins_conflict=%B" has_ins_conflict];

                                  if is_simple_ins then
                                    false
                                  else if has_ins_conflict || to_be_lifted then begin
                                    [%debug_log "k=%s" (key_to_string k)];
                                    if !key_cand = None then begin
                                      [%debug_log "key_cand -> %s" (key_to_string k)];
                                      key_cand := Some k;
                                      base_cand' := !base'
                                    end;
                                    if to_be_lifted then begin
                                      match !key_cand with
                                      | Some k0 -> begin
                                          [%debug_log "k0=%s" (key_to_string k0)];
                                          try
                                            let a, _ = Hashtbl.find ancto_tbl k0 in
                                            [%debug_log "nd=%a a=%a" nps nd nps a];
                                            if nd#initial_parent == a then begin
                                              let k1 = self#get_key_of_node_to_be_lifted nd in
                                              [%debug_log "k1=%s base_cand'=%a" (key_to_string k1) nps !base_cand'];
                                              let bn =
                                                if Hashtbl.mem comp_cand_tbl !base_cand' then
                                                  !cur'
                                                else
                                                  !base_cand'
                                              in
                                              [%debug_log "bn=%a" nps bn];
                                              res := (Some k1, 1, Some (get_subpath k1 bn));
                                              raise Exit
                                            end
                                          with Not_found -> ()
                                      end
                                      | None -> ()
                                    end;
                                    true
                                  end
                                  else begin
                                    if !key_cand = None then begin
                                      [%debug_log "key_cand -> %s" (key_to_string k)];
                                      key_cand := Some k;
                                      base_cand' := !base'
                                    end;

                                    let pnd' = !cur'#initial_parent in
                                    [%debug_log "pnd'=%a" nps pnd'];
                                    if is_stable' pnd' then begin
                                      let stid = stid_of_key k in
                                      let r1', xs1', sz1' =
                                        self#get_subtree_spec stid
                                      in
                                      let _ = r1' in
                                      let _ = sz1' in
                                      [%debug_log "stid=%d r1'=%a xs1'=[%a] sz1'=%d"
                                        stid nps r1' nsps xs1' sz1'];
                                      let sxs1' =
                                        List.filter has_stable_descendant' xs1'
                                      in
                                      [%debug_log "sxs1'=[%a]" nsps sxs1'];
                                      if (List.length sxs1') > 1 then begin
                                        let f i _ =
                                          try
                                            let tn, ms = List.nth tnt i in
                                            let _ = tn in
                                            [%debug_log "i=%d tn=%a ms=[%a]" i nps tn nsps ms];
                                            match ms with
                                            | [] | [_] -> ms
                                            | (*h*)_::t ->
                                                (*let h' = nmap h in
                                                let p' = h'#initial_parent in
                                                [%debug_log "h=%a h'=%a p'=%a" nps h nps h' nps p'];
                                                if
                                                  List.for_all
                                                    (fun x ->
                                                      let x' = nmap x in
                                                      let px' = x'#initial_parent in
                                                      [%debug_log "x=%a x'=%a px'=%a" nps x nps x' nps px'];
                                                      px' == p'
                                                    ) ms
                                                then
                                                  ms
                                                else []*)
                                                  let last = Xlist.last t in
                                                  let last' = nmap last in
                                                  let p' = last'#initial_parent in
                                                  let _ = last' in
                                                  let _ = p' in
                                                  [%debug_log "last=%a last'=%a p'=%a"
                                                    nps last nps last' nps last'#initial_parent];
                                                  (*List.filter (fun x -> (nmap x)#initial_parent == p') *)ms
                                          with
                                            Failure _ -> []
                                        in
                                        let cnds = List.flatten (List.mapi f xs1') in
                                        [%debug_log "nd=%a cnds=[%a]" nps nd nsps cnds];

                                        not (List.memq nd cnds)
                                      end
                                      else begin (* if (List.length sxs1') = 1 *)
                                        match !k_opts with
                                        | (Some k2, _)::_ -> begin
                                            let stid2 = stid_of_key k2 in
                                            let r2', _, _ =
                                              self#get_subtree_spec stid2
                                            in
                                            [%debug_log "r2'=%a" nps r2'];
                                            let it2, _, _, _ = get_ins_target r2' in
                                            List.exists
                                              (fun c' ->
                                                tree#is_initial_ancestor
                                                  it2 (let t, _, _, _ = get_ins_target c' in t)
                                              ) conflicts'
                                        end
                                        | _ -> false
                                      end
                                    end
                                    else (* if is_stable' pnd' *)
                                      false
                                  end
                                end
                                else (* if List.length ss' > 1 *)
                                  false
                              in (* has_parent *)
                              [%debug_log "has_parent=%B" has_parent];
                              if has_parent then begin
                                match !key_cand with
                                | Some k -> begin
                                    [%debug_log "k=%s" (key_to_string k)];
                                    res := (!key_cand, 0, Some (get_subpath k !base_cand'))
                                end
                                | None -> assert false
                              end
                              else begin
                                let has_upper_upstream, last_k_opt =
                                  List.fold_left
                                    (fun (b, _k_opt) k_opt ->
                                      match k_opt with
                                      | (Some k, _) ->
                                          if is_upstream_key k then
                                            true, k_opt
                                          else
                                            b, _k_opt
                                      | _ -> b, _k_opt
                                    ) (false, (None, !cur')) !k_opts
                                in
                                let check_last_key () =
                                  let b =
                                    match last_k_opt with
                                    | (Some k, n') -> begin
                                        try
                                          let a, _ = Hashtbl.find ancto_tbl k in
                                          nmap a == n'#initial_parent
                                        with
                                          Not_found -> false
                                    end
                                    | _ -> false
                                  in
                                  [%debug_log "b=%B" b];
                                  b
                                in
                                let check_keys () =
                                  let b, _, _ =
                                    List.fold_left
                                      (fun ((found, fa, ks) as acc) -> function
                                        | (Some k, n') -> begin
                                            let r' = self#get_subtree_root (stid_of_key k) in
                                            if n' != r' || found then
                                              acc
                                            else begin
                                              [%debug_log "k=%s n'=%a" (key_to_string k) nps n'];
                                              let a, p, nb =
                                                try
                                                  let a0, (pt, ps) = Hashtbl.find ancto_tbl k in
                                                  a0, pt#position, List.length ps
                                                with
                                                  Not_found ->
                                                    let a0, p, nb, _ = get_ins_target n' in
                                                    a0, p, nb
                                              in
                                              [%debug_log "a=%a p=%d nb=%d fa=%a" nps a p nb nps fa];
                                              if fa == nd then
                                                let b0 =
                                                  let gi' = nd'#gindex in
                                                  try
                                                    for i = p to p + nb - 1 do
                                                      let ci = a#initial_children.(i) in
                                                      if is_ancestor ci nd then
                                                        for g = nd#gindex + 1 to ci#gindex - 1 do
                                                          let x = tree#search_node_by_gindex g in
                                                          if is_stable x then
                                                            let x' = nmap x in
                                                            let px' = x'#initial_parent in
                                                            match self#find_key_opt px'#uid with
                                                            | Some pxk when pxk = k -> begin
                                                                if
                                                                  nd'#initial_parent != px' &&
                                                                  gi' < x'#gindex
                                                                then begin
                                                                  [%debug_log "x'=%a" nps x'];
                                                                  raise Exit
                                                                end
                                                            end
                                                            | Some pxk -> begin
                                                                [%debug_log "pxk=%s" (key_to_string pxk)];
                                                                let a1, p1, nb1 =
                                                                  try
                                                                    let a1, (pt1, ps1) = Hashtbl.find ancto_tbl pxk in
                                                                    a1, pt1#position, List.length ps1
                                                                  with
                                                                    Not_found ->
                                                                      let pxr' =
                                                                        self#get_subtree_root (stid_of_key pxk)
                                                                      in
                                                                      let a1, p1, nb1, _ = get_ins_target pxr' in
                                                                      a1, p1, nb1
                                                                in
                                                                if
                                                                  not
                                                                    (is_ancestor ci a1 &&
                                                                     array_range_exists (fun y -> is_ancestor y nd)
                                                                       a1#initial_children p1 (p1+nb1-1))
                                                                then begin
                                                                  [%debug_log "x'=%a" nps x'];
                                                                  raise Exit
                                                                end
                                                            end
                                                            | _ -> ()
                                                        done
                                                    done;
                                                    false
                                                  with
                                                    Exit -> true
                                                in
                                                [%debug_log "b0=%B" b0];
                                                found || b0, a, k::ks
                                              else
                                                if is_ancestor a fa then
                                                  match ks with
                                                  | k0::_ ->
                                                      let r0' = self#get_subtree_root (stid_of_key k0) in
                                                      [%debug_log "k0=%s r0'=%a" (key_to_string k0) nps r0'];
                                                      not (is_stable' r0'#initial_parent), fa, k::ks
                                                  | [] -> assert false
                                                else
                                                  false, fa, k::ks
                                            end
                                        end
                                        | None, _ -> acc
                                      ) (false, nd, []) !k_opts
                                  in
                                  [%debug_log "b=%B" b];
                                  b
                                in
                                [%debug_log "has_upper_upstream=%B" has_upper_upstream];
                                if has_upper_upstream then
                                  res := (None, 0, None)
                                  (*res := (self#find_key_opt nd'#initial_parent#uid, 0, None)*)
                                else if check_last_key() then
                                  res := (None, 0, None)
                                else if has_upward_staying_move() then
                                  res := (None, 0, None)
                                else if try check_keys() with _ -> true then
                                  res := (None, 0, None)
                                else
                                  res := ((Some K_stable), 1, None)
                              end
                            end (* else (xs' = []) *)
                        end
                        | None -> ()
                      end;
                      prev' := !cur';
                      cur' := (!cur')#initial_parent
                    done
                  with
                    Exit -> ()
                end;
                [%debug_log "k_opts: [%s]"
                  (String.concat ";"
                     (List.map
                        (fun (k_opt, n) ->
                          sprintf "%s:%a" (key_opt_to_string k_opt) nps n
                        ) !k_opts))];
                !res
              end
              else
                let key = ref K_stable in
                let base' = ref nd' in
                if
                  let pnd' = nd'#initial_parent in
                  [%debug_log "nd'=%a pnd'=%a" nps nd' nps pnd'];
                  match self#find_key_opt pnd'#uid with
                  | Some pk -> begin
                      [%debug_log "pk=%s" (key_to_string pk)];
                      try
                        let a0, p0, nb0 =
                          try
                            let a0, (pt0, ps0) = Hashtbl.find ancto_tbl pk in
                            a0, pt0#position, List.length ps0
                          with
                            Not_found ->
                              let a0, p0, nb0, _ = get_ins_target (get_subtree_root_by_key' pk) in
                              a0, p0, nb0
                        in
                        let _ = p0 in
                        let _ = nb0 in
                        [%debug_log "a0=%a p0=%d nb0=%d" nps a0 p0 nb0];
                        let r0' = self#get_subtree_root (stid_of_key pk) in
                        [%debug_log "r0'=%a" nps r0'];
                        base' := r0';
                        let pr0' = r0'#initial_parent in
                        [%debug_log "pr0'=%a" nps pr0'];
                        match self#find_key_opt pr0'#uid with
                        | Some ppk -> begin
                            [%debug_log "ppk=%s" (key_to_string ppk)];
                            key := ppk;
                            try
                              let a1, (pt1, ps1) = Hashtbl.find ancto_tbl ppk in
                              let pos1 = pt1#position in
                              [%debug_log "a1=%a pos1=%d ps1=%s" nps a1 pos1 (boundary_to_string ps1)];
                              let r1' = self#get_subtree_root (stid_of_key ppk) in
                              [%debug_log "r1'=%a" nps r1'];
                              try
                                List.iteri
                                  (fun i p1 ->
                                    if p1#key_opt = None then
                                      let ci = a1#initial_children.(pos1+i) in
                                      [%debug_log "i=%d p=%s ci=%a" i p1#to_string nps ci];
                                      if (ci == a0 || is_ancestor ci a0) then begin
                                        let p' = self#acc r1' (Path.get_parent p1#path) in
                                        [%debug_log "p'=%a" nps p'];
                                        if pr0' != p' then begin
                                          [%debug_log "found: ci=%a p1=%s" nps ci p1#to_string];
                                          raise Exit
                                        end
                                      end
                                  ) ps1;
                                false
                              with
                                Exit -> true
                            with
                              Not_found ->
                                let a1, pos1, nb1, _ = get_ins_target (get_subtree_root_by_key' ppk) in
                                let _ = pos1 in
                                let _ = nb1 in
                                [%debug_log "a1=%a pos1=%d nb1=%d" nps a1 pos1 nb1];
                                List.exists
                                  (fun c' ->
                                    let a2, pos2, nb2 =
                                      try
                                        let a2, (pt2, ps2) = Hashtbl.find ancto_tbl (self#find_key c'#uid) in
                                        a2, pt2#position, List.length ps2
                                      with
                                        Not_found ->
                                          let a2, pos2, nb2, _ = get_ins_target c' in
                                          a2, pos2, nb2
                                    in
                                    [%debug_log "c'=%a a2=%a pos2=%d nb2=%d" nps c' nps a2 pos2 nb2];
                                    let ca2 = a2#initial_children in
                                    is_ancestor a1 a2 &&
                                    array_range_exists
                                      (fun x ->
                                        x == a0 || is_ancestor x a0
                                      ) ca2 pos2 (pos2+nb2-1)
                                  ) conflicts'
                        end
                        | None -> false
                      with
                        Not_found -> false
                  end
                  | None -> false
                then begin
                  [%debug_log "key=%s" (key_to_string !key)];
                  Some !key, 1, Some (self#get_subpath tree tree' nmap' !key !base')
                end
                else (* not has_conflict || staying_move_only *)
                  None, 0, None
            in (* key_opt, upc, sp_opt *)
            [%debug_log "parent key of %a: %s (upstream count: %d) (sub path: %s)"
              nps nd (key_opt_to_string key_opt) upc
              (path_opt_to_string sp_opt)];

            key_opt, upc, sp_opt
          end
          else (* not (is_stable nd) *)
            None, 0, None
        in
        Hashtbl.add parent_spec_tbl nd result;
        result

      method private _has_offset_parent_ins parent_key_tbl nd =
        let b =
          match self#find_key_opt nd#uid with
          | Some key -> begin
              try
                let tbl = Hashtbl.find parent_key_tbl key in
                Hashtbl.iter
                  (fun k pl ->
                    let _ = k in
                    match pl with
                    | [] -> ()
                    | _ ->
                        if List.for_all (fun p -> try Path.get_offset p <> 0.0 with _ -> false) pl then begin
                          [%debug_log "k=%s pl=[%s]"
                            (key_to_string k) (String.concat ";" (List.map Path.to_string pl))];
                          raise Exit
                        end
                  ) tbl;
                false
              with
              | Exit -> true
              | Not_found -> false
          end
          | None -> false
        in
        [%debug_log "%a -> %B" nps nd b];
        b

      method private has_offset_parent_ins1 = self#_has_offset_parent_ins parent_key_tbl1
      method private has_offset_parent_ins2 = self#_has_offset_parent_ins parent_key_tbl2

      method private _has_parent_ins parent_key_tbl ?(multi=false) nd =
        let b =
          match self#find_key_opt nd#uid with
          | Some key -> begin
              try
                let tbl = Hashtbl.find parent_key_tbl key in
                Hashtbl.iter
                  (fun k pl ->
                    let _ = k in
                    match pl with
                    | [] -> ()
                    | [p] when not multi ->
                        let _ = p in
                        [%debug_log "k=%s p=%s" (key_to_string k) (Path.to_string p)];
                        raise Exit
                    | [p] when try Path.get_offset p = 0.0 with _ -> false ->
                        [%debug_log "k=%s p=%s (no offset)" (key_to_string k) (Path.to_string p)];
                        raise Exit
                    | [_] -> ()
                    (*| _ when List.for_all (fun p -> try Path.get_offset p <> 0.0 with _ -> false) pl -> ()*)
                    | _ ->
                        [%debug_log "k=%s pl=[%s]"
                          (key_to_string k) (String.concat ";" (List.map Path.to_string pl))];
                        raise Exit
                  ) tbl;
                false
              with
              | Exit -> true
              | Not_found -> false
          end
          | None -> false
        in
        [%debug_log "%a -> %B (multi=%B)" nps nd b multi];
        b

      method private has_parent_ins1 = self#_has_parent_ins parent_key_tbl1
      method private has_parent_ins2 = self#_has_parent_ins parent_key_tbl2

      method private _is_ancestor_key finder ak k =
        let rec f k =
          try
            let k' = finder k in
            if k' = ak then
              true
            else
              f k'
          with
            _ -> false
        in
        let b = f k in
        [%debug_log "ak=%s k=%s -> %B" (key_to_string ak) (key_to_string k) b];
        b

      method private is_ancestor_key1 ak k =
        self#_is_ancestor_key (fun k -> let t = Hashtbl.find parent_key_tbl1 k in List.hd (tbl_keys t)) ak k ||
        self#_is_ancestor_key (Hashtbl.find edit_parent_tbl1) ak k

      method private is_ancestor_key2 ak k =
        self#_is_ancestor_key (fun k -> let t = Hashtbl.find parent_key_tbl2 k in List.hd (tbl_keys t)) ak k ||
        self#_is_ancestor_key (Hashtbl.find edit_parent_tbl2) ak k

      method dump_delta_ch (* dump delta to channel *)
          ?(extra_ns_decls=[])
          ?(fact_file_name="")
          ?(info_file_name="")
          (nmapping : 'node Node_mapping.c)
          (ch : Xchannel.out_channel)
          =
        let node_diff_elem_attrs node1 node2 =
          let a1 = node1#data#orig_elem_attrs_for_delta in
          let a2 = node2#data#orig_elem_attrs_for_delta in
          Fmt.diff_attrs
            ~irreversible_flag
            (new path_c node1#apath) a1 (new path_c node2#apath) a2
        in

        let is_left tree n nd =
          n#gindex < nd#gindex &&
          not (tree#is_initial_ancestor nd n)
        in
        let is_right tree n nd =
          nd#gindex < n#gindex &&
          not (tree#is_initial_ancestor n nd)
        in

        let get_remote_stable_tbl is_stable nodes =
          [%debug_log "[%s]" (nodes_to_uids_string nodes)];

          let rec find nd =
            if is_stable nd then
              if not (self#is_canceled_stable_node nd) then
                [nd]
              else
                []
            else
              List.concat_map find (Array.to_list nd#initial_children)
          in
          let tbl =
            List.filter
              (fun (_, nl) -> nl <> []) (List.map (fun n -> n, find n) nodes)
          in

          begin %debug_block
            List.iter
              (fun (n, nds) ->
                [%debug_log "%a --> [%a]" nps n nsps nds]
              ) tbl;
          end;

          tbl
        in

        let get_base_pos' is_stable' base_nd' =
          [%debug_log "base_nd'=%a" nps base_nd'];
          let pnd' = base_nd'#initial_parent in
          let p' = ref base_nd'#initial_pos in
          let children' = pnd'#initial_children in
          for i = 0 to !p' - 1 do
            let x' = children'.(i) in
            [%debug_log "i=%d x'=%a" i nps x'];
            if
              self#is_excluded x' &&
              not (is_stable' x') &&
              not (has_p_descendant is_stable' x')
            then
              decr p'
          done;
          !p'
        in

        let check_stable_node_cache = Hashtbl.create 0 in
        let check_stable_node
            ?(set_nodes_to_be_lifted=true)
            is_stable' tree nmap' nd'
            =
          [%debug_log "nd'=%a" nps nd'];

          let lifted_nodes, tree', is_ancestor_key, (*ancto_tbl*)_ =
            if tree == tree1 then
              lifted_nodes1, tree2, self#is_ancestor_key1, anc1to_tbl
            else
              lifted_nodes2, tree1, self#is_ancestor_key2, anc2to_tbl
          in
          let is_stable'_ x' =
            is_stable' x' && not (self#is_canceled_stable_node x') &&
            not (Xset.mem lifted_nodes x')
          in
          try
            let result = Hashtbl.find check_stable_node_cache nd' in
            [%debug_log "result=%B (cached)" result];
            result
          with
            Not_found -> begin
            let result = ref false in
            let nd = nmap' nd' in
            begin
              try
                let stid = self#find_stid nd'#initial_parent#uid in
                let (sr', xs', _) = self#get_subtree_spec stid in
                [%debug_log "sr'=%a" nps sr'];
                (*let ss' = get_p_descendants is_stable' sr' in*)
                let ss' =
                  get_p_descendants ~moveon:(fun x' -> not (is_stable' x')) is_stable'_ sr'
                in
                [%debug_log "ss'=[%a]" nsps ss'];

                let to_be_lifted0 =
                  if ss' = [] then
                    false
                  else
                  let a' = get_p_ancestor is_stable' nd' in
                  let a = nmap' a' in
                  [%debug_log "a'=%a a=%a" nps a' nps a];
                  let ss = List.map nmap' ss' in
                  [%debug_log "ss=[%a]" nsps ss];
                  let ca, (*tnt*)_ = self#get_latest_common_ancestor tree ss in
                  if ca == a then begin
                    try
                      let k = self#find_key sr'#uid in
                      [%debug_log "k=%s" (key_to_string k)];
                      let rec get_sr1' x' =
                        [%debug_log "x'=%a" nps x'];
                        match self#find_key_opt x'#initial_parent#uid with
                        | Some k1 ->
                            [%debug_log "k1=%s" (key_to_string k1)];
                            if is_ancestor_key k1 k then
                              get_sr1' x'#initial_parent
                            else
                              let stid1 = self#find_stid x'#initial_parent#uid in
                              let sr1', _, _ = self#get_subtree_spec stid1 in
                              sr1'
                        | None -> raise Not_found
                      in
                      let sr1' = get_sr1' sr' in
                      (*let stid1 = self#find_stid sr'#initial_parent#uid in
                      let sr1', _, _ = self#get_subtree_spec stid1 in*)

                      [%debug_log "sr1'=%a" nps sr1'];
                      if is_stable' sr1'#initial_parent then
                        false
                      else
                        let ss1' = get_p_descendants is_stable' sr1' in
                        let ss1 = List.map nmap' ss1' in
                        [%debug_log "ss1=[%a]" nsps ss1];
                        let b =
                          List.exists
                            (fun x ->
                              is_left tree x nd && x#initial_parent != nd#initial_parent
                            ) (Xlist.subtractq ss1 ss)
                        in
                        [%debug_log "b=%B" b];
                        b
                    with
                      Not_found -> false
                  end
                  else
                    false
                in
                if to_be_lifted0 then
                  result := true
                else

                let ndgi' = nd'#gindex in
                let lss' = List.rev (List.filter (fun x' -> x'#gindex < ndgi') ss') in
                [%debug_log "lss'=[%a]" nsps lss'];

                match lss' with
                | [] | [_] -> ()
                | _ -> begin
                  let ss = List.map nmap' ss' in
                  [%debug_log "ss=[%a]" nsps ss];
                  let ca, tnt = self#get_latest_common_ancestor tree ss in
                  let lss = List.map nmap' lss' in
                  let ln = Xlist.last lss in

                  let b =
                    if
                      List.for_all (fun ln' -> ln'#initial_parent == nd'#initial_parent) lss'
                    then
                      List.for_all
                        (fun (_, ns) -> not (List.memq ln ns) || List.memq nd ns) tnt
                    else
                      true
                  in
                  [%debug_log "b=%B" b];

                  if b then

                  let a, _ = self#get_latest_common_ancestor tree lss in
                  [%debug_log "a=%a" nps a];
                  if a != nd#initial_parent then begin
                    try
                      List.iter
                        (fun s' ->
                          [%debug_log "s'=%a" nps s'];
                          if not (Xset.mem lifted_nodes s') then
                            scan_initial_cluster sr' xs'
                              (fun n' ->
                                [%debug_log "n'=%a" nps n'];
                                if
                                  n' != sr' &&
                                  not (is_ancestor n' s') &&
                                  not (is_ancestor n' nd') &&
                                  not (is_ancestor s' n') &&
                                  not (is_ancestor nd' n')
                                then begin
                                  let gi' = n'#gindex in
                                  if s'#gindex < gi' && gi' < ndgi' then begin
                                    let a0', _ =
                                      self#get_latest_common_ancestor tree' [s';n']
                                    in
                                    [%debug_log "a0'=%a" nps a0'];
                                    let x' = get_ancestor_below n' a0' in
                                    [%debug_log "x'=%a" nps x'];
                                    let cond =
                                      let ss0' =
                                        get_p_descendants (fun y' -> List.memq y' lss') x'
                                      in
                                      [%debug_log "ss0'=[%a]" nsps ss0'];
                                      let s = nmap' s' in
                                      let ca0, _ =
                                        self#get_latest_common_ancestor tree' [s;nd]
                                      in
                                      [%debug_log "ca=%a, ca0=%a" nps ca nps ca0];
                                      let cond0 = is_ancestor ca ca0 in
                                      [%debug_log "cond0=%B" cond0];
                                      if ss0' = [] && cond0 then
                                        true
                                      else
                                        cond0 &&
                                        let ss = List.map nmap' ss' in
                                        [%debug_log "ss=[%a]" nsps ss];
                                        let a0, _ =
                                          self#get_latest_common_ancestor tree ss
                                        in
                                        [%debug_log "a0=%a" nps a0];
                                        let ss0 = List.map nmap' ss0' in
                                        [%debug_log "ss0=[%a]" nsps ss0];
                                        List.exists
                                          (fun x ->
                                            [%debug_log "x=%a" nps x];
                                            let a1, _ =
                                              self#get_latest_common_ancestor tree [x;nd]
                                            in
                                            [%debug_log "a1=%a" nps a1];
                                            tree#is_initial_ancestor a0 a1
                                          ) ss0
                                    in
                                    if cond then begin
                                      [%debug_log "s'=%a n'=%a nd'=%a" nps s' nps n' nps nd'];
                                      [%debug_log "another conflict found: %a between %a and %a"
                                        nps n' nps s' nps nd'];
                                      [%debug_log "%a will be lifted" nps nd];
                                      result := true;
                                      if set_nodes_to_be_lifted then
                                        self#add_node_to_be_lifted nd;
                                      raise Exit
                                    end
                                  end
                                end
                              )
                        ) lss'
                    with
                      Exit -> ()
                  end
                end
              with
                Not_found -> ()
            end;
            Hashtbl.add check_stable_node_cache nd' !result;
            [%debug_log "result=%B" !result];
            !result
          end
        in (* check_stable_node *)

        let check_to_be_lifted is_stable is_stable' nmap lifted_nodes tree nmap' n =
          let b =
            if is_stable n then begin
              [%debug_log "n=%a is stable" nps n];
              let n' = nmap n in
              [%debug_log "n'=%a" nps n'];
              self#is_canceled_stable_node n' ||
              if
                not (Xset.mem lifted_nodes n') &&
                not (self#is_node_to_be_lifted n)
              then
                check_stable_node
                  ~set_nodes_to_be_lifted:false
                  is_stable' tree nmap' n'
              else
                false
            end
            else
              false
          in
          [%debug_log "%a -> %B" nps n b];
          b
        in

        let reg_subtree1 = self#reg_subtree tree1 in
        let reg_subtree2 = self#reg_subtree tree2 in

        let rec get_opposite_path ?(lv=0)
            nmap nmap' find_edit find_edit' tree tree' get_adjusted_path
            nd excluded
            =
          [%debug_log "[lv=%d] %s" lv nd#initial_to_string];

          let (*find_ipos*)_, find_iofs, stid_of_mid, get_subtree_root, lifted_nodes,
              simple_ins_roots, find_iparent, _has_parent_ins, _has_offset_parent_ins, ancto_tbl
              =
            if tree == tree2 then
              self#find_intermediate_pos1, self#find_intermediate_ofs1,
              self#stid_of_mid2,
              self#get_subtree_root_by_key2,
              lifted_nodes1,
              simple_ins_roots2, self#find_intermediate_parent1,
              self#has_parent_ins1, self#has_offset_parent_ins1,
              anc1to_tbl
            else
              self#find_intermediate_pos2, self#find_intermediate_ofs2,
              self#stid_of_mid1,
              self#get_subtree_root_by_key1,
              lifted_nodes2,
              simple_ins_roots1, self#find_intermediate_parent2,
              self#has_parent_ins2, self#has_offset_parent_ins2,
              anc2to_tbl
          in

          let has_parent_ins_cache = Hashtbl.create 0 in
          let has_parent_ins x =
            try
              let b = Hashtbl.find has_parent_ins_cache x#uid in
              (*[%debug_log "%a -> %B" nps x b];*)
              b
            with
              Not_found ->
                let b = _has_parent_ins ~multi:true x in
                Hashtbl.add has_parent_ins_cache x#uid b;
                b
          in
          let has_offset_parent_ins_cache = Hashtbl.create 0 in
          let has_offset_parent_ins x =
            try
              let b = Hashtbl.find has_offset_parent_ins_cache x#uid in
              (*[%debug_log "%a -> %B" nps x b];*)
              b
            with
              Not_found ->
                let b = _has_offset_parent_ins x in
                Hashtbl.add has_offset_parent_ins_cache x#uid b;
                b
          in
          let _is_stable find n =
            match find n#uid with
            | [] | [Relabel _] -> true
            | _ -> false
          in
          let is_stable = _is_stable find_edit in
          let is_stable' = _is_stable find_edit' in

          let is_stable_ x = is_stable x && not (self#is_canceled_stable_node x) in
          let _is_simple_ins = self#_is_simple_ins tree' is_stable is_stable_ nmap in

          let pnd = nd#initial_parent in
          let pos = nd#initial_pos in
          let children = pnd#initial_children in
          let nchildren = pnd#initial_nchildren in

          [%debug_log "pnd: %s" pnd#initial_to_string];

          let xmap = Array.map self#is_excluded children in
          [%debug_log "xmap: %s"
            (String.concat ""
               (List.mapi
                  (fun _ b -> if b then "x" else ".")
                  (Array.to_list xmap)))];

          let all_excluded = Array.for_all (fun x -> x) xmap in

          [%debug_log "all_excluded=%B" all_excluded];

          let excluded_map, base_pos, base_orig_pos =
            let base_pos = ref (-1) in
            let orig_pos = ref (-1) in
            let pos_found = ref false in
            let simple_ins_cands = ref [] in
            let cond =
              if all_excluded then
                fun _ n ->
                  [%debug_log "n=%a" nps n];
                  let stable = is_stable n in
                  let not_canceled = not (self#is_canceled_stable_node n) in
                  [%debug_log "stable=%B not_canceled=%B" stable not_canceled];
                  (*(stable && not_canceled) ||*)
                  let b =
                  (let b0 = Hashtbl.mem walls n in [%debug_log "b0=%B" b0]; b0) ||
                  (let b1 = has_parent_ins n in [%debug_log "b1=%B" b1]; b1) ||
                  (let b2 =
                    not
                      (Array.exists
                         (fun c ->
                           c != n && (is_stable c || Hashtbl.mem walls c || has_parent_ins c)
                         ) n#initial_parent#initial_children) &&
                    not stable && not (has_p_descendant is_stable_ n)
                  in
                  [%debug_log "b2=%B" b2];
                  b2) ||
                  let ss0 =
                    if stable && not not_canceled then
                      []
                    else
                      get_p_descendants
                        ~moveon:(fun x -> not (is_stable x))
                        is_stable_ n
                  in
                  [%debug_log "ss0=[%a]" nsps ss0];
                  if not stable && ss0 = [] then
                    simple_ins_cands := n :: !simple_ins_cands;
                  (let b3 =
                    match ss0 with
                      (*| [] when not (_is_simple_ins n) -> true*)
                    | [_] -> true
                    | _ -> false
                  in
                  [%debug_log "b3=%B" b3];
                  b3) ||
                  try
                    let a', _ =
                      let ss0' =
                        List.filter
                          (fun x -> not (self#is_node_to_be_lifted x)) (List.map nmap ss0)
                      in
                      [%debug_log "ss0'=[%a]" nsps ss0'];
                      match ss0' with
                      | [] -> raise Not_found
                      | _ -> self#get_latest_common_ancestor tree' ss0'
                    in
                    [%debug_log "a'=%a" nps a'];
                    let (sr0, _, _) =
                      let stid = self#find_stid pnd#uid in
                      [%debug_log "stid=%d" stid];
                      self#get_subtree_spec stid
                    in
                    [%debug_log "sr0=%a" nps sr0];
                    let pa', _ =
                      let xss0' =
                        List.filter
                          (fun x -> not (self#is_node_to_be_lifted x))
                          (List.map nmap (get_p_descendants is_stable sr0))
                      in
                      [%debug_log "xss0'=[%a]" nsps xss0'];
                      match xss0' with
                      | [] -> raise Not_found
                      | _ -> self#get_latest_common_ancestor tree' xss0'
                    in
                    [%debug_log "pa'=%a" nps pa'];
                    tree'#is_initial_ancestor pa' a'
                  with
                    Not_found -> false
                  in
                  [%debug_log "n=%a b=%B" nps n b];
                  b
              else
                fun i _ -> not (xmap.(i))
            in (* cond *)

            let cond_ =
              if all_excluded then begin
                let cond_vec = Array.mapi cond children in
                let cond_vec =
                  Array.mapi
                    (fun i b ->
                      let ci = children.(i) in
                      if List.memq ci !simple_ins_cands then
                        let b_ =
                          (try
                            for j = i - 1 downto (*0*)i - 1 do
                              let cj = children.(j) in
                              if Hashtbl.mem walls cj then begin
                                [%debug_log "wall found: j=%d cj=%a" j nps cj];
                                raise Exit
                              end
                            done;
                            false
                          with
                          | Exit -> true
                          | _ -> false) &&
                          (try
                            for j = i + 1 to (*nchildren - 1*)i + 1 do
                              let cj = children.(j) in
                              if cond_vec.(j) then begin
                                let _ = cj in
                                [%debug_log "found: j=%d cj=%a" j nps cj];
                                raise Exit
                              end
                            done;
                            false
                          with
                          | Exit -> true
                          | _ -> false)
                        in
                        [%debug_log "i=%d ci=%a %B->%B" i nps ci b b_];
                        b_
                      else
                        b
                    ) cond_vec
                in
                fun i _ ->
                  let b = cond_vec.(i) in
                  [%debug_log "i=%d b=%B" i b];
                  b
              end
              else
                cond
            in
            Array.iteri
              (fun i c ->
                [%debug_log "i=%d c=%a" i nps c];
                if not (Hashtbl.mem quasi_walls c) && cond_ i c then begin
                  if i < pos then begin
                    incr base_pos;
                    [%debug_log "%a" nps c];
                    orig_pos := i;
                    [%debug_log "base_pos=%d orig_pos=%d" !base_pos !orig_pos];
                    if Hashtbl.mem walls c then begin
                      [%debug_log "base_pos: %d -> 0" !base_pos];
                      base_pos := 0
                    end
                  end
                  else if i > pos && not !pos_found then begin
                    if not all_excluded || !base_pos < 0 then begin
                      incr base_pos;
                      orig_pos := i;
                      [%debug_log "base_pos=%d orig_pos=%d" !base_pos !orig_pos];
                      pos_found := true
                    end
                  end
                  else if i > pos && Hashtbl.mem walls c then begin
                    incr base_pos;
                    orig_pos := i;
                    [%debug_log "base_pos=%d orig_pos=%d" !base_pos !orig_pos];
                  end
                end
              ) children;

            if !base_pos < 0 && Hashtbl.mem walls nd then begin
              base_pos := 0;
              orig_pos := 0
            end;

            xmap, !base_pos, !orig_pos
          in

          [%debug_log "excluded_map: %s"
            (String.concat ""
               (List.mapi
                  (fun i b -> if i = pos then "o" else if b then "x" else ".")
                  (Array.to_list excluded_map)))];
          [%debug_log "base_pos=%d (orig:%d)" base_pos base_orig_pos];

          let adjust_pos pos =
            let count = ref 0 in
            for i = 0 to pos - 1 do
              if excluded_map.(i) then
                incr count
            done;
            pos - !count
          in

          let _stable_node_opt' = ref None in
          let _stable_nodes' = ref [] in
          let _count = ref 0 in

          [%debug_log "initial pos=%d" pos];

          let check i count =
            [%debug_log "check: %d (count=%d)" i count];
            let moveon n =
              try
                let n' = nmap n in
                not (is_stable' n') ||
                (not (Xset.mem lifted_nodes n') &&
                not (self#is_node_to_be_lifted n) &&
                not (self#is_canceled_stable_node n))
              with
                Not_found -> true
            in
            let forward = count < 0 in
            let scanner =
              if forward then begin
                [%debug_log "preorder scan"];
                preorder_scan_whole_initial_subtree ~moveon
              end
              else begin
                [%debug_log "reverse postorder scan"];
                rev_scan_whole_initial_subtree ~moveon
              end
            in
            let ci = children.(i) in
            let ck_opt = self#find_key_opt ci#uid in
            [%debug_log "i=%d ci=%a ck_opt=%s" i nps ci (key_opt_to_string ck_opt)];
            let ci_is_top_ins_root =
              is_stable ci#initial_parent &&
              match ck_opt with
              | Some ck when try get_subtree_root ck == ci with _ -> false -> true
              | _ -> false
            in
            [%debug_log "ci_is_top_ins_root=%B" ci_is_top_ins_root];
            let can_ignore_lift x =
              let b =
                ci_is_top_ins_root &&
                not
                  (has_p_ancestor ~limit_opt:(Some ci)
                     (fun y ->
                       match self#find_key_opt y#uid with
                       | Some _ as yk_opt -> yk_opt <> ck_opt
                       | _ -> false
                     ) x)
              in
              [%debug_log "%a -> %B" nps x b];
              b
            in
            scanner ci
              (fun n ->
                [%debug_log "n=%a" nps n];
                try
                  let n' = nmap n in
                  [%debug_log "n'=%a" nps n'];
                  if
                    is_stable' n' &&
                    (can_ignore_lift n ||
                    not (Xset.mem lifted_nodes n') &&
                    not (self#is_node_to_be_lifted n) &&
                    not (self#is_canceled_stable_node n))
                  then begin
                    if
                      can_ignore_lift n && (Xset.mem lifted_nodes n' ||
                      self#is_node_to_be_lifted n ||
                      self#is_canceled_stable_node n)
                    then
                      [%debug_log "!!!!!!!!!!"];

                    if forward then begin
                      begin
                        match !_stable_nodes' with
                        | [] ->
                            _stable_node_opt' := Some n'; _stable_nodes' := n' :: !_stable_nodes'
                        | _ -> ()
                      end;
                      if
                        not (List.memq n' !_stable_nodes') &&
                        not (is_stable' n'#initial_parent) &&
                        not (List.exists (fun x' -> is_ancestor x' n') !_stable_nodes')
                      then
                        _stable_nodes' := n' :: !_stable_nodes'
                    end
                    else begin (* backward *)
                      _stable_node_opt' := Some n';
                      [%debug_log "check: count=%d: a stable node %a found" count nps n'];
                      raise Exit
                    end
                  end
                with
                  Not_found -> ()
              )
          in (* check *)

          let boundary_node = ref nd in

          begin (* check if interleaving *)
            let moveon n =
              not (is_stable n) && not (self#is_canceled_stable_node n)
            in
            List.iter
              (fun c ->
                try
                  preorder_scan_whole_initial_subtree ~moveon c
                    (fun n ->
                      try
                        let n' = nmap n in
                        if is_stable' n' && not (self#is_canceled_stable_node n) then begin
                          _stable_node_opt' := Some n';
                          boundary_node := c;
                          raise Exit
                        end
                      with
                        Not_found -> ()
                    );
                with
                  Exit -> ()
              ) excluded
          end;

          let c_stable_node_opt' = !_stable_node_opt' in

          [%debug_log "c_stable_node'=%s boundary_node=%a"
            (match c_stable_node_opt' with
            | Some sn' -> node_to_uid_string sn'
            | None -> "")
            nps !boundary_node];

          begin (* search right siblings *)
            _stable_node_opt' := None;
            _count := 0;
            try
              for i = pos + 1 to nchildren - 1 do
                decr _count;
                check i !_count
              done
            with
              Exit -> ()
          end;

          let r_stable_node_opt' = !_stable_node_opt' in
          let r_stable_nodes' = !_stable_nodes' in
          let r_count = !_count in

          [%debug_log "r_stable_node'=%s r_count=%d"
            (match r_stable_node_opt' with
            | Some sn' -> node_to_uid_string sn'
            | None -> "")
            r_count];
          [%debug_log "r_stable_nodes'=[%a]" nsps r_stable_nodes'];

          begin (* search left siblings *)
            _stable_node_opt' := None;
            _count := 0;
            try
              for i = pos - 1 downto 0 do
                incr _count;
                check i !_count
              done
            with
              Exit -> ()
          end;

          let l_stable_node_opt' = !_stable_node_opt' in
          let l_count = !_count in

          [%debug_log "l_stable_node'=%s l_count=%d"
            (match l_stable_node_opt' with
            | Some sn' -> node_to_uid_string sn'
            | None -> "")
            l_count];


          let default () =

            if is_stable pnd then begin
              [%debug_log "pnd=%a is stable" nps pnd]
            end
            else begin
              [%debug_log "pnd=%a is not stable" nps pnd];
              raise Parent_not_stable
            end;

            let pnd' = nmap pnd in

            [%debug_log "pnd'=%a" nps pnd'];

            let get_pos n' =
              [%debug_log "n'=%a" nps n'];
              let a' = get_ancestor_below n' pnd' in
              a'#initial_pos
            in

            let l_pos_opt' =
              match l_stable_node_opt' with
              | Some x -> (try Some (get_pos x) with _ -> None)
              | None -> None
            in
            let c_pos_opt' =
              match c_stable_node_opt' with
              | Some x -> (try Some (get_pos x) with _ -> None)
              | None -> None
            in
            let r_pos_opt' =
              match r_stable_node_opt' with
              | Some x -> (try Some (get_pos x) with _ -> None)
              | None -> None
            in

            let elem =
              let pos', count =
                match l_pos_opt', c_pos_opt', r_pos_opt' with
                | _, Some p', _ -> p', 0
                | Some p', _, _ -> p', l_count
                | _, _, Some p' -> p', r_count
                | _ -> -1, pnd'#initial_nchildren
              in
              if pos' < 0 then
                Elem.make ~ofs:(float (pos+count)) 0
              else
                Elem.make ~ofs:(float count) pos'
            in
            [%debug_log "elem=%s" (Elem.to_string elem)];
            pnd', (Path.append pnd'#apath elem), 0, true

          in (* default *)

          let is_upstream anc' =
            let a = get_p_ancestor is_stable nd in
            let a' = nmap a in
            let c =
              if tree'#is_initial_ancestor a' anc' && anc'#initial_parent != a' then
                1
              else
                0
            in
            [%debug_log "%a -> %d" nps anc' c];
            c
          in

          let get_pos a n =
            (get_ancestor_below n a)#initial_pos
          in

          let l_has_conflicts = ref false in
          let r_is_desc_of_conflict = ref false in

          try

            let anc', path', upstream, simple =
              if lv = 0 then begin
                [%debug_log "l_stable_node_opt'=%s" (node_opt_to_string l_stable_node_opt')];
                [%debug_log "c_stable_node_opt'=%s" (node_opt_to_string c_stable_node_opt')];
                [%debug_log "r_stable_node_opt'=%s" (node_opt_to_string r_stable_node_opt')];
                match l_stable_node_opt', c_stable_node_opt', r_stable_node_opt' with
                | Some lsn', Some csn', _ -> begin
                    let anc', _ =
                      self#get_latest_common_ancestor tree' [lsn';csn']
                    in
                    let upstream = is_upstream anc' in

                    let elem = Elem.make (get_pos anc' csn') in
                    [%debug_log "elem=%s" (Elem.to_string elem)];
                    anc', (Path.append anc'#apath elem), upstream, false
                end
                | _, Some csn', Some rsn' -> begin
                    let anc', _ =
                      self#get_latest_common_ancestor tree' [csn';rsn']
                    in
                    let upstream = is_upstream anc' in

                    let elem = Elem.make (get_pos anc' csn') in
                    [%debug_log "elem=%s" (Elem.to_string elem)];
                    anc', (Path.append anc'#apath elem), upstream, false
                end
                | Some lsn', _, Some rsn' -> begin
                    let lr_sns' = [lsn'; rsn'] in
                    [%debug_log "lr_sns'=[%a]" nsps lr_sns'];

                    let anc', _ =
                      self#get_latest_common_ancestor tree' lr_sns'
                    in
                    [%debug_log "anc'=%a" nps anc'];

                    let lsn = nmap' lsn' in
                    let rsn = nmap' rsn' in

                    let rec find_parent_keys x =
                      match self#find_key_opt x#initial_parent#uid with
                      | Some k -> begin
                          [%debug_log "%a -> %s" nps x (key_to_string k)];
                          let y = get_subtree_root k in
                          k::(find_parent_keys y)
                      end
                      | None -> []
                    in

                    let ks = find_parent_keys rsn in

                    let rsn', rsn, (*lr_sns'*)_, anc' =
                      let ini = (rsn', rsn, lr_sns', anc') in
                      match r_stable_nodes' with
                      | r' :: (_::_) when
                          not (is_stable pnd) &&
                          not (is_stable' anc'#initial_parent) &&
                          lsn'#initial_parent == rsn'#initial_parent &&
                          try
                            lsn'#initial_parent#initial_children.(lsn'#initial_pos+1) == rsn'
                          with _ -> false
                        -> begin
                          let r = nmap' r' in
                          if Xlist.overlap (find_parent_keys r) ks then begin
                            let conflicts, _, _, _ =
                              self#get_conflicts is_stable' is_stable tree' tree nmap' nmap lsn' lsn
                            in
                            let _l_has_conflicts = conflicts <> [] in
                            [%debug_log "_l_has_conflicts=%B" _l_has_conflicts];
                            if _l_has_conflicts then begin
                              l_has_conflicts := true;
                              if
                                not (is_ancestor anc' r') &&
                                let b =
                                  List.exists (fun c -> is_ancestor c rsn) conflicts
                                in
                                if b then r_is_desc_of_conflict := true;
                                [%debug_log "r_is_desc_of_conflict=%B" b];
                                not b
                              then begin
                                [%debug_log "rsn': %a -> %a" nps rsn' nps r'];
                                let lr_sns_' = [lsn'; r'] in
                                let a', _ = self#get_latest_common_ancestor tree' lr_sns_' in
                                [%debug_log "anc': %a -> %a" nps anc' nps a'];
                                r', r, lr_sns_', a'
                              end
                              else
                                ini
                            end
                            else
                              ini
                          end
                          else
                            ini
                      end
                      | _ -> ini
                    in

                    let lr_sns = [lsn; rsn] in
                    [%debug_log "lr_sns=[%a]" nsps lr_sns];
                    let anc, tnt =
                      self#get_latest_common_ancestor tree lr_sns
                    in
                    [%debug_log "anc=%a" nps anc];

                    let upstream0, is_simple0 =
                      match self#find_key_opt anc#uid with
                      | Some (K_mid _|K_stid _) -> begin
                          if tree#is_initial_ancestor anc nd then
                            0, true
                          else
                            1, false
                      end
                      | _ -> begin
                          if is_stable anc then begin
                            [%debug_log "%a -> %a:stable" nps nd nps anc];
                            Hashtbl.add key_opt_cache nd#uid (Some K_stable)
                          end;
                          1, false
                      end
                    in
                    [%debug_log "upstream0=%d is_simple0=%B" upstream0 is_simple0];
                    let upstream = is_upstream anc' land upstream0 in
                    [%debug_log "upstream=%d" upstream];

                    [%debug_log "anc'=%a lsn'=%a rsn'=%a" nps anc' nps lsn' nps rsn'];
                    let context_cond =
                      let b =
                        self#has_parent_path lsn' && self#has_parent_path rsn'
                      in
                      if b then [%debug_log "!!!!!"];
                      b ||
                      let plsn' = lsn'#initial_parent in
                      let prsn' = rsn'#initial_parent in
                      plsn' == prsn' && prsn' == anc' &&
                      (let ss = get_p_descendants is_stable pnd in
                      let a', _ =
                        self#get_latest_common_ancestor tree' (List.map nmap ss)
                      in
                      not (tree'#is_initial_ancestor a' anc')) ||
                      plsn' != anc' ||
                      prsn' != anc' ||
                      (match self#find_key_opt pnd#uid with
                      | Some (K_mid _|K_stid _) as k_opt ->
                          Xarray.exists
                            (fun x ->
                              (self#find_key_opt x#uid) = k_opt
                            ) children ||
                          (match k_opt with
                          | Some (K_mid mid) ->
                              if self#is_staying_move mid then begin
                                let stid = stid_of_mid mid in
                                let _, xs, sz = self#get_subtree_spec stid in
                                sz = 1 ||
                                List.for_all (fun x -> x#initial_parent == pnd) xs
                              end
                              else
                                false
                          | _ -> false)
                      | _ -> false)
                    in
                    [%debug_log "context_cond=%B" context_cond];

                    let _ = check_stable_node is_stable tree' nmap rsn in

                    let not_simple =
                      try
                        match self#find_key_opt pnd#uid with
                        | Some pk -> begin
                            [%debug_log "pk=%s" (key_to_string pk)];
                            try
                              let a', (pt, ps) = Hashtbl.find ancto_tbl pk in
                              let pos = pt#position in
                              let nb = List.length ps in
                              [%debug_log "a'=%a pos=%d nb=%d" nps a' pos nb];
                              if self#has_parent_path lsn' && self#has_parent_path rsn' then begin
                                [%debug_log "!!!!!"];
                                false
                              end
                              else if is_ancestor a' anc' then begin
                                [%debug_log "a' is an ancestor of anc'"];
                                if !l_has_conflicts && is_simple0 && not !r_is_desc_of_conflict then begin
                                  [%debug_log "l_has_conflicts && is_simple0 && not r_is_desc_of_conflict"];
                                  false
                                end
                                else
                                  true
                              end
                              else if
                                not
                                  (lsn'#initial_parent == a' && rsn'#initial_parent == a' &&
                                   pos <= lsn'#initial_pos && rsn'#initial_pos <= pos + nb - 1)
                              then
                                raise Exit
                              else
                                false
                            with
                              Not_found -> raise Exit
                        end
                        | None -> raise Exit
                      with
                        Exit ->
                      let l_or_r_to_be_lifted =
                        (*List.exists (self#is_node_to_be_lifted) lr_sns' ||*)
                        List.exists (Xset.mem lifted_nodes) lr_sns ||
                        List.exists self#is_canceled_stable_node lr_sns
                      in
                      [%debug_log "l_or_r_to_be_lifted=%B" l_or_r_to_be_lifted];

                      try
                        let stid = self#find_stid pnd#uid in
                        [%debug_log "stid=%d" stid];
                        if
                          List.for_all
                            (fun (x, _) ->
                              [%debug_log "x=%a" nps x];
                              try
                                (self#find_stid x#uid) = stid
                              with
                                Not_found -> false
                            ) tnt ||
                          l_or_r_to_be_lifted
                        then
                          false
                        else begin
                          let rt, xs, sz = self#get_subtree_spec stid in
                          [%debug_log "stid=%d rt=%a xs=[%a] sz=%d"
                            stid nps rt nsps xs sz];

                          let ss =
                            List.concat_map
                              (fun x ->
                                if is_stable x then
                                  [x]
                                else
                                  get_p_descendants is_stable x
                              ) xs
                          in
                          let ss = List.filter (fun x -> not (self#is_canceled_stable_node x)) ss in
                          [%debug_log "ss=[%a]" nsps ss];
                          if (List.length ss) > 2 then begin
                            let ss' = List.map nmap ss in
                            let panc', _ =
                              self#get_latest_common_ancestor tree' ss'
                            in
                            [%debug_log "panc'=%a anc'=%a" nps panc' nps anc'];
                            let parent_move_opt =
                              try
                                let m = self#find_mid stid in
                                [%debug_log "m=%a" MID.ps m];
                                Some m
                              with
                                Not_found -> None
                            in
                            let b0 =
                              tree'#is_initial_ancestor panc' anc'
                            in
                            let b1 =
                              not (sz > 1 &&
                                   match parent_move_opt with
                                   | Some m -> begin
                                       try
                                         self#is_staying_move m &&
                                         (nmap rt) == anc'
                                       with
                                         Not_found -> false
                                   end
                                   | None -> false
                                  )
                            in
                            let b2 =
                              not
                                (match parent_move_opt with
                                | Some m ->
                                    let has_parent_staying_move =
                                      if tree == tree2 then
                                        self#has_parent_staying_move1
                                      else
                                        self#has_parent_staying_move2
                                    in
                                    self#is_staying_move m &&
                                    not (is_stable rt#initial_parent) &&
                                    not (has_parent_staying_move m)
                                | None -> false)
                            in
                            let b3 =
                              (match parent_move_opt with
                              | Some m -> self#is_staying_move m
                              | None -> false) &&
                              (pnd == anc &&
                               (match tnt with
                               | (x, _)::_ -> begin
                                   try
                                     for i = 0 to x#initial_pos - 1 do
                                       let n = pnd#initial_children.(i) in
                                       if not (self#is_excluded n) then
                                         raise Exit
                                     done;
                                     false
                                   with
                                     Exit -> true
                               end
                               | [] ->  false))
                            in
                            let b4 =
                              sz = 1 && get_p_descendants is_stable nd = []
                            in
                            [%debug_log "b0=%B, b1=%B, b2=%B, b3=%B, b4=%B" b0 b1 b2 b3 b4];
                            (b0 && b1 && b2) || (b0 && b3) || (b0 && b4)
                          end
                          else (* (List.length ss) <= 2 *)
                            false
                        end
                      with
                        Not_found -> false
                    in
                    [%debug_log "not_simple=%B" not_simple];

                    let is_simple =
                      not not_simple &&
                      context_cond &&
                      (is_simple0 ||
                      try
                        anc' == nmap pnd
                      with
                        Not_found -> false)
                    in
                    [%debug_log "is_simple: %a -> %B" nps nd is_simple];

                    if is_simple then begin
                      [%debug_log "simple_ins_root: %a" nps nd];
                      Xset.add simple_ins_roots nd;
                      default ()
                    end
                    else begin
                      let lr_parents =
                        try
                          let lk = self#find_key lsn#initial_parent#uid in
                          let rk = self#find_key rsn#initial_parent#uid in
                          [%debug_log "lk=%s, rk=%s" (key_to_string lk) (key_to_string rk)];
                          let (lr, rr) = ((get_subtree_root lk), (get_subtree_root rk)) in
                          if
                            lk <> rk &&
                            not (tree#is_initial_ancestor lr nd) &&
                            not (tree#is_initial_ancestor rr nd)
                          then
                            Some (lr, rr)
                          else
                            None
                        with
                          Not_found -> None
                      in
                      match lr_parents with
                      | Some (lr, rr) -> begin
                          let _ = lr in
                          [%debug_log "lr=%a rr=%a" nps lr nps rr];
                          [%debug_log "lsn'=%a rsn'=%a" nps lsn' nps rsn'];
                          let rss = get_p_descendants is_stable rr in
                          [%debug_log "rss=[%a]" nsps rss];
                          let rss' = List.map nmap rss in
                          [%debug_log "rss'=[%a]" nsps rss'];

                          (*let lss = get_p_descendants is_stable lr in
                          [%debug_log "lss=[%a]" nsps lss];
                          let lss' = Xlist.subtractq (List.map nmap lss) [lsn'] in
                          [%debug_log "lss'=[%a]" nsps lss'];*)

                          let a' =
                            let a', _ = self#get_latest_common_ancestor tree' [lsn'; rsn'] in
                            let a0', _ = self#get_latest_common_ancestor tree' rss' in
                            if is_ancestor a0' a' || a0' == a' then
                              a'
                            else
                              let _rss' = Xlist.subtractq rss' [rsn'] in
                              [%debug_log "_rss'=[%a]" nsps _rss'];
                              match _rss' with
                              | [] when List.length rss' = 1 -> a'
                              | [] -> lsn'#initial_parent
                              | rsn0'::_ ->
                                  let a0', _ =
                                    self#get_latest_common_ancestor tree' [lsn'; rsn0']
                                  in
                                  a0'
                          in
                          [%debug_log "pnd=%a" nps pnd];
                          [%debug_log "a'=%a" nps a'];
                          let ofs =
                            if !l_has_conflicts && not !r_is_desc_of_conflict then
                              0.0
                            else
                              float l_count
                          in
                          let ok =
                            try
                              a' != (nmap pnd)
                            with
                              _ -> true
                          in
                          [%debug_log "ok=%B" ok];
                          if ok then begin
                            let elem = Elem.make ~ofs (get_pos a' lsn') in
                            [%debug_log "elem=%s" (Elem.to_string elem)];
                            a', (Path.append a'#apath elem), upstream, false
                          end
                          else begin
                            let elem = Elem.make ~ofs (get_pos anc' lsn') in
                            [%debug_log "elem=%s" (Elem.to_string elem)];
                            anc', (Path.append anc'#apath elem), upstream, false
                          end
                      end
                      | None -> begin
                          let ofs =
                            if !l_has_conflicts && not !r_is_desc_of_conflict then
                              0.0
                            else
                              float l_count
                          in
                          let elem = Elem.make ~ofs (get_pos anc' lsn') in
                          [%debug_log "elem=%s" (Elem.to_string elem)];
                          anc', (Path.append anc'#apath elem), upstream, false
                      end
                    end
                end
                | _ -> begin
                    default ()
                end
              end
              else begin (* lv <> 0 *)
                default ()
              end
            in (* anc', path', upstream, simple *)

            let boundary_paths =
              if !boundary_node != nd then begin
                let key_opt = self#find_key_opt (!boundary_node)#uid in
                let rp = get_rel_path nd#apath (!boundary_node)#apath in
                [new boundary_path ~key_opt (get_adjusted_path rp)]
              end
              else
                []
            in

            [%debug_log "path': %s (upstream=%d, simple=%B)"
              (Path.to_string path') upstream simple];
            [%debug_log "boundary: [%s]"
              (boundary_to_string ~sep:"; " boundary_paths)];

            anc', path', boundary_paths, upstream, simple

          with
            Parent_not_stable -> begin
              [%debug_log "lv=%d: parent not stable" lv];
              let a', p', _, upstream, simple =
                get_opposite_path ~lv:(lv+1)
                  nmap nmap' find_edit find_edit' tree tree' get_adjusted_path
                  pnd []
              in
              [%debug_log "a'=%a simple=%B pnd=%a" nps a' simple nps pnd];

              let pos' = adjust_pos pos in
              [%debug_log "excluded_map: %s"
                (String.concat ""
                   (List.mapi
                      (fun i b -> if i = pos then "o" else if b then "x" else ".")
                      (Array.to_list excluded_map)))];
              [%debug_log "[lv=%d] base_pos=%d (base_orig_pos:%d) pos: %d -> %d (simple=%B)"
                lv base_pos base_orig_pos pos pos' simple];

              let intermediate_ofs_opt =
                try
                  if all_excluded && simple then
                    Some (find_iofs nd)
                  else
                    None
                with
                  Not_found -> None
              in
              [%debug_log "intermediate_ofs_opt=%s"
                (match intermediate_ofs_opt with
                | Some iofs -> string_of_int iofs
                | None -> "")];

              let elem =
                if lv <> 0 then begin
                  Elem.make pos'
                end
                else if intermediate_ofs_opt <> None then begin
                  match intermediate_ofs_opt with
                  | Some iofs ->
                      Elem.make ~ofs:(float iofs) 0
                  | None -> assert false
                end
                else if base_pos >= 0 then begin
                  let is_sibling = function
                    | Some n' -> begin
                        let n = nmap' n' in
                        n#initial_parent == pnd
                    end
                    | _ -> false
                  in
                  let check_wall w =
                    let b =
                      try
                        let g' =
                          match Hashtbl.find walls w with
                          | Some x -> x
                          | _ -> raise Not_found
                        in
                        let pk = self#find_key pnd#uid in
                        let t', (pt', ps) = Hashtbl.find ancto_tbl pk in
                        let pos' = pt'#position in
                        [%debug_log "t'=%a pos'=%d g'=%a" nps t' pos' nps g'];
                        if t' == g'#initial_parent then begin
                          try
                            let pp = (*Path.get_parent *)(List.nth ps (g'#initial_pos - pos'))#path in
                            let r = get_subtree_root pk in
                            [%debug_log "pp=%s r=%a" (Path.to_string pp) nps r];
                            self#acc r pp != w#initial_parent
                          with _ -> true
                        end
                        else
                          true
                      with
                        Not_found -> true
                    in
                    [%debug_log "%a -> %B" nps w b];
                    b
                  in
                  let ofs, base_pos' =
                    if all_excluded then begin
                      let is_wall = Hashtbl.mem walls children.(pos) in
                      let wall_opt =
                        let w_opt = ref None in
                        try
                          for i = 0 to nd#initial_pos - 1 do
                            let ci = children.(i) in
                            if Hashtbl.mem walls ci && check_wall ci then begin
                              [%debug_log "wall found: %a (i=%d)" nps ci i];
                              w_opt := Some (i, ci);
                              raise Exit
                            end;
                            (*if has_parent_ins ci then begin
                              Xset.add walls ci;
                              [%debug_log "parent ins found: %a" nps ci];
                              raise Exit
                            end;
                            if _is_simple_ins ci then begin
                              Xset.add walls ci;
                              [%debug_log "simple ins found: %a" nps ci];
                              raise Exit
                            end*)
                          done;
                          None
                        with
                          Exit -> !w_opt
                      in
                      [%debug_log "wall_opt=%s"
                        (match wall_opt with Some (_, w) -> node_to_uid_string w | _ -> "")];

                      let has_wall = wall_opt <> None in
                      [%debug_log "has_wall=%B" has_wall];
                      let quasi_wall_count =
                        match wall_opt with(*REGRESSION:elastic/elasticsearch 179, elastic/elasticsearch 264*)
                        | Some (_, wall) when begin
                            try
                              wall == nd#initial_parent#initial_children.(nd#initial_pos-1)
                            with _ -> false
                        end -> 0
                        | Some (idx, wall) -> begin
                            let check_flag = ref false in
                            let w_grp_cond =
                              if is_stable wall then
                                let wall' = nmap wall in
                                let t' =
                                  try
                                    let t', _ = Hashtbl.find ancto_tbl (self#find_key pnd#uid) in
                                    t'
                                  with _ -> a'
                                in
                                [%debug_log "t'=%a wall'=%a idx=%d" nps t' nps wall' idx];
                                if wall'#initial_parent != t' then begin
                                  check_flag := true;
                                  fun x ->
                                    try
                                      let x' = nmap x in
                                      [%debug_log "x=%a x'=%a" nps x nps x'];
                                      let b = x'#initial_parent == wall'#initial_parent in
                                      [%debug_log "b=%B" b];
                                      b
                                    with _ -> false
                                end
                                else
                                  fun _ -> false
                              else
                                fun _ -> false
                            in
                            let is_non_simple_ins x =
                              not (is_stable x) && List.length(get_p_descendants is_stable x) > 1
                            in
                            [%debug_log "check_flag=%B" !check_flag];
                            let w_grp_flag =
                              !check_flag &&
                              let w_grp_count = ref 0 in
                              let non_simple_ins_count = ref 0 in
                              try
                                for i = idx + 1 to (*nd#initial_pos - 1*)nchildren - 1 do
                                  let ci = children.(i) in
                                  [%debug_log "i=%d ci=%a" i nps ci];
                                  if w_grp_cond ci then
                                    incr w_grp_count;
                                  if is_non_simple_ins ci then begin
                                    [%debug_log "non_simple_ins: %a" nps ci];
                                    incr non_simple_ins_count
                                  end
                                done;
                                [%debug_log "w_grp_count=%d non_simple_ins_count=%d" !w_grp_count !non_simple_ins_count];
                                !w_grp_count > 1 && !non_simple_ins_count > 0 && !w_grp_count <> nchildren - 1 - idx
                              with
                                Exit -> true
                            in
                            [%debug_log "w_grp_flag=%B" w_grp_flag];
                            let ini =
                              if
                                not !check_flag ||
                                try
                                  for i = 0 to wall#initial_pos - 1 do
                                    if Hashtbl.mem quasi_walls children.(i) then
                                      raise Exit
                                  done;
                                  false
                                with
                                  Exit -> true
                              then begin
                                [%debug_log "!!!!!!"];
                                max 0 (idx - 1)
                              end
                              else
                                0
                            in
                            [%debug_log "ini=%d nd=%a" ini nps nd];
                            let c = ref ini in
                            (*REGRESSION:broadgsa/gatk 27 vs griddynamics/jagger 140*)
                            for i = idx + 1(*0*) to nd#initial_pos - 1 do
                              let ci = children.(i) in
                              if Hashtbl.mem quasi_walls ci then begin
                                incr c;
                                [%debug_log "quasi-wall found: %a (c->%d)" nps ci !c];
                              end;
                              if has_offset_parent_ins ci then begin
                                incr c;
                                [%debug_log "%a has offset parent ins (c->%d)" nps ci !c];
                              end;
                              if w_grp_flag && w_grp_cond ci then begin
                                [%debug_log "wall group member: %a (c->%d)" nps ci ini];
                                c := (*0*)ini;
                              end;(*REGRESSION:apache/accumulo 551 vs johannilsson/android-actionbar 2*)
                            done;
                            !c
                        end
                        | None -> 0
                      in
                      [%debug_log "quasi_wall_count=%d" quasi_wall_count];

                      begin %debug_block
                      let _quasi_wall_count =
                        let c = ref 0 in
                        for i = 0 to nd#initial_pos - 1 do
                          let ci = children.(i) in
                          if Hashtbl.mem quasi_walls ci then begin
                            incr c;
                            [%debug_log "quasi-wall found: %a (c->%d)" nps ci !c];
                          end;
                        done;
                        !c
                      in
                      [%debug_log "_quasi_wall_count=%d" _quasi_wall_count];
                      if quasi_wall_count <> _quasi_wall_count then
                        [%debug_log "!!!!!!"];
                      end;

                      let has_no_right_wall =
                        try
                          for i = nd#initial_pos + 1 to nchildren - 1 do
                            let ci = children.(i) in
                            if Hashtbl.mem walls ci && check_wall ci then begin
                              [%debug_log "wall found: %a (i=%d)" nps ci i];
                              raise Exit
                            end
                          done;
                          true
                        with
                        | Exit -> false
                        | _ -> true
                      in
                      [%debug_log "has_no_right_wall=%B" has_no_right_wall];
                      if
                        c_stable_node_opt' = None &&
                        is_sibling l_stable_node_opt' &&
                        r_stable_node_opt' <> None &&
                        has_no_right_wall
                      then begin
                        [%debug_log "regard %a as a member of parent insertion" nps nd];
                        begin %debug_block
                          [%debug_log "l_stable_node_opt'=%s" (node_opt_to_string l_stable_node_opt')];
                          [%debug_log "r_stable_node_opt'=%s" (node_opt_to_string r_stable_node_opt')]
                        end;
                        let o =
                          if has_wall then
                            float (base_pos + 1 + quasi_wall_count)
                          else
                            0.
                        in
                        o, (adjust_pos base_pos)
                      end
                      else begin
                        let base_nd = children.(base_orig_pos) in
                        [%debug_log "base_nd=%a" nps base_nd];
                        if
                          self#is_canceled_stable_node base_nd &&
                          not (has_p_descendant is_stable nd)
                        then begin
                          [%debug_log "!!!!!"];
                          0., 0(*REGRESSION:k9mail/k-9 99 vs cgeo/cgeo 82*)
                        end
                        else
                        try
                          if not (is_stable base_nd) then
                            raise Not_found;

                          let base_nd' = nmap base_nd in
                          [%debug_log " -> base_nd'=%a" nps base_nd'];

                          let pnd' =
                            if
                              let mid = self#find_mid (self#find_stid pnd#uid) in
                              [%debug_log "mid=%a" MID.ps mid];
                              let r = get_subtree_root (K_mid mid) in
                              [%debug_log "r=%a" nps r];
                              r == pnd && self#is_staying_move mid
                            then
                              nmap pnd
                            else
                              raise Not_found
                          in

                          if pnd' == base_nd'#initial_parent then begin
                            [%debug_log "pnd'(=%a) == base_nd'#initial_parent" nps pnd'];
                            let ofs = pos - base_orig_pos in
                            [%debug_log "ofs=%d" ofs];
                            let zero_ofs = ref false in
                            if ofs > 0 then begin
                              [%debug_log "ofs(=%d) > 0" ofs];
                              [%debug_log "nchildren=%d" nchildren];
                              let base_pos' =
                                let base_nd_is_stable = is_stable base_nd in
                                if
                                  base_nd_is_stable && base_orig_pos = 0 &&
                                  (try
                                    for i = 1 to nchildren - 1 do
                                      let ci = children.(i) in
                                      [%debug_log "ci=%a" nps ci];
                                      if simple then begin
                                        if not (self#is_excluded ci) then
                                          raise Exit
                                      end
                                      else begin
                                        if is_stable ci && not (Hashtbl.mem quasi_walls ci) then
                                          raise Exit
                                      end
                                    done;
                                    true
                                  with
                                    Exit -> false
                                  )
                                then
                                  0
                                else if
                                  base_nd_is_stable && base_orig_pos > 0 &&
                                  pos = nchildren - 1 &&
                                  (try
                                    for i = 0 to nchildren - 2 do
                                      let ci = children.(i) in
                                      [%debug_log "ci=%a" nps ci];
                                      if not (is_stable ci) then
                                        raise Exit
                                    done;
                                    true
                                  with
                                    Exit -> false
                                  )
                                then begin
                                  zero_ofs := true;
                                  0
                                end
                                else
                                  try
                                    if not (is_stable base_nd) then
                                      raise Not_found;

                                    let d = find_iparent base_nd in
                                    let c0 = children.(0) in
                                    [%debug_log "c0=%a" nps c0];
                                    if is_stable c0 then
                                      if (find_iparent c0) == d then
                                        0
                                      else
                                        raise Not_found
                                    else
                                      raise Not_found
                                  with
                                    Not_found -> get_base_pos' is_stable' base_nd'
                              in
                              [%debug_log "base_pos'=%d" base_pos'];

                              (if !zero_ofs then 0.0 else float ofs), base_pos'
                            end
                            else if ofs < 0 then begin
                              [%debug_log "ofs(=%d) < 0" ofs];
                              (float ofs), 0
                            end
                            else begin
                              [%debug_log "ofs(=%d) = 0" ofs];
                              raise Not_found
                            end
                          end
                          else begin
                            [%debug_log "pnd'(=%a) != base_nd'#initial_parent(=%a)"
                              nps pnd' nps base_nd'#initial_parent];
                            raise Not_found
                          end
                        with
                          Not_found -> begin
                            let ofs =
                              if simple && is_wall then begin
                                [%debug_log "simple && is_wall: ofs -> 0"];
                                0
                              end
                              else if simple && has_wall then begin
                                let o = base_pos + 1 + quasi_wall_count in
                                [%debug_log "simple && has_wall: ofs -> %d" o];
                                let adj =
                                  try
                                    if
                                      find_iparent children.(0)
                                        == find_iparent (children.(base_orig_pos-1))
                                    then
                                      1
                                    else
                                      0
                                  with
                                    _ -> 0
                                in
                                [%debug_log "adj=%d" adj];
                                o + adj
                              end
                              else if base_pos = base_orig_pos then begin
                                [%debug_log "base_pos = base_orig_pos: ofs -> %d" pos];
                                pos
                              end
                              else begin
                                let o = pos - base_orig_pos in
                                [%debug_log "base_pos <> base_orig_pos: ofs -> %d" o];
                                o
                              end
                            in
                            (float ofs), if simple then 0 else base_pos
                          end
                      end
                    end
                    else begin(* not all_excluded *)
                      [%debug_log "not all_excluded"];
                      (float (pos-base_orig_pos)), base_pos
                    end
                  in (* ofs, base_pos' *)
                  Elem.make ~ofs base_pos'
                end
                else begin (* base_pos < 0 *)
                  [%debug_log "pos=%d" pos];
                  let c = ref 0 in
                  for i = 0 to pos - 1 do
                    let ci = children.(i) in
                    [%debug_log "i=%d ci=%a" i nps ci];
                    if self#is_canceled_stable_node ci then
                      incr c
                  done;
                  [%debug_log "c=%d" !c];
                  let p = pos - !c in
                  (*let nc = nchildren - !c in
                  let ofs = float (p - (nc - 1 - p)) in
                  [%debug_log "p=%d, nc=%d, ofs=%.4f" p nc ofs];*)
                  let ofs = float p in
                  Elem.make ~ofs 0
                end
              in
              let path' = Path.append p' elem in

              [%debug_log "path'=%s" (Path.to_string path')];

              a', path', [], upstream, simple

            end
        in (* get_opposite_path *)

        let get_path1 =
          get_opposite_path
            nmapping#inv_find nmapping#find self#find2 self#find1 tree2 tree1
        in
        let get_path2 =
          get_opposite_path
            nmapping#find nmapping#inv_find self#find1 self#find2 tree1 tree2
        in

        let get_depth rt nd =
          if nd == rt then
            0
          else
            let cur = ref nd in
            let count = ref 0 in
            begin
              try
                while !cur != rt do
                  incr count;
                  cur := (!cur)#initial_parent
                done
              with
                _ -> ()
            end;
            !count
        in

        let get_parent_info excepted_nds nd path' tree' nmap is_stable is_stable' simple' =

          [%debug_log "excepted_nds=[%a] nd=%a path'=%s simple'=%B"
            nsps excepted_nds nps nd path'#to_string simple'];

          let has_iofs, simple_ins_roots =
            if tree' == tree1 then
              self#has_intermediate_ofs1, simple_ins_roots2
            else
              self#has_intermediate_ofs2, simple_ins_roots1
          in

          let pnd = nd#initial_parent in

          let key_opt, adj_opt, depth_opt, shift_opt =
            if excepted_nds <> [] || not simple' then begin
              None, None, None, None
            end
            else begin (* excepted_nds = [] && simple' *)
              try
                let stid = self#find_stid pnd#uid in
                let key, parent_is_staying_move =
                  try
                    let mid = self#find_mid stid in
                    key_of_mid mid, self#is_staying_move mid
                  with
                    Not_found -> key_of_stid stid, false
                in
                [%debug_log "key=%s" (key_to_string key)];
                [%debug_log "parent_is_staying_move=%B" parent_is_staying_move];

                let st_root = self#get_subtree_root stid in

                let adj_opt =
                  if parent_is_staying_move then begin
                    try
                      if has_iofs nd then
                        raise Not_found;

                      let base_elem' = Path.tail path'#path in
                      let base_pos = base_elem'.Elem.pos in
                      let not_excluded =
                        List.filter
                          (fun x ->
                            not (self#is_excluded x)
                          ) (Array.to_list pnd#initial_children)
                      in
                      let base_nd =
                        if not_excluded = [] then
                          pnd#initial_children.(base_pos)
                        else
                          List.nth not_excluded base_pos
                      in
                      let nmems =
                        let c = ref 0 in
                        for i = 0 to base_nd#initial_pos - 1 do
                          match self#find_key_opt pnd#initial_children.(i)#uid with
                          | Some k when k = key -> incr c
                          | _ -> ()
                        done;
                        !c
                      in
                      [%debug_log "nmems=%d" nmems];
                      if nmems = base_pos then
                        raise Not_found;

                      let base_nd' = nmap base_nd in
                      let base_pos' = get_base_pos' is_stable' base_nd' in

                      [%debug_log "base_nd=%a (base_pos=%d) -> base_nd'=%a (base_pos'=%d)"
                        nps base_nd base_pos nps base_nd' base_pos'];

                      if base_nd'#initial_parent != (nmap pnd) then
                        raise Not_found;

                      let ca = base_nd#initial_parent#initial_children in
                      let c = ref 0 in
                      for i = 0 to base_nd#initial_pos - 1 do
                        let ci = ca.(i) in
                        [%debug_log "ci=%a" UID.ps ci#uid];
                        [%debug_log " excluded: %B" (self#is_excluded ci)];
                        [%debug_log " stable: %B" (is_stable ci)];
                        [%debug_log " stable descendants: [%a]" nsps (get_p_descendants is_stable ci)];
                        if
                          ci != nd &&
                          self#is_excluded ci &&
                          not (is_stable ci) &&
                          (get_p_descendants is_stable ci) = []
                        then
                          incr c
                      done;
                      [%debug_log "c=%d" !c];

                      let ca' = base_nd'#initial_parent#initial_children in
                      let count = ref 0 in
                      for i = 0 to base_pos' - 1 do
                        if self#is_excluded ca'.(i) then begin
                          [%debug_log "%a (excluded)" UID.ps ca'.(i)#uid];
                          incr count
                        end
                        else
                          [%debug_log "%a" UID.ps ca'.(i)#uid];
                      done;
                      [%debug_log "count=%d" !count];

                      if (base_pos' - !count) = base_pos - !c then
                        count := 0
                      else if not (self#is_excluded base_nd') then
                        if !count < base_pos' then
                          decr count
                        else
                          count := 0;
                      if !count <= 0 then
                        None
                      else begin
                        let adj = !count in
                        [%debug_log "adj=%d" adj];
                        Some adj
                      end
                    with
                    | Not_found -> None
                    | _ -> None
                  end
                  else
                    None
                in (* adj_opt *)
                let shift_opt =
                  if Xset.mem simple_ins_roots nd then
                    None
                  else
                    self#get_pos_shift is_stable stid nd
                in
                Some key, adj_opt, Some (get_depth st_root nd), shift_opt
              with
                Not_found -> None, None, None, None
            end
          in (* key_opt, adj_opt, depth_opt, shift_opt *)
          key_opt, adj_opt, depth_opt, shift_opt

        in (* get_parent_info *)

        let rec get_anc_below_mid nd mid =
          [%debug_log "%a" nps nd];
          try
            let pnd = nd#initial_parent in
            match self#find_key_opt pnd#uid with
            | Some (K_mid m) ->
                if m = mid then
                  Some nd
                else
                  get_anc_below_mid pnd mid
            | Some (K_stid _) -> get_anc_below_mid pnd mid
            | Some K_stable | Some (K_del _) | None -> None
          with
            _ -> None
        in

        let count_upstream_nds mid rt rt'
            anc path paths simple child_staying_moves
            is_stable is_stable'
            remote_stable_tbl remote_stable_tbl' nmap nmap' tree tree' lift_tbl lifted_nodes
            nd
            =
          [%debug_log "mid=%a rt=%a rt'=%a nd=%a child_staying_moves=[%s]"
            MID.ps mid nps rt nps rt' nps nd (mids_to_string child_staying_moves)];

          let mid_key = K_mid mid in

          let find_ipos, find_iofs, simple_ins_roots', is_ancestor_key, ancto_tbl =
            if tree == tree1 then
              self#find_intermediate_pos1, self#find_intermediate_ofs1, simple_ins_roots2,
              self#is_ancestor_key1, anc1to_tbl
            else
              self#find_intermediate_pos2, self#find_intermediate_ofs2, simple_ins_roots1,
              self#is_ancestor_key2, anc2to_tbl
          in

          [%debug_log "path=%s paths=%s" path#to_string (boundary_to_string ~sep:";" paths)];
          let pos = path#position in
          let nb = List.length paths in
          [%debug_log "anc=%a pos=%d nb=%d" nps anc pos nb];
          let comp_flag =
            path#offset = 0.0 &&
            match paths with
            | [] -> false
            | p::_ -> p#key_opt <> None
          in
          [%debug_log "comp_flag=%B" comp_flag];
          let group_heads = ref [] in
          (*let group_tbl = Hashtbl.create 0 in*)
          let foreign_mem_list = ref [] in
          let patha = Array.of_list paths in
          List.iter
            (fun (n', ss') ->
              let ss = List.rev_map nmap' ss' in
              [%debug_log "n'=%a ss'=[%a] ss=[%a]" nps n' nsps ss' nsps ss];
              List.iter
                (fun s ->
                  for _i = 0 to nb - 1 do
                    let i = _i + pos in
                    let ci = anc#initial_children.(i) in
                    if is_ancestor ci s then begin
                      tbl_add group_tbl ci n';
                      if patha.(_i)#key_opt <> None then
                        foreign_mem_list := n' :: !foreign_mem_list
                    end
                  done
                ) ss
            ) remote_stable_tbl';
          Hashtbl.iter
            (fun tn nl' ->
              let _ = tn in
              [%debug_log "%a -> [%a]" nps tn nsps nl'];
              match List.rev nl' with
              | h::_ -> group_heads := h :: !group_heads
              | _ -> ()
            ) group_tbl;
          [%debug_log "group_heads=[%a]" nsps !group_heads];
          let is_stable_' x' = is_stable' x' && not (self#is_canceled_stable_node x') in
          let top_nodes =
            if nb > 0 then
              Array.to_list (Array.sub anc#initial_children pos nb)
            else
              []
          in
          let is_simple_ins x' =
            let b =
              Xset.mem simple_ins_roots' x' ||
              not comp_flag && self#_is_simple_ins tree' is_stable' is_stable_' nmap' ~top_nodes x'
            in
            [%debug_log "%a -> %B" nps x' b];
            b
          in
          let is_foreign_mem x' =
            let b = List.memq x' !foreign_mem_list in
            [%debug_log "%a -> %B" nps x' b];
            b
          in

          let is_upw_stg_mov = ref false in
          let indirect_conflict = ref false in

          let upc, k_opt, sp_opt =
            if self#is_staying_move mid then begin
              [%debug_log "%a is a staying move" MID.ps mid];

              let pnd = nd#initial_parent in

              (*let on_another_staying_move =
                match self#find_key_opt nd#uid with
                | Some ((K_mid m) as k) -> begin
                try
                let b =
                m <> mid &&
                self#is_staying_move m &&
                (nmap' (self#get_subtree_root_by_key k)) == nd
                in
                if b then
                [%debug_log "%a is root of another staying move %a"
                nps nd MID.ps m];
                b
                with
                Not_found -> false
                end
                | _ -> false
                in
                if on_another_staying_move then
                0, None, None
                else!!!!!*)

              let rss, rss', is_upward_staying_move =
                self#is_upward_staying_move mid rt remote_stable_tbl' nmap' tree
              in
              let _ = rss' in
              [%debug_log "rss=[%a]" nsps rss];
              [%debug_log "rss'=[%a]" nsps rss'];
              [%debug_log "is_upward_staying_move=%B" is_upward_staying_move];

              is_upw_stg_mov := is_upward_staying_move;

              if is_upward_staying_move && self#is_deleted nd then begin
                [%debug_log "nd=%a" nps nd];
                0, None, None
              end
              else begin
                try
                  let stable_nds =
                    if is_stable nd then
                      [nd]
                    else
                      try
                        List.assq nd remote_stable_tbl
                      with
                        Not_found -> []
                  in
                  [%debug_log "stable_nds=[%s]" (nodes_to_uids_string stable_nds)];

                  let pnd' = nmap pnd in
                  [%debug_log "pnd=%a -> pnd'=%a" nps pnd nps pnd'];
                  List.fold_left
                    (fun (c, key_opt, sub_path_opt) n ->
                      [%debug_log "n=%a" nps n];
                      let n' = nmap n in
                      [%debug_log "n'=%a" nps n'];

                      let single_conflicting_staying_move = ref None in

                      let ins_target = ref None in

                      let has_conflict =
                        is_foreign_mem n' ||
                        if not (tree'#is_initial_ancestor pnd' n') then begin
                          [%debug_log "%a is not an ancestor of %a" nps pnd' nps n'];
                          try
                            let pn' = n'#initial_parent in
                            [%debug_log "pn'=%a" nps pn'];
                            let stid = self#find_stid pn'#uid in
                            [%debug_log "stid=%d" stid];

                            let m_opt =
                              try
                                Some (self#find_mid stid)
                              with
                                Not_found -> None
                            in
                            match m_opt with
                            | Some m -> begin
                                [%debug_log "m=%a" MID.ps m];
                                if m = mid then begin
                                  [%debug_log "simple=%B" simple];
                                  if simple then
                                    false
                                  else
                                    let pos = path#position in
                                    [%debug_log "pos=%d" pos];
                                    match get_anc_below_mid n mid with
                                    | Some _bn -> begin
                                        let bn = _bn#initial_parent in
                                        [%debug_log "bn=%a" nps bn];
                                        try
                                          let x = get_ancestor_below bn rt in
                                          [%debug_log "x=%a" nps x];
                                          try
                                            List.iteri
                                              (fun i p ->
                                                [%debug_log "anc#initial_children.(%d)=%a"
                                                  (pos+i) nps anc#initial_children.(pos+i)];

                                                if x == anc#initial_children.(pos+i) then begin
                                                  let ins =
                                                    self#acc rt (Path.get_parent p#path)
                                                  in
                                                  [%debug_log "ins=%a" nps ins];
                                                  if
                                                    ins == x ||
                                                    tree#is_initial_ancestor x ins &&
                                                    tree#is_initial_ancestor ins bn
                                                  then
                                                    ()
                                                  else
                                                    raise Exit
                                                end
                                              ) paths;
                                            false
                                          with
                                            Exit -> true
                                        with
                                          Not_found -> true
                                    end
                                    | None -> true
                                end
                                else begin
                                  let r' = self#get_subtree_root stid in
                                  [%debug_log "r'=%a" nps r'];
                                  let ss' = get_p_descendants is_stable' r' in
                                  [%debug_log "ss'=[%a]" nsps ss'];
                                  match ss' with
                                  | [] -> assert false
                                  | [_] -> not (tree'#is_initial_ancestor rt' r')
                                  | _ -> begin
                                      let ss = List.map nmap' ss' in
                                      let a, _ =
                                        self#get_latest_common_ancestor tree ss
                                      in
                                      [%debug_log "a=%a rt=%a" nps a nps rt];
                                      not (tree#is_initial_ancestor a rt) &&
                                      not (tree#is_initial_ancestor rt a)
                                  end
                                end
                            end
                            | None ->
                                let b =
                                  let r' = self#get_subtree_root stid in
                                  [%debug_log "r'=%a" nps r'];
                                  let ss' = get_p_descendants is_stable' r' in
                                  [%debug_log "ss'=[%a]" nsps ss'];
                                  match ss' with
                                  | [] -> assert false
                                  | [_] -> begin
                                      let b =
                                        r' != pn' && not (tree'#is_initial_ancestor r' rt')
                                      in
                                      [%debug_log "b=%B" b];
                                      if not b then begin
                                        let rec up n' =
                                          [%debug_log "n'=%a" nps n'];
                                          let pn' = n'#initial_parent in
                                          [%debug_log "pn'=%a" nps pn'];
                                          let stid = self#find_stid pn'#uid in
                                          [%debug_log "stid=%d" stid];
                                          let r' = self#get_subtree_root stid in
                                          [%debug_log "r'=%a" nps r'];
                                          let b =
                                            try
                                              let _ = self#find_mid stid in
                                              false
                                            with
                                              Not_found ->
                                                r' != pn' &&
                                                not (tree'#is_initial_ancestor r' rt')
                                          in
                                          [%debug_log "b=%B" b];
                                          if not b then
                                            up r'
                                          else begin
                                            ins_target := Some (stid, n');
                                            indirect_conflict := true;
                                            true
                                          end
                                        in
                                        try
                                          up r'
                                        with
                                          _ -> false
                                      end
                                      else
                                        true
                                  end
                                  | _ -> begin
                                      let ss = List.map nmap' ss' in
                                      [%debug_log "ss=[%a]" nsps ss];
                                      let a, _ =
                                        self#get_latest_common_ancestor tree ss
                                      in
                                      [%debug_log "anc=%a a=%a rt=%a"
                                        nps anc nps a nps rt];

                                      if anc == a then begin
                                        a != rt &&
                                        let gi' = n'#gindex in
                                        (tree'#initial_leftmost rt')#gindex > gi' ||
                                        gi' > rt'#gindex
                                      end
                                      else if a == rt then begin (* !!! *)
                                        false
                                      end
                                      else if
                                        tree#is_initial_ancestor a anc &&
                                        let ss' = get_p_descendants is_stable' rt' in
                                        not (List.memq (nmap nd) ss')
                                      then
                                        false
                                      else begin
                                        let c0 = tree#is_initial_ancestor anc a in
                                        let c1 =
                                          List.for_all
                                            (fun x ->
                                              not (tree#is_initial_ancestor a x))
                                            rss
                                        in
                                        let c2 =
                                          List.for_all
                                            (fun x ->
                                              is_right tree x a &&
                                              tree#is_initial_ancestor anc x
                                            ) rss ||
                                          List.for_all
                                            (fun x ->
                                              is_left tree x a &&
                                              tree#is_initial_ancestor anc x
                                            ) rss
                                        in
                                        [%debug_log "c0=%B c1=%B c2=%B" c0 c1 c2];
                                        not (c0 && c1 && c2)
                                      end
                                  end
                                in
                                [%debug_log "n=%a b=%B" nps n b];
                                b
                          with
                            Not_found -> true
                        end
                        else begin (* tree'#is_initial_ancestor pnd' n' *)
                          [%debug_log "%a is an ancestor of %a" nps pnd' nps n'];
                          let conflicts', staying_move_only, conflicting_staying_moves, insttbl =
                            self#get_conflicts is_stable is_stable' tree tree' nmap nmap' n n'
                          in
                          begin
                            match child_staying_moves with
                            | [m] ->
                                if conflicting_staying_moves = [m] then begin
                                  [%debug_log "%a -> single_conflicting_staying_move" MID.ps m];
                                  single_conflicting_staying_move := (Some m)
                                end
                            | _ -> ()
                          end;
                          if
                            conflicts' = [] ||
                            staying_move_only &&
                            (!single_conflicting_staying_move = None)
                          then begin
                            false
                          end
                          else begin
                            [%debug_log "n'=%a" nps n'];
                            let instgts =
                              List.map (fun c' -> Hashtbl.find insttbl c') conflicts'
                            in
                            let _ = instgts in
                            [%debug_log "instgts=[%a]" nsps instgts];
                            let res = ref false in
                            let cur' = ref n'#initial_parent in
                            begin
                              try
                                while not (is_stable' !cur') do
                                  [%debug_log "cur'=%a" nps !cur'];
                                  [%debug_log "conflicts'=[%a]" nsps conflicts'];
                                  [%debug_log "instgts=[%a]" nsps instgts];
                                  begin
                                    match self#find_key_opt (!cur')#uid with
                                    | Some k -> begin
                                        [%debug_log "k=%s" (key_to_string k)];
                                        let a0, pos0, nb0 =
                                          try
                                            let a, (pt, ps) = Hashtbl.find ancto_tbl k in
                                            a, pt#position, List.length ps
                                          with
                                            Not_found ->
                                              match k with
                                              | K_mid m when m = mid -> anc, pos, nb
                                              | _ ->
                                                  let a0, pos0, nb0, _ =
                                                    self#get_ins_target tree nmap' is_stable' !cur'
                                                  in
                                                  a0, pos0, nb0
                                        in
                                        [%debug_log "a0=%a pos0=%d nb0=%d" nps a0 pos0 nb0];
                                        for i = 0 to nb0 - 1 do
                                          let ci = a0#initial_children.(pos0+i) in
                                          [%debug_log "ci=%a" nps ci];
                                          if
                                            List.exists
                                              (fun c' ->
                                                [%debug_log "c'=%a" nps c'];
                                                match self#find_key_opt c'#uid with
                                                | Some ck -> begin
                                                    [%debug_log "ck=%s" (key_to_string ck)];
                                                    let a1, pos1, nb1 =
                                                      try
                                                        let a, (pt, ps) = Hashtbl.find ancto_tbl ck in
                                                        a, pt#position, List.length ps
                                                      with
                                                        Not_found ->
                                                          let a1, pos1, nb1, _ =
                                                            self#get_ins_target tree nmap' is_stable' c'
                                                          in
                                                          a1, pos1, nb1
                                                    in
                                                    [%debug_log "a1=%a pos1=%d nb1=%d" nps a1 pos1 nb1];
                                                    (ci == a1 || is_ancestor ci a1) &&
                                                    let t = get_ancestor_below n a1 in
                                                    let tpos = t#initial_pos in
                                                    [%debug_log "t=%a tpos=%d" nps t tpos];
                                                    pos1 <= tpos && tpos <= pos1 + nb1 - 1
                                                end
                                                | None -> false
                                              ) conflicts'
                                          then begin
                                            [%debug_log "found: i=%d ci=%a" i nps ci];
                                            res := true;
                                            raise Exit
                                          end
                                        done
                                    end
                                    | None -> ()
                                  end;
                                  cur' := (!cur')#initial_parent;
                                done
                              with
                                Exit -> ()
                            end;
                            !res
                          end
                        end
                      in (* has_conflict *)
                      [%debug_log "has_conflict: %a -> %B" nps n has_conflict];

                      if has_conflict then begin

                        [%debug_log "upstream node found: n=%a - n'=%a" nps n nps n'];

                        let a, _ =
                          self#get_latest_common_ancestor tree
                            (List.map nmap' (get_p_descendants is_stable' rt'))
                        in
                        if a == nd#initial_parent then
                          let pn'_is_stable = is_stable' n'#initial_parent in
                          let u_opt =
                            if is_stable' rt'#initial_parent || pn'_is_stable then
                              Some K_stable
                            else
                              None
                          in
                          let c' =
                            if u_opt <> None && n == nd && pn'_is_stable then
                              c
                            else
                              c + 1
                          in
                          if c' > c && u_opt <> None then
                            let is_quasi_upstream_impossible =
                              self#is_quasi_upstream_impossible tree' is_stable is_stable'
                            in
                            if is_quasi_upstream_impossible rt' then
                              c, None, None
                            else
                              c', u_opt, None
                          else
                            c', u_opt, None
                        else
                          let anc_of_mid' = get_anc_below_mid n' mid in

                          [%debug_log "anc_of_mid' %a: %a -> %s" MID.ps mid nps n'
                            (match anc_of_mid' with
                            | Some x' -> node_to_uid_string x'
                            | None -> "")];

                          match anc_of_mid' with
                          | Some bn' -> begin
                              [%debug_log "bn'=%a" nps bn'];
                              let rp = get_rel_path rt'#apath bn'#apath in
                              let _is_excluded x' =
                                self#is_excluded x' &&
                                not (List.memq x' !group_heads) &&
                                (is_stable' x' || not (is_simple_ins x'))
                              in
                              let key = key_of_mid mid in
                              let is_excluded =
                                match !single_conflicting_staying_move with
                                | Some m -> begin
                                    [%debug_log "m=%a" MID.ps m];
                                    fun _ x' ->
                                      let b =
                                        x' == bn' ||
                                        _is_excluded x' &&
                                        match self#find_key_opt x'#uid with
                                        | Some ((K_mid m') as mk') ->
                                            [%debug_log "mk'=%s" (key_to_string mk')];
                                            m' <> m && not (is_ancestor_key (K_mid m) mk')
                                        | _ -> true
                                      in
                                      [%debug_log "%a -> %B" nps x' b];
                                      b
                                end
                                | None ->
                                    fun _ x' ->
                                      let b =
                                        x' == bn' ||
                                        let b = (try self#has_parent_path (nmap' x') with _ -> false) in if b then [%debug_log "!!!!!"]; b ||
                                        _is_excluded x' &&
                                        match self#find_key_opt x'#uid with
                                        | Some ((K_mid m) as mk) ->
                                            [%debug_log "mk=%s" (key_to_string mk)];
                                            m <> mid && not (is_ancestor_key mid_key mk)
                                        | Some k ->
                                            [%debug_log "k=%s" (key_to_string k)];
                                            not (is_ancestor_key key k)
                                        | _ -> true
                                      in
                                      [%debug_log "%a -> %B" nps x' b];
                                      b
                              in
                              let ap =
                                self#get_adjusted_path
                                  ~is_excluded find_ipos find_iofs is_stable' rt' rp
                              in
                              [%debug_log "internal path change: sub_path=%s"
                                (Path.to_string ap)];

                              let stid = self#find_stid n#initial_parent#uid in
                              if
                                try
                                  (self#find_mid stid) = mid
                                with
                                  Not_found -> false
                              then
                                c(* + 1*), Some key, Some ap
                              else begin
                                let r = self#get_subtree_root stid in
                                let rp = get_rel_path r#apath n#apath in
                                Hashtbl.add lift_tbl (r#apath, rp) (ap, key, 0);
                                Xset.add lifted_nodes n';
                                [%debug_log "%a will be lifted" nps n'];
                                c + 1, None, None
                              end
                          end
                          | None -> begin
                              match !ins_target with
                              | Some (stid', bn') -> begin
                                  let key' = key_of_stid stid' in
                                  [%debug_log "key'=%s" (key_to_string key')];
                                  let ap = self#get_subpath tree tree' nmap' key' bn' in
                                  [%debug_log "ap=%s" (Path.to_string ap)];
                                  c, Some key', Some ap
                              end
                              | None -> begin
                                  if is_stable' n'#initial_parent then
                                    c, Some K_stable, None
                                  else
                                    c + 1, None, None
                              end
                          end

                      end
                      else let nd' = nmap nd in if
                        let pnd' = nd'#initial_parent in
                        [%debug_log "nd'=%a pnd'=%a" nps nd' nps pnd'];
                        match self#find_key_opt pnd'#uid with
                        | Some (K_mid m) when m = mid -> begin
                            try
                              List.iteri
                                (fun i path ->
                                  [%debug_log "i=%d path=%s" i path#to_string];
                                  if path#key_opt = None then
                                    let ci = anc#initial_children.(i+pos) in
                                    [%debug_log "ci=%a" nps ci];
                                    if (ci == nd || is_ancestor ci nd) then begin
                                      let p' = self#acc rt' (Path.get_parent path#path) in
                                      [%debug_log "p'=%a" nps p'];
                                      if p' != pnd' then begin
                                        [%debug_log "found: ci=%a nd=%a pnd'=%a" nps ci nps nd nps pnd'];
                                        raise Exit
                                      end
                                    end
                                ) paths;
                              false
                            with
                              Exit -> true
                        end
                        | _ -> false
                      then begin
                        0, Some mid_key, Some (self#get_subpath tree tree' nmap' mid_key nd')
                      end
                      else begin (* not has_conflict *)
                        c, key_opt, sub_path_opt
                      end
                    ) (0, None, None) stable_nds
                with
                  Not_found -> 0, None, None
              end
            end
            else begin
              [%debug_log "%a is not a staying move" MID.ps mid];
              0, None, None
            end
          in
          [%debug_log "%a -> upc=%d k_opt=%s sp_opt=%s"
            nps nd upc (key_opt_to_string k_opt) (path_opt_to_string sp_opt)];

          upc, k_opt, sp_opt, !is_upw_stg_mov, !indirect_conflict
        in (* count_upstream_nds *)

        let get_extra_insertion tree (*rt*)_ is_stable excluded stable_nds =
          [%debug_log "excluded=[%a]" nsps excluded];
          [%debug_log "stable_nds=[%a]" nsps stable_nds];
          let excluded_, filtered_out =
          if stable_nds = [] then
            excluded, []
          else
            List.partition
              (fun n ->
                let pn = n#initial_parent in
                [%debug_log "n=%a pn=%a excluded=[%a]" nps n nps pn nsps excluded];
                try
                  let stid = self#find_stid n#uid in
                  let _, xs, _ = self#get_subtree_spec stid in
                  [%debug_log "xs=[%a]" nsps xs];
                  let b =
                    n#initial_pos > 0 &&
                    (xs = [] ||
                    List.for_all (fun x -> not (is_stable x)) xs &&
                    List.for_all
                      (fun x -> (get_p_descendants is_stable x) = []) xs) &&
                    Xarray.for_all
                      (fun x ->
                        List.memq x excluded
                      ) pn#initial_children &&
                    let nleft =
                      List.length
                        (List.filter (fun x -> is_left tree x n) stable_nds)
                    in
                    let nright =
                      List.length
                        (List.filter (fun x -> is_right tree x n) stable_nds)
                    in
                    [%debug_log "nleft=%d nright=%d" nleft nright];
                    nleft = 1 && nright = 1 ||
                    (nleft > 0 && nright > 0 &&
                     (*let a, _ = self#get_latest_common_ancestor tree stable_nds in
                     a == rt || tree#is_initial_ancestor rt a*)
                     List.for_all (fun x -> pn == x#initial_parent) stable_nds
                    )
                  in
                  not b
                with
                  Not_found -> true
              ) excluded
          in
          [%debug_log "excluded=[%a] filtered_out=[%a]" nsps excluded nsps filtered_out];
          excluded_, filtered_out
        in (* get_extra_insertion *)

        let check_for_staying_move mid anc_to path_to excepted_paths_to
            nmap nmap' is_stable is_stable' tree tree' nd nd'
            excluded excluded' remote_stable_nds' get_ipos get_iofs lift_tbl lifted_nodes is_ancestor_key'
            =
          [%debug_log "mid=%a nd=%a nd'=%a" MID.ps mid nps nd nps nd'];
          if self#is_staying_move mid then begin
            let conflicts', _, _, _ =
              self#get_conflicts ~ancto_opt:(Some anc_to) is_stable is_stable' tree tree' nmap nmap' nd nd'
            in
            [%debug_log "conflicts'=[%a]" nsps conflicts'];
            if conflicts' <> [] then begin
              let cs' =
                let pnd' = nd'#initial_parent in
                if not (is_stable' pnd') then
                  let pss' = get_p_descendants is_stable' pnd' in
                  let pss = List.map nmap' pss' in
                  let pa, _ = self#get_latest_common_ancestor tree pss in
                  List.filter
                    (fun n' ->
                      let ss' = get_p_descendants is_stable' n' in
                      let ss = List.map nmap' ss' in
                      let a, _ = self#get_latest_common_ancestor tree ss in
                      not (tree#is_initial_ancestor a pa)
                    ) conflicts'
                else
                  conflicts'
              in
              [%debug_log "cs'=[%a]" nsps cs'];
              if cs' <> [] then
                path_to#set_key_opt (Some K_stable)
            end;

            let is_stable_' x' = is_stable' x' && not (self#is_canceled_stable_node x') in

            if self#_is_upward_staying_move tree mid then begin
              [%debug_log "%a is upward_staying_move" MID.ps mid];
              let pps =
                List.fold_left
                  (fun l p ->
                    [%debug_log "p=\"%s\"" p#to_string];
                    let pp = Path.get_parent p#path in
                    if List.mem pp l then
                      l
                    else
                      pp :: l
                  ) [] excepted_paths_to
              in
              [%debug_log "pps=[%s]"
                (String.concat ";" (List.map Path.to_string pps))];
              List.iter
                (fun n' ->
                  [%debug_log "n'=%a" nps n'];
                  let has_no_ins =
                    try
                      let ins_root' =
                        self#get_subtree_root (self#find_stid n'#initial_parent#uid)
                      in
                      not (tree'#is_initial_ancestor nd' ins_root')
                    with
                      Not_found -> true
                  in
                  [%debug_log "has_no_ins=%B" has_no_ins];

                  if has_no_ins then
                  try
                    let e' = get_anc_in excluded' n' in
                    let rp' = get_rel_path nd'#apath e'#apath in
                    [%debug_log "e'=%a rp'=%s" nps e' (Path.to_string rp')];
                    let all_excluded_stable =
                      Array.for_all
                        (fun x' -> is_stable' x' && self#is_excluded x')
                        e'#initial_parent#initial_children
                    in
                    [%debug_log "all_excluded_stable=%B" all_excluded_stable];

                    let simple_ins_roots' = if tree' == tree2 then simple_ins_roots2 else simple_ins_roots1 in
                    let is_simple_ins x' =
                      let b =
                        Xset.mem simple_ins_roots' x' ||
                        let top_nodes = self#get_top_nodes nd' x' anc_to path_to excepted_paths_to in
                        let k_opt = self#find_key_opt x'#uid in
                        List.exists (fun p -> p#key_opt = k_opt) excepted_paths_to ||
                        self#_is_simple_ins tree is_stable' is_stable_' nmap' ~top_nodes x'
                      in
                      [%debug_log "%a -> %B" nps x' b];
                      b
                    in

                    let is_excluded lv x' =
                      [%debug_log "x'=%a" nps x'];
                      if lv = 0 && all_excluded_stable then
                        self#is_canceled_stable_node x' ||
                        List.for_all
                          (fun y' ->
                            self#is_canceled_stable_node y'
                          ) (get_p_descendants is_stable' x')
                      else
                        x' == e' ||
                        self#is_excluded x' &&
                        (not (is_stable' x') ||
                        self#is_excluded_tn is_stable' nmap' nd' x' e' anc_to path_to excepted_paths_to) &&
                        (is_stable' x' ||
                        not (is_simple_ins x') ||
                        let moveon x' = not (is_stable' x') in
                        let ss' = get_p_descendants ~moveon is_stable_' x' in
                        [%debug_log "x'=%a ss'=[%a]" nps x' nsps ss'];
                        match ss' with
                        | [] -> false
                        | _ when
                            (try
                              is_ancestor_key' (self#find_key x'#initial_parent#uid) (self#find_key x'#uid)
                            with _ -> false) -> false
                        | _ -> true)
                        (*(is_stable' x' ||
                        let moveon x' = not (is_stable' x') in
                        let ss' = get_p_descendants ~moveon is_stable_' x' in
                        [%debug_log "x'=%a ss'=[%a]" nps x' nsps ss'];
                        match ss' with
                        | [] -> false
                        (*| [s'] ->
                            let top_nodes = self#get_top_nodes nd' x' anc_to path_to excepted_paths_to in
                            let s = nmap' s' in
                            List.exists (fun tn -> is_ancestor tn s) top_nodes*)
                        | _ -> true)*)
                        (*self#is_excluded_tn is_stable' nmap' nd' x' e' anc_to path_to excepted_paths_to*)
                    in
                    (*let simple_ins_roots' = if tree' == tree2 then simple_ins_roots2 else simple_ins_roots1 in
                    let is_stable_' x' = is_stable' x' && not (self#is_canceled_stable_node x') in
                    let is_simple_ins x' =
                      let b =
                        Xset.mem simple_ins_roots' x' ||
                        self#_is_simple_ins tree' is_stable' is_stable_' nmap' x'
                      in
                      [%debug_log "%a -> %B" nps x' b];
                      Some b
                    in*)
                    let ap =
                      self#get_adjusted_path ~is_excluded(* ~is_simple_ins*)
                        get_ipos get_iofs is_stable' nd' rp'
                    in
                    [%debug_log "e'=%a rp'=%s ap=%s"
                      nps e' (Path.to_string rp') (Path.to_string ap)];

                    let n = nmap' n' in
                    let e = get_anc_in excluded n in
                    let rp = get_rel_path nd#apath e#apath in
                    [%debug_log "n'=%a n=%a e=%a rp=%s" nps n' nps n nps e (Path.to_string rp)];
                    (*let count_left_siblings is_stable e x =
                      assert (e == x || is_ancestor e x);
                      let has_stable_desc x = is_stable x || has_p_descendant is_stable x in
                      let doit x =
                        let c = ref 0 in
                        for i = 0 to x#initial_pos - 1 do
                          if has_stable_desc x#initial_parent#initial_children.(i) then
                            incr c
                        done;
                        !c
                      in
                      let count = ref (doit x) in
                      let cur = ref x in
                      while !cur != e do
                        cur := (!cur)#initial_parent;
                        count := !count + (doit !cur)
                      done;
                      [%debug_log "e=%a x=%a count=%d" nps e nps x !count];
                      !count
                    in
                    let rpc = count_left_siblings is_stable e n in
                    let rpc' = count_left_siblings is_stable' e' n' in
                    if rpc <> rpc' then begin
                      [%debug_log "%a will be lifted" nps n];
                      self#add_node_to_be_lifted n
                    end;*)

                    if
                      List.memq n' excluded' &&
                      List.for_all (fun p -> not (Path.is_prefix p ap)) pps
                    then begin
                      let apath_rp = nd#apath, rp in
                      if not (Hashtbl.mem lift_tbl apath_rp) then begin
                        [%debug_log "%a should be lifted" nps n];
                        Hashtbl.add lift_tbl apath_rp (ap, K_mid mid, 0);
                        Xset.add lifted_nodes n';
                        [%debug_log "%a is lifted" nps n']
                      end
                    end
                  with
                    Not_found -> ()
                ) remote_stable_nds'
            end
          end
        in (* check_for_staying_move *)

        let check_path_to ncond mcond tree' is_stable' is_stable nmap nmap' nd path_to paths_to key =
          let _ = paths_to in
          [%debug_log "nd=%a path_to=%s key=%s" nps nd path_to#to_string (key_to_string key)];
          let get_subtree_root_by_key, get_subtree_root_by_key', ancto_tbl, (*is_ancestor_key*)_ =
            if tree' == tree1 then
              self#get_subtree_root_by_key2, self#get_subtree_root_by_key1, anc1to_tbl, self#is_ancestor_key1
            else
              self#get_subtree_root_by_key1, self#get_subtree_root_by_key2, anc2to_tbl, self#is_ancestor_key2
          in

          if Xset.mem forced_upstream_nodes nd then begin
            let pnd = nd#initial_parent in
            let key_opt =
              match self#find_key_opt pnd#uid with
              | Some _ as k_opt -> k_opt
              | None when is_stable pnd -> Some K_stable
              | _ -> None
            in
            match key_opt with
            | Some _ -> begin
                path_to#set_key_opt key_opt;
                path_to#set_upstream 1;
                path_to#set_stay false;
                [%debug_log "nd=%a path_to=%s" nps nd path_to#to_string]
            end
            | _ -> ()
          end
          else if
            let moveon x = not (is_stable x) in
            let qups =
              get_p_descendants ~moveon (fun x -> is_stable x && self#is_quasi_upstream (nmap x)) nd
            in
            [%debug_log "qups=[%a]" nsps qups];
            List.exists
              (fun s ->
                let b =
                  try
                    let k_opt =
                      try
                        let k_opt, _, _ = self#get_parent_spec s in
                        k_opt
                      with
                        Not_found ->
                          let k_opt, _, _ =
                            self#get_parent_key_opt is_stable' is_stable tree1 tree2 nmap' nmap (nmap s)
                          in
                          k_opt
                    in
                    [%debug_log "k_opt=%s" (key_opt_to_string k_opt)];
                    match k_opt with
                    | Some K_stable -> is_stable nd#initial_parent
                    | Some k ->
                        let pk = self#find_key nd#initial_parent#uid in
                        k = pk
                    | None -> false
                  with
                    _ -> false
                in
                if b then
                  [%debug_log "found: s=%a" nps s];
                b
              ) qups(*qups <> []*)
            (*let ss =
              get_p_descendants ~moveon (fun x -> is_stable x && self#is_quasi_upstream (nmap x)) nd
            in
            [%debug_log "ss=[%a]" nsps ss];
            ss <> [] &&
            let ss' = List.map nmap ss in
            [%debug_log "ss'=[%a]" nsps ss'];
            let a, (pt, ps) = Hashtbl.find ancto_tbl key in
            let pos, nb = pt#position, List.length ps in
            let ca = a#initial_parent#initial_children in
            try
              for i = pos to pos + nb - 1 do
                if List.exists (is_ancestor ca.(i)) ss' then
                  raise Exit
              done;
              false
            with
              Exit -> true*)
          then
            [%debug_log "has quasi upstream descendant"]
          else if path_to#upstream > 0 && path_to#key_opt = None then begin
            match self#find_key_opt nd#uid with
            | Some K_stable as ko -> begin
                [%debug_log "%s" path_to#to_string];
                (*path_to#set_upstream 0;*)
                path_to#set_key_opt ko;
                path_to#set_stay false;
                [%debug_log " -> %s" path_to#to_string];
            end
            | _ -> ()
          end
          else begin
            let pos = path_to#position in
            let pnd = nd#initial_parent in
            [%debug_log "nd=%a pnd=%a" nps nd nps pnd];
            let key_opt = Some key(*self#find_key_opt nd#uid*) in
            try
              let pnd' =
                self#acc ~simple:true tree'#root (Path.get_parent path_to#path)
              in
              [%debug_log "pnd'=%a" nps pnd'];
              let key_cond () =
                match key_opt with
                | Some key -> begin
                    try
                      let sr' = get_subtree_root_by_key' key in
                      let moveon x' = x' != pnd' && not (is_stable' x') in
                      let ss' = get_p_descendants ~moveon is_stable' sr' in
                      [%debug_log "ss'=[%a]" nsps ss'];
                      let ss = List.map nmap' ss' in
                      [%debug_log "ss=[%a]" nsps ss];
                      let b = List.exists (fun x -> not (is_stable x#initial_parent)) ss in
                      [%debug_log "b=%B" b];
                      b
                    with _ -> true
                end
                | _ -> true
              in
              let cond =
                let moveon x' = not (is_stable' x') in
                let pred x' =
                  [%debug_log "x'=%a" nps x'];
                  match self#find_key_opt x'#uid with
                  | Some (K_mid m) as k_opt -> begin
                      [%debug_log "  -> %a" MID.ps m];
                      let b =
                        match key_opt with
                        | Some (K_mid mid) when m = mid -> false
                        | _ -> true
                      in
                      let b =
                        b &&
                        (path_to#key_opt = Some K_stable || k_opt <> key_opt || key_cond())
                      in
                      let b = b && mcond m pnd' pos && not (self#_is_upward_staying_move tree' m) in
                      if b then
                        [%debug_log "found: %a (%a)" nps x' MID.ps m];
                      b
                  end
                  | _ -> false
                in
                try
                  pred pnd' ||
                  let _ = get_p_ancestor ~moveon pred pnd' in
                  true
                with
                  Not_found -> false
              in
              [%debug_log "cond=%B" cond];
              let cond = cond || ncond() in
              [%debug_log "cond=%B" cond];
              (*let cond =
                cond ||
                try
                  let ppnd' = pnd'#initial_parent in
                  let ndp = nd#initial_pos in
                  is_stable ppnd' &&
                  nmap' ppnd' == pnd &&
                  Array.exists
                    (fun c ->
                      c#initial_pos < ndp &&
                      not (is_stable c) &&
                      let ss = get_p_descendants is_stable c in
                      [%debug_log "c=%a ss=[%a]" nps c nsps ss];
                      match ss with
                      | [] | [_] -> false
                      | _ ->
                          let ss' = List.map nmap ss in
                          [%debug_log "ss'=[%a]" nsps ss'];
                          let a', tnt' =
                            self#get_latest_common_ancestor tree' ss'
                          in
                          a' == ppnd' && List.exists (fun (x', _) -> x' == pnd') tnt'
                    ) pnd#initial_children
                with
                  _ -> false
              in
              [%debug_log "cond=%B" cond];*)
              let cond =
                cond ||
                (*let np = List.length paths_to in*)
                let _ = [%debug_log "pos=%d np=%d" pos (List.length paths_to)] in
                let moveon x = not (is_stable x) in
                let is_stable_ x = is_stable x && not (self#is_canceled_stable_node x) in
                try
                  is_stable pnd &&
                  let ndp = nd#initial_pos in
                  rev_array_exists
                    (fun c ->
                      c#initial_pos <> ndp &&
                      not (is_stable c) &&

                      let ss = get_p_descendants ~moveon is_stable_ c in
                      [%debug_log "c=%a ss=[%a]" nps c nsps ss];
                      match ss with
                      | [](* | [_]*) -> false
                      | _ ->
                          match self#find_key_opt c#uid with
                          | Some ck -> begin
                              [%debug_log "ck=%s" (key_to_string ck)];
                              try
                                let a', (pt, ps) = Hashtbl.find ancto_tbl ck in
                                let pos0 = pt#position in
                                let nb0 = List.length ps in
                                [%debug_log "a'=%a pos0=%d nb0=%d" nps a' pos0 nb0];
                                let pnd0' = nmap pnd in
                                (pnd0' == a' || is_ancestor pnd0' a') &&
                                (is_ancestor a' pnd' &&
                                 (
                                  (get_p_descendants ~moveon is_stable_ nd) = [] ||
                                  (try
                                    for i = pos0 to pos0+nb0-1 do
                                      let ai' = a'#initial_children.(i) in
                                      if ai' == pnd' || is_ancestor ai' pnd' then
                                        raise Exit
                                    done;
                                    false
                                  with
                                    Exit -> true
                                  )
                                 )
                                )
                              with
                                _ -> raise Defer
                          end
                          | _ -> false

                      (*let ss = get_p_descendants is_stable c in
                      [%debug_log "c=%a ss=[%a]" nps c nsps ss];
                      match ss with
                      | [] | [_] -> false
                      | _ ->
                          let ss' = List.map nmap ss in
                          [%debug_log "ss'=[%a]" nsps ss'];
                          let a', tnt' =
                            self#get_latest_common_ancestor tree' ss'
                          in
                          let pnd0' = nmap pnd in
                          (pnd0' == a' || is_ancestor pnd0' a') &&
                          (is_ancestor a' pnd' &&
                           ((get_p_descendants is_stable nd) = [] ||
                           List.exists
                             (fun x' ->
                               let b =
                                 try
                                   for i = pos to pos + np - 1 do
                                     let t' = pnd'#initial_children.(i) in
                                     if t' == x' || is_ancestor t' x' then
                                       raise Exit
                                   done;
                                   false
                                 with
                                   Exit -> true
                               in
                               [%debug_log "x'=%a b=%B" nps x' b];
                               b
                             ) ss' ||
                           a' == pnd')) &&
                          List.exists (fun (x', _) -> x' == pnd') tnt'*)

                    ) pnd#initial_children
                with
                | Defer -> raise Defer
                | _ -> false
              in
              [%debug_log "cond=%B" cond];
              if
                cond &&
                is_stable pnd &&
                not (is_stable' pnd') &&
                path_to#upstream = 0
              then begin
                path_to#set_upstream 1;
                path_to#set_stay false;
                [%debug_log "path_to=%s" path_to#to_string]
              end
              else if not (is_stable pnd) then begin
                let get_ins_target = self#get_ins_target tree' nmap is_stable in
                let has_ins () =
                  let moveon x = not (is_stable x) in
                  let pred x =
                    [%debug_log "x=%a" nps x];
                    match self#find_key_opt x#uid with
                    | Some _ as k_opt ->
                        k_opt <> key_opt && has_p_descendant is_stable x &&
                        let t', _, _, _ = get_ins_target x in t' != pnd'
                    | _ -> false
                  in
                  let b =
                    has_p_descendant ~moveon pred nd ||
                    has_p_sibling pred nd ||
                    has_p_sibling pred pnd
                  in
                  b,
                  try
                    let r = get_subtree_root_by_key (self#find_key pnd#uid) in
                    [%debug_log "r=%a" nps r];
                    has_p_sibling pred r
                  with _ -> false
                in
                let has_lower, has_upper = has_ins() in
                [%debug_log "has_lower=%B has_upper=%B" has_lower has_upper];
                if has_lower || has_upper then begin
                  match self#find_key_opt pnd#uid with
                  | Some k as k_opt -> begin
                      [%debug_log "k=%s" (key_to_string k)];
                      let ancto_tbl =
                        if tree' == tree1 then anc1to_tbl else anc2to_tbl
                      in
                      try
                        let a', (ppath_to, paths) = Hashtbl.find ancto_tbl k in
                        let ppos = ppath_to#position in
                        let nbdry = List.length paths in
                        [%debug_log "a'=%a ppos=%d nbdry=%d" nps a' ppos nbdry];
                        let pred ?(upper=false) n =
                          [%debug_log "n=%a" nps n];
                          let b =
                            n != nd && n != pnd &&
                            let k0_opt = self#find_key_opt n#uid in
                            (upper || k0_opt <> k_opt) &&
                            n != nd && not (is_stable n) &&
                            match k0_opt with
                            | Some k0 when k0 <> K_stable -> begin
                                [%debug_log "k0=%s" (key_to_string k0)];
                                try
                                  let t', (pt, ps) = Hashtbl.find ancto_tbl k0 in
                                  let p = pt#position in
                                  let nb = List.length ps in
                                  [%debug_log "a'=%a ppos=%d nbdry=%d: t'=%a p=%d nb=%d" nps a' ppos nbdry nps t' p nb];
                                  nb = 1 && t' == a' && ppos <> p && overlaps ppos (ppos+nbdry-1) p (p+nb-1) ||
                                  nb > 1 &&
                                  (t' == a' &&
                                   (p = ppos ||
                                   ppos < p && p <= ppos + nbdry - 1 &&
                                   not
                                     (array_range_exists
                                        (fun x' -> x' == pnd' || is_ancestor x' pnd')
                                        a'#initial_children ppos (p-1)) &&
                                   (List.nth paths (p - ppos))#key_opt = Some k0) ||
                                   is_ancestor a' t' &&
                                   array_range_exists
                                     (fun x' -> x' == pnd' || is_ancestor x' pnd')
                                     t'#initial_children p (p+nb-1))
                                with
                                  Not_found -> raise Defer
                                      (*try
                                        let t', p, nb = get_ins_target n in
                                        [%debug_log "t'=%a p=%d nb=%d" nps t' p nb];
                                        t' == a' && p = ppos ||
                                        is_ancestor a' t' &&
                                        array_range_exists (fun x -> is_ancestor x pnd') t'#initial_children p (p+nb-1)
                                        with
                                        _ -> false*)
                            end
                            | _ -> false
                          in
                          [%debug_log "%a -> %B" nps n b];
                          b
                        in (* pred *)
                        if
                          has_lower &&
                          ((is_ancestor a' pnd' &&
                           let moveon x' = x' != a' && not (is_stable' x') in
                           let pred x' =
                             [%debug_log "x'=%a" nps x'];
                             match self#find_key_opt x'#uid with
                             | Some (K_mid m) as xk_opt -> begin
                                 [%debug_log "  -> %a" MID.ps m];
                                 let b =
                                   xk_opt <> key_opt && xk_opt <> k_opt && mcond m pnd' pos
                                 in
                                 if b then
                                   [%debug_log "found: %a (%a)" nps x' MID.ps m];
                                 b
                             end
                             | _ -> false
                           in
                           try
                             let _ = get_p_ancestor ~moveon pred pnd' in
                             true
                           with
                             Not_found -> false
                          ) ||
                          let ca = pnd#initial_children in
                          [%debug_log "nd=%a pnd=%a ca=%a" nps nd nps pnd nsps (Array.to_list ca)];
                          Array.exists pred ca ||
                          (is_stable pnd#initial_parent &&
                          let pca = pnd#initial_parent#initial_children in
                          [%debug_log "pca=%a" nsps (Array.to_list pca)];
                          Array.exists pred pca))
                        then begin
                          let to_be_canceled =
                            let moveon x = not (is_stable x) in
                            has_p_descendant ~moveon
                              (fun x -> is_stable x &&
                                let x' = nmap x in
                                List.exists
                                  (fun (k_opt', _, _) ->
                                    [%debug_log "parent key found: %a -> %s" nps x' (key_opt_to_string k_opt')];
                                    k_opt' = k_opt
                                  ) (Hashtbl.find_all parent_spec_tbl x')
                              ) nd
                          in
                          if to_be_canceled then begin
                            [%debug_log "nd=%a: modification canceled" nps nd]
                          end
                          else begin
                            path_to#set_upstream 1;
                            path_to#set_stay false;
                            path_to#set_key_opt k_opt;
                            [%debug_log "nd=%a path_to=%s" nps nd path_to#to_string]
                          end
                        end
                        else if
                          has_upper &&
                          try
                            let r = get_subtree_root_by_key (self#find_key pnd#uid) in
                            is_stable r#initial_parent &&
                            let rca = r#initial_parent#initial_children in
                            [%debug_log "r=%a rca=%a" nps r nsps (Array.to_list rca)];
                            let moveon x = not (is_stable x) in
                            Array.exists
                              (fun n ->
                                n != r &&
                                (pred ~upper:true n ||
                                let b = has_p_descendant ~moveon (pred ~upper:false) n in
                                if b then
                                  [%debug_log "!!! n=%a" nps n];
                                b)
                              ) rca
                          with _ -> false
                        then begin
                          path_to#set_upstream 1;
                          path_to#set_stay false;
                          path_to#set_key_opt k_opt;
                          [%debug_log "nd=%a path_to=%s" nps nd path_to#to_string]
                        end
                      with
                        Not_found -> ()
                  end
                  | None -> ()
                end
              end
            with
              Not_found -> ()
          end
        in (* check_path_to *)

        let mkncond xs is_stable is_stable' tree tree' nmap nmap' () =
          let ss = List.filter is_stable xs in
          [%debug_log "ss=[%a]" nsps ss];
          let sxs =
            List.filter
              (fun x ->
                is_stable x && not (self#is_canceled_stable_node x)
              ) xs
          in
          [%debug_log "sxs=[%a]" nsps sxs];
          let nss = List.length ss in
          match sxs with
          (*| [] when nss > 0 -> true*)
          | [sx] when nss > 1 ->
              let sx' = nmap sx in
              let conflicts, _, _, _ =
                self#get_conflicts
                  is_stable' is_stable tree' tree nmap' nmap sx' sx
              in
              conflicts <> []
          | _ -> false
        in

        let recover_excluded filtered_out =
          if filtered_out <> [] then
            List.iter (Xset.add excluded_nodes) filtered_out
        in

        let dump_content tree root excluded =
          tree#dump_subtree_for_delta_ch root excluded
        in

        let irrf x = Fmt.Irr x in
        let revf x = Fmt.Rev x in

        (*let _get_child_staying_moves tbl stid_of_mid mid =
          let stid = stid_of_mid mid in
          let rt = self#get_subtree_root stid in
          let mids = ref [] in
          let _ =
            get_p_descendants
              (fun n ->
                match self#find_key_opt n#uid with
                | Some (K_mid m) ->
                    if self#is_staying_move m then begin
                      [%debug_log "%a -> %a" MID.ps m MID.ps mid];
                      Hashtbl.replace tbl m mid;
                      if not (List.mem m !mids) then
                        mids := m :: !mids;
                      true
                    end
                    else
                      false
                | _ -> false
              ) rt
          in
          !mids
        in
        let get_child_staying_moves1 =
          _get_child_staying_moves parent_staying_move_tbl1 self#stid_of_mid1
        in
        let get_child_staying_moves2 =
          _get_child_staying_moves parent_staying_move_tbl2 self#stid_of_mid2
        in!!!!!*)

        let _get_child_staying_moves tbl mid paths =
          Xlist.uniq
            (List.filter_map
               (fun p ->
                 match p#key_opt with
                 | Some (K_mid m) -> begin
                     if self#is_staying_move m then begin
                       if self#is_staying_move mid then begin
                         [%debug_log "%a -> %a" MID.ps m MID.ps mid];
                         Hashtbl.replace tbl m mid;
                       end;
                       Some m
                     end
                     else
                       None
                 end
                 | _ -> None
               ) paths)
        in
        let get_child_staying_moves1 mid paths =
          _get_child_staying_moves parent_staying_move_tbl1 mid paths
        in
        let get_child_staying_moves2 mid paths =
          _get_child_staying_moves parent_staying_move_tbl2 mid paths
        in

        let delta_info_flag = true in

        let is_def nd = Binding.is_def nd#data#binding in

        let info_add, paths_info_add, dump_info =
          if delta_info_flag && info_file_name <> "" then begin
            let scope_nodes = Xset.create 0 in
            let info_tbl = Hashtbl.create 0 in (* apath -> syn_cat * line_num * column_num *)
            let add ?(add_scope_node=true) ?(path="") nd =
              let ap =
                if path = "" then
                  Path.to_string nd#apath
                else
                  path
              in
              if not (Hashtbl.mem info_tbl ap) then begin
                let ndata = nd#data in
                let ln, cn = ndata#src_loc.Loc.start_line, ndata#src_loc.Loc.start_char in
                let scope_path_opt =
                  if is_def nd then begin
                    try
                      let sn = ndata#scope_node in
                      if add_scope_node then
                        Xset.add scope_nodes sn;
                      Some (Path.to_string sn#apath)
                    with
                      _ -> None
                  end
                  else
                    None
                in
                Hashtbl.add info_tbl ap (ndata, ln, cn, scope_path_opt)
              end
            in
            let paths_add anc path pathl tid tree rt =
              let len = List.length pathl in
              if len > 0 then begin
                let children = anc#initial_children in
                for i = path#position to len - 1 do
                  add children.(i)
                done;
                List.iter
                  (fun p ->
                    let n = tree#initial_acc ?from:(Some rt) p#path in
                    let path = sprintf "%s:%s" tid (Path.to_string p#path) in
                    add ~path n
                  ) pathl
              end
              else
                ()
            in
            let add_defs nd =
              let moveon _ = true in
              preorder_scan_whole_initial_subtree ~moveon nd
                (fun n ->
                  if is_def n || n#data#is_scope_creating then
                    add ~add_scope_node:false n
                )
            in
            let dump () =
              Xset.iter add_defs scope_nodes;
              let l =
                Hashtbl.fold
                  (fun ap (name, ln, cn, scope_path_opt) l ->
                    (ap, name, ln, cn, scope_path_opt)::l
                  ) info_tbl []
              in
              let sorted =
                List.fast_sort
                  (fun (_, _, ln0, cn0, _) (_, _, ln1, cn1, _) -> compare (ln0, cn0) (ln1, cn1))
                  l
              in
              let dest = Xchannel.Destination.of_file info_file_name in
              let info_ch = new Xchannel.out_channel dest in
              Xchannel.fprintf info_ch "{";
              let _ =
                List.fold_left
                  (fun comma (ap, ndata, ln, cn, scope_path_opt) ->
                    let name = ndata#elem_name_for_delta in
                    let aname_ =
                      try
                        let aname = try ndata#get_orig_name with _ -> ndata#get_name in
                        sprintf ",\"aname\":\"%s\"" (String.escaped aname)
                      with
                        _ -> ""
                    in
                    let scope_path_ =
                      match scope_path_opt with
                      | Some p -> sprintf ",\"scope_path\":\"%s\"" p
                      | None -> ""
                    in
                    Xchannel.fprintf info_ch
                      "%s\"%s\":{\"name\":\"%s\"%s,\"line\":%d,\"column\":%d%s}"
                      comma ap name aname_ ln cn scope_path_;
                    ","
                  ) "" sorted
              in
              Xchannel.fprintf info_ch "}";
              info_ch#close
            in
            add, paths_add, dump
          end
          else
            (fun ?(add_scope_node=true) ?(path="") _ -> ignore add_scope_node; ignore path; ()),
            (fun _ _ _ _ _ _ -> ()), (fun () -> ())
        in

        let fact_for_delta = options#fact_for_delta_flag in
        let fact_tbl = Hashtbl.create 0 in (* chg_inst -> fmt list *)
        let fact_add = Hashtbl.add fact_tbl in
        let triples = Xset.create 0 in
        let mkent = Triple.make_entity options in
        let triple_add cls cinst nd1 nd2 =
          Xset.add triples (cinst, Triple.p_is_a, cls);
          Xset.add triples (cinst, Triple.p_entity1, mkent tree1 nd1);
          Xset.add triples (cinst, Triple.p_entity2, mkent tree2 nd2)
        in

        let parent_path_tbl1 = Hashtbl.create 0 in (* path -> (pos, range) list *)
        let parent_path_tbl2 = Hashtbl.create 0 in (* path -> (pos, range) list *)

        (*let setup_parent_path_tbl tbl path excepted_paths rt =
          if not (Hashtbl.mem comp_cand_tbl rt) then
          let w = List.length excepted_paths in
          if w > 0 then begin
            let ppath, elem = Path.split path#path in
            if elem.Elem.ofs = 0. then
              tbl_add tbl ppath (elem.Elem.pos, w, rt)
          end
        in*)

        let nmap1 = nmapping#find in
        let nmap2 = nmapping#inv_find in

        (*let filter_out_canceled lifted_nodes =
          List.filter
            (fun x ->
              not (Xset.mem lifted_nodes x) && not (self#is_canceled_stable_node x))
        in
        let filter_out_canceled1 = filter_out_canceled lifted_nodes2 in
        let filter_out_canceled2 = filter_out_canceled lifted_nodes1 in*)

        let reg_edit_parent tbl parent_key_opt mkkey =
          match parent_key_opt with
          | Some k -> begin
              let k' = mkkey() in
              [%debug_log "%s -> %s" (key_to_string k') (key_to_string k)];
              Hashtbl.add tbl k' k
          end
          | None -> ()
        in

        let _mkfmt ed =

          [%debug_log "* %s" (to_string ed)];

          match ed with
          | Delete(nd1, excluded1) -> begin
              info_add nd1;
              let pnd1 = nd1#initial_parent in
              info_add pnd1;
              begin
                try
                  info_add pnd1#initial_parent;
                with _ -> ()
              end;

              let path1 = new path_c nd1#apath in

              let excepted_paths1 =
                List.map
                  (fun n1 ->
                    info_add n1; info_add n1#initial_parent;

                    let rel_path = get_rel_path path1#path n1#apath in

                    let force_lift =
                      check_to_be_lifted
                        self#is_stable1 self#is_stable2
                        nmap1 lifted_nodes1 tree1 nmapping#inv_find
                        n1
                    in
                    [%debug_log "force_lift: %a -> %B" nps n1 force_lift];

                    let key_opt, upstream, sub_path_opt =
                      self#get_parent_key_opt ~force_lift
                        self#is_stable1 self#is_stable2 tree1 tree2
                        nmapping#find nmapping#inv_find n1
                    in
                    new boundary_path ~upstream ~key_opt ~sub_path_opt rel_path
                  ) excluded1
              in
              [%debug_log "excepted_paths1: %s" (boundary_to_string excepted_paths1)];

              if irreversible_flag then begin
                let fmt = irrf (Fmt.Irr.mkdel path1 excepted_paths1) in

                [%debug_log "%s" (Fmt.to_string fmt)];

                if fact_for_delta then begin
                  let nd2 = self#find_from_or_into tree2 nmapping#find nd1 in
                  try
                    let cinst = self#make_chg_inst Editop.Tdel nd1 nd2 in
                    fact_add cinst [fmt];
                    triple_add Triple.c_del cinst nd1 nd2
                  with
                    Invalid_argument _(*"Triple._make_entity"*) -> ()
                end;

                [fmt]
              end
              else begin

                let stid = self#find_stid nd1#uid in

                [%debug_log "stid=%s" (stid_to_str stid)];

                let remote_stable_tbl1 =
                  get_remote_stable_tbl self#is_stable1 excluded1
                in
                let remote_stable_nds1 =
                  flatten_remote_stable_tbl remote_stable_tbl1
                in
                [%debug_log "remote_stable_nds1: [%s]"
                  (nodes_to_uids_string remote_stable_nds1)];

                (*let remote_stable_nds1 = filter_out_canceled1 remote_stable_nds1 in
                [%debug_log "filtered remote_stable_nds1=[%a]" nsps remote_stable_nds1];*)

                let excluded1_, filtered_out1 =
                  get_extra_insertion tree1 nd1 self#is_stable1 excluded1 remote_stable_nds1
                in

                let anc2, path2, excepted_paths2, simple2 =
                  self#get_opposite_path_and_excepted_paths lift_tbl2 lifted_nodes2
                    self#is_stable1 self#is_stable2
                    get_path2 nmapping#find nmapping#inv_find tree1 tree2
                    nd1 excluded1_ remote_stable_nds1
                in

                info_add anc2;
                paths_info_add anc2 path2 excepted_paths2 (stid_to_str stid) tree1 nd1;

                if simple2 then begin
                  [%debug_log "simple_ins_root: %a" nps nd1];
                  Xset.add simple_ins_roots1 nd1;
                end;

                recover_excluded filtered_out1; (* recovering excluded1 *)

                let excepted_nds1 =
                  List.filter
                    (fun n1 ->
                      self#is_stable1 n1 && not (self#is_canceled_stable_node n1) ||
                      List.mem_assq n1 remote_stable_tbl1
                    ) excluded1
                in
                [%debug_log "excepted_nds1: [%a]" nsps excepted_nds1];

                let key_opt, adj_opt, depth_opt, shift_opt =
                  get_parent_info excepted_nds1 nd1 path2 tree2 nmapping#find
                    self#is_stable1 self#is_stable2 simple2
                in

                let dumper = dump_content tree1 nd1 excluded1 in (* for reverse patch *)

                (*let pnd1 = nd1#initial_parent in*)
                [%debug_log "nd1=%a pnd1=%a" nps nd1 nps nd1#initial_parent];

                let ncond =
                  mkncond excluded1 self#is_stable1 self#is_stable2 tree1 tree2 nmap1 nmap2
                in
                let mcond m pnd' pos =
                  [%debug_log "m=%a pnd'=%a pos=%d" MID.ps m nps pnd' pos];
                  not (Hashtbl.mem edit_parent_tbl2 (key_of_mid m)) &&
                  self#is_staying_move m &&
                  try
                    let a', (pt, _) = Hashtbl.find anc2to_tbl (K_mid m) in
                    is_ancestor a' pnd' ||
                    a' == pnd' && pt#position = pos
                  with
                    Not_found -> raise Defer
                in
                let stid_key = K_stid stid in

                let check_path_to_ () =
                  check_path_to ncond mcond
                    tree2 self#is_stable2 self#is_stable1 nmap1 nmap2
                    nd1 path2 excepted_paths2 stid_key
                in
                begin
                  (*try
                    check_path_to_()
                  with
                    Defer ->
                      [%debug_log "deferred"];*)
                      self#reg_deferred_check check_path_to_
                end;

                [%debug_log "anc2to_tbl: %s -> %a" (key_to_string stid_key) nps anc2];
                Hashtbl.add anc2to_tbl stid_key (anc2, (path2, excepted_paths2));
                self#rev_ancto_tbl_add edit_seq#mem_mov2 rev_anc2to_tbl
                  stid_key anc2 path2 excepted_paths2 nd1;

                if path2#upstream > 0 then begin
                  [%debug_log "upstream_key: %s" (key_to_string stid_key)];
                  Xset.add upstream_keys2 stid_key
                end;

                self#reg_parent_key2 excepted_paths2 stid_key;

                let fmt =
                  revf (Fmt.Rev.mkdel stid
                          path1 excepted_paths1
                          path2 excepted_paths2 key_opt adj_opt depth_opt shift_opt dumper)
                in

                reg_edit_parent edit_parent_tbl2 key_opt (fun () -> key_of_stid stid);

                (*setup_parent_path_tbl parent_path_tbl2 path2 excepted_paths2 nd1;*)

                [%debug_log "%s" (Fmt.to_string fmt)];

                [fmt]
              end
          end
          | Insert(nd2, excluded2) -> begin

              let stid = self#find_stid nd2#uid in

              [%debug_log "stid=%s" (stid_to_str stid)];

              let remote_stable_tbl2 =
                get_remote_stable_tbl self#is_stable2 excluded2
              in
              let remote_stable_nds2 =
                flatten_remote_stable_tbl remote_stable_tbl2
              in
              [%debug_log "remote_stable_nds2: [%s]"
                (nodes_to_uids_string remote_stable_nds2)];

              let excluded2_, filtered_out2 =
                get_extra_insertion tree2 nd2 self#is_stable2 excluded2 remote_stable_nds2
              in

              let anc1, path1, excepted_paths1, simple1 =
                self#get_opposite_path_and_excepted_paths lift_tbl1 lifted_nodes1
                  self#is_stable2 self#is_stable1
                  get_path1 nmapping#inv_find nmapping#find tree2 tree1
                  nd2 excluded2_ remote_stable_nds2
              in

              info_add anc1;
              paths_info_add anc1 path1 excepted_paths1 (stid_to_str stid) tree2 nd2;

              if simple1 then begin
                [%debug_log "simple_ins_root: %a" nps nd2];
                Xset.add simple_ins_roots2 nd2;
              end;

              recover_excluded filtered_out2; (* recovering excluded2 *)

              let path2 = new path_c nd2#apath in

              let excluded2_ =
                (List.filter
                   (fun n2 ->
                     self#is_stable2 n2 && not (self#is_canceled_stable_node n2)
                   ) excluded2)
              in
              [%debug_log "excluded2 (stable and not canceled): [%a]" nsps excluded2_];
              let excepted_nds2 =
                List.filter
                  (fun n2 ->
                    self#is_stable2 n2 && not (self#is_canceled_stable_node n2) ||
                    List.mem_assq n2 remote_stable_tbl2
                  ) excluded2_
              in
              [%debug_log "excepted_nds2: [%a]" nsps excepted_nds2];

              let key_opt, adj_opt, depth_opt, shift_opt =
                get_parent_info excepted_nds2 nd2 path1 tree1 nmapping#inv_find
                  self#is_stable2 self#is_stable1 simple1
              in

              let dumper = dump_content tree2 nd2 excluded2 in

              (*let pnd2 = nd2#initial_parent in*)
              [%debug_log "nd2=%a pnd2=%a" nps nd2 nps nd2#initial_parent];

              let ncond =
                mkncond excluded2 self#is_stable2 self#is_stable1 tree2 tree1 nmap2 nmap1
              in
              let mcond m pnd' pos =
                [%debug_log "m=%a pnd'=%a pos=%d" MID.ps m nps pnd' pos];
                not (Hashtbl.mem edit_parent_tbl1 (key_of_mid m)) &&
                self#is_staying_move m &&
                try
                  let a', (pt, _) = Hashtbl.find anc1to_tbl (K_mid m) in
                  is_ancestor a' pnd' ||
                  a' == pnd' && pt#position = pos
                with
                  Not_found -> raise Defer
              in
              let stid_key = K_stid stid in

              let check_path_to_ () =
                check_path_to ncond mcond
                  tree1 self#is_stable1 self#is_stable2 nmap2 nmap1
                  nd2 path1 excepted_paths1 stid_key
              in
              begin
                (*try
                  check_path_to_()
                with
                  Defer ->
                    [%debug_log "deferred"];*)
                    self#reg_deferred_check check_path_to_
              end;

              [%debug_log "anc1to_tbl: %s -> %a" (key_to_string stid_key) nps anc1];
              Hashtbl.add anc1to_tbl stid_key (anc1, (path1, excepted_paths1));
              self#rev_ancto_tbl_add edit_seq#mem_mov1 rev_anc1to_tbl
                stid_key anc1 path1 excepted_paths1 nd2;

              if path1#upstream > 0 then begin
                [%debug_log "upstream_key: %s" (key_to_string stid_key)];
                Xset.add upstream_keys1 stid_key
              end
              else if self#is_moved anc1 then begin
                path1#set_stay true
              end;

              self#reg_parent_key1 excepted_paths1 stid_key;

              if irreversible_flag then begin
                let fmt =
                  irrf (Fmt.Irr.mkins stid
                          path1 excepted_paths1 key_opt adj_opt depth_opt shift_opt dumper)
                in

                reg_edit_parent edit_parent_tbl1 key_opt (fun () -> key_of_stid stid);

                (*setup_parent_path_tbl parent_path_tbl1 path1 excepted_paths1 nd2;*)

                [%debug_log "%s" (Fmt.to_string fmt)];

                if fact_for_delta then begin
                  let nd1 = self#find_from_or_into tree1 nmapping#inv_find nd2 in
                  try
                    let cinst = self#make_chg_inst Editop.Tins nd1 nd2 in
                    fact_add cinst [fmt];
                    triple_add Triple.c_ins cinst nd1 nd2
                  with
                    Invalid_argument _(*"Triple._make_entity"*) -> ()
                end;

                [fmt]
              end
              else begin
                let excepted_paths2 =
                  List.map
                    (fun n2 ->
                      let rel_path = get_rel_path path2#path n2#apath in

                      let force_lift =
                        check_to_be_lifted
                          self#is_stable2 self#is_stable1
                          nmap2 lifted_nodes2 tree2 nmapping#find
                          n2
                      in
                      [%debug_log "force_lift: %a -> %B" nps n2 force_lift];

                      let key_opt, upstream, sub_path_opt =
                        self#get_parent_key_opt ~force_lift
                          self#is_stable2 self#is_stable1 tree2 tree1
                          nmapping#inv_find nmapping#find n2
                      in
                      new boundary_path ~upstream ~key_opt ~sub_path_opt rel_path
                    ) excluded2
                in
                [%debug_log "excepted_paths2: %s" (boundary_to_string excepted_paths2)];

                let fmt =
                  revf (Fmt.Rev.mkins stid
                          path1 excepted_paths1 key_opt adj_opt depth_opt shift_opt dumper
                          path2 excepted_paths2)
                in

                [%debug_log "%s" (Fmt.to_string fmt)];

                [fmt]
              end
          end
          | Relabel(nd1, excluded1, nd2, excluded2) -> begin
              info_add nd1; info_add nd1#initial_parent;

              let path1 = new path_c nd1#apath in
              let path2 = new path_c nd2#apath in

              let sz1 = tree1#size_of_cluster (nd1, excluded1) in
              let sz2 = tree2#size_of_cluster (nd2, excluded2) in

              let same_elem =
                try
                  nd1#data#orig_elem_name_for_delta = nd2#data#orig_elem_name_for_delta
                with
                  Not_element -> false
              in
              if same_elem && sz1 = 1 && sz2 = 1 then begin
                let fmtl = node_diff_elem_attrs nd1 nd2 in

                if fact_for_delta then begin
                  try
                    let cinst = self#make_chg_inst Editop.Trel nd1 nd2 in
                    if fmtl <> [] then
                      fact_add cinst fmtl;
                    triple_add Triple.c_rel cinst nd1 nd2
                  with
                    Invalid_argument _(*"Triple._make_entity"*) -> ()
                end;

                fmtl
              end
              else begin
                let paths1 = nodes_to_paths path1 excluded1 in
                let paths2 = nodes_to_paths path2 excluded2 in

                let dumper =
                  if irreversible_flag then
                    dump_content tree2 nd2 excluded2
                  else
                    fun ch ->
                      output_st_elem_old ch;
                      dump_content tree1 nd1 excluded1 ch;
                      output_ed_elem_old ch;
                      output_st_elem_new ch;
                      dump_content tree2 nd2 excluded2 ch;
                      output_ed_elem_new ch
                in

                if irreversible_flag then begin
                  let fmt = irrf (Fmt.Irr.mkchg path1 paths1 dumper) in

                  [%debug_log "%s" (Fmt.to_string fmt)];

                  if fact_for_delta then begin
                    try
                      let cinst = self#make_chg_inst Editop.Trel nd1 nd2 in
                      fact_add cinst [fmt];
                      triple_add Triple.c_rel cinst nd1 nd2
                    with
                      Invalid_argument _(*"Triple._make_entity"*) -> ()
                  end;

                  [fmt]
                end
                else begin
                  let fmt = revf (Fmt.Rev.mkchg path1 paths1 path2 paths2 dumper) in

                  [%debug_log "%s" (Fmt.to_string fmt)];

                  [fmt]
                end
              end
          end
          | MoveInsert(mid, _, nd2, excluded2) -> begin
              let remote_stable_tbl2 =
                get_remote_stable_tbl self#is_stable2 excluded2
              in

              let remote_stable_nds2 =
                flatten_remote_stable_tbl remote_stable_tbl2
              in
              [%debug_log "remote_stable_nds2: [%s]"
                (nodes_to_uids_string remote_stable_nds2)];

              let excepted_nds2 =
                List.filter
                  (fun n2 ->
                    let b =
                      self#is_stable2 n2 && not (self#is_canceled_stable_node n2) ||
                      List.mem_assq n2 remote_stable_tbl2
                    in
                    b
                  ) excluded2
              in
              [%debug_log "excepted_nds2: [%a]" nsps excepted_nds2];

              let excluded2_, filtered_out2 =
                get_extra_insertion
                  tree2 nd2 self#is_stable2 excluded2 remote_stable_nds2
              in

              let anc1to, path1to, excepted_paths1to, simple1 =
                self#get_opposite_path_and_excepted_paths lift_tbl1 lifted_nodes1
                  self#is_stable2 self#is_stable1
                  get_path1 nmapping#inv_find nmapping#find tree2 tree1
                  nd2 excluded2_
                  (if remote_stable_nds2 = [] then
                    excepted_nds2
                  else
                    remote_stable_nds2)
              in
              [%debug_log "anc1to=%a path1to=%s excepted_paths1to=[%s]"
                nps anc1to path1to#to_string (boundary_to_string excepted_paths1to)];
              (*let pos = path1to#position in*)
              (*let nboundary = List.length excepted_paths1to in*)
              info_add anc1to;
              paths_info_add anc1to path1to excepted_paths1to
                (sprintf "m%s" (MID.to_raw mid)) tree2 nd2;

              let mid_key = K_mid mid in
              Hashtbl.add pre_anc1to_tbl mid_key anc1to;

              [%debug_log "excepted_paths1to: %s"
                (boundary_to_string excepted_paths1to)];

              if simple1 then begin
                [%debug_log "simple_ins_root: %a" nps nd2];
                Xset.add simple_ins_roots2 nd2;
              end;

              recover_excluded filtered_out2; (* recovering excluded2 *)

              (*let apath2 = nd2#apath in*)

              (*let path2from = new path_c apath2 in*)

              begin %debug_block
              let child_staying_moves1 =
                get_child_staying_moves1 mid excepted_paths1to
              in
              [%debug_log "child_staying_moves1=[%s]"
                (mids_to_string child_staying_moves1)];
              end;

              (*let mid_is_staying_move = self#is_staying_move mid in*)

              let excepted_nds2 =
                List.filter (fun x -> not (self#is_canceled_stable_node x)) excepted_nds2
              in
              [%debug_log "excepted_nds2: [%a]" nsps excepted_nds2];

              let key_opt1, adj_opt1, depth_opt1, shift_opt1 =
                get_parent_info excepted_nds2 nd2 path1to tree1 nmapping#inv_find
                  self#is_stable2 self#is_stable1 simple1
              in

              [%debug_log "anc1to_tbl: %s -> %a" (key_to_string mid_key) nps anc1to];
              Hashtbl.add anc1to_tbl mid_key (anc1to, (path1to, excepted_paths1to));
              self#rev_ancto_tbl_add edit_seq#mem_mov1 rev_anc1to_tbl
                mid_key anc1to path1to excepted_paths1to nd2;

              if path1to#upstream > 0 then begin
                [%debug_log "upstream_key: %s" (key_to_string mid_key)];
                Xset.add upstream_keys1 mid_key
              end
              else if self#is_moved anc1to then begin
                path1to#set_stay true
              end;

              self#reg_parent_key1 excepted_paths1to mid_key;

              Hashtbl.add movins_tbl mid
                (anc1to, path1to, excepted_paths1to, simple1,
                 key_opt1, adj_opt1, depth_opt1, shift_opt1);

              if irreversible_flag then begin
                reg_edit_parent edit_parent_tbl1 key_opt1 (fun () -> key_of_mid mid);
              end
              else begin
                (* not yet *)
              end;
              []
          end
          | Move(mid, _, nd1, excluded1, nd2, excluded2) -> begin
              info_add nd1;
              let pnd1 = nd1#initial_parent in
              info_add pnd1;
              begin
                try
                  info_add pnd1#initial_parent;
                with _ -> ()
              end;

              let remote_stable_tbl1 =
                get_remote_stable_tbl self#is_stable1 excluded1
              in
              let remote_stable_tbl2 =
                get_remote_stable_tbl self#is_stable2 excluded2
              in

              let remote_stable_nds1 =
                flatten_remote_stable_tbl remote_stable_tbl1
              in
              [%debug_log "remote_stable_nds1: [%s]"
                (nodes_to_uids_string remote_stable_nds1)];

              let remote_stable_nds2 =
                flatten_remote_stable_tbl remote_stable_tbl2
              in
              [%debug_log "remote_stable_nds2: [%s]"
                (nodes_to_uids_string remote_stable_nds2)];

              let excepted_nds2 =
                List.filter
                  (fun n2 ->
                    let b =
                      self#is_stable2 n2 && not (self#is_canceled_stable_node n2) ||
                      List.mem_assq n2 remote_stable_tbl2
                    in
                    b
                  ) excluded2
              in
              [%debug_log "excepted_nds2: [%a]" nsps excepted_nds2];

              (*let excluded2_, filtered_out2 =
                get_extra_insertion
                  tree2 nd2 self#is_stable2 excluded2 remote_stable_nds2
              in*)

              let anc1to, path1to, excepted_paths1to, simple1,
                key_opt1, adj_opt1, depth_opt1, shift_opt1
                  =
                try
                  Hashtbl.find movins_tbl mid
                with _ -> assert false
              in

              (*let anc1to, path1to, excepted_paths1to, simple1 =
                self#get_opposite_path_and_excepted_paths lift_tbl1 lifted_nodes1
                  self#is_stable2 self#is_stable1
                  get_path1 nmapping#inv_find nmapping#find tree2 tree1
                  nd2 excluded2_
                  (if remote_stable_nds2 = [] then
                    excepted_nds2
                  else
                    remote_stable_nds2)
              in*)
              [%debug_log "anc1to=%a path1to=%s excepted_paths1to=[%s]"
                nps anc1to path1to#to_string (boundary_to_string excepted_paths1to)];

              let pos = path1to#position in
              let nboundary = List.length excepted_paths1to in
              (*info_add anc1to;
              paths_info_add anc1to path1to excepted_paths1to
                (sprintf "m%s" (MID.to_raw mid)) tree2 nd2;*)

              let mid_key = K_mid mid in
              (*Hashtbl.add pre_anc1to_tbl mid_key anc1to;*)

              [%debug_log "excepted_paths1to: %s"
                (boundary_to_string excepted_paths1to)];

              (*if simple1 then
                Xset.add simple_ins_roots2 nd2;*)

              (*recover_excluded filtered_out2; (* recovering excluded2 *)*)

              let apath1 = nd1#apath in
              let apath2 = nd2#apath in

              let path1from = new path_c apath1 in
              let path2from = new path_c apath2 in

              let child_staying_moves1 =
                get_child_staying_moves1 mid excepted_paths1to
              in
              [%debug_log "child_staying_moves1=[%s]"
                (mids_to_string child_staying_moves1)];

              let mid_is_staying_move = self#is_staying_move mid in

              let excepted_paths1from =
                let parent_ins_point_opt =
                  Some (mid_key, anc1to, pos, nboundary)
                in
                List.map
                  (fun n1 ->
                    [%debug_log "n1=%a" nps n1];
                    info_add n1; info_add n1#initial_parent;

                    let rel_path = get_rel_path path1from#path n1#apath in

                    if not (self#is_stable1 n1) then
                      new boundary_path rel_path
                    else

                    let n2 = nmap1 n1 in

                    let upc, k_opt, sp_opt, is_upward_staying_move, indirect_conflict =
                      count_upstream_nds mid nd1 nd2
                        anc1to path1to excepted_paths1to simple1 child_staying_moves1
                        self#is_stable1 self#is_stable2
                        remote_stable_tbl1 remote_stable_tbl2
                        nmapping#find nmapping#inv_find tree1 tree2 lift_tbl1 lifted_nodes1
                        n1
                    in
                    [%debug_log "indirect_conflict: %a -> %B" nps n1 indirect_conflict];
                    [%debug_log "n1=%a n2=%a nd1=%a" nps n1 nps n2 nps nd1];
                    (*let force_lift0 =
                      try
                        (*let n2 = nmap1 n1 in*)
                        let p2 = n2#initial_parent in
                        not (self#has_mid (self#find_stid nd1#initial_parent#uid)) &&
                        not (self#is_stable2 p2) &&
                        not (self#has_mid (self#find_stid p2#uid)) &&
                        not (self#is_canceled_stable_node n2) &&
                        not (Xset.mem lifted_nodes1 n1) &&
                        upc > 0
                      with _ -> false
                    in
                    [%debug_log "force_lift0: %a -> %B" nps n1 force_lift0];*)

                    let force_lift =
                      (*force_lift0 ||*)
                      check_to_be_lifted
                        self#is_stable1 self#is_stable2
                        nmap1 lifted_nodes1 tree1 nmapping#inv_find
                        n1
                    in
                    [%debug_log "force_lift: %a -> %B" nps n1 force_lift];

                    let is_downward_staying_move =
                      let get_ancestor_mids n =
                        let l = ref [] in
                        begin
                          try
                            scan_ancestors n
                              (fun n ->
                                match self#find_key_opt n#uid with
                                | Some ((K_mid _) as key) -> l := key :: !l
                                | _ -> ()
                              )
                          with _ -> ()
                        end;
                        !l
                      in
                      try
                        (*if self#is_stable1 n1 then
                          let n2 = nmap1 n1 in*)
                          let _mids1 = Xlist.uniq (get_ancestor_mids n1) in
                          let _mids2 = Xlist.uniq (get_ancestor_mids n2) in
                          let mids1 = List.filter (fun x -> List.mem x _mids2) _mids1 in
                          let mids2 = List.filter (fun x -> not (List.mem x _mids1)) _mids2 in
                          [%debug_log "mids1: [%s]" (keys_to_string mids1)];
                          [%debug_log "mids2: [%s]" (keys_to_string mids2)];

                          List.exists
                            (fun mk ->
                              let r1 = self#get_subtree_root (self#stid_of_key1 mk) in
                              [%debug_log "r1=%a" nps r1];
                              try
                                let a1 =
                                  get_p_ancestor
                                    (fun x ->
                                      match self#find_key_opt x#uid with
                                      | Some k -> List.mem k mids1
                                      | _ -> false
                                    ) r1
                                in
                                let _ = a1 in
                                [%debug_log "a1=%a" nps a1];
                                true
                              with _ -> false
                            ) mids2
                        (*else
                          false*)

                      with _ -> false
                    in
                    [%debug_log "is_downward_staying_move: %a -> %B"
                      nps n1 is_downward_staying_move];

                    let is_excluded x =
                      let b =
                      if
                        not (self#is_stable2 x) &&
                        excepted_nds2 = [] &&
                        match self#find_key_opt x#initial_parent#uid with
                        | Some (K_mid m) -> self#is_staying_move m
                        | _ -> false
                      then
                        false
                      else
                        self#is_excluded x
                      in
                      [%debug_log "x=%a b=%B" nps x b];
                      b
                    in

                    let has_another_ins, to_be_lifted, force_lift =
                      (*if self#is_stable1 n1 then
                        let n2 = nmap1 n1 in*)
                        match self#find_key_opt n2#initial_parent#uid with
                        | Some (K_mid m) when m = mid -> false, true, force_lift
                        | Some k -> begin
                            [%debug_log "k=%s" (key_to_string k)];
                            if not (Hashtbl.mem anc1to_tbl k) then
                              true, false, force_lift
                            else
                            try
                              (*let get_stable_anc x =
                                let a = get_p_ancestor self#is_stable1 x in
                                [%debug_log "a=%a" nps a];
                                a
                              in*)
                              (*let r2 = self#get_subtree_root (self#stid_of_key2 k) in
                              [%debug_log "r2=%a" nps r2];
                              let t1, _, _ = self#get_ins_target tree1 nmap2 self#is_stable2 r2 in
                              [%debug_log "anc1to=%a n1=%a n2=%a k=%s r2=%a t1=%a"
                                nps anc1to nps n1 nps n2 (key_to_string k) nps r2 nps t1];*)
                              let t1, p1, nb1 =
                                let t1, (pt1, ps1) = Hashtbl.find anc1to_tbl k in
                                t1, pt1#position, List.length ps1
                              in
                              [%debug_log "anc1to=%a n1=%a n2=%a k=%s t1=%a p1=%d nb1=%d"
                                nps anc1to nps n1 nps n2 (key_to_string k) nps t1 p1 nb1];
                              [%debug_log "k_opt=%s upc=%d sp_opt=%s"
                                (key_opt_to_string k_opt) upc (path_opt_to_string sp_opt)];
                              (*let get_ins_target =
                               self#get_ins_target tree1 nmap2 self#is_stable2
                              in*)
                              true,
                              not (self#is_staying_move mid) ||
                              (*not (self#has_destined_upstream tree2 get_ins_target n2) ||*)
                              (*t1 == anc1to || *)is_ancestor t1 anc1to && is_ancestor anc1to n1(* ||
                              get_stable_anc t1 != get_stable_anc anc1to*),
                              force_lift ||
                              is_ancestor t1 anc1to && is_ancestor anc1to n1 &&
                              let xp1 = (get_ancestor_below anc1to t1)#initial_pos in
                              let xp = (get_ancestor_below n1 anc1to)#initial_pos in
                              [%debug_log "xp1=%d p1=%d nb1=%d" xp1 p1 nb1];
                              [%debug_log "xp=%d pos=%d nboundary=%d" xp pos nboundary];
                              p1 <= xp1 && xp1 <= p1 + nb1 - 1 &&
                              pos <= xp && xp <= pos + nboundary - 1 ||
                              let conflicts', _, _, _ =
                                self#get_conflicts
                                  ~parent_ins_point_opt:(Some (k, t1, p1, nb1))
                                  self#is_stable1 self#is_stable2 tree1 tree2 nmap1 nmap2 n1 n2
                              in
                              conflicts' <> []
                            with
                              _ -> true, true, false(*force_lift*)
                        end
                        | _ -> true, true, force_lift
                      (*else
                        false, true, force_lift*)
                    in
                    [%debug_log "has_another_ins: %a -> %B" nps n1 has_another_ins];
                    [%debug_log "to_be_lifted: %a -> %B" nps n1 to_be_lifted];
                    [%debug_log "force_lift: %a -> %B" nps n1 force_lift];

                    let has_composite_ins () =
                      let b =
                        try
                          is_upward_staying_move && anc1to == nd1#initial_parent &&
                          let path1to_pos = path1to#position in
                          let i = path1to_pos - nd1#initial_pos in
                          [%debug_log "path1to=%s i=%d nd1#initial_pos=%d"
                            path1to#to_string i nd1#initial_pos];
                          let bpath = List.nth excepted_paths1to i in
                          [%debug_log "bpath=%s" bpath#to_string];
                          bpath#key_opt <> None
                        with
                          _ -> false
                      in
                      [%debug_log "b=%B" b];
                      b
                    in

                    let key_opt, upstream, sub_path_opt =
                      if
                        not has_another_ins &&
                        (force_lift || has_composite_ins()) &&
                        (is_upward_staying_move || is_downward_staying_move)
                      then begin
                        let find_ipos, find_iofs =
                          self#find_intermediate_pos1, self#find_intermediate_ofs1
                        in
                        (*let n2 = nmap1 n1 in*)
                        if tree2#is_initial_ancestor nd2 n2 then begin
                          let all_excluded =
                            Array.for_all
                              (*self#*)is_excluded
                              n2#initial_parent#initial_children
                          in
                          [%debug_log "all_excluded=%B" all_excluded];

                          let all_excluded_stable =
                            Array.for_all
                              (fun x -> self#is_stable2 x && (*self#*)is_excluded x)
                              n2#initial_parent#initial_children
                          in
                          [%debug_log "all_excluded_stable=%B" all_excluded_stable];

                          let is_stable2_ x =
                            let b =
                            self#is_stable2 x &&
                            not (self#is_canceled_stable_node x) &&
                            not (self#is_node_to_be_lifted x) &&
                            not (Xset.mem lifted_nodes1 (nmap2 x))
                            in
                            [%debug_log "x=%a b=%B" nps x b];
                            b
                          in
                          (*let get_ins_target =
                            self#get_ins_target tree1 nmap2 self#is_stable2
                          in*)
                          let is_simple_ins x =
                            let b =
                              Xset.mem simple_ins_roots2 x ||
                              let top_nodes =
                                self#get_top_nodes nd2 x anc1to path1to excepted_paths1to
                              in
                              let k_opt = self#find_key_opt x#uid in
                              List.exists (fun p -> p#key_opt = k_opt) excepted_paths1to ||
                              self#_is_simple_ins tree1 self#is_stable2 is_stable2_ nmap2
                                ~top_nodes x
                            in
                            [%debug_log "%a -> %B" nps x b];
                            b
                          in

                          let is_excluded =
                            if all_excluded then
                              fun lv x ->
                                if lv = 0 && all_excluded_stable then
                                  self#is_canceled_stable_node x ||
                                  List.for_all
                                    (fun y ->
                                      self#is_canceled_stable_node y
                                    ) (get_p_descendants self#is_stable2 x)
                                else
                                  self#is_excluded x &&
                                  (match self#find_key_opt x#uid with
                                  | Some xk -> begin
                                      match self#find_key_opt x#initial_parent#uid with
                                      | Some pk -> not (self#is_ancestor_key1 pk xk)
                                      | None -> true
                                  end
                                  | None -> true) &&
                                  (
                                   not (self#is_stable2 x) ||
                                   self#is_excluded_tn self#is_stable2 nmap2
                                     nd2 x n2 anc1to path1to excepted_paths1to
                                  ) &&
                                  (
                                   self#is_stable2 x ||
                                   (match get_p_descendants self#is_stable2 x with
                                   | [] -> false
                                   | [s2] ->
                                       let top_nodes =
                                         self#get_top_nodes nd2 x anc1to path1to excepted_paths1to
                                       in
                                       let s1 = nmap2 s2 in
                                       List.exists (fun tn -> is_ancestor tn s1) top_nodes
                                   | _ -> true
                                   ) &&
                                   not (is_simple_ins x) &&
                                   try
                                     not
                                       (self#is_ancestor_key1
                                          (self#find_key x#initial_parent#uid)
                                          (self#find_key x#uid))
                                   with _ -> true
                                  )
                            (*else if self#paths_to_have_frac_ofs excepted_paths1to then
                              fun _ x -> is_excluded x*)
                            else
                              let group_heads =
                                Hashtbl.fold
                                  (fun _ nl l ->
                                    try (List.hd (List.rev nl))::l with _ -> l
                                  ) group_tbl []
                              in
                              fun _ x ->
                                let b =
                                  x == n2 ||
                                  (*self#*)is_excluded x && not (List.memq x group_heads) &&
                                  (self#is_stable2 x ||
                                  not (is_simple_ins x) ||
                                  let moveon x = not (self#is_stable2 x) in
                                  get_p_descendants ~moveon is_stable2_ x <> [] &&
                                  try
                                    not
                                      (self#is_ancestor_key1
                                         (self#find_key x#initial_parent#uid)
                                         (self#find_key x#uid))
                                  with _ -> true) &&
                                  self#is_excluded_tn self#is_stable2 nmap2
                                    nd2 x n2 anc1to path1to excepted_paths1to
                                in
                                [%debug_log "b=%B x=%a n2=%a" b nps x nps n2];
                                b
                          in
                          (*let is_stable_ x = self#is_stable2 x && not (self#is_canceled_stable_node x) in
                          let is_simple_ins x =
                            let b =
                              Xset.mem simple_ins_roots2 x ||
                              let top_nodes = self#get_top_nodes nd2 x anc1to path1to excepted_paths1to in
                              self#_is_simple_ins tree1 self#is_stable2 is_stable_ nmap2 ~top_nodes x
                            in
                            [%debug_log "%a -> %B" nps x b];
                            Some b
                          in*)
                          let rp = get_rel_path nd2#apath n2#apath in
                          let ap =
                            self#get_adjusted_path ~is_excluded(* ~is_simple_ins*)
                              find_ipos find_iofs self#is_stable2 nd2 rp
                          in
                          [%debug_log "internal path change: sub_path=%s" (Path.to_string ap)];
                          let key = key_of_mid mid in
                          Some key, 0, Some ap
                        end
                        else
                          k_opt, upc, sp_opt
                      end
                      else if
                        mid_is_staying_move && (not force_lift || indirect_conflict) &&
                        to_be_lifted
                      then begin
                        [%debug_log "%a is a staying move" MID.ps mid];
                        k_opt, upc, sp_opt
                      end
                      else
                        let parent_ins_point_opt =
                          if is_ancestor nd2 n2 then
                            parent_ins_point_opt
                          else
                            None
                        in
                        self#get_parent_key_opt
                          ~force_lift ~parent_ins_point_opt ~anc_to_opt:(Some anc1to)
                          self#is_stable1 self#is_stable2 tree1 tree2
                          nmapping#find nmapping#inv_find n1
                    in
                    [%debug_log "%a -> (%s, %d, %s)"
                      nps n1 (key_opt_to_string key_opt) upstream (path_opt_to_string sub_path_opt)];
                    Hashtbl.add parent_spec_tbl n1 (key_opt, upstream, sub_path_opt);
                    new boundary_path ~upstream ~key_opt ~sub_path_opt rel_path
                  ) excluded1
              in
              [%debug_log "excepted_paths1from: %s"
                (boundary_to_string excepted_paths1from)];

              (*let excepted_nds2 =
                List.filter (fun x -> not (self#is_canceled_stable_node x)) excepted_nds2
              in
              [%debug_log "excepted_nds2: [%a]" nsps excepted_nds2];

              let key_opt1, adj_opt1, depth_opt1, shift_opt1 =
                get_parent_info excepted_nds2 nd2 path1to tree1 nmapping#inv_find
                  self#is_stable2 self#is_stable1 simple1
              in*)

              let excepted_nds1 =
                List.filter
                  (fun n1 ->
                    let b =
                      self#is_stable1 n1 && not (self#is_canceled_stable_node n1) ||
                      List.mem_assq n1 remote_stable_tbl1
                    in
                    b
                  ) excluded1
              in
              [%debug_log "excepted_nds1: [%a]" nsps excepted_nds1];

              check_for_staying_move mid anc1to path1to excepted_paths1to
                nmap1 nmap2 self#is_stable1 self#is_stable2 tree1 tree2 nd1 nd2
                excluded1 excluded2 remote_stable_nds2
                self#find_intermediate_pos1 self#find_intermediate_ofs1
                lift_tbl1 lifted_nodes1 self#is_ancestor_key1;

              if
                try
                  List.iter2
                    (fun p1 n1 ->
                      if
                        p1#upstream > 0 &&
                        (match p1#key_opt with
                        | Some k when k <> mid_key -> true
                        | _ -> false) &&
                        self#is_stable1 n1 && is_ancestor nd2 (nmap1 n1)
                      then
                        raise Exit
                  ) excepted_paths1from excluded1;
                  true
                with
                  Exit -> false
              then begin
                let ncond =
                  mkncond excluded2 self#is_stable2 self#is_stable1 tree2 tree1 nmap2 nmap1
                in
                let mcond m (*pnd'*)_ (*pos*)_ =
                  [%debug_log "mid=%a m=%a" MID.ps mid MID.ps m];
                  not (Hashtbl.mem edit_parent_tbl1 (key_of_mid m)) &&
                  m = mid || self#is_staying_move m && not (self#_is_upward_staying_move tree1 m)
                in
                let check_path_to_ () =
                  check_path_to ncond mcond
                    tree1 self#is_stable1 self#is_stable2 nmap2 nmap1
                    nd2 path1to excepted_paths1to mid_key
                in
                begin
                  (*try
                    check_path_to_()
                  with
                    Defer ->
                      [%debug_log "deferred"];*)
                      self#reg_deferred_check check_path_to_
                end
              end;

              (*[%debug_log "anc1to_tbl: %s -> %a" (key_to_string mid_key) nps anc1to];
              Hashtbl.add anc1to_tbl mid_key (anc1to, (path1to, excepted_paths1to));
              self#rev_ancto_tbl_add edit_seq#mem_mov1 rev_anc1to_tbl mid_key anc1to path1to excepted_paths1to nd2;

              if path1to#upstream > 0 then begin
                [%debug_log "upstream_key: %s" (key_to_string mid_key)];
                Xset.add upstream_keys1 mid_key
              end;

              self#reg_parent_key1 excepted_paths1to mid_key;*)

              let _ =
                let set_to_be_lifted x =
                  self#add_node_to_be_lifted ~key:mid_key x;
                  begin
                    try
                      List.iter2
                        (fun e1 rp1 ->
                          if x == e1 && rp1#key_opt = None then begin
                            [%debug_log "x=%a rp1=%s" nps x rp1#to_string];
                            let k_opt, upc, sp_opt =
                              self#get_parent_key_opt ~force_lift:true
                                self#is_stable1 self#is_stable2 tree1 tree2
                                nmapping#find nmapping#inv_find x
                            in
                            rp1#set_key_opt k_opt;
                            rp1#set_upstream upc;
                            rp1#set_sub_path_opt sp_opt
                          end
                        ) excluded1 excepted_paths1from
                    with
                      Exit -> ()
                  end
                in
                let pos = path1to#position in
                let npaths = List.length excepted_paths1to in
                [%debug_log "anc_to=%a pos=%d npaths=%d" nps anc1to pos npaths];
                let cl = ref [] in
                for i = pos + npaths - 1 downto pos do
                  let ci = anc1to#initial_children.(i) in
                  cl := ci :: !cl
                done;
                [%debug_log "cl=[%a]" nsps !cl];
                let ss1 = List.map nmap2 remote_stable_nds2 in
                [%debug_log "remote_stable_nds2=[%a]" nsps remote_stable_nds2];
                [%debug_log "ss1=[%a]" nsps ss1];
                List.iter2
                  (fun s1 s2 ->
                    if not (self#is_node_to_be_lifted s1) then
                    let b = ref false in
                    List.iter2
                      (fun c rp2 ->
                        if c == s1 || is_ancestor c s1 then begin
                          [%debug_log "c=%a rp2=%s" nps c rp2#to_string];
                          b := true;
                          [%debug_log "s1=%a s2=%a" nps s1 nps s2];
                          let prp2 = Path.get_parent rp2#path in
                          [%debug_log "prp2=%s" (Path.to_string prp2)];
                          try
                            let p2 = self#acc nd2 prp2 in
                            [%debug_log "p2=%a" nps p2];
                            if
                              match rp2#key_opt with
                              | Some _ -> not (is_ancestor p2 s2)
                              | None -> (*p2 != s2#initial_parent*)not (is_ancestor p2 s2)
                            then begin
                              [%debug_log "to be lifted: %a" nps s1];
                              set_to_be_lifted s1
                            end
                            else if
                              self#find_key_opt s2#initial_parent#uid = Some mid_key &&
                              let ss01 = get_p_descendants self#is_stable1 c in
                              List.exists
                                (fun s01 ->
                                  let s02 = nmap1 s01 in
                                  [%debug_log "c=%a s01=%a s02=%a" nps c nps s01 nps s02];
                                  match self#find_key_opt s02#initial_parent#uid with
                                  | Some k0 ->
                                      if self#is_ancestor_key1 mid_key k0 then begin
                                        let r2 = self#get_subtree_root (self#stid_of_key2 k0) in
                                        if
                                          List.exists
                                            (fun sx2 ->
                                              let sx1 = nmap2 sx2 in
                                              sx1#initial_parent != anc1to &&
                                              not (is_ancestor c sx1)
                                            ) (get_p_descendants self#is_stable2 r2)
                                        then begin
                                          [%debug_log "found: %a (k=%s)" nps s02 (key_to_string k0)];
                                          true
                                        end
                                        else
                                          false
                                      end
                                      else
                                        false
                                  | None -> false
                                ) ss01
                            then begin
                              [%debug_log "to be lifted: %a" nps s1];
                              set_to_be_lifted s1
                            end
                          with
                            Not_found -> ()
                        end
                      ) !cl excepted_paths1to;
                    if not !b then begin
                      [%debug_log "to be lifted: %a" nps s1];
                      set_to_be_lifted s1
                    end
                  ) ss1 remote_stable_nds2
              in

              if irreversible_flag then begin
                let mctl_opt =
                  if is_indivisible_move mid then
                    Some Mfull
                  else
                    None
                in
                let fmt =
                  irrf (Fmt.Irr.mkmov mid mctl_opt
                          path1from excepted_paths1from path1to excepted_paths1to
                          key_opt1 adj_opt1 depth_opt1 shift_opt1)
                in

                (*reg_edit_parent edit_parent_tbl1 key_opt1 (fun () -> key_of_mid mid);*)

                (*setup_parent_path_tbl parent_path_tbl1 path1to excepted_paths1to nd2;*)

                [%debug_log "%s" (Fmt.to_string fmt)];

                if fact_for_delta then begin
                  try
                    let cinst = self#make_chg_inst Editop.Tmov nd1 nd2 in
                    fact_add cinst [fmt];
                    triple_add Triple.c_mov cinst nd1 nd2
                  with
                    Invalid_argument _(*"Triple._make_entity"*) -> ()
                end;

                [fmt]
              end
              else begin

                let excluded1_, filtered_out1 =
                  get_extra_insertion tree1 nd1 self#is_stable1 excluded1 remote_stable_nds1
                in

                let anc2to, path2to, excepted_paths2to, simple2 =
                  self#get_opposite_path_and_excepted_paths lift_tbl2 lifted_nodes2
                    self#is_stable1 self#is_stable2
                    get_path2 nmapping#find nmapping#inv_find tree1 tree2
                    nd1 excluded1_
                    (if remote_stable_nds1 = [] then
                      excepted_nds1
                    else
                      remote_stable_nds1)
                in
                Hashtbl.add pre_anc2to_tbl mid_key anc2to;

                [%debug_log "excepted_paths2to: %s"
                  (boundary_to_string excepted_paths2to)];

                if simple2 then begin
                  [%debug_log "simple_ins_root: %a" nps nd1];
                  Xset.add simple_ins_roots1 nd1;
                end;

                recover_excluded filtered_out1; (* recovering excluded1 *)

                let child_staying_moves2 =
                  get_child_staying_moves2 mid excepted_paths2to
                in
                [%debug_log "child_staying_moves2=[%s]"
                  (mids_to_string child_staying_moves2)];

                let excepted_paths2from =
                  let parent_ins_point_opt =
                    Some (mid_key, anc2to, path2to#position, List.length excepted_paths2to)
                  in
                  List.map
                    (fun n2 ->
                      [%debug_log "n2=%a" nps n2];

                      let rel_path = get_rel_path path2from#path n2#apath in

                      if not (self#is_stable2 n2) then
                        new boundary_path rel_path
                      else

                      let n1 = nmap2 n2 in

                      let upc, k_opt, sp_opt, is_upward_staying_move, indirect_conflict =
                        count_upstream_nds
                          mid nd2 nd1 anc2to path2to excepted_paths2to simple2
                          child_staying_moves2 self#is_stable2 self#is_stable1
                          remote_stable_tbl2 remote_stable_tbl1
                          nmapping#inv_find nmapping#find tree2 tree1
                          lift_tbl2 lifted_nodes2
                          n2
                      in
                      [%debug_log "indirect_conflict=%B" indirect_conflict];
                      let force_lift0 =
                        try
                          (*let n1 = nmap2 n2 in*)
                          let p1 = n1#initial_parent in
                          not (self#has_mid (self#find_stid nd2#initial_parent#uid)) &&
                          not (self#is_stable1 p1) &&
                          not (self#has_mid (self#find_stid p1#uid)) &&
                          not (self#is_canceled_stable_node n1) &&
                          not (Xset.mem lifted_nodes2 n2) &&
                          upc > 0
                        with _ -> false
                      in
                      [%debug_log "force_lift0=%B" force_lift0];

                      let force_lift =
                        force_lift0 ||
                        check_to_be_lifted
                          self#is_stable2 self#is_stable1
                          nmap2 lifted_nodes2 tree2 nmapping#find
                          n2
                      in
                      [%debug_log "force_lift: %a -> %B" nps n2 force_lift];

                      let key_opt, upstream, sub_path_opt =
                        if force_lift && is_upward_staying_move then begin
                          let find_ipos, find_iofs =
                            self#find_intermediate_pos2, self#find_intermediate_ofs2
                          in
                          (*let n1 = nmap2 n2 in*)
                          if tree1#is_initial_ancestor nd1 n1 then begin
                            let all_excluded =
                              Array.for_all
                                self#is_excluded
                                n1#initial_parent#initial_children
                            in
                            [%debug_log "all_excluded=%B" all_excluded];

                            let all_excluded_stable =
                              Array.for_all
                                (fun x -> self#is_stable1 x && self#is_excluded x)
                                n1#initial_parent#initial_children
                            in
                            [%debug_log "all_excluded_stable=%B" all_excluded_stable];

                            let is_excluded =
                              if all_excluded then
                                fun lv x ->
                                  if lv = 0 && all_excluded_stable then
                                    self#is_canceled_stable_node x ||
                                    List.for_all
                                      (fun y ->
                                        self#is_canceled_stable_node y
                                      ) (get_p_descendants self#is_stable1 x)
                                  else
                                    self#is_excluded x &&
                                    (self#is_stable1 x ||
                                    (get_p_descendants self#is_stable1 x) <> [])
                              else
                                fun _ -> self#is_excluded
                            in
                            let rp = get_rel_path nd1#apath n1#apath in
                            let ap =
                              self#get_adjusted_path ~is_excluded
                                find_ipos find_iofs self#is_stable1 nd1 rp
                            in
                            [%debug_log "internal path change: sub_path=%s" (Path.to_string ap)];
                            let key = key_of_mid mid in
                            Some key, 0, Some ap
                          end
                          else
                            k_opt, upc, sp_opt
                        end
                      else if
                        self#is_staying_move mid && (not force_lift0 || indirect_conflict)
                      then
                          k_opt, upc, sp_opt
                      else
                        let parent_ins_point_opt =
                          if is_ancestor nd1 n1 then
                            parent_ins_point_opt
                          else
                            None
                        in
                        self#get_parent_key_opt
                          ~force_lift ~parent_ins_point_opt ~anc_to_opt:(Some anc2to)
                          self#is_stable2 self#is_stable1 tree2 tree1
                          nmapping#inv_find nmapping#find n2
                      in
                      [%debug_log "n2=%a" nps n2];
                      new boundary_path ~upstream ~key_opt ~sub_path_opt rel_path
                    ) excluded2
                in

                let excepted_nds1 =
                  List.filter (fun x -> not (self#is_canceled_stable_node x)) excepted_nds1
                in
                [%debug_log "excepted_nds1: [%a]" nsps excepted_nds1];

                let key_opt2, adj_opt2, depth_opt2, shift_opt2 =
                  get_parent_info excepted_nds1 nd1 path2to tree2 nmapping#find
                    self#is_stable1 self#is_stable2 simple2
                in

                check_for_staying_move mid anc2to path2to excepted_paths2to
                  nmap2 nmap1 self#is_stable2 self#is_stable1 tree2 tree1 nd2 nd1
                  excluded2 excluded1 remote_stable_nds1
                  self#find_intermediate_pos2 self#find_intermediate_ofs2
                  lift_tbl2 lifted_nodes2 self#is_ancestor_key2;

                if
                  try
                    List.iter2
                      (fun p2 n2 ->
                        if
                          p2#upstream > 0 && p2#key_opt <> None &&
                          self#is_stable2 n2 && is_ancestor nd1 (nmap2 n2)
                        then
                          raise Exit
                      ) excepted_paths2from excluded2;
                    true
                  with
                    Exit -> false
                then begin
                  let ncond =
                    mkncond excluded1 self#is_stable1 self#is_stable2 tree1 tree2 nmap1 nmap2
                  in
                  let mcond m (*pnd'*)_ (*pos*)_ =
                    [%debug_log "mid=%a m=%a" MID.ps mid MID.ps m];
                    not (Hashtbl.mem edit_parent_tbl2 (key_of_mid m)) &&
                    m = mid || self#is_staying_move m && not (self#_is_upward_staying_move tree2 m)
                  in
                  let check_path_to_ () =
                    check_path_to ncond mcond
                      tree2 self#is_stable2 self#is_stable1 nmap1 nmap2
                      nd1 path2to excepted_paths2to mid_key
                  in
                  begin
                    (*try
                      check_path_to_()
                    with
                      Defer ->
                        [%debug_log "deferred"];*)
                        self#reg_deferred_check check_path_to_
                  end
                end;

                [%debug_log "anc2to_tb;: %s -> %a" (key_to_string mid_key) nps anc2to];
                Hashtbl.add anc2to_tbl mid_key (anc2to, (path2to, excepted_paths2to));
                self#rev_ancto_tbl_add edit_seq#mem_mov2 rev_anc2to_tbl
                  mid_key anc2to path2to excepted_paths2to nd1;

                if path2to#upstream > 0 then begin
                  [%debug_log "upstream_key: %s" (key_to_string mid_key)];
                  Xset.add upstream_keys2 mid_key
                end;

                self#reg_parent_key2 excepted_paths2to mid_key;

                let mctl_opt =
                  if is_indivisible_move mid then
                    Some Mfull
                  else
                    None
                in

                let fmt =
                  revf (Fmt.Rev.mkmov mid mctl_opt
                          path1from excepted_paths1from path1to excepted_paths1to
                          key_opt1 adj_opt1 depth_opt1 shift_opt1
                          path2from excepted_paths2from path2to excepted_paths2to
                          key_opt2 adj_opt2 depth_opt2 shift_opt2)
                in

                reg_edit_parent edit_parent_tbl1 key_opt1 (fun () -> key_of_mid mid);
                reg_edit_parent edit_parent_tbl2 key_opt2 (fun () -> key_of_mid mid);

                (*setup_parent_path_tbl parent_path_tbl1 path1to excepted_paths1to nd2;
                setup_parent_path_tbl parent_path_tbl2 path2to excepted_paths2to nd1;*)

                [%debug_log "%s" (Fmt.to_string fmt)];

                [fmt]
              end
          end

        in (* _mkfmt *)

        let fmt_tbl = Hashtbl.create 0 in (* fmt -> edit *)

        let mkfmt ed =
          let fmtl = _mkfmt ed in
          List.iter (fun fmt -> Hashtbl.add fmt_tbl fmt ed) fmtl;
          fmtl
        in

        self#iter
          (function
            | Insert(nd2, excluded2) -> ignore (reg_subtree2 nd2 excluded2)
            | Delete(nd1, excluded1) -> ignore (reg_subtree1 nd1 excluded1)

            | Move(mid, kind, nd1, excluded1, nd2, excluded2) -> begin
                let stid1 = reg_subtree1 nd1 excluded1 in
                let stid2 = reg_subtree2 nd2 excluded2 in
                self#reg_mid1 stid1 mid;
                self#reg_mid2 stid2 mid;

                (* check if staying move *)
                let remote_stable_tbl1 =
                  get_remote_stable_tbl self#is_stable1 excluded1
                in
                let remote_stable_tbl2 =
                  get_remote_stable_tbl self#is_stable2 excluded2
                in
                let is_staying_move =
                  let a1 = get_p_ancestor self#is_stable1 nd1 in
                  let a2 = get_p_ancestor self#is_stable2 nd2 in
                  (nmapping#find a1) == a2 &&
                  kind <> Editop.Mpermutation &&
                  (List.length remote_stable_tbl1) > 1 &&
                  (List.length remote_stable_tbl2) > 1
                in

                if is_staying_move then begin
                  [%debug_log "is_staying_move: %a" MID.ps mid];
                  Xset.add staying_moves mid
                end;
                Hashtbl.add remote_stable_tbl mid
                  (remote_stable_tbl1, remote_stable_tbl2)

            end

            | _ -> ()
          );

        let fmtl = List.flatten (self#map_for_delta mkfmt) in

        let fmtl =
          List.filter
            (fun fmt ->
              let ed = Hashtbl.find fmt_tbl fmt in
              self#filter ed
            ) fmtl
        in

        begin %debug_block
          let pr_tbl tbl =
            Hashtbl.iter
              (fun ppath pos_w_rt_list ->
                if (List.length pos_w_rt_list) > 1 then begin
                  [%debug_log "%s ->" (Path.to_string ppath)];
                  List.iter
                    (fun (pos, w, rt) ->
                      [%debug_log " (%d, %d, %a)" pos w nps rt]
                    ) pos_w_rt_list
                end
              ) tbl
          in
          [%debug_log "parent_path_tbl1:"];
          pr_tbl parent_path_tbl1;
          [%debug_log "parent_path_tbl2:"];
          pr_tbl parent_path_tbl2;
        end;

        let conv_tbl1 = Hashtbl.create 0 in (* key -> int *)
        let conv_tbl2 = Hashtbl.create 0 in (* key -> int *)

        let check_parent_path_tbl tree tbl =
          let is_stable, is_stable', nmap, lift_tbl, lifted_nodes, conv_tbl =
            if tree == tree1 then
              self#is_stable1,
              self#is_stable2,
              nmapping#find,
              lift_tbl1,
              lifted_nodes1,
              conv_tbl1
            else
              self#is_stable2,
              self#is_stable1,
              nmapping#inv_find,
              lift_tbl2,
              lifted_nodes2,
              conv_tbl2
          in
          let should_be_lifted_tbl = Hashtbl.create 0 in
          Hashtbl.iter
            (fun ppath pos_w_rt_list ->
              if (List.length pos_w_rt_list) > 1 then begin
                [%debug_log "ppath=%s" (Path.to_string ppath)];
                let conflicts = Xset.create 0 in
                let cmp (p0, w0, _) (p1, w1, _) =
                  let p = Stdlib.compare p0 p1 in
                  if p = 0 then
                    Stdlib.compare w1 w0
                  else
                    p
                in
                let sorted_pos_w_rt_list = List.fast_sort cmp pos_w_rt_list in
                let scan = function
                  | [] | [_] -> ()
                  | ((p0, w0, rt0) as x0)::t ->
                      [%debug_log " p0=%d w0=%d rt0=%a" p0 w0 nps rt0];
                      List.iter
                        (fun ((p1, w1, rt1) as x1) ->
                          [%debug_log "  p1=%d w1=%d rt1=%a" p1 w1 nps rt1];
                          if p1 < p0 + w0 && p1 + w1 > p0 + w0 then begin
                            for i = p1 to p0 + w0 - 1 do
                              [%debug_log "  i=%d" i];
                              tbl_add_tbl_list should_be_lifted_tbl ppath i rt0;
                              tbl_add_tbl_list should_be_lifted_tbl ppath i rt1
                            done;
                            Xset.add conflicts x0;
                            Xset.add conflicts x1
                          end
                        ) t
                in
                scan sorted_pos_w_rt_list;

                let sorted_conflicts = List.fast_sort cmp (Xset.to_list conflicts) in
                let posl = ref [] in
                let rtbl = Hashtbl.create 0 in (* root -> num of xs to be removed *)
                List.iter (* resolve conflicts *)
                  (fun (p, w, rt) ->
                    [%debug_log "p=%d, w=%d, rt=%a" p w nps rt];
                    let count = ref 0 in
                    for i = p to p + w - 1 do
                      if List.mem i !posl then
                        incr count;
                      posl := i :: !posl
                    done;
                    Hashtbl.add rtbl rt !count
                  ) sorted_conflicts;
                Hashtbl.iter
                  (fun rt c ->
                    if c > 0 then begin (* pos shift + xs shrink *)
                      [%debug_log "%a: first %d xs should be removed" nps rt c];
                      try
                        let k = self#find_key rt#uid in
                        Hashtbl.add conv_tbl k c
                      with
                        Not_found -> assert false
                    end
                  ) rtbl
              end
            ) tbl;

          Hashtbl.iter
            (fun ppath tbl ->
              let pnd = self#acc ~simple:true tree#root ppath in
              [%debug_log "ppath=%s pnd=%a" (Path.to_string ppath) nps pnd];
              let ppath =
                try
                  let del_root =
                    let stid = self#find_stid pnd#uid in
                    [%debug_log "stid=%s" (stid_to_str stid)];
                    self#get_subtree_root stid
                  in
                  [%debug_log "del_root=%a" nps del_root];
                  del_root#apath
                with
                  Not_found -> ppath
              in
              Hashtbl.iter
                (fun pos rts' ->
                  [%debug_log " pos=%d rts'=[%a]" pos nsps rts'];
                  let cnd = pnd#initial_children.(pos) in
                  let sns = get_p_descendants is_stable cnd in
                  [%debug_log " sns=[%a]" nsps sns];
                  let rps = List.map (fun n -> get_rel_path ppath n#apath) sns in
                  [%debug_log " rps=[%s]" (String.concat ";" (List.map Path.to_string rps))];
                  let sns' = List.map nmap sns in
                  [%debug_log " sns'=[%a]" nsps sns'];

                  List.iter
                    (fun rt' ->
                      [%debug_log " rt'=%a" nps rt'];
                      List.iter2
                        (fun rp sn' ->
                          try
                            let ins_root' =
                              self#get_subtree_root (self#find_stid sn'#initial_parent#uid)
                            in

                            let rp' = get_rel_path ins_root'#apath sn'#apath in
                            let ap' =
                              self#get_adjusted_path
                                (fun _ -> raise Not_found)
                                (fun _ -> raise Not_found)
                                is_stable' ins_root' rp'
                            in
                            [%debug_log "  sn'=%a rp'=%s ap'=%s"
                              nps sn' (Path.to_string rp')  (Path.to_string ap')];
                            let key = self#find_key ins_root'#uid in
                            [%debug_log "  (%s,%s) -> (%s,%s)"
                              (Path.to_string ppath) (Path.to_string rp)
                              (Path.to_string ap') (key_to_string key)];

                            let k = (ppath, rp) in
                            if not (Hashtbl.mem lift_tbl k) then begin
                              Hashtbl.add lift_tbl k (ap', key, 0);
                              Xset.add lifted_nodes rt';
                              [%debug_log "%a is lifted" nps rt']
                            end
                          with
                            _ -> ()
                        ) rps sns'
                    ) rts'

                ) tbl
            ) should_be_lifted_tbl
        in
        check_parent_path_tbl tree1 parent_path_tbl1;
        check_parent_path_tbl tree2 parent_path_tbl2;

        [%debug_log "executing deferred checks..."];
        self#do_deferred_checks();
        [%debug_log "deferred checks completed."];

        begin %debug_block
          let pr_tbl tbl =
            Hashtbl.iter
              (fun (p, rp) (ap, key, upc) ->
                [%debug_log "%s %s -> %s %s %d"
                  (Path.to_string p) (Path.to_string rp)
                  (key_to_string key) (Path.to_string ap) upc]
              ) tbl
          in
          [%debug_log "lift_tbl1 (%d):" (Hashtbl.length lift_tbl1)];
          pr_tbl lift_tbl1;
          [%debug_log "lift_tbl2 (%d):" (Hashtbl.length lift_tbl2)];
          pr_tbl lift_tbl2;
        end;

        let dump_cache = Hashtbl.create 0 in

        let dump ch fmt =
          try
            Fmt.dump ch (Hashtbl.find dump_cache fmt)
          with
            Not_found ->

          if (Hashtbl.length lift_tbl1) = 0 && (Hashtbl.length lift_tbl2) = 0 then begin
            Hashtbl.add dump_cache fmt fmt;
            Fmt.dump ch fmt
          end
          else begin
            let modify lift_tbl parent_tbl path =
              let is_parent pk k =
                try
                  Hashtbl.find parent_tbl k = pk
                with
                  Not_found -> false
              in
              List.iter
                (fun p ->
                  try
                    let rp, key, upc = Hashtbl.find lift_tbl (path#path, p#path) in
                    [%debug_log "%s: orig: %s" path#to_string p#to_string];
                    match p#key_opt with
                    | None -> begin
                        p#set_key_opt (Some key);
                        p#set_sub_path_opt (Some rp);
                        p#set_upstream upc;
                        [%debug_log "modified: -> %s" p#to_string]
                    end
                    | Some k when k <> key && is_parent k key || upc > 0 -> begin
                        p#set_key_opt (Some key);
                        p#set_sub_path_opt (Some rp);
                        p#set_upstream upc;
                        [%debug_log "modified: -> %s" p#to_string]
                    end
                    | Some k when k = key && p#sub_path_opt = None -> begin
                        p#set_sub_path_opt (Some rp);
                        p#set_upstream upc;
                        [%debug_log "modified: -> %s" p#to_string]
                    end
                    | _ -> ()
                  with
                    Not_found -> ()
                )
            in
            let get_conv tbl k =
              let c = Hashtbl.find tbl k in
              c
            in
            let conv_path path c =
              let e = Path.tail path#path in
              if e.Elem.ofs = 0. then begin
                e.Elem.pos <- e.Elem.pos + c;
                [%debug_log "%s -> %s" path#to_string path#to_string];
              end
              else
                Xprint.warning "offset is not 0: %s" path#to_string;
              path
            in
            let conv_paths paths c =
              let len = List.length paths in
              if c < len then
                let paths' = Xlist.lastn (len - c) paths in
                [%debug_log "[%s] -> [%s]"
                  (String.concat ";" (List.map (fun p -> p#to_string) paths))
                  (String.concat ";" (List.map (fun p -> p#to_string) paths'))];
                paths'
              else begin
                Xprint.warning "length of paths (=%d) >= c (%d)" len c;
                paths
              end
            in
            let open Fmt in

            let fmt' =
              match fmt with
              | Irr (Irr.Del(path, paths)) -> begin
                  modify lift_tbl1 edit_parent_tbl1 path paths;
                  fmt
              end
              | Rev (Rev.Del(stid, x0, x1, path, paths, x2, x3, x4, x5, x6)) -> begin
                  try
                    let c = get_conv conv_tbl2 (K_stid stid) in
                    Rev (Rev.Del(stid, x0, x1,
                                 conv_path path c, conv_paths paths c,
                                 x2, x3, x4, x5, x6))
                  with
                    Not_found -> fmt
              end
              | Irr (Irr.Ins(stid, path, paths, x0, x1, x2, x3, x4)) -> begin
                  try
                    let c = get_conv conv_tbl1 (K_stid stid) in
                    Irr (Irr.Ins(stid,
                                 conv_path path c, conv_paths paths c,
                                 x0, x1, x2, x3, x4))
                  with
                    Not_found -> fmt
              end
              | Rev (Rev.Ins(stid, path1, paths1, x0, x1, x2, x3, x4, path2, paths2))
                -> begin
                  modify lift_tbl2 edit_parent_tbl2 path2 paths2;
                  try
                    let c = get_conv conv_tbl1 (K_stid stid) in
                    Rev (Rev.Ins(stid,
                                 conv_path path1 c, conv_paths paths1 c,
                                 x0, x1, x2, x3, x4, path2, paths2))
                  with
                    Not_found -> fmt
                end
              | Irr (Irr.Mov(mid, mctl_opt, path1, paths1, path2, paths2, x0, x1, x2, x3)) -> begin
                  modify lift_tbl1 edit_parent_tbl1 path1 paths1;
                  try
                    let c = get_conv conv_tbl1 (K_mid mid) in
                    Irr (Irr.Mov(mid, mctl_opt, path1, paths1,
                                 conv_path path2 c, conv_paths paths2 c,
                                 x0, x1, x2, x3))
                  with
                    Not_found -> fmt
              end
              | Rev (Rev.Mov(mid, mctl_opt, path1, paths1, path2, paths2, x0, x1, x2, x3,
                             path1', paths1', path2', paths2', x4, x5, x6, x7))
                -> begin
                  modify lift_tbl1 edit_parent_tbl1 path1 paths1;
                  modify lift_tbl2 edit_parent_tbl2 path1' paths1';
                  try
                    let c = get_conv conv_tbl1 (K_mid mid) in
                    let c' = get_conv conv_tbl2 (K_mid mid) in
                    Rev (Rev.Mov(mid, mctl_opt, path1, paths1,
                                 conv_path path2 c, conv_paths paths2 c,
                                 x0, x1, x2, x3, path1', paths1',
                                 conv_path path2' c', conv_paths paths2' c',
                                 x4, x5, x6, x7))
                  with
                    Not_found -> fmt
                end
              | _ -> fmt
            in
            Hashtbl.add dump_cache fmt fmt';
            Fmt.dump ch fmt'
          end
        in (* dump *)

        output_string ch XML.header;

        if tree1#parser_name <> tree2#parser_name then
          [%warn_log "different parser: %s and %s"
            tree1#parser_name tree2#parser_name];

        output_st_elem_root
          ~extra_ns_decls
          ~irreversible_flag
          ~normalized_delta_flag:(not options#recover_orig_ast_flag && options#sort_unordered_flag)
          tree1#parser_name
          tree1#encoded_source_digest
          tree2#encoded_source_digest
          ch;

        List.iter (dump ch) fmtl;

        output_ed_elem_root ch;

        dump_info();

        if fact_for_delta then begin
          let fact_buf =
            let into_virtuoso = options#fact_into_virtuoso <> "" in
            let into_directory = options#fact_into_directory <> "" in
            if into_virtuoso then begin
              assert (not into_directory);
              new Triple.buffer_virtuoso options
            end
            else if into_directory then
              let cache_name =
                Cache.get_cache_name options (Filename.dirname fact_file_name)
              in
              new Triple.buffer_directory options cache_name
            else
              new Triple.buffer ~overwrite:false options fact_file_name
          in

          Hashtbl.iter
            (fun cinst fmtl ->
              let buf = Buffer.create 0 in
              let dest = Xchannel.Destination.of_buffer buf in
              let bch = new Xchannel.out_channel dest in
              List.iter (dump bch) fmtl;
              let xml = Buffer.contents buf in
              let xml_lit = Triple.make_literal xml in
              fact_buf#add (cinst, Triple.p_xml, xml_lit)
            ) fact_tbl;

          Xset.iter fact_buf#add triples;

          fact_buf#close
        end

      (* end of method dump_delta_ch *)


      method dump_delta
          ?(extra_ns_decls=[])
          ?(comp=Compression.none)
          ?(info_file_path="")
          nmapping
          file_name
          =
        let fact_file_name = Xfile.change_extension file_name ".nt" in
        let info_file_name =
          if info_file_path = "" then
            Xfile.change_extension file_name "_info.json"
          else
            info_file_path
        in
        Xchannel.dump ~comp file_name
          (self#dump_delta_ch ~extra_ns_decls ~fact_file_name ~info_file_name nmapping)


    end (* of class Delta.Edit.seq *)


end (* of module Delta.Edit *)
]
