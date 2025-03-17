(*
   Copyright 2024-2025 Codinuum Software Lab <https://codinuum.com>

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
(* Mapping.ml *)

[%%prepare_logger]

module Xfile = Diffast_misc.Xfile
module Xhash = Diffast_misc.Xhash
module Xset = Diffast_misc.Xset
module Xlist = Diffast_misc.Xlist
module Xchannel = Diffast_misc.Xchannel
module UID = Diffast_misc.UID
module GI = Diffast_misc.GIndex
module Comp = Diffast_misc.Compression
module Loc = Diffast_misc.Loc

module Nodetbl = Node.Tbl


let fprintf = Printf.fprintf
let sprintf = Printf.sprintf

type node_t = Spec.node_t

let nps = Misc.nps
let nups = Misc.nups


let is_crossing nd1 nd2 n1 n2 =
  let b = (nd1#gindex - n1#gindex) * (nd2#gindex - n2#gindex) < 0 in
  (*[%debug_log "%a-%a vs %a-%a -> %B" nups nd1 nups nd2 nups n1 nups n2 b;*)
  b

let _is_incompatible tree1 tree2 nd11 nd12 nd21 nd22 =
  let in_subtree_mutually1 = tree1#in_subtree_mutually nd11 nd21 in
  let in_subtree_mutually2 = tree2#in_subtree_mutually nd12 nd22 in
  let b =
    (in_subtree_mutually1 && not in_subtree_mutually2) ||
    (not in_subtree_mutually1 && in_subtree_mutually2)
  in
  (*[%debug_log "%a-%a vs %a-%a -> %B" nups nd11 nups nd12 nups nd21 nups nd22 b;*)
  b

let is_incompatible tree1 tree2 nd11 nd12 nd21 nd22 =
  not (is_crossing nd11 nd12 nd21 nd22) && _is_incompatible tree1 tree2 nd11 nd12 nd21 nd22


[%%capture_path
let add map1 map1rev map2 map2rev nd1 nd2 =
  let conflict1 = ref None in
  let conflict2 = ref None in
  begin
    try
      let nd1' = Nodetbl.find map1 nd1 in
      if nd1' != nd2 then begin

        Nodetbl.replace map1 nd1 nd2;
        Nodetbl.remove map1rev nd1';
        Nodetbl.remove map2rev nd1';

        conflict2 := Some nd1';

        begin %debug_block
          [%debug_log "conflict: %a-%a" nups nd1 nups nd1'];
          [%debug_log "overridden by: %a-%a" nups nd1 nups nd2]
        end

      end
    with
      Not_found ->
        try
          let nd1' = Nodetbl.find map2 nd1 in
          if nd1' != nd2 then begin

            Nodetbl.replace map2 nd1 nd2;
            Nodetbl.remove map2rev nd1';
            Nodetbl.remove map1rev nd1';

            conflict2 := Some nd1';

            begin %debug_block
              [%debug_log "conflict: %a-%a" nups nd1 nups nd1'];
              [%debug_log "overridden by: %a-%a" nups nd1 nups nd2]
            end

          end
    with
      Not_found -> Nodetbl.add map1 nd1 nd2
  end;
  begin
    try
      let nd2' = Nodetbl.find map1rev nd2 in
      if nd2' != nd1 then begin

        Nodetbl.replace map1rev nd2 nd1;
        Nodetbl.remove map1 nd2';
        Nodetbl.remove map2 nd2';

        conflict1 := Some nd2';

        begin %debug_block
          [%debug_log "conflict: %a-%a" nups nd2' nups nd2];
          [%debug_log "overridden by: %a-%a" nups nd1 nups nd2]
        end

      end
    with
      Not_found ->
        try
          let nd2' = Nodetbl.find map2rev nd2 in
          if nd2' != nd1 then begin

            Nodetbl.replace map2rev nd2 nd1;
            Nodetbl.remove map2 nd2';
            Nodetbl.remove map1 nd2';

            conflict1 := Some nd2';

            begin %debug_block
              [%debug_log "conflict: %a-%a" nups nd2' nups nd2];
              [%debug_log "overridden by: %a-%a" nups nd1 nups nd2]
            end

          end
    with
      Not_found -> Nodetbl.add map1rev nd2 nd1
  end;
  !conflict1, !conflict2
]


let tbl_remove tbl k =
  (*while Nodetbl.mem tbl k do*)
    Nodetbl.remove tbl k
  (*done*)


module Json = struct

  let find_nearest_unordered_ancestor_node =
    Sourcecode.find_nearest_p_ancestor_node (fun x -> x#data#is_order_insensitive)

  let _fprintf ch fmt =
    Printf.ksprintf (fun s -> ignore (ch#output_ s 0 (String.length s))) fmt

  let get_gid (nd : node_t) =
    let gid = nd#data#gid in
    if gid > 0 then
      gid
    else
      nd#gindex

  let get_loc nd =
    let loc = nd#data#src_loc in
    let sl = loc.Loc.start_line in
    let el = loc.Loc.end_line in
    let sc = loc.Loc.start_char in
    let ec = loc.Loc.end_char in
    sprintf "{\"start_line\":%d,\"start_char\":%d,\"end_line\":%d,\"end_char\":%d}" sl sc el ec

  let get_cat nd = "\""^nd#data#get_category^"\""

  let get_name nd =
    if nd#data#is_named && nd#data#is_named_orig && not nd#data#has_value then
      nd#data#get_orig_name
    else
      ""

  let get_digest tree nd =
    try
      if nd#initial_nchildren = 0 then
        nd#data#get_orig_name
      else
        raise Not_found
    with Not_found ->
      let d =
        match nd#data#_digest with
        | Some d -> d
        | None -> tree#get_digest nd
      in
      Xhash.to_hex d

  let get_info1
      ?(is_subtree_root=fun _ -> false)
      ?(get_root=None)
      tree
      (nd : node_t)
      =
    let named_nameless = nd#data#is_named && not nd#data#is_named_orig in
    let name = get_name nd in
    let phantom = nd#data#is_phantom in
    let unordered = nd#data#is_order_insensitive in
    let l = ref [] in
    l := (sprintf "\"loc\":%s" (get_loc nd)) :: !l;
    l := (sprintf "\"cat\":%s" (get_cat nd)) :: !l;

    begin
      try
        let pgi = get_gid nd#initial_parent in
        let pos = nd#initial_pos in
        l := (sprintf "\"parent\":%a" GI.rs pgi) :: !l;
        l := (sprintf "\"pos\":%d" pos) :: !l
      with _ -> ()
    end;

    if is_subtree_root nd && not phantom then begin
      let h = get_digest tree nd in
      let lmnd = tree#initial_leftmost nd in
      let lgi = get_gid lmnd in
      l := (sprintf "\"digest\":\"%s\"" h) :: !l;
      l := (sprintf "\"leftmost\":%a" GI.rs lgi) :: !l;
      match get_root with
      | Some get -> begin
          try
            if get lmnd == get nd then
              l := (sprintf "\"mem_leftmost\":true") :: !l
          with _ -> ()
      end
      | _ -> ()
    end;

    begin
      match get_root with
      | Some get -> begin
          try
            l := (sprintf "\"root\":%a" GI.rs (get_gid (get nd))) :: !l;
          with _ -> ()
      end
      | _ -> ()
    end;

    if name <> "" then
      l := (sprintf "\"name\":\"%s\"" name) :: !l;
    if named_nameless then
      l := "\"named_nameless\":true" :: !l;
    if phantom then
      l := "\"phantom\":true" :: !l;
    if unordered then
      l := "\"unordered\":true" :: !l;
    "{"^(String.concat "," !l)^"}"

  let get_info
      ?(is_subtree_root=fun _ -> false)
      tree1 tree2
      mapped_node_tbl
      (nd1 : node_t) (nd2 : node_t)
      =
    let named_nameless =
      nd1#data#is_named && not nd1#data#is_named_orig &&
      nd2#data#is_named && not nd2#data#is_named_orig
    in
    let name1 = get_name nd1 in
    let name2 = get_name nd2 in
    let phantom = nd1#data#is_phantom || nd2#data#is_phantom in
    let unordered =
      nd2#data#is_order_insensitive ||
      try
        let un2 = find_nearest_unordered_ancestor_node nd2 in
        let un1 = Nodetbl.find mapped_node_tbl un2 in
        let ug1, ug2 = get_gid un1, get_gid un2 in
        let gi1, gi2 = get_gid nd1, get_gid nd2 in
        (ug1 - gi1) * (ug2 - gi2) > 0
      with _ -> false
    in
    let l = ref [] in
    l := (sprintf "\"from_loc\":%s,\"to_loc\":%s" (get_loc nd1) (get_loc nd2)) :: !l;
    l := (sprintf "\"from_cat\":%s,\"to_cat\":%s" (get_cat nd1) (get_cat nd2)) :: !l;

    if is_subtree_root nd1 && not nd1#data#is_phantom then begin
      let h = get_digest tree1 nd1 in
      let lgi = get_gid (tree1#initial_leftmost nd1) in
      l := (sprintf "\"from_digest\":\"%s\"" h) :: !l;
      l := (sprintf "\"from_leftmost\":%a" GI.rs lgi) :: !l
    end;
    if is_subtree_root nd2 && not nd2#data#is_phantom then begin
      let h = get_digest tree2 nd2 in
      let lgi = get_gid (tree2#initial_leftmost nd2) in
      l := (sprintf "\"to_digest\":\"%s\"" h) :: !l;
      l := (sprintf "\"to_leftmost\":%a" GI.rs lgi) :: !l
    end;

    begin
      try
        let pgi1 = get_gid nd1#initial_parent in
        l := (sprintf "\"from_parent\":%a" GI.rs pgi1) :: !l;
        l := (sprintf "\"from_pos\":%d" nd1#initial_pos) :: !l
      with _ -> ()
    end;
    begin
      try
        let pgi2 = get_gid nd2#initial_parent in
        l := (sprintf "\"to_parent\":%a" GI.rs pgi2) :: !l;
        l := (sprintf "\"to_pos\":%d" nd2#initial_pos) :: !l
      with _ -> ()
    end;

    if name1 <> "" then
      l := (sprintf "\"from_name\":\"%s\"" name1) :: !l;
    if name2 <> "" then
      l := (sprintf "\"to_name\":\"%s\"" name2) :: !l;
    if named_nameless then
      l := "\"named_nameless\":true" :: !l;
    if phantom then
      l := "\"phantom\":true" :: !l;
    if unordered then
      l := "\"unordered\":true" :: !l;
    "{"^(String.concat "," !l)^"}"

end (* module Json *)


[%%capture_path
class ['node_t] c (cenv : 'a Node.cenv_t) = object (self : 'self)

  val mutable use_crossing_or_incompatible_matches_count_cache = false

  method use_crossing_or_incompatible_matches_count_cache =
    use_crossing_or_incompatible_matches_count_cache

  val crossing_or_incompatible_matches_count_cache = Hashtbl.create 0

  val mutable size_of_crossing_or_incompatible_matches_count_cache = 0
  method size_of_crossing_or_incompatible_matches_count_cache =
    size_of_crossing_or_incompatible_matches_count_cache +
      (Hashtbl.length crossing_or_incompatible_matches_count_cache)

  method clear_crossing_or_incompatible_matches_count_cache =
    if use_crossing_or_incompatible_matches_count_cache then begin
      size_of_crossing_or_incompatible_matches_count_cache <-
        size_of_crossing_or_incompatible_matches_count_cache +
          (Hashtbl.length crossing_or_incompatible_matches_count_cache);
      Hashtbl.clear crossing_or_incompatible_matches_count_cache;

      [%debug_log "crossing_or_incompatible_matches_count_cache cleared"]
    end

  val mutable crossing_or_incompatible_matches_count_cache_hit_count = 0
  method crossing_or_incompatible_matches_count_cache_hit_count =
    crossing_or_incompatible_matches_count_cache_hit_count

  val mutable starting_pairs_for_glueing = ([] : ('node_t * 'node_t) list)

  method clear_starting_pairs_for_glueing =
    [%debug_log "@"];
    starting_pairs_for_glueing <- []

  method set_starting_pairs_for_glueing l =
    [%debug_log "@"];
    starting_pairs_for_glueing <- l

  method remove_starting_pairs_for_glueing l =
    starting_pairs_for_glueing <- Xlist.subtract starting_pairs_for_glueing l

  method add_starting_pairs_for_glueing l =
    starting_pairs_for_glueing <- Xlist.union l starting_pairs_for_glueing

  method add_starting_pair_for_glueing p =
    if not (List.mem p starting_pairs_for_glueing) then
      starting_pairs_for_glueing <- p :: starting_pairs_for_glueing

  method starting_pairs_for_glueing = starting_pairs_for_glueing

  val mutable locked_nodes = (Nodetbl.create 0 : Key.t Nodetbl.t)

  method is_locked_node n = Nodetbl.mem locked_nodes n

  method lock_node ?(key=Key.any_key) n =
    [%debug_log "locking %a with %s" nups n (Key.to_string key)];
    try
      let k = Nodetbl.find locked_nodes n in
      [%debug_log "found: %s" (Key.to_string k)];
      if key <> k then
        Nodetbl.add locked_nodes n key
    with
      Not_found -> Nodetbl.add locked_nodes n key

  method unlock_node n =
    [%debug_log "unlocking %a" nups n];
    Nodetbl.remove locked_nodes n

  method key_of_locked_node n = Nodetbl.find locked_nodes n


  val mutable locked_mappings = (Xset.create 0 : ('node_t * 'node_t) Xset.t)

  method lock_mapping n1 n2 =
    [%debug_log "%a-%a" nups n1 nups n2];
    Xset.add locked_mappings (n1, n2)

  method is_locked_mapping n1 n2 =
    let b = Xset.mem locked_mappings (n1, n2) in
    [%debug_log "%a-%a -> %B" nups n1 nups n2 b];
    b

  val mutable final_mappings = (Xset.create 0 : ('node_t * 'node_t) Xset.t)

  method finalize_mapping n1 n2 =
    [%debug_log "%a-%a" nups n1 nups n2];
    Xset.add final_mappings (n1, n2)

  method is_final_mapping n1 n2 =
    let b = Xset.mem final_mappings (n1, n2) in
    [%debug_log "%a-%a -> %B" nups n1 nups n2 b];
    b

  val mutable pre_boundary_mappings = (Xset.create 0 : ('node_t * 'node_t) Xset.t)

  method add_to_pre_boundary_mapping n1 n2 =
    [%debug_log "%a-%a" nups n1 nups n2];
    Xset.add pre_boundary_mappings (n1, n2)

  method is_pre_boundary_mapping n1 n2 =
    let b = Xset.mem pre_boundary_mappings (n1, n2) in
    [%debug_log "%a-%a -> %B" nups n1 nups n2 b];
    b

  val mutable stable_pairs = (Nodetbl.create 0: 'node_t Nodetbl.t)
  method stable_pairs = stable_pairs
  method set_stable_pairs ps = stable_pairs <- ps
  method is_stable_pair n1 n2 =
    try
      let ns = Nodetbl.find_all stable_pairs n1 in
      List.memq n2 ns
    with
      Not_found -> false

  method add_stable_pair n1 n2 =
    try
      let n1' = Nodetbl.find stable_pairs n1 in
      if n1' != n2 then
        Nodetbl.add stable_pairs n1 n2
    with
      Not_found -> Nodetbl.add stable_pairs n1 n2

  method find_stable_pair n1 =
    try
      Nodetbl.find_all stable_pairs n1
    with
      Not_found -> []

  method iter_stable_pairs f = Nodetbl.iter f stable_pairs

  val map = (Nodetbl.create 0 : 'node_t Nodetbl.t)

  (* for settled nodes *)
  val s_map = (Nodetbl.create 0 : 'node_t Nodetbl.t)

  val mutable settled_roots = (Xset.create 0 : ('node_t * 'node_t) Xset.t)

  val rev_map = (Nodetbl.create 0 : 'node_t Nodetbl.t)
  val rev_s_map = (Nodetbl.create 0 : 'node_t Nodetbl.t)

  val mutable blacklist1 = (Xset.create 0 : 'node_t Xset.t)
  val mutable blacklist2 = (Xset.create 0 : 'node_t Xset.t)

  method set_blacklist1 h = blacklist1 <- h
  method set_blacklist2 h = blacklist2 <- h

  method size = (Nodetbl.length map) + (Nodetbl.length s_map)

  method iter_unsettled f = Nodetbl.iter f map
  method iter_settled f = Nodetbl.iter f s_map

  method iter (f : 'node_t -> 'node_t -> unit) =
    begin
      Nodetbl.iter f map;
      Nodetbl.iter f s_map
    end

  method private _iter_sorted cmp dom f =
    let doma = Array.of_seq dom in
    Array.fast_sort cmp doma;
    Array.iter
      (fun u1 ->
        try
          let u2 = self#find u1 in
          f u1 u2
        with
          Not_found -> assert false
      ) doma

  method iter_sorted cmp f =
    self#_iter_sorted cmp self#dom_unsettled f;
    self#_iter_sorted cmp self#dom_settled f

  method iter_unsettled_sorted cmp f =
    self#_iter_sorted cmp self#dom_unsettled f

  method iter_settled_sorted cmp f =
    self#_iter_sorted cmp self#dom_settled f


  method iter_rev f =
    begin
      Nodetbl.iter f rev_map;
      Nodetbl.iter f rev_s_map
    end


  method find_unsettled nd =
    Nodetbl.find map nd

  method find_settled nd =
    Nodetbl.find s_map nd

  method find nd =
    try
      Nodetbl.find map nd
    with
      Not_found ->
        Nodetbl.find s_map nd

  method inv_find nd =
    try
      Nodetbl.find rev_map nd
    with
      Not_found ->
        Nodetbl.find rev_s_map nd


  method add_unsettled nd1 nd2 =
    [%debug_log "%a-%a" nups nd1 nups nd2];
    let conflict = add map rev_map s_map rev_s_map nd1 nd2 in
    self#clear_crossing_or_incompatible_matches_count_cache;
    self#clear_reptbl();
    conflict


  method add_settled ?(stable=false) nd1 nd2 =

    [%debug_log "[stable=%B]: %a-%a" stable nups nd1 nups nd2];

    let conflict =
      if Xset.mem blacklist1 nd1 || Xset.mem blacklist2 nd2 then
        self#add_unsettled nd1 nd2

      else begin
        let c = add s_map rev_s_map map rev_map nd1 nd2 in

        if stable then
          self#add_stable_pair nd1 nd2; (* MODIFIED-> ADOPTED *)

        c
      end
    in
    self#clear_crossing_or_incompatible_matches_count_cache;
    self#clear_reptbl();
    conflict


  method add_settled_roots nd1 nd2 =
    if Xset.mem blacklist1 nd1 || Xset.mem blacklist2 nd2 then
      ()
    else
      Xset.add settled_roots (nd1, nd2)

  method is_settled_root_pair nd1 nd2 =
    Xset.mem settled_roots (nd1, nd2)

  method iter_settled_roots f =
    Xset.iter (fun (nd1, nd2) -> f nd1 nd2) settled_roots

  method iter_settled_roots_sorted cmp f =
    let sorted =
      List.fast_sort (fun (n1, _) (n2, _) -> cmp n1 n2) (Xset.to_list settled_roots)
    in
    List.iter (fun (nd1, nd2) -> f nd1 nd2) sorted

  method merge_no_override (m : 'self) =
    m#iter_settled
      (fun n1 n2 ->
        if not (self#mem_dom n1 || self#mem_cod n2) then
          ignore (self#add_settled ~stable:false n1 n2)
      );
    m#iter_unsettled
      (fun n1 n2 ->
        if not (self#mem_dom n1 || self#mem_cod n2) then
          ignore (self#add_unsettled n1 n2)
      );
    m#iter_settled_roots self#add_settled_roots

  method merge (m : 'self) =
    let conflicts = ref [] in
    m#iter_settled
      (fun n1 n2 ->
        let c = self#add_settled ~stable:false n1 n2 in
        conflicts := c :: !conflicts
      );
    m#iter_unsettled
      (fun n1 n2 ->
        let c = self#add_unsettled n1 n2 in
        conflicts := c :: !conflicts
      );
    m#iter_settled_roots self#add_settled_roots;
    !conflicts

  method check_for_ref (ref_npairs : Spec.npairs_t) (m : 'self) =
    let check n1 n2 =
      (*[%debug_log "checking %a-%a" nups n1 nups n2];*)
      if not (ref_npairs#mem n1 n2) then begin
        [%debug_log "adding %a-%a" nups n1 nups n2];
        ref_npairs#add n1 n2
      end

    in
    m#iter_unsettled check;
    m#iter_settled check

  method merge_checked (m : 'self) = (* only applicable to pre_uidmapping *)
    let invalidated_settled_root_tbl = Hashtbl.create 0 in

    let check adder n1 n2 =
      if m#is_pre_boundary_mapping n1 n2 then
        adder n1 n2
      else begin

      [%debug_log "checking %a-%a" nups n1 nups n2];
      let mem1 = self#mem_dom n1 in
      let mem2 = self#mem_cod n2 in
      if mem1 || mem2 then begin
        let n1' = try self#find n1 with _ -> n2 in
        let n2' = try self#inv_find n2 with _ -> n1 in
        if n1' != n2 || n2' != n1 then begin (* conflict *)
          let score = cenv#get_adjacency_score n1 n2 in
          let cond1 =
            if mem1 then begin
              [%debug_log "conflict with %a-%a" nups n1 nups n1'];
              let score' = cenv#get_adjacency_score n1 n1' in
              score > score'
            end
            else
              true
          in
          let cond2 =
            if mem2 then begin
              [%debug_log "conflict with %a-%a" nups n2' nups n2];
              let score' = cenv#get_adjacency_score n2' n2 in
              score > score'
            end
            else
              true
          in
          if cond1 && cond2 then
            adder n1 n2
          else begin
            let cl1 = Array.to_list n1#initial_children in
            let cl2 = Array.to_list n2#initial_children in
            [%debug_log "not added: %a-%a" nups n1 nups n2];
            assert (List.length cl1 = List.length cl2);
            Hashtbl.add invalidated_settled_root_tbl (n1, n2) (List.combine cl1 cl2)
          end
        end
        else
          [%debug_log "already have %a-%a" nups n1 nups n2]
      end
      else
        adder n1 n2

      end
    in

    m#iter_settled
      (check
         (fun n1 n2 ->
           ignore (self#add_settled ~stable:false n1 n2);
           if m#is_final_mapping n1 n2 then
             self#finalize_mapping n1 n2
         )
      );
    m#iter_unsettled (check (fun n1 n2 -> ignore (self#add_unsettled n1 n2)));

    let rec get_settled_roots (nd1, nd2) =
      try
        let pairs = Hashtbl.find invalidated_settled_root_tbl (nd1, nd2) in
        List.concat_map get_settled_roots pairs
      with
        Not_found -> [(nd1, nd2)]
    in

    m#iter_settled_roots
      (fun nd1 nd2 ->
        let pairs = get_settled_roots (nd1, nd2) in
        match pairs with
        | [] -> self#add_settled_roots nd1 nd2
        | _ ->
            List.iter
              (fun (n1, n2) ->
                self#add_settled_roots n1 n2
              ) pairs
      )


  method mem nd = Nodetbl.mem map nd || Nodetbl.mem s_map nd

  method mem_unsettled nd = Nodetbl.mem map nd

  method mem_settled nd = Nodetbl.mem s_map nd

  method has_unsettled_mapping nd1 nd2 =
    try
      let nd1' = self#find_unsettled nd1 in
      nd1' == nd2
    with
      Not_found -> false

  method has_settled_mapping nd1 nd2 =
    try
      let nd1' = self#find_settled nd1 in
      nd1' == nd2
    with
      Not_found -> false

  method has_mapping nd1 nd2 =
    self#has_unsettled_mapping nd1 nd2 ||
    self#has_settled_mapping nd1 nd2


  method remove nd1 nd2 =
    [%debug_log "%a-%a" nups nd1 nups nd2];
    try
      if self#find nd1 == nd2 then begin
        if self#mem_dom_settled nd1 || self#mem_cod_settled nd2 then begin
          self#remove_settled nd1 nd2;
          [%debug_log "settled map %a-%a removed" nups nd1 nups nd2]
        end;
        if self#mem_dom_unsettled nd1 || self#mem_cod_unsettled nd2 then begin
          tbl_remove map nd1;
          tbl_remove rev_map nd2;
          [%debug_log "unsettled map %a-%a removed" nups nd1 nups nd2]
        end;
        self#clear_crossing_or_incompatible_matches_count_cache;
        self#clear_reptbl();
        self#unlock_node nd1;
        self#unlock_node nd2;
        true
      end
      else
        false
    with
      Not_found -> false

  method remove_settled nd1 nd2 =
    [%debug_log "%a-%a" nups nd1 nups nd2];
    try
      if self#find nd1 == nd2 then begin
        if not (self#is_settled_root_pair nd1 nd2) then begin
          let tree1 = cenv#tree1 in
          let tree2 = cenv#tree2 in
          let gi1 = nd1#gindex in
          let gi2 = nd2#gindex in
          self#iter_settled_roots
            (fun n1 n2 ->
              if
                gi1 < n1#gindex && (tree1#initial_leftmost n1)#gindex <= gi1 ||
                gi2 < n2#gindex && (tree2#initial_leftmost n2)#gindex <= gi2
              then
                Xset.remove settled_roots (n1, n2)
            )
        end;
        tbl_remove s_map nd1;
        tbl_remove rev_s_map nd2;
        Xset.remove settled_roots (nd1, nd2);
        let ca1 = nd1#initial_children in
        Array.iteri
          (fun _ c ->
            try
              let c' = self#find c in
              if c'#initial_parent == nd2 then
                Xset.add settled_roots (c, c')
            with
              _ -> ()
          ) ca1;
        self#clear_crossing_or_incompatible_matches_count_cache;
        self#clear_reptbl()
      end
    with
      Not_found -> ()

  method filter f =
    Nodetbl.iter
      (fun n1 n2 ->
        if not (f n1 n2) then begin
          Nodetbl.remove map n1;
          Nodetbl.remove rev_map n2;
          Nodetbl.remove rev_s_map n2
        end
      ) map;
    Nodetbl.iter
      (fun n1 n2 ->
        if not (f n1 n2) then begin
          Nodetbl.remove s_map n1;
          Nodetbl.remove rev_s_map n2;
          Nodetbl.remove rev_map n2;
          Xset.remove settled_roots (n1, n2);
        end
      ) s_map

  method promote nd1 nd2 =
    if self#has_unsettled_mapping nd1 nd2 then begin
      let _ = self#remove nd1 nd2 in
      self#add_settled ~stable:false nd1 nd2
    end
    else
      None, None

  method demote nd1 nd2 =
    if self#has_settled_mapping nd1 nd2 then begin
      let _ = self#remove nd1 nd2 in
      self#add_unsettled nd1 nd2
    end
    else
      None, None


  method private _to_seq m = Nodetbl.to_seq m

  method private _dom m = Nodetbl.to_seq_keys m
  method private _cod m = Nodetbl.to_seq_values m


  method to_seq_unsettled = self#_to_seq map
  method to_seq_settled = self#_to_seq s_map
  method to_seq = Seq.append self#to_seq_unsettled self#to_seq_settled

  method to_array = Array.of_seq self#to_seq
  method to_array_unsettled = Array.of_seq self#to_seq_unsettled
  method to_array_settled = Array.of_seq self#to_seq_settled

  method cod_unsettled = self#_cod map
  method dom_unsettled = self#_dom map

  method cod_settled = self#_cod s_map
  method dom_settled = self#_dom s_map

  method cod = Seq.append self#cod_unsettled self#cod_settled
  method dom = Seq.append self#dom_unsettled self#dom_settled


  method to_string_gid =
    let buf = Buffer.create 0 in
    let gi_pairs = ref [] in
    let cmp (gi1, _, _, _, _, _) (gi2, _, _, _, _, _) = Stdlib.compare gi1 gi2 in

    let add nd1 nd2 =
      let gi1 = nd1#gindex in
      let gi2 = nd2#gindex in
      let lgi1 = (cenv#tree1#initial_leftmost nd1)#gindex in
      let lgi2 = (cenv#tree2#initial_leftmost nd2)#gindex in
      let u1 = nd1#uid in
      let u2 = nd2#uid in
      gi_pairs := (gi1, gi2, lgi1, lgi2, u1, u2) :: !gi_pairs
    in
    let pr mark =
    List.iter
      (fun (gi1, gi2, lgi1, lgi2, u1, u2) ->
        Buffer.add_string buf
          (sprintf
             "%s: (%a)%a-(%a)%a (%a-%a)\n"
             mark
             GI.ps lgi1 GI.ps gi1
             GI.ps lgi2 GI.ps gi2
             UID.ps u1 UID.ps u2
          )
      ) (List.fast_sort cmp !gi_pairs)
    in
    self#iter_unsettled add;
    pr "U";
    gi_pairs := [];
    self#iter_settled add;
    pr "S";
    Buffer.contents buf

  method get_mapping_list () =
    let ml = ref [] in
    self#iter_unsettled (fun n1 n2 -> ml := (n1, n2)::!ml);
    self#iter_settled (fun n1 n2 -> ml := (n1, n2)::!ml);
    let sort = List.fast_sort (fun (n, _) (n', _) -> UID.compare n#uid n'#uid) in
    sort !ml

  method get_reduced_mapping_list () =
    let reduce list =
      let r, reduced =
        List.fold_left
          (fun (range, l) (n1, n2) ->
            match range with
            | [] -> [(n1, n2)], l

            | [(n1', n2')] ->
                if n1#uid = UID.succ n1'#uid && n2#uid = UID.succ n2'#uid then
                  [(n1', n2'); (n1, n2)], l
                else
                  [(n1, n2)], [(n1', n2')]::l

            | [(n1', n2'); (n1'', n2'')] ->
                if n1#uid = UID.succ n1''#uid && n2#uid = UID.succ n2''#uid then
                  [(n1', n2'); (n1, n2)], l
                else
                  [(n1, n2)], [(n1', n2'); (n1'', n2'')]::l

            | _ -> assert false
          ) ([], []) list
      in
      List.rev
        (match r with
        | [] -> reduced
        | [_] -> r::reduced
        | [_; _] -> r::reduced
        | _ -> assert false
        )
    in
    reduce (self#get_mapping_list())

  method to_string =
    let l1 = ref [] in
    let l1s = ref [] in
    let l2 = ref [] in

    self#iter_unsettled (fun n1 n2 -> l1 := (n1, n2)::!l1);
    self#iter_settled (fun n1 n2 -> l1s := (n1, n2)::!l1s);
    self#iter_rev (fun n1 n2 -> l2 := (n1, n2)::!l2);

    let sort = List.fast_sort (fun (n, _) (n', _) -> UID.compare n#uid n'#uid) in

    let unsettled = sort !l1 in
    let settled = sort !l1s in
    let rev = sort !l2 in

    let reduce list =
      let r, reduced =
        List.fold_left
          (fun (range, l) (n1, n2) ->
            match range with
            | [] -> [(n1, n2)], l

            | [(n1', n2')] ->
                if n1#uid = UID.succ n1'#uid && n2#uid = UID.succ n2'#uid then
                  [(n1', n2'); (n1, n2)], l
                else
                  [(n1, n2)], [(n1', n2')]::l

            | [(n1', n2'); (n1'', n2'')] ->
                if n1#uid = UID.succ n1''#uid && n2#uid = UID.succ n2''#uid then
                  [(n1', n2'); (n1, n2)], l
                else
                  [(n1, n2)], [(n1', n2'); (n1'', n2'')]::l

            | _ -> assert false
          ) ([], []) list
      in
      List.rev
        (match r with
        | [] -> reduced
        | [_] -> r::reduced
        | [_; _] -> r::reduced
        | _ -> assert false
        )
    in

    let range_to_string = function
      | [n1, n2] -> sprintf "%a-%a" nups n1 nups n2
      | [n1, n2; n1', n2'] -> sprintf "[%a:%a]-[%a:%a]" nups n1 nups n1' nups n2 nups n2'
      | _ -> assert false
    in
    let sz = List.length !l1 in
    let szs = List.length !l1s in
    let szr = List.length !l2 in
    sprintf "map size: %d (rev map size: %d)" (sz+szs) szr ^
    sprintf "\nUNSETTLED (size=%d):\n" sz ^
    (Xlist.to_string range_to_string ";" (reduce unsettled)) ^
    sprintf "\nSETTLED (size=%d):\n" szs ^
    (Xlist.to_string range_to_string ";" (reduce settled)) ^
    sprintf "\nREV_MAP (size=%d):\n" szr ^
    (Xlist.to_string range_to_string ";" (reduce rev))

  method dump fname =
    let arr = self#to_array in
    Array.fast_sort (fun (n1, _) (n2, _) -> compare n1#uid n2#uid) arr;
    try
      let ch = open_out fname in
      Array.iter
        (fun (nd1, nd2) ->
          fprintf ch "%a -- %a\n" UID.r nd1#uid UID.r nd2#uid
        ) arr;
      close_out ch
    with
      Sys_error s -> let _ = s in [%warn_log "%s" s]

  method dump_json ?(comp=Comp.none) fname =
    let _fprintf ch fmt =
      Printf.ksprintf (fun s -> ignore (ch#output_ s 0 (String.length s))) fmt
    in
    let dump_node ch nd =
      let loc = nd#data#src_loc in
      let so = loc.Loc.start_offset in
      let eo = loc.Loc.end_offset in
      let sl = loc.Loc.start_line in
      let el = loc.Loc.end_line in
      let lab = nd#data#get_category in
      _fprintf ch "{";
      _fprintf ch "\"label\":\"%s\"" lab;
      _fprintf ch ",\"start_offset\":%d,\"end_offset\":%d,\"start_line\":%d,\"end_line\":%d" so eo sl el;
      _fprintf ch "}";
    in
    let dump_map ?(comma=false) ch map =
      let comma_flag = ref comma in
      Nodetbl.iter
        (fun n1 n2 ->
          if !comma_flag then
            _fprintf ch ",";
          _fprintf ch "[";
          dump_node ch n1;
          _fprintf ch ",";
          dump_node ch n2;
          _fprintf ch "]";
          comma_flag := true;
        ) map;
      !comma_flag
    in
    try
      let ch = new Xchannel.out_channel ~comp (Xchannel.Destination.of_file fname) in
      _fprintf ch "[";
      let comma = dump_map ch map in
      let _ = dump_map ~comma ch s_map in
      _fprintf ch "]";
      ch#close
    with
    | Xchannel.Error s -> let _ = s in [%warn_log "%s" s]


  method dump_with_info ?(comp=Comp.none) fname =
    let _fprintf ch fmt =
      Printf.ksprintf (fun s -> ignore (ch#output_ s 0 (String.length s))) fmt
    in

    let arr_unsettled = self#to_array_unsettled in
    Array.fast_sort (fun (n1, _) (n2, _) -> compare n1#uid n2#uid) arr_unsettled;
    let arr_settled = self#to_array_settled in
    Array.fast_sort (fun (n1, _) (n2, _) -> compare n1#uid n2#uid) arr_settled;
    let get_gid nd =
      let gid = nd#data#gid in
      if gid > 0 then gid else nd#gindex
    in
    try
      let ch = new Xchannel.out_channel ~comp (Xchannel.Destination.of_file fname) in
      let f =
        fun (nd1, nd2) ->
          let k = if nd1#data#eq nd2#data then "E" else "R" in
          _fprintf ch "%s[%a:%a]%s -- [%a:%a]%s\n" k
            nups nd1 GI.ps (get_gid nd1) nd1#data#to_string
            nups nd2 GI.ps (get_gid nd2) nd2#data#to_string
      in
      _fprintf ch
        "%d unsettled entries and %d settled entries\n"
        (Array.length arr_unsettled) (Array.length arr_settled);
      _fprintf ch "*** Unsettled ***\n";
      Array.iter f arr_unsettled;
      _fprintf ch "*** Settled ***\n";
      Array.iter f arr_settled;
      ch#close
    with
    | Xchannel.Error s -> let _ = s in [%warn_log "%s" s]


  method dump_gid_json ?(comp=Comp.none) is_mov fname =
    let mapped_node_tbl = Nodetbl.create 0 in
    let sps, mvs =
      Seq.partition_map
        (fun (nd1, nd2) ->
          Nodetbl.add mapped_node_tbl nd2 nd1;
          if is_mov nd1 nd2 then
            Right (nd1, nd2)
          else
            Left (nd1, nd2)
        ) self#to_seq
    in
    let spa = Array.of_seq sps in
    Array.fast_sort (fun (n1, _) (n2, _) -> compare n1#gindex n2#gindex) spa;
    let mva = Array.of_seq mvs in
    Array.fast_sort (fun (n1, _) (n2, _) -> compare n1#gindex n2#gindex) mva;

    let is_subtree_root x =
      x#data#is_boundary
    in

    let _fprintf = Json._fprintf in
    let get_gid = Json.get_gid in
    let get_info = Json.get_info ~is_subtree_root cenv#tree1 cenv#tree2 mapped_node_tbl in

    try
      let d = Filename.dirname fname in
      if not (Xfile.dir_exists d) then
        Xfile.mkdir d;
      let ch = new Xchannel.out_channel ~comp (Xchannel.Destination.of_file fname) in
      let dump ch a =
        let comma_flag = ref false in
        Array.iter
          (fun (nd1, nd2) ->
            if !comma_flag then
              _fprintf ch ",";
            let info = get_info nd1 nd2 in
            let gid1 = get_gid nd1 in
            let gid2 = get_gid nd2 in
            (*[%debug_log "!!! gid1=%a gid2=%a" GI.ps gid1 GI.ps gid2];
            [%debug_log "!!! nd1=%s nd2=%s" nd1#to_string nd2#to_string];*)
            _fprintf ch "[%a,%a,%s]" GI.rs gid1 GI.rs gid2 info;
            comma_flag := true
          ) a
      in
      _fprintf ch "{\"SPM\":[";
      dump ch spa;
      _fprintf ch "],\"MM\":[";
      dump ch mva;
      _fprintf ch "]}";
      ch#close
    with
    | Xchannel.Error s -> let _ = s in [%warn_log "%s" s]


  method print_status =
    [%debug_log "num of unsettled bindings: %d" (Nodetbl.length map)];
    [%debug_log "num of settled bindings: %d" (Nodetbl.length s_map)]

  method setup_rev_map =
    [%debug_log "setup_rev_map: deprecated!"]

  method mem_dom n = self#mem n
  method mem_cod n = Nodetbl.mem rev_map n || Nodetbl.mem rev_s_map n

  method mem_dom_settled n = self#mem_settled n
  method mem_cod_settled n = Nodetbl.mem rev_s_map n

  method mem_dom_unsettled n = self#mem_unsettled n
  method mem_cod_unsettled n = Nodetbl.mem rev_map n

  method cleanup_ghost =
    let is_ghost_node nd = nd#data#src_loc = Loc.ghost in
    self#iter
      (fun nd1 nd2 ->
        if is_ghost_node nd1 || is_ghost_node nd2 then begin
          [%debug_log "cleanup_ghost: %a-%a" nups nd1 nups nd2];
          ignore (self#remove nd1 nd2)
        end
      )


  method count_p_mapping
      (p : 'node_t -> 'node_t -> 'node_t -> 'node_t -> bool)
      (nd1 : 'node_t)
      (nd2 : 'node_t)
      =
    let count = ref 0 in
    let f ?(settled=false) n1 n2 =
      let tree1 = cenv#tree1 in
      if p nd1 nd2 n1 n2 then begin
(*
          [%debug_log " crossing: %a-%a -> %a-%a"
              nups nd1 nups nd2 nups n1 nups n2];
*)
        if settled then
          let step = n1#gindex - (tree1#initial_leftmost n1)#gindex + 1 in
          count := !count + step
        else
          incr count
      end
    in
    self#iter_unsettled f;
    self#iter_settled_roots (f ~settled:true);
    !count

  method count_crossing_mapping nd1 nd2 =
    self#count_p_mapping is_crossing nd1 nd2

  method count_crossing_matches nd1 nd2 =
    self#count_p_mapping
      (fun nd1 nd2 n1 n2 ->
        is_crossing nd1 nd2 n1 n2 && n1#data#eq n2#data
      )
      nd1 nd2

  method count_crossing_or_incompatible_matches nd1 nd2 =
    try
      if not self#use_crossing_or_incompatible_matches_count_cache then
        raise Not_found;

      let count =
        Hashtbl.find crossing_or_incompatible_matches_count_cache (nd1, nd2)
      in

      [%debug_log "cache hit!"];

      crossing_or_incompatible_matches_count_cache_hit_count <-
        crossing_or_incompatible_matches_count_cache_hit_count + 1;

      count
    with
      Not_found ->
        let count =
          self#count_p_mapping
            (fun nd1 nd2 n1 n2 ->
              n1#data#eq n2#data &&
              (is_crossing nd1 nd2 n1 n2 || cenv#is_incompatible nd1 nd2 n1 n2)
            )
            nd1 nd2
        in
        if self#use_crossing_or_incompatible_matches_count_cache then
          Hashtbl.add crossing_or_incompatible_matches_count_cache (nd1, nd2) count;

        count

  method count_compatible_noncrossing_matches nd1 nd2 =
    let count =
      self#count_p_mapping
        (fun nd1 nd2 n1 n2 ->
          n1#data#eq n2#data &&
          (not (is_crossing nd1 nd2 n1 n2) && not (cenv#is_incompatible nd1 nd2 n1 n2))
        )
        nd1 nd2
    in
    count

  method iter_p_mapping
      (p : 'node_t -> 'node_t -> 'node_t -> 'node_t -> bool)
      (nd1 : 'node_t)
      (nd2 : 'node_t)
      (f : 'node_t -> 'node_t -> unit)
      =
    self#iter
      (fun n1 n2 ->
        if p nd1 nd2 n1 n2 then
          f n1 n2
      )

  method iter_crossing_mapping nd1 nd2 (f : 'node_t -> 'node_t -> unit) : unit =
    self#iter_p_mapping is_crossing nd1 nd2 f

  method iter_incompatible_mapping nd1 nd2 (f : 'node_t -> 'node_t -> unit) : unit =
    self#iter_p_mapping cenv#is_incompatible nd1 nd2 f

  method iter_crossing_or_incompatible_mapping nd1 nd2 (f : 'node_t -> 'node_t -> unit) : unit =
    self#iter_p_mapping
      (fun nd1 nd2 n1 n2 ->
        is_crossing nd1 nd2 n1 n2 ||
        cenv#is_incompatible nd1 nd2 n1 n2
      ) nd1 nd2 f


  val reptbl = (Nodetbl.create 0 : 'node_t Nodetbl.t)

  val mutable reptbl_is_empty = true

  method private clear_reptbl () =
    Nodetbl.clear reptbl;
    reptbl_is_empty <- true

  method iter_rep_for_crossing is_move (f : 'node_t -> 'node_t -> unit) : unit =
    if reptbl_is_empty then begin
      self#cache_rep_for_crossing is_move ();
      reptbl_is_empty <- false
    end;
    Nodetbl.iter f reptbl

  method private cache_rep_for_crossing is_move () : unit =
    [%debug_log "mapping:\n%s" self#to_string_gid];
    let last_g1 = ref GI.unknown in
    let last_g2 = ref GI.unknown in
    let last_lg1 = ref GI.unknown in
    let last_lg2 = ref GI.unknown in
    let last_is_mov = ref false in
    cenv#tree1#fast_scan_whole_initial
      (fun n1 ->
        try
          let n2 = self#find n1 in
          let g1 = n1#gindex in
          let g2 = n2#gindex in
          let lg1 = (cenv#tree1#initial_leftmost n1)#gindex in
          let lg2 = (cenv#tree2#initial_leftmost n2)#gindex in
          let is_mov = is_move n1 n2 in
          if g1 - !last_g1 = 1 && g2 - !last_g2 = 1 then begin
            if
              is_mov <> !last_is_mov &&
              (lg1 <> !last_lg1 || lg2 <> !last_lg2)
            then begin
              [%debug_log "%a-%a %a" GI.ps g1 GI.ps g2 nps n1];
              Nodetbl.add reptbl n1 n2;
            end
            else if
              n1#data#is_boundary && n2#data#is_boundary &&
              n1#data#is_order_insensitive && n2#data#is_order_insensitive
            then begin
              [%debug_log "%a-%a %a" GI.ps g1 GI.ps g2 nps n1];
              Nodetbl.add reptbl n1 n2;
            end
            else
              [%debug_log "(%a-%a %a)" GI.ps g1 GI.ps g2 nps n1]
          end
          else begin
            [%debug_log " %a-%a %a" GI.ps g1 GI.ps g2 nps n1];
            Nodetbl.add reptbl n1 n2;
          end;
          last_g1 := g1;
          last_g2 := g2;
          last_lg1 := lg1;
          last_lg2 := lg2;
          last_is_mov := is_mov
        with
          Not_found -> ()
       )

  method add_to_rep nd1 nd2 =
    [%debug_log "%a-%a" nups nd1 nups nd2];
    try
      let nd1' = Nodetbl.find reptbl nd1 in
      if nd1' = nd2 then begin
        [%debug_log "not added"]
      end
      else begin
        [%debug_log "not added: nd1'(=%a) != nd2(=%a)" nups nd1' nups nd2]
      end
    with Not_found -> begin
      Nodetbl.add reptbl nd1 nd2;
      [%debug_log "added"]
    end

  method invalidate_rep nd1 nd2 =
    [%debug_log "%a-%a" nups nd1 nups nd2];
    try
      if Nodetbl.find reptbl nd1 = nd2 then begin
        let g1 = GI.offset nd1#gindex 1 in
        [%debug_log "g1=%a" GI.ps g1];
        let n1 = cenv#tree1#search_node_by_gindex g1 in
        [%debug_log "n1=%a" nups n1];
        let n1' = self#find n1 in
        [%debug_log "n1'=%a" nups n1'];
        let g2 = GI.offset nd2#gindex 1 in
        [%debug_log "g2=%a" GI.ps g2];
        if n1'#gindex = g2 then begin
          let n2 = cenv#tree2#search_node_by_gindex g2 in
          [%debug_log "added to reptbl: %a-%a" nups n1 nups n2];
          Nodetbl.add reptbl n1 n2
        end
      end
    with Not_found -> ()

  method iter_crossing_mapping_rep
      (is_move : 'node_t -> 'node_t -> bool)
      (nd1 : 'node_t)
      (nd2 : 'node_t)
      (f : 'node_t -> 'node_t -> unit)
      : unit
      =
    self#iter_rep_for_crossing is_move
      (fun n1 n2 ->
        if is_crossing nd1 nd2 n1 n2 then
          f n1 n2
        (*else
          [%debug_log "not crossing: %a-%a" nups n1 nups n2]*)
      )

  method iter_incompatible_mapping_rep nd1 nd2 (f : 'node_t -> 'node_t -> unit) : unit =
    let tree1 = cenv#tree1 in
    let tree2 = cenv#tree2 in
    let is_incompat = cenv#is_incompatible nd1 nd2 in
    let gi2 = nd2#gindex in
    let lgi2 = (tree2#initial_leftmost nd2)#gindex in
    tree1#fast_scan_whole_initial_subtree nd1
      (fun n1 ->
        try
          let n2 = self#find n1 in
          let g2 = n2#gindex in
          if
            (g2 < lgi2 || gi2 <= g2) &&
            is_incompat n1 n2
          then
            f n1 n2
        with
          Not_found -> ()
      );
    let gi1 = nd1#gindex in
    let lgi1 = (tree1#initial_leftmost nd1)#gindex in
    tree2#fast_scan_whole_initial_subtree nd2
      (fun n2 ->
        try
          let n1 = self#inv_find n2 in
          let g1 = n1#gindex in
          if
            (g1 < lgi1 || gi1 <= g1) &&
            is_incompat n1 n2
          then
            f n1 n2
        with
          Not_found -> ()
      );
    tree1#iter_initial_ancestor_nodes nd1
      (fun n1 ->
        try
          let n2 = self#find n1 in
          if is_incompat n1 n2 then
            f n1 n2
        with
          Not_found -> ()
      );
    tree2#iter_initial_ancestor_nodes nd2
      (fun n2 ->
        try
          let n1 = self#inv_find n2 in
          if is_incompat n1 n2 then
            f n1 n2
        with
          Not_found -> ()
      )

  method iter_crossing_or_incompatible_mapping_rep is_move nd1 nd2 f =
    [%debug_log "iter_crossing_mapping_rep %a %a" nups nd1 nups nd2];
    self#iter_crossing_mapping_rep is_move nd1 nd2 f;
    [%debug_log "iter_incompatible_mapping_rep %a %a" nups nd1 nups nd2];
    self#iter_incompatible_mapping_rep nd1 nd2 f


  val mutable partition_a1 = [||]
  val mutable partition_a2 = [||]

  method setup_partitions =
    let nds1, nds2 = ref [], ref [] in
    self#iter_settled_roots
      (fun n1 n2 ->
        if n1#data#is_partition && n1#data#_digest <> None then begin
          nds1 := n1 :: !nds1;
          nds2 := n2 :: !nds2;
        end
    );
    let a1 = Array.of_list !nds1 in
    let a2 = Array.of_list !nds2 in
    let cmp n1 n2 = Stdlib.compare n1#gindex n2#gindex in
    Array.fast_sort cmp a1;
    Array.fast_sort cmp a2;
    let al1 = Array.map (fun n -> n#data#_label) a1 in
    let al2 = Array.map (fun n -> n#data#_label) a2 in
    let m, _, _, _ = Adiff.adiff al1 al2 in
    let p1, p2 = List.split (List.map (fun (i, j) -> a1.(i), a2.(j)) m) in
    let pa1 = Array.of_list p1 in
    let pa2 = Array.of_list p2 in
    Array.fast_sort cmp pa1;
    Array.fast_sort cmp pa2;

    let get_to_be_filtered tree pa =
      let l = ref [] in
      Array.iteri
        (fun i n ->
          let lmn = tree#initial_leftmost n in
          try
            if lmn#gindex - 1 = pa.(i-1)#gindex then
              l := n :: !l
          with
            _ -> ()
        ) pa;
      !l
    in
    let tree1 = cenv#tree1 in
    let tree2 = cenv#tree2 in
    let to_be_filtered1 = get_to_be_filtered tree1 pa1 in
    let to_be_filtered2 = get_to_be_filtered tree2 pa2 in

    let fp1, fp2 = ref [], ref [] in
    for i = (Array.length pa1) - 1 downto 0 do
      if
        not (List.memq pa1.(i) to_be_filtered1 &&
             List.memq pa2.(i) to_be_filtered2)
      then begin
        fp1 := pa1.(i)#gindex :: !fp1;
        fp2 := pa2.(i)#gindex :: !fp2
      end
    done;

    partition_a1 <- Array.of_list !fp1;
    partition_a2 <- Array.of_list !fp2;

    begin %debug_block
      Array.iteri
        (fun i gi1 ->
          let n1 = tree1#search_node_by_gindex gi1 in
          let n2 = tree2#search_node_by_gindex (partition_a2.(i)) in
          [%debug_log "partition[%d]: %a-%a %s" i nups n1 nups n2 n1#data#label]
        ) partition_a1
    end


  method private _partition_nodes partition_a (nds : 'node_t list) =
    let plen = Array.length partition_a in

    if plen = 0 then
      raise (Invalid_argument "Mapping.c#_partition_nodes");

    let a = Array.make (plen + 1) (ref []) in
    Array.iteri (fun i _ -> a.(i) <- ref []) a;
    List.iter
      (fun n ->
        let g = n#gindex in

        if g < partition_a.(0) then
          a.(0) := n :: !(a.(0));

        if plen > 1 then
          for i = 1 to plen - 1 do
            if partition_a.(i - 1) < g && g < partition_a.(i) then
              a.(i) := n :: !(a.(i))
          done;

        if g > partition_a.(plen - 1) then
          a.(plen) := n :: !(a.(plen))

      ) nds;

    begin %debug_block
      Array.iteri
        (fun i ndsr ->
          if !ndsr <> [] then
            [%debug_log "partition[%d] = [%s]" i
              (Xlist.to_string (fun n -> UID.to_string n#uid) ";" !ndsr)]
        ) a
    end;

    Array.map (fun lr -> !lr) a


  method partition_nodes1 nds = self#_partition_nodes partition_a1 nds
  method partition_nodes2 nds = self#_partition_nodes partition_a2 nds


  method get_subtree_match_score (nd1 : 'node_t) (nd2 : 'node_t) =
    let score = ref 0 in
    let tree1 = cenv#tree1 in
    let tree2 = cenv#tree2 in
    tree1#fast_scan_whole_initial_subtree nd1
      (fun n1 ->
        let ns2 = self#find_stable_pair n1 in
        List.iter
          (fun n2 ->
            if tree2#initial_subtree_mem nd2 n2 then
              incr score
          ) ns2;
      );
    !score


  method get_proximity
      ?(extra=Nodetbl.create 0) (nd1 : 'node_t) (nd2 : 'node_t)
      =
  let ancs1 = Array.of_list nd1#initial_ancestor_nodes in
  let ancs2 = Array.of_list nd2#initial_ancestor_nodes in
  let lai1 = (Array.length ancs1) - 1 in
  let lai2 = (Array.length ancs2) - 1 in

  let prox = new Proximity.node_proximity in

  let _cands = ref [] in

  for i = lai1 downto 0 do
    let ni = ancs1.(i) in
    try
      let n, high_conf =
        try
          let x = self#find ni in
          x, true
        with
          Not_found ->
            let x = Nodetbl.find extra ni in
            [%debug_log "(%a,%a): pivot derived from extra map" nups nd1 nups nd2];
            x, false
      in
      for j = lai2 downto 0 do
        if n == ancs2.(j) then
          _cands := (high_conf, ni, n, i + j) :: !_cands
      done
    with
      Not_found -> ()
  done;

  let cands =
    List.fast_sort
      (fun (_, _, _, p0) (_, _, _, p1) -> Stdlib.compare p1 p0)
      !_cands
  in
  begin
    match cands with
    | [] -> ()
    | (high, n1, n2, p)::rest ->

        [%debug_log "(%a,%a): prox=%d pivot=(%a,%a) (confidence=%s)" nups nd1 nups nd2 p
          nups n1 nups n2 (if high then "high" else "low")];

        prox#set_primary_prox p;
        prox#set_primary_pivot (n1, n2);
        if not high then
          prox#lower_confidence;

        let rest' =
          List.filter (fun (h, _, _, _) -> h = not high) rest
        in
        match rest' with
        | [] -> ()
        | (_, n1, n2, p)::_ ->
            prox#set_secondary_prox p;
            prox#set_secondary_pivot (n1, n2)
  end;
  prox
  (* end of method get_proximity *)

end (* of class Mapping.c *)
]
