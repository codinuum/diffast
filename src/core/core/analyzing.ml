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
(* analyzing.ml *)

[%%prepare_logger]

module Xhash = Diffast_misc.Xhash
module Xset = Diffast_misc.Xset
module Xlist = Diffast_misc.Xlist
module Xprint = Diffast_misc.Xprint
module Xfile = Diffast_misc.Xfile
module Compression = Diffast_misc.Compression
module UID = Diffast_misc.UID
module GI = Diffast_misc.GIndex
module Otree = Diffast_misc.Otree
module Mapping = Diffast_misc.Mapping
module SMP = Diffast_misc.SMP
module Otreelib = Diffast_misc.Otreelib
module MID = Moveid
module B = Diffast_misc.Binding
module Nodetbl = Node.Tbl

let matched_sibling_ratio_thresh = 0.9

let sprintf = Printf.sprintf
let printf = Printf.printf

type node_t = Spec.node_t
type tree_t = Spec.tree_t

let ups = Misc.ups
let gps = Misc.gps
let nps = Misc.nps
let nups = Misc.nups
let ngps = Misc.ngps
let nsps = Misc.nsps
let locps = Misc.locps
let labps = Misc.labps
let ndps = Misc.ndps

(*
exception No_differences_found
*)
exception Found

[%%capture_path
module F (Label : Spec.LABEL_T) = struct

  module Postprocessing = Postprocessing.F (Label)

  let mkinfo = Info.make

  (* generates movement info from isomorphic subtrees *)
  let classify_isomorphic (tree1 : tree_t) (tree2 : tree_t) mapping iso =
    List.fold_left
      (fun r i ->
        let j = Mapping.find i mapping in
        let nd1 = tree1#get i in
        let nd2 = tree2#get j in
        let gi1 = nd1#gindex in
        let gi2 = nd2#gindex in
        let lgi1 = (tree1#initial_leftmost nd1)#gindex in (* dangerous access to global data from subtree *)
        let lgi2 = (tree2#initial_leftmost nd2)#gindex in (* dangerous access to global data from subtree *)
        let lgi_gi1, lgi_gi2 = (lgi1, gi1), (lgi2, gi2) in
        let info1, info2 = mkinfo nd1, mkinfo nd2 in

        let has_initial_parent1 = nd1#has_initial_parent in
        let has_initial_parent2 = nd2#has_initial_parent in

        if  has_initial_parent1 && has_initial_parent2 then
          let p1, p2 = nd1#initial_parent, nd2#initial_parent in
          let pi, pj = p1#index, p2#index in
          begin
            try
              if pj = (Mapping.find pi mapping) then
                (Pruned.make_isomorphic lgi_gi1 lgi_gi2 info1 info2)::r
              else
                raise Not_found

            with Not_found ->
              (Pruned.make_migratory lgi_gi1 lgi_gi2 info1 info2)::r
          end

        else if has_initial_parent1 || has_initial_parent2 then
          (Pruned.make_migratory lgi_gi1 lgi_gi2 info1 info2)::r

        else
          (Pruned.make_isomorphic lgi_gi1 lgi_gi2 info1 info2)::r

      ) [] iso

  let not_redundant mem tree i =
    let nd = tree#get i in
    let b = not (mem tree nd) in

    [%debug_log "%d -> %B" i b];

    b


  (* to avoid pruning too much *)
  let shrink_iso tree1 tree2 mapping iso1 =

    let iso2 =
      try
        List.map (fun i -> Mapping.find i mapping) iso1
      with Not_found -> assert false
    in

    let tbl1 = Nodetbl.create 0 in
    let tbl2 = Nodetbl.create 0 in

    let tadd tbl k v =
      try
        Nodetbl.replace tbl k (v::(Nodetbl.find tbl k))
      with Not_found ->
        Nodetbl.add tbl k [v]
    in

    let ison1 = List.map tree1#get iso1 in
    let ison2 = List.map tree2#get iso2 in

    [%debug_log "[%a]" nsps ison1];

    List.iter2
      (fun nd1 nd2 ->
        tadd tbl1 nd1#parent nd1;
        tadd tbl2 nd2#parent nd2
      ) ison1 ison2;

    let cands1 = ref [] in
    let cands2 = ref [] in

    Nodetbl.iter
      (fun pnd nds ->
        if
          Array.for_all
            (fun n -> List.memq n nds)
            pnd#children
        then begin

          [%debug_log "all children are to be pruned: %a" nups pnd];

          cands1 := (List.hd nds)::!cands1
        end
      ) tbl1;
    Nodetbl.iter
      (fun pnd nds ->
        if
          Array.for_all
            (fun n -> List.memq n nds)
            pnd#children
        then begin

          [%debug_log "all children are to be pruned: %a" nups pnd];

          cands2 := (List.hd nds)::!cands2
        end
      ) tbl2;

    let iso1' = ref [] in

    List.iter2
      (fun nd1 nd2 ->
        if List.memq nd1 !cands1 || List.memq nd2 !cands2 then begin
          iso1' := nd1#children_indexes @ !iso1'
        end
        else begin
          iso1' := nd1#index::!iso1'
        end
      ) ison1 ison2;

    [%debug_log "[%a]" nsps (List.rev_map tree1#get (!iso1'))];

    !iso1'
  (* end of func shrink_iso *)


  (*
   * generates Edit.seq, determines nodes to be expanded, and
   * accumulates nodes to be pruned
   *)
  let analyze0
      options
      (tree1 : tree_t)
      (tree2 : tree_t)
      eds     (* edit sequence by the base algorithm *)
      mapping (* mapping by the base algorithm *)
      iso     (* isomorphic subtrees by the base algorithm *)
      pruned  (* subtrees to be pruned (global) *)
      =
    let expnd1, expnd2 = ref [], ref [] in

    let moderate_nchildren =
      Misc.moderate_nchildren ~threshold:options#moderate_nchildren_threshold
    in

    let proc_one = function
      | Diffast_misc.Edit.Relabel(i1, i2) ->
          let nd1, nd2 = tree1#get i1, tree2#get i2 in

          if nd1#is_collapsed && (moderate_nchildren nd1) then
            if nd1#collapse_not_locked then
              expnd1 := i1::!expnd1;
(*
            else
              if nd1#data#eq nd2#data then begin
                expnd1 := i1::!expnd1;
                nd1#unlock_collapse;
                Array.iter (fun n -> n#lock_collapse) nd1#initial_children
              end;
*)

          if nd2#is_collapsed && (moderate_nchildren nd2) then
            if nd2#collapse_not_locked then
              expnd2 := i2::!expnd2;
(*
            else
              if nd2#data#eq nd1#data then begin
                expnd2 := i2::!expnd2;
                nd2#unlock_collapse;
                Array.iter (fun n -> n#lock_collapse) nd2#initial_children
              end;
*)
          begin %debug_block
            [%debug_log "[RELABELED]: \"(%a)%s\" --> \"(%a)%s\""
              nups nd1 nd1#to_qualified_string nups nd2 nd2#to_qualified_string];
          end;

      | Diffast_misc.Edit.Delete i ->
          let nd = tree1#get i in
          if nd#is_collapsed && nd#collapse_not_locked && (moderate_nchildren nd) then
            expnd1 := i::!expnd1

      | Diffast_misc.Edit.Insert(j, (*children_ref*)_) ->
          let nd = tree2#get j in
          if nd#is_collapsed && nd#collapse_not_locked && (moderate_nchildren nd) then
            expnd2 := j::!expnd2

    in (* end of func proc_one *)

    Diffast_misc.Edit.seq_iter proc_one eds;

    pruned#add_pruned_nodes (classify_isomorphic tree1 tree2 mapping iso);

    begin %debug_block
      [%debug_log "Mapping:\n"];
      Mapping.iter
        (fun i j -> [%debug_log "%a -- %a" nups (tree1#get i) nups (tree2#get j)])
        mapping
    end;

    !expnd1, !expnd2
  (* end of func analyze0 *)


  let do_compare options cenv count cid tree1 tree2 pruned =
    let _ = count in
    let _ = cid in

    let sz1, sz2 = tree1#size, tree2#size in

    [%debug_log "*** %d: ANALYZING SUBTREE PAIR [%s] ***\n" count cid];
    [%debug_log "[%s]: sizes of (sub) trees: old=%d new=%d" cid sz1 sz2];


    [%debug_log "T1:\n%s\nT2:\n%s\n" tree1#to_string tree2#to_string];


    let eds, mapping, iso =
      if Misc.check_hard_tree_size_limit options sz1 sz2 then begin

        Xprint.warning "exceeds HARD (sub)tree size LIMIT! |T1|=%d |T2|=%d limit=%d"
          sz1 sz2 options#hard_tree_size_limit;

        if tree1#is_flat && tree2#is_flat (* && not options#ignore_huge_arrays_flag *) then begin
          Xprint.warning "trying to do array diff...";
          Flattreediff.find tree1 tree2
        end
        else
          Otreelib.find_trivial tree1 tree2
      end
      else
        if tree1#is_flat && tree2#is_flat then begin
          [%debug_log "using flattreediff..."];
          Flattreediff.find tree1 tree2
        end
        else begin
          [%debug_log "using otreediff..."];
          Treediff.sfind tree1 tree2
        end
    in

(*    let iso = shrink_iso tree1 tree2 mapping iso in *)


    (* exclude iso-subtree of size 1 *)
    let iso =
      List.filter
        (fun i ->
          let b = (tree1#leftmost i) <> i in

          if not b then
            [%debug_log "isomorphic subtree of size 1: %a (not treated as iso)" nups (tree1#get i)];
          b
        ) iso
    in

    begin %debug_block
      let to_s1 i = UID.to_string (tree1#get i)#uid in
      let to_s2 j = UID.to_string (tree2#get j)#uid in
      [%debug_log "edit sequence:\n%s\nmapping:\n%s"
        (Diffast_misc.Edit._seq_to_string to_s1 to_s2 eds)
        (Mapping._to_string to_s1 to_s2 mapping)];
    end;

    let iso_pairs =
      List.map (fun i -> i, Mapping.find i mapping) iso
    in

    let para_iso_mems = ref [] in
    let para_iso = ref [] in
    let non_iso = ref [] in

    let iso_members =
      List.fold_left
        (fun l (i, j) ->
          let mems = tree1#fast_subtree_members i in
          let nmems1 = List.length mems in

          if nmems1 < options#prune_threshold then begin
            non_iso := i::!non_iso;
            l
          end
          else
            let nmems2 = List.length (tree2#fast_subtree_members j) in
            let nimems1 = tree1#whole_initial_subtree_size (tree1#get i) in
            let nimems2 = tree2#whole_initial_subtree_size (tree2#get j) in

            if nmems1 < nimems1 || nmems2 < nimems2 then begin
              para_iso_mems := mems @ !para_iso_mems;
              para_iso := i::!para_iso
            end
            else
              if nmems1 > nimems1 || nmems2 > nimems2 then begin
                [%fatal_log "inconsistent iso: %d" i];
                exit 1
              end;

            l @ mems

        ) [] iso_pairs
    in
    let iso_pairs =
      List.filter (fun (i, _) -> not (List.mem i !non_iso)) iso_pairs
    in
    let iso, _ = List.split iso_pairs in

    [%debug_log "iso_members: [%s]"
      (Xlist.to_string string_of_int ";" iso_members)];

    let expnd1, expnd2 (* simply analyzed edit sequence *) =
      analyze0 options tree1 tree2 eds mapping iso pruned
    in

    let nmapping = new Node_mapping.c cenv in

    Mapping.iter
      (fun i j ->
        let nd1 = tree1#get i in
        let nd2 = tree2#get j in
        if not (nd1#is_collapsed || nd2#is_collapsed) || (nd1#data#equals nd2#data) then
          if List.mem i iso_members && not (List.mem i !para_iso_mems) then begin
            ignore (nmapping#add_settled ~stable:false nd1 nd2);

            if List.mem i iso then
              nmapping#add_settled_roots nd1 nd2
          end
          else
            ignore (nmapping#add_unsettled nd1 nd2)

      ) mapping;

    eds, mapping, iso_pairs, expnd1, expnd2, nmapping,
    iso_members, !para_iso_mems, !para_iso
  (* end of func do_compare *)



  let prune_and_expand
      cid
      (tree1 : tree_t)
      (tree2 : tree_t)
      (iso1, iso2, expnd1, expnd2)
      ((*g_nmapping*)_ : node_t Node_mapping.c)
      =
    let _ = cid in

    [%debug_log "[%s]: prune: T1[%a] T2:[%a]" cid nsps iso1 nsps iso2];
    [%debug_log "[%s]: expand: T1[%a] T2:[%a]" cid nsps expnd1 nsps expnd2];

    [%debug_log "pruning..."];

    let rt1, rt2 = tree1#root, tree2#root in

    if iso1 = [rt1] then rt1#unhide_parent;
    if iso2 = [rt2] then rt2#unhide_parent;

    (* change also 'pruned#add_pruned*' somewhere, if you change this *)
    tree1#prune_nodes iso1;
    tree2#prune_nodes iso2;

    [%debug_log "prune_and_expand: done."];

    [%debug_log "prune_and_expand: expanding..."];

    tree1#expand_nodes expnd1;
    tree2#expand_nodes expnd2;

    [%debug_log "prune_and_expand: done."];

    tree1#init; tree2#init
  (* end of func prune_and_expand *)


  let matching_cond options tree1 tree2 nd1 nd2 = (* for Analyzing.F.find_matching_subtrees *)
(*
  (nd1#data#is_named && nd2#data#is_named &&
  nd1#data#eq nd2#data) ||

  (nd1#is_collapsed && nd2#is_collapsed &&
  nd1#data#eq nd2#data) ||
 *)
(*
  (tree1#is_flat && tree2#is_flat)
 *)

    let cc1 = Misc.get_collapsed_children nd1 in
    let cc2 = Misc.get_collapsed_children nd2 in

    let _moderate_nchildren =
      Misc._moderate_nchildren ~threshold:options#moderate_nchildren_threshold
    in


    if (_moderate_nchildren cc1 nd1) || (_moderate_nchildren cc2 nd2) then
      tree1#is_flat && tree2#is_flat
    else begin

      [%debug_log "have huge amount of children:\n%d <-- %s\nand\n%d <-- %s"
        (List.length cc1) nd1#to_string
        (List.length cc2) nd2#to_string];

      (Misc._to_be_flat cc1 nd1) && (Misc._to_be_flat cc2 nd2)
    end

  let map_cond tree1 tree2 =
    try
      let rt1, rt2 = tree1#root, tree2#root in
      rt1#data#is_named && rt2#data#is_named &&
      rt1#data#eq rt2#data
    with Otree.Empty -> false


  let find_matching_subtrees options (tree1 : tree_t) (tree2 : tree_t) eds =

    let addtree subs nd1 nd2 =
      [%debug_log "addtree: %a %a" nups nd1 nups nd2];
      if nd1#data#eq nd2#data then
        if
          nd1#is_collapsed && nd2#is_collapsed &&
          not (nd1#data#equals nd2#data)
        then
          let tree1' = tree1#make_subtree_from_node nd1 in
          let tree2' = tree2#make_subtree_from_node nd2 in

          nd1#hide_parent;
          nd2#hide_parent;

          tree1'#expand_root; (* tree1'#init; *)
          tree2'#expand_root; (* tree2'#init; *)

          (tree1', tree2')::subs
        else subs
      else subs
    in (* end of func addtree *)

    let rels =
      List.filter
        (function Diffast_misc.Edit.Relabel _ -> true | _ -> false)
        eds
    in

    begin %debug_block
      let to_s1 i = UID.to_string (tree1#get i)#uid in
      let to_s2 j = UID.to_string (tree2#get j)#uid in
      [%debug_log "rels: [\n%s\n]"
        (Xlist.to_string (Diffast_misc.Edit._to_string to_s1 to_s2) "\n" rels)]
    end;

    match rels with
(*
  [Diffast_misc.Edit.Relabel(i1, i2)] ->
  let nd1, nd2 = tree1#get i1, tree2#get i2 in
  addtree [] nd1 nd2
 *)
    | _ ->
        let subs =
          List.fold_left
            (fun subs ed ->
              match ed with
                Diffast_misc.Edit.Relabel(i1, i2) ->
                  let nd1, nd2 = tree1#get i1, tree2#get i2 in
                  if matching_cond options tree1 tree2 nd1 nd2 then
                    addtree subs nd1 nd2
                  else
                    subs
              | _ -> subs
            ) [] rels
        in
        begin %debug_block
          let len = (List.length subs) in
          [%debug_log "%d subtree(s)\n" len];
          List.iter
            (fun (t1, t2) ->
              [%debug_log "T1:\n%s\nT2:\n%s\n"
                t1#to_string t2#to_string]
            ) subs
        end;

        subs
  (* end of func find_matching_subtrees *)


  (* compare subtrees *)
  let rec compare_subtree
      options
      counter
      cenv
      dirname
      (g_nmapping : node_t Node_mapping.c)
      pruned
      ((tree1 : tree_t), (tree2 : tree_t))
      =
    let ouid = UID.to_string tree1#root#uid in
    let nuid = UID.to_string tree2#root#uid in
    let cid = sprintf "%s-%s" ouid nuid in

    (* repeats until no nodes are expanded *)
    let rec loop() =

      counter#incr;
      let c = counter#value in

      if options#dots_flag then begin
        tree1#save_dot "Old" [] (Filename.concat dirname (sprintf "%d.old%s.dot" c ouid));
        tree2#save_dot "New" [] (Filename.concat dirname (sprintf "%d.new%s.dot" c nuid))
      end;

      let eds, mapping, iso_pairs, expnd1, expnd2, nmapping,
        iso_mems, para_iso_mems, para_iso
          =
        do_compare options cenv c cid tree1 tree2 pruned
      in

      let iso, iso2 = List.split iso_pairs in

      let get_nds t = List.map t#get in
      let para_iso2 =
        List.map (fun i -> Mapping.find i mapping) para_iso
      in
      pruned#add_para_iso1 (get_nds tree1 para_iso);
      pruned#add_para_iso2 (get_nds tree2 para_iso2);


      if options#dots_flag then
        Otreelib.to_dot (Filename.concat dirname (sprintf "%d.%s.dot" c cid))
          tree1 tree2 eds mapping iso_pairs;


      let to_be_pruned1 = iso_mems in

      List.iter (* add nodes to be pruned to global node mapping *)
        (fun i ->
          let is_para_iso = List.mem i para_iso_mems in
          let j = Mapping.find i mapping in
          let nd1 = tree1#get i in
          let nd2 = tree2#get j in

          [%debug_log "to_be_pruned: %a-%a" nups nd1 nups nd2];

          if nd1#is_collapsed && nd2#is_collapsed then begin
            let l1, l2 = ref [], ref [] in

            tree1#fast_scan_whole_initial_subtree nd1 (fun nd -> l1 := nd::!l1);
            tree2#fast_scan_whole_initial_subtree nd2 (fun nd -> l2 := nd::!l2);
            let sz1, sz2 = List.length !l1, List.length !l2 in
            if sz1 <> sz2 then begin
              [%fatal_log "pruned subtree size mismatch: %a vs %a: %d != %d"
                nups nd1 nups nd2 sz1 sz2];
              exit 1
            end;
            List.iter2
              (fun n1 n2 ->
                ignore (g_nmapping#add_settled ~stable:false n1 n2)
              ) !l1 !l2
          end
          else
            (* both are not collapsed *)
            if not (nd1#is_collapsed || nd2#is_collapsed) then
              if is_para_iso then
                ignore (g_nmapping#add_unsettled nd1 nd2)
              else
                ignore (g_nmapping#add_settled ~stable:false nd1 nd2)

            else begin
              [%debug_log "nd1#is_collapsed=%B nd1#data#digest=%s"
                nd1#is_collapsed nd1#data#digest_string];
              [%debug_log "nd2#is_collapsed=%B nd2#data#digest=%s"
                nd2#is_collapsed nd2#data#digest_string];
              assert false
            end;

          if not is_para_iso && List.mem i iso then
            g_nmapping#add_settled_roots nd1 nd2

        ) to_be_pruned1;


      begin %debug_block
        [%debug_log "* %d: iso=[%s]" c
          (Xlist.to_string
             (fun i -> UID.to_string (tree1#get i)#uid) "," iso)];
        [%debug_log "* %d: to_be_pruned1=[%s]" c
          (Xlist.to_string
             (fun i -> UID.to_string (tree1#get i)#uid) "," to_be_pruned1)]
      end;


      let clusters = (* by only using nodes not to be pruned *)
        Diffast_misc.Clustering.exact_cluster tree1 tree2
          (List.filter
             (fun (i, _) -> not (List.mem i to_be_pruned1)) mapping)
          eds
      in

      [%debug_log "* %d: contracting..." c];

      let deferred_cluster, pruned_clusters =
        Misc.contract tree1 tree2 clusters
      in

      [%debug_log "* %d: done." c];

      List.iter (* adding nodes in pruned clusters to global node mapping *)
        (fun clu ->
          List.iter
            (fun (n1, n2) ->
              ignore (g_nmapping#add_unsettled n1 n2)
            ) clu
        ) pruned_clusters;

      let subs = find_matching_subtrees options tree1 tree2 eds in

      List.iter (fun (t1, t2) -> t1#init; t2#init) subs;

      let subnmapping_list, deferred_clusters =
        if counter#value = 1 then begin
(*
            begin %info_block
              Xprint.verbose options#verbose_flag "found %d subtree pair(s)" (List.length subs);
              printf "comparing.%!";
            end;
*)
          let a =
            List.map
              (fun sub ->
                let b =
                  compare_subtree options counter cenv dirname g_nmapping pruned sub
                in
(*
                begin %info_block
                  printf ".%!";
                end;
*)
                b
              ) subs
          in
(*
          if not (options#viewer_flag) then
            begin %info_block
              printf "done.\n%!";
            end;
*)
          List.split a
        end
        else
          List.split
            (List.map
               (compare_subtree options counter cenv dirname g_nmapping pruned)
               subs)
      in

      let subs_data = List.combine subs subnmapping_list in

      let get_nds t = List.map (fun i -> t#get i) in
      let iso1_nds = get_nds tree1 iso in
      let iso2_nds = get_nds tree2 iso2 in
      let expnd1_nds = get_nds tree1 expnd1 in
      let expnd2_nds = get_nds tree2 expnd2 in

      [%debug_log "* %d: calling prune_and_expand" c];

      prune_and_expand cid tree1 tree2
        (iso1_nds, iso2_nds, expnd1_nds, expnd2_nds) g_nmapping;


      (* contract deferred clusters *)

      List.iter
        (fun (t1, t2) ->
          begin
            try
              t1#root#unhide_parent;
            with Otree.Empty -> ()
          end;
          begin
            try
              t2#root#unhide_parent
            with Otree.Empty -> ()
          end
        ) subs;

      tree1#init; tree2#init;

      [%debug_log "* %d: contracting deferred clusters..." c];

      if options#dots_flag then begin
        tree1#save_dot "Old" [] (Filename.concat dirname (sprintf "%d.old+.dot" c));
        tree2#save_dot "New" [] (Filename.concat dirname (sprintf "%d.new+.dot" c))
      end;

      List.iter
        (function
            Some clu ->

              [%debug_log "cluster: %s"
                (Xlist.to_string
                   (fun (n1, n2) ->
                     sprintf "%a-%a" nups n1 nups n2) "," clu)];

              if (List.length clu) <= 1 then ()
              else
                let deferred, pruned =
                  Misc.contract tree1 tree2
                    [List.map
                       (fun (n1, n2) ->
                         n1#index, n2#index
                       ) clu]
                in
                if deferred = None && (List.length pruned = 1) then
                  List.iter
                    (fun clu ->
                      List.iter
                        (fun (n1, n2) ->
                          ignore (g_nmapping#add_unsettled n1 n2)
                        ) clu
                    ) pruned
                else begin
                  [%fatal_log "deferred clusters contraction"];
                  exit 1
                end

          | None -> ()
        ) deferred_clusters;


      [%debug_log "* done."];

      tree1#init; tree2#init;


      (*
       * if the sizes of two trees exceed the limit, subtrees are pruned,
       * and their edit sequences are incorporated into the global report
       *)

      let sz1, sz2 = tree1#size, tree2#size in

      let r2s tree =
        try
          UID.to_string tree#root#uid
        with
          Otree.Empty -> "-"
      in
      let _ = r2s in
      [%debug_log "* %d: |T1(root:%s)|=%d |T2(root:%s)|=%d" c
        (r2s tree1) sz1 (r2s tree2) sz2];

      match sz1, sz2 with
        0, 0 -> nmapping, None
      | 0, _ | _, 0 -> nmapping, deferred_cluster
      | _ -> begin
          Misc.set_tree_size_limit options sz1 sz2;

          [%debug_log "* %d: tree size limit: %d %d" c
            options#tree_size_limit1 options#tree_size_limit2];

          [%debug_log "* %d: checking tree size limit (1)" c];

          let too_large = Misc.check_tree_size_limit options sz1 sz2 in

          if too_large then
            [%debug_log "* %d: tree size TOO LARGE!" c];

          (* may be in path of some nodes *)
          List.iter
            (fun ((t1, t2), subnmapping) ->

              [%debug_log "* %d: checking subtree pair %s - %s"
                c (r2s t1) (r2s t2)];

              if too_large || (map_cond t1 t2) then begin
                begin
                  try
                    let nd1 = t1#root in
                    if nd1#pos < 0 then
                      [%debug_log "already (to be) pruned: %a" nups nd1]
                    else begin
                      nd1#prune;
                      if nd1#in_path then begin

                        [%debug_log "aborted1: %a -> [%a]" nups nd1 nsps nd1#get_substances];

                        pruned#add_abortedl1 nd1#get_substances
                      end
                      else begin
                        [%debug_log "aborted1: %a" nups nd1];
                        pruned#add_aborted1 nd1
                      end
                    end
                  with Otree.Empty -> ()
                end;

                begin
                  try
                    let nd2 = t2#root in
                    if nd2#pos < 0 then
                      [%debug_log "already (to be) pruned: %a" nups nd2]
                    else begin
                      nd2#prune;
                      if nd2#in_path then begin

                        [%debug_log "aborted2: %a -> [%a]" nups nd2 nsps nd2#get_substances];

                        pruned#add_abortedl2 nd2#get_substances
                      end
                      else begin
                        [%debug_log "aborted2: %a" nups nd2];
                        pruned#add_aborted2 nd2
                      end
                    end
                  with Otree.Empty -> ()
                end;


                begin %debug_block
                  [%debug_log "g_nmapping:\n%s" g_nmapping#to_string];
                  [%debug_log "subnmapping:\n%s" subnmapping#to_string];
                  [%debug_log "g_nmapping#merge_no_override subnmapping"];
                end;

                g_nmapping#merge_no_override subnmapping

              end;

            ) subs_data;
          tree1#init; tree2#init;


          let sz1, sz2 = tree1#size, tree2#size in

          [%debug_log "* %d: |T1(root:%a)|=%d |T2(root:%a)|=%d" c nups tree1#root sz1 nups tree2#root sz2];

          [%debug_log "* %d: tree size limit: %d %d" c
            options#tree_size_limit1 options#tree_size_limit2];

          [%debug_log "* %d: checking tree size limit (2)" c];

          if Misc.check_tree_size_limit options sz1 sz2 then begin

            [%debug_log "* %d: STILL tree size TOO LARGE!" c];

            nmapping, deferred_cluster
          end
          else
            if Misc.check_hard_tree_size_limit options sz1 sz2 then begin

              [%debug_log "* %d: exceeds HARD tree size LIMIT!" c];

              nmapping, deferred_cluster
            end
            else
              if expnd1 = [] && expnd2 = [] then
                nmapping, deferred_cluster
              else
                try
                  let um, dc = loop() in
                  let _ = um#check_for_ref cenv#ref_npairs nmapping in
                  um, dc
                with Otreelib.Distance_too_far ->
                  [%debug_log "* %d: distance too far, aborting" c];
                  nmapping, deferred_cluster
      end
    in (* end of func loop *)

    let result = loop() in

    result
  (* end of func compare_subtree *)


  let dump_sources file src1 src2 =
    let dumper ch =
      Printf.fprintf ch "%s\n%s\n" src1 src2
    in
    Xfile.dump file dumper


  let get_diff_status
      options
      lang
      cenv
      (orig_edits : Edit.seq)
      (edits : Edit.seq)
      (nmapping : node_t Node_mapping.c)
      (tree1 : tree_t)
      (tree2 : tree_t)
      =
    let cache_path = cenv#cache_path in
    (*let diff      = Filename.concat cache_path Stat.diff_file_name in*)
    let diff_json = Filename.concat cache_path Stat.diff_file_name^".json" in
    let gdiff_json = Filename.concat cache_path "g"^Stat.diff_file_name^".json" in
    let dinfo     = Filename.concat cache_path Stat.info_file_name in
    (*let dsummary  = Filename.concat cache_path Stat.summary_file_name in*)
    (*let dstat     = Filename.concat cache_path Stat.stat_file_name in*)
    let dstat_json = Filename.concat cache_path Stat.stat_file_name^".json" in
    let dmap      = Filename.concat cache_path Stat.map_file_name in
    let dgmap     = Filename.concat cache_path "g"^Stat.map_file_name in
    let dmapfact  = Filename.concat cache_path Stat.map_file_name^".nt" in
    let dsrc      = Filename.concat cache_path Stat.sources_file_name in
    let dparser   = Filename.concat cache_path Stat.parser_file_name in
    let dchange   = Filename.concat cache_path Stat.changes_file_name in
    let ddot1     = Filename.concat cache_path Stat.dot_file_name1 in
    let ddot2     = Filename.concat cache_path Stat.dot_file_name2 in
    let delta     = Filename.concat cache_path Delta_base.delta_file_name^".xml" in

    let is_modified = not edits#is_empty in

    if is_modified then begin

      let getlab n = (Obj.obj n#data#_label : Label.t) in
      let is_anon n =
        try
          let _ = Label.get_value (getlab n) in
          false
        with
          Not_found -> not n#data#is_named_orig
      in
      edits#finalize nmapping is_anon;

      begin %debug_block
        [%debug_log "checking SPSM..."];
        let spsm = ref [] in
        let moved_nodes = edits#get_moved_nodes tree1 in

        [%debug_log "|moved_nodes|=%d" (Xset.length moved_nodes)];

        let map_count = ref 0 in
        let mov_count = ref 0 in
        let rel_count = ref 0 in
        let movrel_count = ref 0 in

        nmapping#iter
          (fun n1 n2 ->
            incr map_count;

            let is_mov = Xset.mem moved_nodes n1 in
            let is_rel = edits#mem_rel12 n1 n2 in

            if is_mov then
              incr mov_count;

            if is_rel then
              incr rel_count;

            if is_mov && is_rel then
              incr movrel_count;

            if not is_mov && not is_rel then
              spsm := (n1#gindex, n2#gindex)::!spsm
          );

        [%debug_log "SPSM: size=%d" (List.length !spsm)];
        List.iter
          (fun (g1, g2) ->
            [%debug_log "SPSM: %a-%a" gps g1 gps g2]
          ) (List.fast_sort Stdlib.compare !spsm);
        [%debug_log "map_count: %d" !map_count];
        [%debug_log "mov_count: %d" !mov_count];
        [%debug_log "rel_count: %d" !rel_count];
        [%debug_log "movrel_count: %d" !movrel_count];
        [%debug_log "done."]
      end;

      if options#dump_dot_flag then begin
        edits#dump_dot1 ~final:true ddot1 tree1 tree2 nmapping;
        edits#dump_dot2 ~final:true ddot2 tree2 tree1 nmapping;
      end;

      if not options#dist_flag then begin
        let edits_copy = edits#copy in
        edits_copy#cleanup_ghost tree1 tree2;

        let line_align = edits_copy#get_line_align tree1 tree2 nmapping in
        (*edits_copy#dump_diff_simple ~line_align tree1 tree2 diff;*)
        edits_copy#dump_diff_json ~line_align tree1 tree2 diff_json;
        edits_copy#dump_gdiff_json ~comp:Compression.gzip tree1 tree2 (gdiff_json^".gz");

        edits#dump_diff_info dinfo tree1 tree2;
        (*edits#dump_diff_summary dsummary tree1 tree2 nmapping;*)
      end;

      let diff_stat = edits#get_diff_stat tree1 tree2 nmapping in
(*
  edits#dump_diff_stat dstat tree1 tree2 nmapping;
 *)
      (*Stat.File.dump_diff_stat dstat diff_stat;*)
      Stat.File.dump_diff_stat_json dstat_json diff_stat;

      if not options#dist_flag then begin
        nmapping#dump_with_info ~comp:Compression.gzip (dmap^".gz");
        nmapping#dump_json ~comp:Compression.gzip (dmap^".json.gz");

        let moved_nodes = edits#get_moved_nodes tree1 in
        let is_mov n1 n2 =
          try
            if Xset.mem moved_nodes n1 then
              nmapping#find n1 == n2
            else
              false
          with _ -> false
        in
        nmapping#dump_gid_json ~comp:Compression.gzip is_mov (dgmap^".json.gz");
      end;

      if options#fact_for_mapping_flag then
        Lang.extract_mapping_fact options lang nmapping dmapfact tree1 tree2;

      Stat.dump_parser_name dparser tree1#parser_name;
      dump_sources dsrc tree1#source_path tree2#source_path;

      [%debug_log "\nEdits:\n%s\n" (edits#to_string)];

      if options#verbose_flag then
        edits#show_diff_stat ~short:true tree1 tree2 nmapping;

      let edits_copy = edits#copy in
      edits_copy#ungroup tree1 tree2;
      edits_copy#cleanup_ghost tree1 tree2;

      Edit.dump_changes options lang tree1 tree2 nmapping edits_copy edits dchange;

      if options#dump_delta_flag then begin
        edits#dump_delta tree1 tree2 nmapping edits_copy delta
      end;

      (*if options#dump_ccs_flag then begin (* dump common code structure *)

        if options#check_flag then
          Xprint.warning "result check and ccs dump are mutually exclusive";

(*        let deleted1, deleted2 = edits#remove_unmapped tree1 tree2 in *)
        ignore (edits#remove_unmapped tree1 tree2);
        let mold = Filename.concat cache_path "mapped_old"^Astml.ccs_ext in
        let mnew = Filename.concat cache_path "mapped_new"^Astml.ccs_ext in
        let mold_nodes = Filename.concat cache_path "mapped_old.gids" in
        let mnew_nodes = Filename.concat cache_path "mapped_new.gids" in
        let get_gids tree =
          let l = ref [] in
          tree#scan_all
            (fun nd ->
              let gid =
                let g = nd#data#gid in
                if g > 0 then g else nd#gindex
              in
              l := gid::!l
            );
          List.rev !l
        in
(*
  Xfile.dump mold tree1#dump_xml_ch;
  Xfile.dump mnew tree2#dump_xml_ch;
 *)
        tree1#dump_astml ~comp:options#ast_compression mold;
        tree2#dump_astml ~comp:options#ast_compression mnew;

        Xfile.dump mold_nodes (fun ch -> output_string ch (GI.list_to_string (get_gids tree1)));
        Xfile.dump mnew_nodes (fun ch -> output_string ch (GI.list_to_string (get_gids tree2)));

(*
            let dtrees1 = List.map (fun n -> tree1#make_subtree_from_node n) deleted1 in
            let dtrees2 = List.map (fun n -> tree2#make_subtree_from_node n) deleted2 in
            let gen_fn1, gen_fn2 =
              let c1, c2 = ref 0, ref 0 in
              let gen1() =
                let n = Filename.concat cache_path (sprintf "deleted%d%s" !c1 Astml.ccs_ext) in
                incr c1;
                n
              in
              let gen2() =
                let n = Filename.concat cache_path (sprintf "inserted%d%s" !c2 Astml.ccs_ext) in
                incr c2;
                n
              in
              gen1, gen2
            in
            List.iter (fun t -> Xfile.dump (gen_fn1()) t#dump_xml_ch) dtrees1;
            List.iter (fun t -> Xfile.dump (gen_fn2()) t#dump_xml_ch) dtrees2;
*)
      end
      else *)begin (* dump_ccs_flag = false *)

        if options#check_flag then
          if orig_edits#check tree1 tree2 nmapping then begin
            Xprint.message "result check: PASSED!"
          end
          else begin
            Xprint.message "result check: FAILED!";
            let f = open_out (Filename.concat cache_path "INCORRECT") in
            close_out f
          end

      end;

      diff_stat

    end (* if is_modified *)
    else begin
      let diff_stat = edits#get_diff_stat tree1 tree2 nmapping in

      let is_mov _ _ = false in
      nmapping#dump_gid_json ~comp:Compression.gzip is_mov (dgmap^".json.gz");

      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_SAME*)

      (*else *)begin
        (*Stat.File.dump_diff_stat dstat diff_stat;*)
        Stat.File.dump_diff_stat_json dstat_json diff_stat;
(*
  edits#dump_diff_stat dstat tree1 tree2 nmapping;
 *)
        if options#fact_for_mapping_flag then begin
          if tree1#source_digest <> tree2#source_digest then
            Lang.extract_mapping_fact options lang nmapping dmapfact tree1 tree2
        end;
        (*Xprint.warning "no differences found: %s -- %s" tree1#source_path tree2#source_path*)
(*
  raise No_differences_found
 *)
      end;

      diff_stat

    end

  let find_boundary = Sourcecode.find_nearest_p_ancestor_node (fun x -> x#data#is_boundary)

  let has_mapped_boundary nmapping n1 n2 =
    let b =
      try
        let bn1 = find_boundary n1 in
        let bn2 = find_boundary n2 in
        try
          nmapping#find bn1 == bn2
        with _ -> false
      with _ -> false
    in
    [%debug_log "%a %a: %B" nups n1 nups n2 b];
    b

  (* top level comarison *)
  let compare_tree
      options
      lang
      (cenv : (node_t, tree_t) Comparison.c)
      pre_nmapping
      may_be_unsettled1
      may_be_unsettled2
      ref_nmapping
      tree1 tree2
      =
    let cache_path = cenv#cache_path in

    Cache.prepare_cache_dir options cache_path;

    begin
(*
    try
*)

      begin %debug_block
        [%debug_log "Old:\n%s" tree1#to_string];
        [%debug_log "New:\n%s" tree2#to_string];
        [%debug_log "size of tree: old:%d new:%d" tree1#size tree2#size];
      end;

      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_OUTLINE_COMP
      else*)
        [%debug_log "comparing outlines..."];

      let g_nmapping = new Node_mapping.c cenv in

      g_nmapping#set_blacklist1 may_be_unsettled1;
      g_nmapping#set_blacklist2 may_be_unsettled2;

      let pruned = new Pruned.nodes in

      let counter = new Misc.counter in (* count calls of do_compare *)

      let nmapping, _ =
        compare_subtree options counter cenv cache_path g_nmapping pruned (tree1, tree2)
      in


      begin %debug_block
        [%debug_log "nmapping:\n%s" nmapping#to_string];
        [%debug_log "g_nmapping:\n%s" g_nmapping#to_string];
        [%debug_log "merging mappings..."];
      end;

      ignore (nmapping#merge g_nmapping);

      [%debug_log "mapping merged."];


      if options#check_flag then
        pruned#iter
          (fun (kind, _, _, info1, info2) ->
            let _ = kind in
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            [%debug_log "checking nodes to be pruned: %s %a %a"
              (Pruned.kind_to_string !kind) nups nd1 nups nd2];
            try
              let nd1' = nmapping#find nd1 in
              if nd1' != nd2 then begin
                [%fatal_log
                  "nodes to be pruned (%a-%a) does not contained in the mapping: %a is mapped to %a"
                  nups nd1 nups nd2 nups nd1 nups nd1'];
                exit 1
              end
            with
              Not_found ->
                [%fatal_log "pruned %a: not found" nups nd1];
                exit 1
          );


      (*** postprocessing ***)

      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_POSTPROCESS
      else*)
        Xprint.verbose options#verbose_flag "postprocessing...";

      begin %debug_block
        [%debug_log "aborted1: [%a]" nsps pruned#aborted1];
        [%debug_log "para_iso1: [%a]" nsps pruned#para_iso1];
        [%debug_log "aborted2: [%a]" nsps pruned#aborted2];
        [%debug_log "para_iso2: [%a]" nsps pruned#para_iso2];
        [%debug_log "T1:\n%s" tree1#to_string];
        [%debug_log "T2:\n%s" tree2#to_string];
        [%debug_log "nmapping BEFORE POSTPROCESSING: %s" nmapping#to_string];
        [%debug_log "ref_nmapping BEFORE POSTPROCESSING:\n%s" ref_nmapping#to_string];
        (*[%debug_log "ref_nmapping BEFORE POSTPROCESSING:\n%s" ref_nmapping#to_string_gid];*)
      end;

      if options#preprune_flag then begin
        [%debug_log "MERGING PRE-NODEMAPPING"];
        [%debug_log "|nmapping|=%d |pre_nmapping|=%d" nmapping#size pre_nmapping#size];
        nmapping#merge_checked pre_nmapping;
        [%debug_log "PRE-NODEMAPPING MERGED.\n"]
      end;


      if options#prematch_flag (* || options#prematch_named_flag *) then begin
        [%debug_log "MERGING REF-NODEMAPPING..."];
        let count = ref 0 in
        ref_nmapping#iter
          (fun nd1 nd2 ->
            if
              nd1#data#is_named && not nd1#data#has_value && not (B.is_use nd1#data#binding) &&
              nd2#data#is_named && not nd2#data#has_value && not (B.is_use nd2#data#binding) &&
              (
               (try not (nmapping#mem_dom (Comparison.get_bn nd1)) with _ -> false) ||
               (try not (nmapping#mem_cod (Comparison.get_bn nd2)) with _ -> false)
              )
            then begin
              [%debug_log "merge canceled: %a-%a" nups nd1 nups nd2]
            end
            else if nd1#data#is_boundary || nd2#data#is_boundary then begin
              [%debug_log "merge canceled: %a-%a" nups nd1 nups nd2]
            end
            else begin
              incr count;
              [%debug_log "merging %a-%a" nups nd1 nups nd2];
              ignore (nmapping#add_unsettled nd1 nd2)
            end
          );
        nmapping#set_stable_pairs ref_nmapping#stable_pairs;
        [%debug_log "%d pairs from REF-NODEMAPPING MERGED.\n" !count]
      end;

      [%debug_log "|nmapping|=%d\n%s" nmapping#size nmapping#to_string];

      let _ = cenv#elaborate_nmapping nmapping in

      [%debug_log "|nmapping|=%d" nmapping#size];

      Postprocessing.postprocess options cenv tree1 tree2 nmapping pruned ref_nmapping;

      Xprint.verbose options#verbose_flag "postprocessing completed.";

      let initial_starting_pairs_for_glueing =
        let find_anc_stmt =
          let moveon x = not x#data#is_sequence in
          Misc.get_p_ancestor ~moveon (fun x -> x#data#is_statement)
        in
        let count_occurences stmt n =
          let pred x = x#data#eq n#data in
          let moveon x = not x#data#is_sequence in
          let l = Misc.get_p_descendants ~moveon pred stmt in
          let c = List.length l in
          [%debug_log "%a %a -> %d" nups stmt nups n c];
          c
        in
        let is_mapped n1 n2 =
          try
            nmapping#find n1 == n2
          with
            Not_found -> false
        in
        let has_mapped_stmt n1 n2 =
          let b =
            try
              let s1 = find_anc_stmt n1 in
              let s2 = find_anc_stmt n2 in
              [%debug_log "stmt: %a %a -> %a %a" nups n1 nups n2 nups s1 nups s2];

              List.for_all
                (fun (_, s) ->
                  Array.exists (fun n -> n#data#is_sequence) s#initial_children
                ) [n1, s1; n2, s2] &&
              if
                s1#data#relabel_allowed s2#data
              then begin
                is_mapped s1 s2 ||

                (nmapping#mem_dom s1 &&
                 let s1' = nmapping#find s1 in
                 not n1#data#is_named_orig || count_occurences s1 n1 < 2 && count_occurences s1' n1 = 0) ||

                (nmapping#mem_cod s2 &&
                 let s2' = nmapping#inv_find s2 in
                 not n2#data#is_named_orig || count_occurences s2 n2 < 2 && count_occurences s2' n2 = 0)

              end
              else
                is_mapped s1 s2 && count_occurences s1 n1 < 2 && count_occurences s2 n2 < 2
            with
              _ -> false
          in
          [%debug_log "%a %a -> %B" nups n1 nups n2 b];
          b
        in
        let pre_mapped_nds = Xset.create 0 in
        let _ =
          pre_nmapping#iter_settled_roots
            (fun n1 n2 ->
              try
                if
                  (*tree1#whole_initial_subtree_size n1 > 2 &&*)
                  n1#initial_nchildren > 0 &&
                  n1#data#is_named
                then begin
                  Xset.add pre_mapped_nds n1;
                  Xset.add pre_mapped_nds n2
                end
              with _ -> ()
            )
        in
        let is_matched_subtree x =
          let b =
            match x#data#_digest with
            | None -> false
            | Some d ->
                try
                  match cenv#multiple_subtree_matches#find d with
                  | [], _, _ | _, [], _ -> false
                  | [_], [_], _ -> false
                  | _::_, _::_, _ -> true
                with
                  Not_found -> false
          in
          (*[%debug_log "%a -> %B" nups x b];*)
          b
        in
        let has_matched_subtree ?(moveon=fun _ -> true) n =
          let b =
            let pred x =
              Xset.mem pre_mapped_nds x ||
              is_matched_subtree x
            in
            Misc.has_p_descendant ~moveon pred n
          in
          [%debug_log "%a -> %B" nups n b];
          b
        in
        let contained_in_stmt_having_matched_subtree n =
          let moveon x = not x#data#is_sequence in
          let b =
            try
              let s = find_anc_stmt n in
              is_matched_subtree s ||
              has_matched_subtree ~moveon s
            with
              Not_found -> false
          in
          [%debug_log "%a -> %B" nups n b];
          b
        in
        let has_other_names n1 n2 =
          try
            let name = n1#data#get_orig_name in
            let moveon x = not x#data#is_sequence in
            let is_named_orig n x =
              x#data#is_named_orig && x#data#get_orig_name <> name &&
              try n#initial_parent != x && x#initial_parent != n with _ -> true
            in
            let s1 = find_anc_stmt n1 in
            let s2 = find_anc_stmt n2 in
            let dl1 = Misc.get_p_descendants ~moveon (is_named_orig n1) s1 in
            let dl2 = Misc.get_p_descendants ~moveon (is_named_orig n2) s2 in
            let nl1 = List.map (fun x -> x#data#get_orig_name) dl1 in
            let nl2 = List.map (fun x -> x#data#get_orig_name) dl2 in
            let nl = Xlist.intersection nl1 nl2 in
            [%debug_log "other names found: [%s]" (String.concat "; " nl)];
            let b = nl <> [] in
            [%debug_log "%a %a -> %B" nups n1 nups n2 b];
            b
          with
            _ -> true
        in
        let contained_in_stmt_having_boundary n =
          let b =
            try
              let s = find_anc_stmt n in
              Misc.has_p_descendant (fun x -> x#data#is_boundary) s
            with
              Not_found -> false
          in
          if b then
            [%debug_log "%a -> %B" nups n b];
          b
        in
        [%debug_log "cenv#ref_npairs compatible with nmapping:"];
        let npairs = ref [] in
        cenv#ref_npairs#iter
          (fun nd1 nd2 ->
            try
              (*[%debug_log "checking %a-%a" nups nd1 nups nd2];*)
              if
                nd1#data#eq nd2#data &&
                not (is_mapped nd1 nd2) &&
                (not nd1#data#is_common) &&
                (not nd1#data#is_op) &&
                (not nd1#data#is_statement) &&
                (not nd1#data#is_sequence) &&
                (not nd1#data#has_value || nd1#data#has_non_trivial_value) &&
                (not nd1#data#is_named || nd1#data#is_named_orig) &&
                not (is_matched_subtree nd1) && not (is_matched_subtree nd2) &&
                has_mapped_boundary nmapping nd1 nd2 &&
                has_mapped_stmt nd1 nd2 &&
                not (has_matched_subtree nd1) && not (has_matched_subtree nd2) &&
                not (contained_in_stmt_having_matched_subtree nd1) &&
                not (contained_in_stmt_having_matched_subtree nd2) &&
                has_other_names nd1 nd2 &&
                not (contained_in_stmt_having_boundary nd1) &&
                not (contained_in_stmt_having_boundary nd2)
              then begin
                [%debug_log "!!!!! %a-%a: %a [%a]-[%a]" nups nd1 nups nd2 labps nd1 locps nd1 locps nd2];
                npairs := (nd1, nd2) :: !npairs
              end
            with _ -> ()
          );
        !npairs
      in
      if initial_starting_pairs_for_glueing <> [] then
        nmapping#add_starting_pairs_for_glueing initial_starting_pairs_for_glueing;

if not options#no_glue_flag then begin
      if lang#has_elaborate_edits then begin
        let _, added_pairs = cenv#elaborate_nmapping nmapping in
        nmapping#add_starting_pairs_for_glueing added_pairs;

        let _, added_pairs, (*conflicted_pairs*)_ =
          Postprocessing.glue_deletes_and_inserts options cenv tree1 tree2
            ~no_moves:options#no_moves_flag nmapping (new Node_mapping.c cenv)
        in
        nmapping#add_starting_pairs_for_glueing added_pairs
      end
      else begin
        let _, added_pairs = cenv#elaborate_nmapping nmapping in
        nmapping#add_starting_pairs_for_glueing added_pairs;

        let _ =
          Postprocessing.glue_deletes_and_inserts options cenv tree1 tree2
            ~override:true ~no_moves:options#no_moves_flag nmapping (new Node_mapping.c cenv)
        in
        nmapping#clear_starting_pairs_for_glueing;
      end;

      ignore (cenv#elaborate_nmapping nmapping);
end;

      [%debug_log "nmapping BEFORE EDIT SEQ GENERATION: %s" nmapping#to_string];

      if options#recover_orig_ast_flag then begin
        tree1#recover_true_children ~initial_only:true ();
        tree2#recover_true_children ~initial_only:true ()
      end;


      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_EDITSEQ_GEN
      else*)
        Xprint.verbose options#verbose_flag "generating edit sequence...";

      let edits = new Edit.seq options in

      Postprocessing.generate_edits options lang cenv pruned edits nmapping;

      [%debug_log "generated edits:\n %s" edits#to_string];

      Xprint.verbose options#verbose_flag "fixing up edit sequences...";
      Postprocessing.fixup_edits options lang cenv tree1 tree2 pruned edits nmapping pre_nmapping;

      let dchange = Filename.concat cache_path Stat.changes_file_name in
      let edits_copy = edits#copy in
      edits_copy#ungroup tree1 tree2;
      edits_copy#cleanup_ghost tree1 tree2;
      Edit.dump_changes options lang tree1 tree2 nmapping edits_copy edits dchange;

      if options#dump_delta_flag then begin
        let delta =
          if options#dump_delta_out <> "" then
            options#dump_delta_out
          else
            Filename.concat cache_path Delta_base.delta_file_name^".xml"
        in
        let info_file_path = Filename.concat cache_path "delta_info.json" in
        edits#dump_delta ~info_file_path tree1 tree2 nmapping edits_copy delta
      end;

      let orig_edits, find_mov_gr, find_mov_gr_mems =
        if options#ignore_non_orig_relabel_flag || options#ignore_move_of_unordered_flag then
          edits#copy, Hashtbl.find edits_copy#_mov_gr_tbl, Hashtbl.find edits_copy#_mov_gr_mem_tbl
        else
          edits, (fun _ -> raise Not_found), (fun _ -> raise Not_found)
      in

      if options#ignore_non_orig_relabel_flag then begin
        [%debug_log "filtering relabels..."];
        edits#filter_relabels
          (function
            | Relabel(_, (info1, _), (info2, _)) as rel -> begin
                let _ = rel in
                let nd1 = Info.get_node info1 in
                let nd2 = Info.get_node info2 in
                (*let is_order_insensitive n = n#data#is_order_insensitive in
                let has_order_insensitive n = Array.exists is_order_insensitive n#initial_children in
                not (has_order_insensitive nd1 || has_order_insensitive nd2) &&*)
                match nd1#data#orig_lab_opt, nd2#data#orig_lab_opt with
                | Some o1, Some o2 when o1 = o2 -> begin
                    [%debug_log "filtered: %s" (Edit.to_string rel)];
                    false
                end
                | _ when begin
                    (not nd1#data#is_named_orig) && (not nd1#data#has_value) &&
                    (not nd2#data#is_named_orig) && (not nd2#data#has_value) &&
                    nd1#data#anonymized_label = nd2#data#anonymized_label &&
                    nd1#data#elem_name_for_delta = nd2#data#elem_name_for_delta
                end -> begin
                  [%debug_log "filtered: %s" (Edit.to_string rel)];
                  false
                end
                | _ when nd1#data#orig_to_elem_data_for_eq = nd2#data#orig_to_elem_data_for_eq -> begin
                    [%debug_log "filtered: %s" (Edit.to_string rel)];
                    false
                end

                | _ -> true
            end
            | _ -> true
          )
      end;
      if options#ignore_move_of_unordered_flag(* && not options#recover_orig_ast_flag*) then begin

        [%debug_log "filtering moves..."];

        let false_moves = Xset.create 0 in
        let rec add_false_mid mid =
          if Xset.mem false_moves mid then
            ()
          else begin
            [%debug_log "%a" MID.ps mid];
            Xset.add false_moves mid;
            begin
              try
                let mid' = find_mov_gr mid in
                if not (Xset.mem false_moves mid') then begin
                  [%debug_log "%a<-%a" MID.ps mid MID.ps mid'];
                  add_false_mid mid'
                end
              with _ -> ()
            end;
            begin
              try
                List.iter
                  (fun mov ->
                    let mid' = Edit_base.get_mid mov in
                    if mid' <> mid && not (Xset.mem false_moves mid') then begin
                      [%debug_log "%a->%a" MID.ps mid MID.ps mid'];
                      add_false_mid mid'
                    end
                  ) (find_mov_gr_mems mid)
              with _ -> ()
            end
          end
        in

        let check_mov_weak nd1 nd2 = function
          | Editop.Move(mid, _, (_, _), (_, _)) as mov -> begin
              let b =
                nd1#data#is_order_insensitive && nd2#data#is_order_insensitive &&
                let pnd1 = nd1#initial_parent in
                let pnd2 = nd2#initial_parent in
                (try nmapping#find pnd1 == pnd2 with _ -> false) &&
                match edits#find12 pnd1 pnd2 with
                | [] -> true
                | [Editop.Relabel _] ->
                    pnd1#data#elem_name_for_delta = pnd2#data#elem_name_for_delta
                | _ -> false
              in
              if b then
                add_false_mid !mid;
              let _ = mov in
              [%debug_log "%s -> %B" (Edit.to_string mov) b];
              b
          end
          | _ -> assert false
        in
        let check_mov_for_delta nd1 nd2 = function
          | Editop.Move(mid, _, (_, exc1), (_, exc2)) as mov -> begin
              let b =
                nd1#data#is_order_insensitive && nd2#data#is_order_insensitive &&
                !exc1 = [] && !exc2 = [] &&
                let pnd1 = nd1#initial_parent in
                let pnd2 = nd2#initial_parent in
                (try nmapping#find pnd1 == pnd2 with _ -> false) &&
                (try
                  edits#iter_moves
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
                match edits#find12 pnd1 pnd2 with
                | [] -> true
                | [Editop.Relabel _] -> pnd1#data#elem_name_for_delta = pnd2#data#elem_name_for_delta
                | _ -> false
              in
              if b then
                add_false_mid !mid;
              let _ = mov in
              [%debug_log "%s -> %B" (Edit.to_string mov) b];
              b
          end
          | _ -> assert false
        in
        let check_mov =
          if options#dump_delta_flag then
            check_mov_for_delta
          else
            check_mov_weak
        in

        edits#filter_moves
          (function
            | Editop.Move(_, _, (info1, _), (info2, _)) as mov -> begin
                let _ = mov in
                let nd1 = Info.get_node info1 in
                let nd2 = Info.get_node info2 in
                if
                  check_mov nd1 nd2 mov
                then begin
                  [%debug_log "filtered: %s" (Edit.to_string mov)];
                  begin
                    edits#iter_relabels
                      (function
                        | Relabel(movrel, (i1, _), (i2, _)) -> begin
                            let n1 = Info.get_node i1 in
                            let n2 = Info.get_node i2 in
                            if
                              nd1 == n1 && nd2 == n2 ||
                              tree1#is_initial_ancestor nd1 n1 && tree2#is_initial_ancestor nd2 n2
                            then
                              movrel := false
                        end
                        | _ -> ()
                      )
                  end;
                  false
                end
                else
                  true
            end
            | _ -> true
          );
      edits#filter_moves
        (function
          | Editop.Move(mid, _, (info1, _), (info2, _)) as mov -> begin
              let _ = mov in
              let nd1 = Info.get_node info1 in
              let nd2 = Info.get_node info2 in
              if
                Xset.mem false_moves !mid
              then begin
                [%debug_log "filtered: %s" (Edit.to_string mov)];
                begin
                  edits#iter_relabels
                    (function
                      | Relabel(movrel, (i1, _), (i2, _)) -> begin
                          let n1 = Info.get_node i1 in
                          let n2 = Info.get_node i2 in
                          if
                            nd1 == n1 && nd2 == n2 ||
                            tree1#is_initial_ancestor nd1 n1 && tree2#is_initial_ancestor nd2 n2
                          then
                            movrel := false
                      end
                      | _ -> ()
                    )
                end;
                false
              end
              else
                true
          end
          | _ -> true
        )
      end;
      Xprint.verbose options#verbose_flag "done.";

      begin %debug_block
        let moved_nodes = edits#get_moved_nodes tree1 in
        [%debug_log "|moved_nodes|=%d" (Xset.length moved_nodes)];
      end;

      let diff_status = get_diff_status options lang cenv orig_edits edits nmapping tree1 tree2 in

      if cenv#use_adjacency_cache then
        [%debug_log "size of adjacency cache: %d (cache hit: %d)"
          cenv#size_of_adjacency_cache cenv#adjacency_cache_hit_count];

      if cenv#use_similarity_cache then
        [%debug_log "size of similarity cache: %d (cache hit: %d)"
          cenv#size_of_similarity_cache cenv#similarity_cache_hit_count];

      if cenv#use_mapping_comparison_cache then
        [%debug_log "size of mapping comparison cache: %d (cache hit: %d)"
          cenv#size_of_mapping_comparison_cache cenv#mapping_comparison_cache_hit_count];

      if nmapping#use_crossing_or_incompatible_matches_count_cache then
        [%debug_log "size of crossing or incompatible matches count cache: %d (cache hit: %d)"
          nmapping#size_of_crossing_or_incompatible_matches_count_cache
          nmapping#crossing_or_incompatible_matches_count_cache_hit_count];

      diff_status

(*
    with
      Sys_error msg -> Xprint.error "%s" msg; exit 1
*)
    end
(*
    tree1#show_whole_initial_subtree_size_hist;
    tree1#show_whole_initial_subtree_scan_hist;
    tree2#show_whole_initial_subtree_size_hist;
    tree2#show_whole_initial_subtree_scan_hist;
*)

  (* end of compare_tree *)


  class tree_comparator lang options ?(cache_path="") file1 file2 = object
    inherit Lang.tree_comparator

    val mutable extra_source_files1 = []
    val mutable extra_source_files2 = []

    method extra_source_files1 = extra_source_files1
    method extra_source_files2 = extra_source_files2


    method compare =

      let cache_path =
        if cache_path = "" then
          options#get_cache_path_for_file2 file1 file2
        else
          cache_path
      in

      let multiple_subtree_matches = new Comparison.multiple_subtree_matches options in
      let multiple_node_matches =
        new Comparison.multiple_node_matches (fun l -> Label.to_string (Obj.obj l : Label.t))
      in

(*
    try
*)

      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_PARSE;*)

      let tree1 =
        let tree_builder1 = lang#make_tree_builder options in
        let t = tree_builder1#build_tree file1 in
        extra_source_files1 <- tree_builder1#extra_source_files;
        t
      in
      let tree2 =
        let tree_builder2 = lang#make_tree_builder options in
        let t = tree_builder2#build_tree file2 in
        extra_source_files2 <- tree_builder2#extra_source_files;
        t
      in

      let has_elaborate_edits = lang#has_elaborate_edits in

      begin
        let gain = 1. in
        let a = 32 in
        let t = 50000 in
        let sz = min tree1#initial_size tree2#initial_size in
        let x = (float a) /. (1. +. (exp (gain *. float(t - sz)))) in
        let mt = truncate x in
        options#set_subtree_match_threshold mt;
        Xprint.verbose options#verbose_flag "subtree_match_threshold set to %d" mt;
        if mt = a then begin
          options#set_simple_glue_flag;
          Xprint.verbose options#verbose_flag "simple_glue_flag set";
        end
      end;

      let cenv = new Comparison.c options ~has_elaborate_edits tree1 tree2 in
      cenv#set_cache_path cache_path;
      cenv#set_multiple_subtree_matches multiple_subtree_matches;
      cenv#set_multiple_node_matches multiple_node_matches;

      let cache_path1 = options#get_cache_path_for_file1 file1 in
      let cache_path2 = options#get_cache_path_for_file1 file2 in
      Cache.prepare_cache_dir options cache_path1;
      Cache.prepare_cache_dir options cache_path2;

      begin
        try
          let k, v = options#fact_versions.(0) in
          tree1#set_vkind k;
          tree1#set_version v
        with
          Invalid_argument _ -> ()
      end;
      begin
        try
          let k, v = options#fact_versions.(1) in
          tree2#set_vkind k;
          tree2#set_version v
        with
          Invalid_argument _ -> ()
      end;

      Stat.dump_source options file1 tree1;
      Stat.dump_source options file2 tree2;

      Stat.dump_parser options file1 tree1;
      Stat.dump_parser options file2 tree2;

      Stat.dump_file_info options file1 tree1;
      Stat.dump_file_info options file2 tree2;

      if options#fact_flag then begin
        let extract_fact1 = lang#extract_fact options cache_path1 in
        let extract_fact2 = lang#extract_fact options cache_path2 in

        begin
          try
            let r = options#fact_proj_roots.(0) in
            tree1#set_proj_root r
        with
          Invalid_argument _ -> ()
        end;
        begin
          try
            let r = options#fact_proj_roots.(1) in
            tree2#set_proj_root r
        with
          Invalid_argument _ -> ()
        end;

        extract_fact1 tree1;
        extract_fact2 tree2;

      end;

(*
      Xprint.verbose options#verbose_flag "line terminator of T1: %s"
        tree1#line_terminator_name;
      Xprint.verbose options#verbose_flag "line terminator of T2: %s"
        tree2#line_terminator_name;
*)

      Xprint.verbose options#verbose_flag "|T1|=%d |T2|=%d" tree1#initial_size tree2#initial_size;


      let digest1 = tree1#digest in
      let digest2 = tree2#digest in

      Xprint.verbose options#verbose_flag "digest of T1: %s" (Xhash.to_hex digest1);
      Xprint.verbose options#verbose_flag "digest of T2: %s" (Xhash.to_hex digest2);

      if digest1 = digest2 then begin
        [%debug_log "genarating trivial mapping..."];
        if options#recover_orig_ast_flag then begin
          tree1#recover_true_children ~initial_only:true ();
          tree2#recover_true_children ~initial_only:true ()
        end;
        let nmapping = new Node_mapping.c cenv in
        tree1#fast_scan_whole_initial
          (fun nd1 ->
            let nd2 = tree2#search_node_by_gindex nd1#gindex in
            (*[%debug_log "%a: %s - %s" GI.ps nd1#gindex nd1#data#to_string nd2#data#to_string];*)
            ignore (nmapping#add_settled nd1 nd2)
          );
        let edits = new Edit.seq options in
        get_diff_status options lang cenv edits edits nmapping tree1 tree2
      end
      else begin

        (* pre-pruning and pre-matching *)

        let pre_nmapping = new Node_mapping.c cenv in
        let ref_nmapping = new Node_mapping.c cenv in

        let may_be_unsettled1 = Xset.create 0 in
        let may_be_unsettled2 = Xset.create 0 in

        let add tbl x nd =
          try
            let nds = Hashtbl.find tbl x in
            if not (List.memq nd nds) then
              Hashtbl.replace tbl x (nd::nds)
          with
            Not_found -> Hashtbl.add tbl x [nd]
        in

        let ltbl1 = Hashtbl.create 0 in
        let ltbl2 = Hashtbl.create 0 in

        let b_ltbl1 = Hashtbl.create 0 in (* e.g. methods *)
        let b_ltbl2 = Hashtbl.create 0 in

        let getlab n =
          (*match n#data#orig_lab_opt with
            | Some o -> o
            | None -> *)n#data#_label
        in

        if options#preprune_flag || options#prematch_flag then begin

          tree1#fast_scan_whole_initial
            (fun nd ->
              add ltbl1 (getlab nd) nd;
              if
                nd#data#is_boundary && nd#data#is_named_orig &&
                not nd#data#is_sequence && not nd#data#is_ntuple
              then
                add b_ltbl1 (Comparison.get_orig_name nd) nd
            );
          tree2#fast_scan_whole_initial
            (fun nd ->
              add ltbl2 (getlab nd) nd;
              if
                nd#data#is_boundary && nd#data#is_named_orig &&
                not nd#data#is_sequence && not nd#data#is_ntuple
              then
                add b_ltbl2 (Comparison.get_orig_name nd) nd
            );

          begin %debug_block
            List.iter
              (fun (tag, tbl) ->
                Hashtbl.iter
                  (fun l nds ->
                    [%debug_log "%s: [%s]%s --> %d times (%a)"
                      tag
                      (Label.to_string (Obj.obj l))
                      (if (List.hd nds)#initial_nchildren = 0 then "[LEAF]" else "")
                      (List.length nds)
                      nsps nds]
                  ) tbl;
                [%debug_log "%d entries in %s" (Hashtbl.length tbl) tag]
              ) [("ltbl1", ltbl1); ("ltbl2", ltbl2)];
            List.iter
              (fun (tag, tbl) ->
                Hashtbl.iter
                  (fun l nds ->
                    [%debug_log "%s: [%s]%s --> %d times (%a)"
                      tag
                      l
                      (if (List.hd nds)#initial_nchildren = 0 then "[LEAF]" else "")
                      (List.length nds)
                      nsps nds]
                  ) tbl;
                [%debug_log "%d entries in %s" (Hashtbl.length tbl) tag]
              ) [("b_ltbl1", b_ltbl1); ("b_ltbl2", b_ltbl2)];
          end;

          let visited1 = Xset.create 0 in
          let visited2 = Xset.create 0 in

          let rec check_ancestors nd1 nd2 =
            [%debug_log "%a-%a" nps nd1 nps nd2];
            try
              let pnd1 = nd1#initial_parent in
              let pnd2 = nd2#initial_parent in

              if
                pnd1#data#is_boundary || pnd2#data#is_boundary ||
                Xset.mem visited1 pnd1 || Xset.mem visited2 pnd2
              then
                raise Exit;

              if
                pnd1#data#anonymized_label = pnd2#data#anonymized_label &&
                nd1#data#eq nd2#data && pnd1#data#is_sequence
              then begin
                cenv#add_permutation_hub_cand pnd1 pnd2 nd1#data#label
              end
              else begin
                Xset.add visited1 pnd1;
                Xset.add visited2 pnd2;
              end;

              if pnd1#data#anonymized_label = pnd2#data#anonymized_label then
                check_ancestors pnd1 pnd2

            with _ -> ()
          in

          Hashtbl.iter
            (fun _lab nds1 ->
              let lab = Obj.obj _lab in
              try
                let nds2 = Hashtbl.find ltbl2 _lab in
                if Label.is_named lab || Label.has_value lab then begin
                  match nds1, nds2 with
                  | [nd1], [nd2] -> check_ancestors nd1 nd2
                  | _ -> ()
                end
              with
                Not_found -> ()
            ) ltbl1;

          cenv#finalize_permutation_hub_tbl();

        end;

        let sort_nds =
          List.fast_sort (fun nd1 nd2 -> Stdlib.compare nd2#gindex nd1#gindex)
        in

        let pruned_list1 = ref [] in
        let pruned_list2 = ref [] in

        let pruned1 = Xset.create 0 in
        let pruned2 = Xset.create 0 in

        let prune1 nd =
          [%debug_log "%a to be pruned" nups nd];
          Xset.add pruned1 nd
        in
        let prune2 nd =
          [%debug_log "%a to be pruned" nups nd];
          Xset.add pruned2 nd
        in

        let part pruned_nodes =
          List.partition
            (fun n ->
              let b =
                try
                  let ba = find_boundary n in
                  not (Xset.mem pruned_nodes ba)
                with _ -> true
              in
              if not b then
                [%debug_log "filtered: %a %s" nups n n#data#to_string];
              b
            )
        in

        let locked1 = Xset.create 0 in
        let locked2 = Xset.create 0 in

        let lock1 nd =
          [%debug_log "%a to be locked" nups nd];
          Xset.add locked1 nd
        in
        let lock2 nd =
          [%debug_log "%a to be locked" nups nd];
          Xset.add locked2 nd
        in

        (* pre-pruning *)

        if options#preprune_flag then begin

          [%debug_log "prepruning (and locking collapsed nodes)..."];

          let tbl1 = Hashtbl.create 0 in
          let tbl2 = Hashtbl.create 0 in

          tree1#fast_scan_whole_initial
            (fun nd ->
              match nd#data#digest with
              | None when begin
                  nd#data#has_non_trivial_value && nd#initial_nchildren = 0 &&
                  cenv#under_permutation_hub1 nd
              end -> begin
                let v = nd#data#get_value in
                [%debug_log "value(tree1): %a(%a) -> %s" nups nd ngps nd v];
                add tbl1 v nd
              end
              | None -> ()
              | Some d ->
                  [%debug_log "digest(tree1): %a(%a) -> %s" nups nd ngps nd nd#data#digest_string];

                  add tbl1 d nd
            );
          tree2#fast_scan_whole_initial
            (fun nd ->
              match nd#data#digest with
              | None when begin
                  nd#data#has_non_trivial_value && nd#initial_nchildren = 0 &&
                  cenv#under_permutation_hub2 nd
              end -> begin
                let v = nd#data#get_value in
                [%debug_log "value(tree1): %a(%a) -> %s" nups nd ngps nd v];
                add tbl2 v nd
              end
              | None -> ()
              | Some d ->
                  [%debug_log "digest(tree2): %a(%a) -> %s" nups nd ngps nd nd#data#digest_string];

                  add tbl2 d nd
            );

          begin %debug_block
            [%debug_log "size of digest table1: %d" (Hashtbl.length tbl1)];
            [%debug_log "size of digest table2: %d" (Hashtbl.length tbl2)]
          end;

          let add_may_be_unsettled may_be_unsettled nd =
            try
              let pnd = nd#initial_parent in
              Xset.add may_be_unsettled pnd
            with
              Otree.Parent_not_found _ -> ()
          in (* end of func add_may_be_unsettled *)

          let pre_map_add nd1 nd2 =
            let ns1 = ref [] in
            let ns2 = ref [] in
            tree1#fast_scan_whole_initial_subtree nd1 (fun n -> ns1 := n::!ns1);
            tree2#fast_scan_whole_initial_subtree nd2 (fun n -> ns2 := n::!ns2);

            begin %debug_block
              List.iter2
                (fun n1 n2 ->
                  [%debug_log "adding %a - %a" nups n1 nups n2]
                ) !ns1 !ns2
            end;

            List.iter2
              (fun n1 n2 ->
                ignore (pre_nmapping#add_settled ~stable:false n1 n2)
              ) !ns1 !ns2;

            pre_nmapping#add_settled_roots nd1 nd2;

            List.iter2
              (fun n1 n2 -> pre_nmapping#add_stable_pair n1 n2)
              !ns1 !ns2;

            (* regard the parents as possible unsettled mapping sources *)
            add_may_be_unsettled may_be_unsettled1 nd1;
            add_may_be_unsettled may_be_unsettled2 nd2;
          in (* end of func pre_map_add *)

          Hashtbl.iter
            (fun d nds ->
              Hashtbl.replace tbl2 d (sort_nds nds)
            ) tbl2;

          let _multi_match_list = ref [] in

          let lock_cond nd =
            let b =
              let pred n =
                (not n#data#has_value || n#data#has_non_trivial_value)(* &&
                (not n#data#is_named_orig || not n#data#is_common)*)
              in
              nd#data#is_statement && nd#initial_nchildren > 0 &&
              Array.for_all
                (fun x -> pred x(* || Misc.has_p_descendant pred x*))
                nd#initial_children
            in
            [%debug_log "%a --> %B" nups nd b];
            b
          in

          let parent_matches = Xset.create 0 in

          let add_subtree_match ?(add_parent_match_only=false) ?(add_parent_match=true) ?(mes="") nd1 nd2 =

            let _ = mes in

            let sz = tree1#whole_initial_subtree_size nd1 in

            [%debug_log "%sdigest (or value) match: %a[%a] <--> %a[%a] <%a> (size=%d)" mes
              nups nd1 locps nd1 nups nd2 locps nd2 labps nd1 sz];

            cenv#add_subtree_match (nd1, nd2, sz);

            if not add_parent_match_only then begin
              pre_map_add nd1 nd2;
              if
                nd1#data#is_boundary ||
                nd1#data#has_non_trivial_value && nd1#initial_nchildren = 0
              then begin
                prune1 nd1;
                prune2 nd2;
              end
              else begin
                lock1 nd1;
                lock2 nd2;
              end
            end;

            if add_parent_match && lock_cond nd1 then begin
              try
                let pnd1 = nd1#initial_parent in
                let pnd2 = nd2#initial_parent in
                [%debug_log "adding parent match: (%a,%a)" nups pnd1 nups pnd2];
                Xset.add parent_matches (pnd1, pnd2)
              with _ -> ()
            end
          in

          let matched_digests = Xset.create 0 in

          Hashtbl.iter
            (fun d nds ->
              let nds1 = sort_nds nds in
              Hashtbl.replace tbl1 d nds1;
              try
                let nds2 = Hashtbl.find tbl2 d in

                let nds1 = List.filter (fun n -> tree1#root != n) nds1 in
                let nds2 = List.filter (fun n -> tree2#root != n) nds2 in

                match nds1, nds2 with
                | [], _ | _, [] -> ()
                | [nd1], [nd2] ->
                    (*Xset.add matched_digests d;*)
                    if cenv#is_bad_pair nd1 nd2 then begin
                      [%debug_log "@"];
                    end
                    else if
                      cenv#is_scope_breaking_mapping ~subtree:true pre_nmapping nd1 nd2
                    then begin
                      [%debug_log "@"];
                      cenv#scan_subtree_pair nd1 nd2 cenv#add_bad_pair
                    end
                    else begin
                      [%debug_log "@"];
                      add_subtree_match ~add_parent_match:false nd1 nd2
                    end

                | _ ->
                    Xset.add matched_digests d;
                    _multi_match_list := (d, nds1, nds2) :: !_multi_match_list
              with
                _ -> ()
            ) tbl1;

          let multi_match_list =
            List.fast_sort
              (fun (_, nds10, nds20) (_, nds11, nds21) ->
                match nds10, nds20, nds11, nds21 with
                | nd10::_, nd20::_, nd11::_, nd21::_ ->
                    compare (nd10#gindex, nd20#gindex) (nd11#gindex, nd21#gindex)
                | _ -> 0
              ) !_multi_match_list
          in

          let getmems tree nd =
            let m = ref [] in
            tree#fast_scan_whole_initial_subtree nd (fun n -> m := n::!m);
            !m
          in

          let lock_cand_tbl = Nodetbl.create 0 in

          let count = ref 0 in

          let is_matched_subtree x =
            let b =
              match x#data#_digest with
              | None -> false
              | Some d -> Xset.mem matched_digests d
            in
            [%debug_log "%a -> %B" nups x b];
            b
          in
          let get_matched_sibling_ratio nd =
            let count = ref 0 in
            let matched = ref 0 in
            try
              Array.iter
                (fun c ->
                  incr count;
                  if c != nd && is_matched_subtree c then
                    incr matched
                ) nd#initial_parent#initial_children;
              if !count > 0 then begin
                let m = !matched + 1 in
                let c = !count in
                let r = (float m) /. (float c) in
                [%debug_log "%d/%d=%.3f" m c r];
                r
              end
              else
                0.0
            with _ -> 0.0
          in
          let find_anc_stmt =
            Sourcecode.find_nearest_p_ancestor_node (fun x -> x#data#is_statement)
          in
          let has_no_anc_stmt x =
            try
              let _ = find_anc_stmt x in
              false
            with
              Not_found -> true
          in

          List.iter
            (fun (d, nds1, nds2) ->

              [%debug_log "[%a] <--> [%a]" nsps nds1 nsps nds2];

              match nds1, nds2 with
              | [], _ | _, [] -> ()
              | [nd1], [nd2] -> begin
                  [%debug_log "!!!!!"];
                  add_subtree_match ~mes:"2ND " nd1 nd2
              end
              | _ -> begin

                  let nds1_, filtered_nds1 = part pruned1 nds1 in
                  let nds2_, filtered_nds2 = part pruned2 nds2 in
                  let n_filtered_nds1 = List.length filtered_nds1 in
                  let n_filtered_nds2 = List.length filtered_nds2 in
                  assert (n_filtered_nds1 = n_filtered_nds2);
                  (*count := !count + n_filtered_nds1;*)

                  let nds1_, nds2_ =
                    match nds1_, nds2_ with
                    | [nd1], [nd2] -> begin
                        [%debug_log "%a-%a %a [%a]-[%a]" nps nd1 nps nd2 labps nd1 locps nd1 locps nd2];

                        let matched_sibling_ratio1 = get_matched_sibling_ratio nd1 in
                        let matched_sibling_ratio2 = get_matched_sibling_ratio nd2 in

                        [%debug_log "matched_sibling_ratio=%.3f (%a)" matched_sibling_ratio1 nps nd1];
                        [%debug_log "matched_sibling_ratio=%.3f (%a)" matched_sibling_ratio2 nps nd2];

                        let rec in_matched_subtree x =
                          try
                            let p = x#initial_parent in
                            let b =
                              match p#data#_digest with
                              | None -> false
                              | Some d ->
                                  Xset.mem matched_digests d ||
                                  try
                                    match cenv#multiple_subtree_matches#find d with
                                    | [], _, _ | _, [], _ -> false
                                    | _ -> true
                                  with
                                    Not_found -> false
                            in
                            if b then begin
                              [%debug_log "%a -> %B" nups x b];
                              b
                            end
                            else
                              in_matched_subtree p
                          with
                            _ -> false
                        in

                        if
                          nd1#data#is_statement &&
                          has_no_anc_stmt nd1 && has_no_anc_stmt nd2 &&
                          matched_sibling_ratio1 > matched_sibling_ratio_thresh &&
                          matched_sibling_ratio2 > matched_sibling_ratio_thresh
                        then begin
                          [%debug_log "!!!!!"];
                          add_subtree_match ~add_parent_match_only:true ~mes:"3RD " nd1 nd2;
                          count := !count + n_filtered_nds1;
                          nds1_, nds2_
                        end
                        else if
                          nd1#data#is_op &&
                          try
                            not (in_matched_subtree nd1)
                          with _ -> false
                        then begin
                          [%debug_log "!!!!! %a [%a]-[%a]" labps nd1 locps nd1 locps nd2];
                          count := !count + n_filtered_nds1;
                          nds1_, nds2_
                        end
                        else
                          nds1, nds2

                    end
                    | [], _ | _, [] -> begin
                        count := !count + n_filtered_nds1;
                        nds1_, nds2_
                    end
                    | [nd1], _ -> begin
                        (*[%debug_log "!!!!! nd1: %a:%s" nps nd1 nd1#data#to_string];*)
                        try
                          let pnd1 = nd1#initial_parent in
                          let nd2_cands =
                            List.fold_left
                              (fun l nd2 ->
                                let pnd2 = nd2#initial_parent in
                                if Xset.mem parent_matches (pnd1, pnd2) then begin
                                  [%debug_log "nd2=%a" nups nd2];
                                  (pnd2, nd2) :: l
                                end
                                else
                                  l
                              ) [] nds2
                          in
                          match nd2_cands with
                          | [pnd2, nd2] -> begin
                              [%debug_log "!!!!!"];
                              let mes = sprintf "PARENT(%a,%a) " nups pnd1 nups pnd2 in
                              add_subtree_match ~add_parent_match:false ~mes nd1 nd2;
                              count := !count + n_filtered_nds1;
                              [], []
                          end
                          | _ -> nds1, nds2
                        with
                          _ -> nds1, nds2
                    end
                    | _, [nd2] -> begin
                        (*[%debug_log "!!!!! nd2: %a:%s" nps nd2 nd2#data#to_string];*)
                        try
                          let pnd2 = nd2#initial_parent in
                          let nd1_cands =
                            List.fold_left
                              (fun l nd1 ->
                                let pnd1 = nd1#initial_parent in
                                if Xset.mem parent_matches (pnd1, pnd2) then begin
                                  [%debug_log "nd1=%a" nups nd1];
                                  (pnd1, nd1) :: l
                                end
                                else
                                  l
                              ) [] nds1
                          in
                          match nd1_cands with
                          | [pnd1, nd1] -> begin
                              [%debug_log "!!!!!"];
                              let mes = sprintf "PARENT(%a,%a) " nups pnd1 nups pnd2 in
                              add_subtree_match ~add_parent_match:false ~mes nd1 nd2;
                              count := !count + n_filtered_nds1;
                              [], []
                          end
                          | _ -> nds1, nds2
                        with
                          _ -> nds1, nds2
                    end
                    | _ -> nds1, nds2
                  in
                  let nds1, nds2 = nds1_, nds2_ in

                  match nds1, nds2 with
                  | [], _ | _, [] -> ()
                  (*| [_], [_] -> ()*)
                  | _ -> begin
                      match nds1, nds2 with
                      | [], _ | _, [] -> ()
                      | _ -> begin

                          let ndmems1 = List.map (fun nd -> nd, getmems tree1 nd) nds1 in
                          let ndmems2 = List.map (fun nd -> nd, getmems tree2 nd) nds2 in

                          begin %debug_block
                            [%debug_log "multiple digest match: %a" labps (List.hd nds1)];
                            [%debug_log "[%s] <--> [%s]"
                              (Xlist.to_string (fun (n, _) -> UID.to_string n#uid) ";" ndmems1)
                              (Xlist.to_string (fun (n, _) -> UID.to_string n#uid) ";" ndmems2)];
                            let to_s nds =
                              (Xlist.to_string GI.to_string ";"
                                 (List.fast_sort Stdlib.compare
                                    (List.map (fun n -> n#gindex) nds)))
                            in
                            [%debug_log "multiple digest match (gindex): [%s] <--> [%s]" (to_s nds1) (to_s nds2)]
                          end;

                          begin
                            let add_lock_cand nd cand =
                              try
                                let pnd = nd#initial_parent in
                                try
                                  let l = Nodetbl.find lock_cand_tbl pnd in
                                  Nodetbl.replace lock_cand_tbl pnd (cand::l)
                                with Not_found ->
                                  Nodetbl.add lock_cand_tbl pnd [cand]
                              with _ -> ()
                            in
                            (*let is_pre_mapped n1 n2 =
                              let b =
                                try
                                  pre_nmapping#find n1 == n2
                                with
                                  Not_found -> false
                              in
                              [%debug_log "%a %a -> %B" nups n1 nups n2 b];
                              b
                            in*)
                            (*let is_cross_boundary n1 n2 =
                              let b =
                                try
                                  let bn1 = find_boundary n1 in
                                  let bn2 = find_boundary n2 in
                                  let bn_mapped =
                                    try
                                      pre_nmapping#find bn1 == bn2
                                    with Not_found -> false
                                  in
                                  not bn_mapped &&
                                  pre_nmapping#mem_dom bn1 && pre_nmapping#mem_cod bn2 &&
                                  Misc.is_cross_boundary pre_nmapping n1 n2
                                with
                                  _ -> false
                              in
                              [%debug_log "%a %a -> %B" nups n1 nups n2 b];
                              b
                            in*)
                            match nds1, nds2 with
                            (*| [nd1], [nd2] when begin
                                [%debug_log "!!!!! operator to be locked? %a-%a" nups nd1 nups nd2];
                                nd1#data#is_op && not (is_pre_mapped nd1 nd2) &&
                                not (is_cross_boundary nd1 nd2) &&
                                Array.for_all
                                  (fun c ->
                                    not c#data#is_common &&
                                    (not c#data#has_value || c#data#has_non_trivial_value)
                                  ) nd1#initial_children &&
                                try
                                  let sn1 = find_anc_stmt nd1 in
                                  let sn2 = find_anc_stmt nd2 in
                                  let pred n =
                                    n#data#is_sequence ||
                                    Misc.has_p_descendant (fun x -> x#data#is_sequence) n
                                  in
                                  Array.exists pred sn1#initial_children &&
                                  Array.exists pred sn2#initial_children
                                with
                                  _ -> true
                            end -> begin
                              [%debug_log "!!!!! locking operators: %a [%a]-[%a]" labps nd1 locps nd1 locps nd2];
                              lock1 nd1;
                              lock2 nd2;
                            end*)
                            | [_], [_] -> ()
                            | [nd1], _::_ when lock_cond nd1 -> add_lock_cand nd1 (nd1#initial_pos, nds1, nds2)
                            | _::_, [nd2] when lock_cond nd2 -> add_lock_cand nd2 (nd2#initial_pos, nds1, nds2)
                            | _ -> ()
                          end;

                          multiple_subtree_matches#add d (ndmems1, ndmems2)
                      end
                  end
                end
            ) multi_match_list;

          [%debug_log "%d node pairs deleted from multi_match_list" !count];

          begin
            let context_thresh = 5 in

            [%debug_log "context_thresh=%d" context_thresh];

            let lock_cand (_, nds1, nds2) =
              begin %debug_block
                let n_to_str n = (UID.to_string n#uid)^":"^n#data#to_string in
                [%debug_log "[%s]" (String.concat "; " (List.map n_to_str nds1))];
                [%debug_log "-> [%s]" (String.concat "; " (List.map n_to_str nds2))];
              end;
              List.iter lock1 nds1;
              List.iter lock2 nds2;
            in
            Nodetbl.iter
              (fun pnd _cand_list ->
                let _ = pnd in

                let cand_list =
                  List.fast_sort (fun (pos0, _, _) (pos1, _, _) -> compare pos0 pos1) _cand_list
                in
                begin %debug_block
                  [%debug_log "pnd=%a" nups pnd];
                  List.iter
                    (fun (pos, nds1, nds2) ->
                      [%debug_log "%d [%a] [%a]" pos nsps nds1 nsps nds2]
                    ) cand_list
                end;

                let a = Array.of_list cand_list in
                let alen = Array.length a in

                if alen >= context_thresh then begin

                  [%debug_log "* pnd=%a" nups pnd];

                  let _, ns10, ns20 = a.(0) in
                  let len1 = List.length ns10 in
                  let len2 = List.length ns20 in
                  [%debug_log "len1=%d len2=%d" len1 len2];
                  let sel x1 x2 = if len1 = 1 then x2 else x1 in
                  let mat = Array.make_matrix (sel len1 len2) alen GI.dummy in
                  let ok =
                    try
                      Array.iteri
                        (fun i (_, ns1, ns2) ->
                          if List.length ns1 = len1 && List.length ns2 = len2 then begin
                            List.iteri
                              (fun j n ->
                                mat.(j).(i) <- n#gindex
                              ) (sort_nds (sel ns1 ns2))
                          end
                          else
                            raise Exit
                        ) a;
                      Array.iteri
                        (fun j matj ->
                          let _ = j in
                          [%debug_log "j=%d" j];
                          Array.iteri
                            (fun i g ->
                              [%debug_log "%d: %a" i gps g];
                              if try matj.(i-1) > g with _ -> false then
                                raise Exit
                            ) matj
                        ) mat;
                      true
                    with
                      Exit -> false
                  in
                  [%debug_log "ok=%B" ok];

                  if ok then begin
                    Array.iteri
                      (fun i (pos, _nds1, _nds2) ->
                        let nds1, nds2 =
                          match _nds1, _nds2 with
                          | [nd1], _ -> [nd1], []
                          | _, [nd2] -> [], [nd2]
                          | _ -> assert false
                        in
                        a.(i) <- (pos, nds1, nds2)
                      ) a;
                    let head_pos = ref (-1) in
                    let head_i = ref 0 in
                    let delta = ref 1 in
                    try
                      Array.iteri
                        (fun i (pos, _, _) ->
                          [%debug_log "[i=%d pos=%d] head_pos=%d head_i=%d delta=%d"
                            i pos !head_pos !head_i !delta];

                          if !head_pos < 0 then begin
                            [%debug_log "  head_pos->%d head_i->%d" pos i];
                            head_pos := pos;
                            head_i := i
                          end
                          else if pos = !head_pos + !delta then begin
                            incr delta;
                            [%debug_log "  delta->%d" !delta];
                          end
                          else begin
                            if false then begin
                              if !delta >= context_thresh then begin
                                let _i = i - 1 in
                                [%debug_log "  !!!!! locking from %d-th to %d-th" !head_i _i];
                                for c = !head_i to _i do
                                  lock_cand a.(c)
                                done;
                              end;
                              [%debug_log "  head_pos->%d head_i->%d delta->1" pos i];
                              head_pos := pos;
                              head_i := i;
                              delta := 1
                            end
                            else
                              raise Exit
                          end
                        ) a;
                      let _i = Array.length a - 1 in
                      if !head_i + !delta = _i + 1 then begin
                        if !delta >= context_thresh then begin
                          [%debug_log "!!!!! locking from %d-th to %d-th" !head_i _i];
                          for c = !head_i to _i do
                            lock_cand a.(c)
                          done;
                        end;
                      end
                    with
                      Exit -> ()
                  end
                end
              ) lock_cand_tbl
          end;

          pruned_list1 := Xset.to_list pruned1;
          pruned_list2 := Xset.to_list pruned2;

          [%debug_log "@"];

          let _ = (tree1#expand_all : node_t -> bool) in
          let _ = (tree2#expand_all : node_t -> bool) in

          tree1#prune_nodes !pruned_list1;
          tree2#prune_nodes !pruned_list2;

          List.iter
            (fun (tree, set) ->
              let _ = tree in
              Xset.iter
                (fun n ->
                  (*begin
                    match n#data#_digest with
                    | Some d when not n#is_collapsed -> n#collapse n#data#weight d
                    | _ -> ()
                  end;*)
                  n#lock_collapse;

                  [%debug_log "collapsed node locked: %s (subtree size: %d)"
                    n#to_string (tree#whole_initial_subtree_size n)]

                ) set
            ) [(tree1, locked1); (tree2, locked2)];

          begin %debug_block
            [%debug_log "%d node (subtree) pairs pruned" (List.length !pruned_list1)];
            [%debug_log "%d collapsed node pairs locked" (Xset.length locked1)]
          end;

          if not options#no_collapse_flag then begin
            [%debug_log "collapsing nodes..."];
            tree1#collapse;
            tree2#collapse
          end;

          tree1#collapse_nodes (Xset.mem locked1);
          tree2#collapse_nodes (Xset.mem locked2);

          [%debug_log "prepruning (and locking collapsed) completed."]
        end;
        (* end of pre-pruning *)


        (* pre-matching *)

        if options#prematch_flag (* || options#prematch_named_flag *) then begin
          [%debug_log "prematching..."];


          let check_pruned prnd tree nd =
            let b =
              try
                List.iter
                  (fun n ->
                    if tree#initial_subtree_mem n nd then
                      raise Found
                  ) prnd;
                false
              with
                Found -> true
            in
            [%debug_log "%a -> %B" nups nd b];
            b
          in

          let check_locked lckd tree nd =
            let b =
              try
                Xset.iter
                  (fun n ->
                    if tree#initial_subtree_mem n nd then
                      raise Found
                  ) lckd;
                false
              with
                Found -> true
            in
            [%debug_log "%a -> %B" nups nd b];
            b
          in

          let rt1, rt2 = tree1#root, tree2#root in


          let prematch_ok1 nd =
            not (check_pruned !pruned_list1 tree1 nd || check_locked locked1 tree1 nd) &&
            nd != rt1
          in

          let prematch_ok2 nd =
            not (check_pruned !pruned_list2 tree2 nd || check_locked locked2 tree2 nd) &&
            nd != rt2
          in


          let reg nd1 nd2 =

            [%debug_log "node match: %a[%a] <--> %a[%a] <%a>" nups nd1 locps nd1 nups nd2 locps nd2 labps nd1];

            ignore (ref_nmapping#add_unsettled nd1 nd2);
            if
              (nd1#initial_nchildren = 0 && nd2#initial_nchildren = 0 && nd1#data#is_named) (* ||
              (nd1#data#is_boundary && nd2#data#is_boundary) *) (* cf. airo.c 2164L-2673L *)
            then begin
              [%debug_log "STABLE"];
              ref_nmapping#add_stable_pair nd1 nd2
            end
          in

          let register_matches _nds1 _nds2 =
            [%debug_log "_nds1=[%a] _nds2=[%a]" nsps _nds1 nsps _nds2];
            let len1 = List.length _nds1 in
            let len2 = List.length _nds2 in
            let thresh = options#prematch_cands_threshold in

            if len1 > thresh || len2 > thresh then
              ()
            else
              let nds1 = List.filter prematch_ok1 _nds1 in
              let nds2 = List.filter prematch_ok2 _nds2 in

              [%debug_log "nds1=[%a] nds2=[%a]" nsps nds1 nsps nds2];

              match nds1, nds2 with
              | [nd1], [nd2] -> begin
                  (*if
                    try
                      nd1#initial_parent#data#anonymized_label = nd2#initial_parent#data#anonymized_label
                    with _ -> true
                  then*)
                    reg nd1 nd2
              end
              | _ ->
                  if options#prematch_early_resolve_flag then
                    let a1 = Array.of_list nds1 in
                    let a2 = Array.of_list nds2 in
                    let selected =
                      let cmpr = new SMP.ComparatorFloat.c cenv#get_adjacency_score a1 a2 in
                      SMP.get_stable_matches cmpr a1 a2
                    in
                    List.iter (fun (nd1, nd2) -> reg nd1 nd2) selected
          in (* end of func register_matches *)

          (*let get_one nds =
            let tbl = Hashtbl.create 0 in
            List.iter
              (fun x ->
                let a = find_boundary x in
                try
                  let l = Hashtbl.find tbl a in
                  if l <> [] then
                    Hashtbl.replace tbl a []
                with
                  Not_found ->
                    Hashtbl.add tbl a [x]
              ) nds;
            let res = ref None in
            begin
              try
                Hashtbl.iter
                  (fun a l ->
                    match l with
                    | [x] -> begin
                        match !res with
                        | Some _ -> res := None; raise Exit
                        | None -> res := Some x
                    end
                    | _ -> ()
                  ) tbl
              with
                Exit -> ()
            end;
            !res
          in*)

          let setup_boundary_mapping ?(weak=false) ?(stable=false) nd1 nd2 =
            ignore weak;
            [%debug_log "%a-%a" nups nd1 nups nd2];

            let ca1 = nd1#initial_children in
            let ca2 = nd2#initial_children in
            let selected_child_pair_list =
              let cmpr =
                new SMP.ComparatorFloat.c
                  (fun c1 c2 ->
                    if c1#data#eq c2#data then
                      1.0
                    else if c1#data#anonymized_label = c2#data#anonymized_label then
                      0.5
                    else
                      0.0
                  ) ca1 ca2
              in
              SMP.get_stable_matches cmpr ca1 ca2
            in
            List.iter
              (fun (c1, c2) ->
                ignore (pre_nmapping#add_settled ~stable c1 c2);
                pre_nmapping#add_to_pre_boundary_mapping c1 c2;

                if c1#initial_nchildren = 1 && c2#initial_nchildren = 1 then begin
                  let cc1 = c1#initial_children.(0) in
                  let cc2 = c2#initial_children.(0) in
                  if cc1#data#anonymized_label = cc2#data#anonymized_label then begin
                    ignore (pre_nmapping#add_unsettled cc1 cc2);
                    pre_nmapping#add_to_pre_boundary_mapping cc1 cc2
                  end
                end
                else if
                  c1#data#is_ntuple && c2#data#is_ntuple &&
                  (c1#initial_nchildren > 1 || c2#initial_nchildren > 1)
                then begin
                  let cca1 = c1#initial_children in
                  let cca2 = c2#initial_children in
                  let selected_child_child_pair_list =
                    let cmpr =
                      new SMP.ComparatorFloat.c
                        (fun cc1 cc2 ->
                          if cc1#data#eq cc2#data then
                            1.0
                          else if cc1#data#anonymized_label = cc2#data#anonymized_label then
                            0.5
                          else
                            0.0
                        ) cca1 cca2
                    in
                    SMP.get_stable_matches cmpr cca1 cca2
                  in
                  List.iter
                    (fun (cc1, cc2) ->
                      ignore (pre_nmapping#add_settled ~stable cc1 cc2);
                      pre_nmapping#add_to_pre_boundary_mapping cc1 cc2;

                      if cc1#initial_nchildren = 1 && cc2#initial_nchildren = 1 then begin
                        let ccc1 = cc1#initial_children.(0) in
                        let ccc2 = cc2#initial_children.(0) in
                        if ccc1#data#anonymized_label = ccc2#data#anonymized_label then begin
                          ignore (pre_nmapping#add_unsettled ccc1 ccc2);
                          pre_nmapping#add_to_pre_boundary_mapping ccc1 ccc2
                        end
                      end

                    ) selected_child_child_pair_list
                end

                ) selected_child_pair_list;

            ignore (pre_nmapping#add_settled ~stable nd1 nd2);

            pre_nmapping#add_to_pre_boundary_mapping nd1 nd2;

            pre_nmapping#finalize_mapping nd1 nd2;

            (*pre_nmapping#add_settled_roots nd1 nd2*)

          in (* setup_boundary_mapping *)

          Hashtbl.iter
            (fun _lab nds1 ->
              let lab = Obj.obj _lab in
              try
                let nds2 = Hashtbl.find ltbl2 _lab in
                (*let nds1, nds2 =
                  if List.length nds1 > 2 && List.length nds2 > 2 then
                    match get_one nds1, get_one nds2 with
                    | Some n1, Some n2 -> begin
                        reg n1 n2;
                        Xlist.subtract nds1 [n1], Xlist.subtract nds2 [n2]
                    end
                    | _ -> nds1, nds2
                  else
                    nds1, nds2
                in*)
(*
                let b0 = Label.has_non_trivial_value lab in
                let b1 = Label.is_string_literal lab || Label.is_int_literal lab in
                if b0 <> b1 then begin
                  [%debug_log "!!!!! %s: non_trivial_value=%B (string||int)_literal=%B"
                    (Label.to_string lab) b0 b1];

                  [%debug_log "[%a]-[%a]" nsps nds1 nsps nds2];
                  match nds1, nds2 with
                  | [nd1], [nd2] -> [%debug_log "[%a]-[%a]" locps nd1 locps nd2]
                  | _ -> ()
                end;
*)
                if
                  Label.is_named lab ||
                  (*Label.has_non_trivial_value lab*)
                  Label.is_string_literal lab || Label.is_int_literal lab
                then begin
                  register_matches nds1 nds2;
                end;
                if options#multi_node_match_flag then
                  multiple_node_matches#add _lab (nds1, nds2);

                begin
                  [%debug_log "[%a]-[%a]" nsps nds1 nsps nds2];
                  let get_uniq_child_ntuple n =
                    let xl = ref [] in
                    Array.iter
                      (fun c ->
                        if c#data#is_ntuple then
                          xl := c :: !xl
                      ) n#initial_children;
                    match !xl with
                    | [x] -> [%debug_log "%a -> %a" nups n nups x]; x
                    | _ -> raise Not_found
                  in
                  match nds1, nds2 with
                  | [nd1], [nd2] -> begin
                      if
                        nd1#data#is_boundary && nd1#data#is_named_orig &&
                        not nd1#data#is_sequence && not nd1#data#is_ntuple &&
                        try
                          let cnd1 = get_uniq_child_ntuple nd1 in
                          let cnd2 = get_uniq_child_ntuple nd2 in
                          not (cnd1#data#subtree_equals cnd2#data)
                        with _ -> false
                      then begin
                        [%debug_log "boundary node match: %a[%a] <--> %a[%a] <%a>"
                          nups nd1 locps nd1 nups nd2 locps nd2 labps nd1];

                        setup_boundary_mapping ~weak:true(* ~stable:true*) nd1 nd2
                      end
                  end
                  | _ -> ()
                end

              with
                Not_found -> ()

            ) ltbl1;

          Hashtbl.iter
            (fun name nds1 ->
              try
                let nds2 = Hashtbl.find b_ltbl2 name in
                match nds1, nds2 with
                | [nd1], [nd2] when not (nd1#data#eq nd2#data) -> begin
                    [%debug_log "boundary node match: %a[%a] <--> %a[%a] <%a>"
                      nups nd1 locps nd1 nups nd2 locps nd2 labps nd1];

                    setup_boundary_mapping nd1 nd2

                end
                | _ -> ()
              with
                _ -> ()
            ) b_ltbl1;

          [%debug_log "prematching completed."]
        end;
        (* end of pre-matching *)

        compare_tree
          options
          lang
          cenv
          pre_nmapping
          may_be_unsettled1
          may_be_unsettled2
          ref_nmapping
          tree1 tree2

      end
(*
    with
    | Sys_error msg -> Xprint.error "%s" msg; exit 1
    | Xfile.No_extension f -> Xprint.error "have no file extension: \"%s\"" f; exit 1
*)
  (* end of method compare *)


  end (* of class comparator *)




end (* of functor Analyzing.F *)
]

(*
let compare options ?(cache_path="") file1 file2 =
  let ext1 = file1#get_extension in
  let ext2 = file2#get_extension in

  if ext1 <> ext2 then begin
    [%error_log "different extensions: %s and %s" ext1 ext2];
    exit 1
  end;

  let lang = Lang.search options ext1 in

  let comp = lang.Lang.compare in

  comp options lang ~cache_path file1 file2
*)

let get_comparator options ?(cache_path="") file1 file2 =
  let ext1 = file1#get_extension in
  let ext2 = file2#get_extension in

  let lang1 = Lang.search options ext1 in
  let lang2 = Lang.search options ext2 in

  if
    ext1 <> ext2 &&
    lang1 != lang2 &&
    not options#parser_designated
  then begin
    Xprint.error "different extensions: %s and %s" ext1 ext2;
    exit 1
  end;

  lang1#make_tree_comparator options ~cache_path file1 file2
