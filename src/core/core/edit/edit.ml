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
(* edit.ml *)

[%%prepare_logger]


module B = Diffast_misc.Binding
module BID = B.ID

(*let nps = Misc.nps
let nsps = Misc.nsps
let nups = Misc.nups*)
let nugsps = Misc.nugsps

type node_t = Spec.node_t
type tree_t = Spec.tree_t

include Edit_base

exception Abort

class seq options = object (self)
  inherit [node_t, tree_t] seq_base options(* as super*)

  method! dump_delta
      ?(extra_ns_decls=[])
      ?(info_file_path="")
      (tree1 : 'tree_t)
      (tree2 : 'tree_t)
      (nmapping : node_t Node_mapping.c)
      edits_copy
      fname
      =
    let comp = options#delta_compression in
    let irreversible_flag = options#irreversible_flag in
    let dedits =
      new Delta.Edit.seq options ~irreversible_flag tree1 tree2 nmapping edits_copy self
    in
    dedits#dump_delta
      ~extra_ns_decls
      ~comp
      ~info_file_path
      nmapping fname

end (* of class seq *)

[%%capture_path
let dump_changes options lang tree1 tree2 nmapping edits_copy (*edits*)_ file =
  [%debug_log "dumping changes..."];

  let extract = lang#extract_change in

  Xprint.verbose options#verbose_flag "extracting changes...";

  let changes, unused, (*change_infos*)_, triples =
    extract options tree1 tree2 nmapping edits_copy
  in

  Xprint.verbose options#verbose_flag "done.";

  if changes <> [] || unused <> [] then begin

    let dumper ch =
      Xprint.verbose options#verbose_flag "dumping...";

      let sorted =
        List.fast_sort
          (fun (_, s1, _) (_, s2, _) -> Stdlib.compare s2 s1)
          changes
      in
      if changes <> [] then begin
        Printf.fprintf ch "*** Extracted Changes ***\n";
        List.iter
          (fun (chg_ty, lv, mess) ->
            let n = List.length mess in
            Printf.fprintf ch "\n[significance=%d] %s (%d)\n" lv chg_ty n;
            List.iter
              (fun mes ->
                Printf.fprintf ch "  %s\n" mes
              ) mess
          ) sorted
      end;

      if unused <> [] then begin
        Printf.fprintf ch "\n%d edit operations are not classified:\n" (List.length unused);
        List.iter
          (fun ed ->
            Printf.fprintf ch "%s\n" (to_string ed)
          ) unused
      end;
      Xprint.verbose options#verbose_flag "done.";
    in (* dumper *)
(*
    let csv_dumper ch =
      Xprint.verbose options#verbose_flag "dumping csv...";

      let cmp (_, _, _, _, _, loc1, _, _) (_, _, _, _, _, loc2, _, _) =
        if loc1 <> Loc.dummy && loc2 <> Loc.dummy then
          Stdlib.compare loc1.Loc.start_offset loc2.Loc.start_offset
        else begin
          [%warn_log "invalid location"];
          0
        end
      in

      if change_infos <> [] then begin
        let _csv = ref [] in
        List.iter
          (fun (chg_ty, lv, infos) ->
            List.iter
              (fun (desc, adesc, unit1, loc1, unit2, loc2) ->
                _csv := ( chg_ty,
                          string_of_int lv,
                          desc,
                          adesc,
                          unit1,
                          loc1,
                          unit2,
                          loc2
                        )::!_csv
              ) infos
          ) change_infos;

        let sorted =
          List.map
            (fun (ct, lv, d, ad, u1, l1, u2, l2) ->
              [ct; lv; d; ad; u1; Loc.to_string l1; u2; Loc.to_string l2]
            ) (List.stable_sort cmp !_csv)
        in

        let filtered =
          if options#multiple_classification_flag then
            sorted
          else begin
            let tbl = Hashtbl.create 0 in
            List.fold_left
              (fun l ->
                function
                  | [ct; lv; d; ad; u1; l1; u2; l2] ->
                      if Hashtbl.mem tbl (l1, l2) then begin
                        [%debug_log "filtered out: [%s] (%s)-(%s)" ct l1 l2];
                        l
                      end
                      else begin
                        Hashtbl.replace tbl (l1, l2) true;
                        [ct; lv; String.escaped d; ad; u1; l1; u2; l2]::l
                      end
                  | _ -> assert false

              ) [] (List.rev sorted)
          end
        in
        Csv.save_out_readable ch filtered;

        Xprint.verbose options#verbose_flag "done.";
      end
    in (* csv_dumper *)
*)
    Xfile.dump file dumper;
    (*Xfile.dump (file^".csv") csv_dumper;*)

    if options#fact_for_changes_flag && not (Xset.is_empty triples) then begin
      Xprint.verbose options#verbose_flag "dumping change fact...";
      let into_virtuoso = options#fact_into_virtuoso <> "" in
      let into_directory = options#fact_into_directory <> "" in

      if into_virtuoso then begin
        assert (not into_directory);
        Triple.dump_into_virtuoso options triples
      end
      else if into_directory then
        let cache_name = Cache.get_cache_name options (Filename.dirname file) in
        Triple.dump_into_directory options cache_name triples
      else
        Triple.dump options ~overwrite:false ~comp:options#fact_compression (file^".nt") triples;

      Xprint.verbose options#verbose_flag "done."
    end;
    [%debug_log "done."]
  end (* of if changes <> [] || unused <> [] *)
  (* end of func dump_changes *)
]

(* * * * *)

[%%capture_path
let remove_relabels_and_mapping
    cenv
    edits
    nmapping
    to_be_removed
    =
  let tree1 = cenv#tree1 in
  let tree2 = cenv#tree2 in
  List.iter (* remove incompatible relabels and mapping *)
    (fun (nd1, nd2, by_non_renames) -> begin
      [%debug_log "nd1=%a nd2=%a by_non_renames=%B" nups nd1 nups nd2 by_non_renames];
      let nodes1 = ref [] in
      let nodes2 = ref [] in
      tree1#scan_whole_initial_subtree nd1 (fun n -> nodes1 := n::!nodes1);
      tree2#scan_whole_initial_subtree nd2 (fun n -> nodes2 := n::!nodes2);
      [%debug_log "descs1: %a -> [%a]" nups nd1 nsps !nodes1];
      [%debug_log "descs2: %a -> [%a]" nups nd2 nsps !nodes2];
      List.iter
        (fun n ->
          try
            let n' = nmapping#find n in
            if
              not (n#data#eq n'#data) &&
              List.memq n' !nodes2
            then begin

              if by_non_renames then begin
                [%debug_log "by_non_renames=%B n=%a n'=%a" by_non_renames nups n nups n'];
                cenv#add_bad_pair n n'
              end;(*do not remove!!!NG!!!*)

              List.iter
                (fun ed ->
                  [%debug_log "removing %s" (Editop.to_string ed)];
                  edits#remove_edit ed
                ) (edits#find12 n n');

              let _ = nmapping#remove n n' in

              let del = Editop.make_delete n in (* generate delete *)
              [%debug_log "adding %s" (Editop.to_string del)];

              edits#add_edit del;

              let ins = Editop.make_insert n' in (* generate insert *)
              [%debug_log "adding %s" (Editop.to_string ins)];

              edits#add_edit ins

            end
          with
            Not_found -> ()
        ) !nodes1
    end
    ) to_be_removed
(* end of func remove_relabels_and_mapping *)
]

[%%capture_path
let combine_node_lists
    ?(filt=(fun _ _ -> true))
    (cenv : (node_t, tree_t) Comparison.c)
    nmapping
    cands1
    cands2
    =
  [%debug_log "cands1=[%a] cands2=[%a]" nsps cands1 nsps cands2];
  match cands1, cands2 with
  | [], _ | _, [] -> []
  | [nd1], [nd2] -> [nd1, nd2]
  (*| nds1, nds2 when List.length nds1 = List.length nds2 -> begin
      let gcmp n0 n1 = Stdlib.compare n0#gindex n1#gindex in
      let sorted1 = List.fast_sort gcmp nds1 in
      let sorted2 = List.fast_sort gcmp nds2 in
      List.combine sorted1 sorted2
  end*)
  | nds1, nds2 when begin
      List.length nds1 = List.length nds2 &&
      List.for_all2
        (fun n1 n2 ->
          try
            nmapping#find n1#initial_parent == n2#initial_parent
          with _ -> false
        ) nds1 nds2
  end -> begin
    let get_ofs n = n#data#src_loc.Loc.start_offset in
    let cmp n0 n1 = Stdlib.compare (get_ofs n0) (get_ofs n1) in
    let sorted1 = List.fast_sort cmp nds1 in
    let sorted2 = List.fast_sort cmp nds2 in
    List.combine sorted1 sorted2
  end
  | nds1, nds2 -> begin
      let anc1, _ = cenv#tree1#nearest_common_ancestor nds1 in
      let anc2, _ = cenv#tree2#nearest_common_ancestor nds2 in
      [%debug_log "anc1=%a anc2=%a" nps anc1 nps anc2];
      let anchor = Some (anc1, anc2) in
      let pair_weight_list = ref [] in
      List.iter
        (fun nd1 ->
          List.iter
            (fun nd2 ->
              if filt nd1 nd2 then begin
                let a =
                  Stdlib.truncate ((cenv#get_adjacency_score ~anchor nd1 nd2) *. 10000.0)
                in
                let w = Comparison.weight_of_int a in
                pair_weight_list := (nd1, nd2, w) :: !pair_weight_list
              end
            ) nds2
        ) nds1;

      begin %debug_block
        [%debug_log "pair_weight_list:"];
        List.iter
          (fun (n1, n2, w) ->
            [%debug_log " %a(%a)-%a(%a): %a"
              nups n1 GI.ps n1#gindex nups n2 GI.ps n2#gindex Comparison.wps w]
          ) !pair_weight_list
      end;

      let pairs, _ =
        cenv#select_p_pairs (fun _ _ _ _ -> true) !pair_weight_list
      in
      List.map (fun (n1, n2, _) -> n1, n2) pairs
  end
 (* end of func combine_node_lists *)
]

let lock_mapping tree1 tree2 nmapping nd1 nd2 =
  [%debug_log "%a-%a" nups nd1 nups nd2];
  let nodes1 = ref [] in
  let nodes2 = ref [] in
  tree1#scan_whole_initial_subtree nd1 (fun n -> nodes1 := n::!nodes1);
  tree2#scan_whole_initial_subtree nd2 (fun n -> nodes2 := n::!nodes2);
  List.iter
    (fun n ->
      try
        let n' = nmapping#find n in
        if List.memq n' !nodes2 then begin
          let key = Some (Key.make_pair_key nd1 nd2) in
          nmapping#lock_node ?key:key n;
          nmapping#lock_node ?key:key n';
        end
      with
        Not_found -> ()
    ) !nodes1
(* end of func lock_mapping *)

[%%capture_path
let generate_compatible_edits
    options
    cenv
    nmapping
    edits
    compatible_pairs
    is_incompatible
    =
  let tree1 : tree_t = cenv#tree1 in
  let tree2 : tree_t = cenv#tree2 in
  let count = ref 0 in
  List.iter
    (fun (nd1, nd2) -> (* generate compatible edits *)

      if nd1#is_valid && nd2#is_valid then begin

      [%debug_log "compatible pair: %s - %s" nd1#data#to_string nd2#data#to_string];

      let subtree1 = tree1#make_anonymized_subtree_copy nd1 in
      let subtree2 = tree2#make_anonymized_subtree_copy nd2 in
      let subcenv = new Comparison.c options subtree1 subtree2 in
      let m, em, r =
        Treediff.match_trees ~semantic:true
          cenv subtree1 subtree2 (new Node_mapping.c subcenv) (new Node_mapping.c subcenv)
      in
      let matches =
        (Misc.conv_subtree_node_pairs tree1 tree2) (m @ em @ r)
      in

      begin %debug_block
        [%debug_log "matches:"];
        List.iter
          (fun (n1, n2) -> [%debug_log "%a-%a" nups n1 nups n2])
          matches;
        [%debug_log "matches (gindex):"];
        List.iter
          (fun (n1, n2) -> [%debug_log "%a-%a" GI.ps n1#gindex GI.ps n2#gindex])
          matches;
      end;

      List.iter
        (fun (n1, n2) ->
          [%debug_log "%a-%a" nups n1 nups n2];
          let incompat, (*by_non_renames*)_ = is_incompatible n1 n2 in
          if incompat then
            [%debug_log "incompatible"]
          else begin
            (* remove conflicting edits *)
            begin
              let eds1 = edits#find1 n1 in
              let to_be_added = Xset.create 0 in
              let conflict =
                match eds1 with
                | [] -> false

                | [Delete _] -> true

                | [Relabel(_, _, (i2', _))] -> Info.get_node i2' != n2

                | [Relabel(_, _, (i2', _));Move(_, _, _, (i2'', _))]
                | [Move(_, _, _, (i2'', _));Relabel(_, _, (i2', _))] -> begin
                    let n2' = Info.get_node i2' in
                    let n2'' = Info.get_node i2'' in
                    assert (n2' == n2'');
                    let b = n2' != n2 in
                    if b then begin
                      let ins = Editop.make_insert n2' in
                      [%debug_log "to be adde: %s" (Editop.to_string ins)];
                      Xset.add to_be_added ins
                    end;
                    b
                end
                | [Move(_, _, _, (i2', _))] -> begin
                    let n2' = Info.get_node i2' in
                    if n2' != n2 then begin
                      let ins = Editop.make_insert n2' in
                      [%debug_log "to be added: %s" (Editop.to_string ins)];
                      Xset.add to_be_added ins
                    end;
                    true
                end
                | eds -> begin
                    [%debug_log "assertion failed"];
                    List.iter
                      (fun ed ->
                        [%debug_log "%s" (to_string ed)];
                        Xprint.error "%s\n" (to_string ed)
                      ) eds;
                    assert false
                end
              in
              if conflict then begin
                List.iter
                  (fun e ->
                    [%debug_log "removing %s" (Editop.to_string e)];
                    edits#remove_edit e
                  ) eds1;
                Xset.iter
                  (fun e ->
                    [%debug_log "adding %s" (Editop.to_string e)];
                    edits#add_edit e
                  ) to_be_added
              end
            end;
            begin
              let eds2 = edits#find2 n2 in
              let to_be_added = Xset.create 0 in
              let conflict =
                match eds2 with
                | [] -> false

                | [Insert _] -> true

                | [Relabel(_, (i1', _), _)] -> Info.get_node i1' != n1

                | [Relabel(_, (i1', _), _);Move(_, _, (i1'', _), _)]
                | [Move(_, _, (i1'', _), _);Relabel(_, (i1', _), _)] -> begin
                    let n1' = Info.get_node i1' in
                    let n1'' = Info.get_node i1'' in
                    assert (n1' == n1'');
                    let b = n1' != n1 in
                    if b then begin
                      let del = Editop.make_delete n1' in
                      [%debug_log "to be added: %s" (Editop.to_string del)];
                      Xset.add to_be_added del
                    end;
                    b
                end
                | [Move(_, _, (i1', _), _)] -> begin
                    let n1' = Info.get_node i1' in
                    if n1' != n1 then begin
                      let del = Editop.make_delete n1' in
                      [%debug_log "to be added: %s" (Editop.to_string del)];
                      Xset.add to_be_added del
                    end;
                    true
                end
                | eds -> begin
                    [%debug_log "assertion failed"];
                    List.iter
                      (fun ed ->
                        [%debug_log "%s" (to_string ed)];
                        Xprint.error "%s\n" (to_string ed)
                      ) eds;
                    assert false
                end
              in
              if conflict then begin
                List.iter
                  (fun e ->
                    [%debug_log "removing %s" (Editop.to_string e)];
                    edits#remove_edit e
                  ) eds2;
                Xset.iter
                  (fun e ->
                    [%debug_log "adding %s" (Editop.to_string e)];
                    edits#add_edit e
                  ) to_be_added
              end
            end;

            (* add new edit *)
            let eds = edits#find12 n1 n2 in
            if eds = [] then begin
              if not (n1#data#eq n2#data) then begin
                let rel = Editop.make_relabel n1 n2 in
                [%debug_log "adding %s" (Editop.to_string rel)];
                edits#add_edit rel;
                incr count
              end
            end
            else begin
              begin %debug_block
                List.iter
                  (fun ed ->
                    [%debug_log "found %s" (Editop.to_string ed)]
                  ) eds;
              end
            end;

            (* add new mapping (override) *)
            if not (nmapping#has_mapping n1 n2) then begin
              [%debug_log "adding %a -> %a" nups n1 nups n2];
              let conflict = nmapping#add_unsettled n1 n2 in
              match conflict with
              | Some n1, None -> begin
                  let del = Editop.make_delete n1 in
                  [%debug_log "adding %s" (Editop.to_string del)];
                  edits#add_edit del
              end
              | None, Some n2 -> begin
                  let ins = Editop.make_insert n2 in
                  [%debug_log "adding %s" (Editop.to_string ins)];
                  edits#add_edit ins
              end
              | Some n1, Some n2 -> begin
                  let del = Editop.make_delete n1 in
                  [%debug_log "adding %s" (Editop.to_string del)];
                  edits#add_edit del;
                  let ins = Editop.make_insert n2 in
                  [%debug_log "adding %s" (Editop.to_string ins)];
                  edits#add_edit ins
              end
              | _ -> ()
            end;

            if
              nd1#data#_anonymized_label = nd2#data#_anonymized_label ||
              let bnd1 = nd1#data#binding in
              let bnd2 = nd2#data#binding in
              B.is_def bnd1 && B.is_def bnd2 && B.is_local_def bnd1 = B.is_local_def bnd2
            then begin
              let key = Some (Key.make_pair_key nd1 nd2) in
              nmapping#lock_node ?key:key n1;
              nmapping#lock_node ?key:key n2
            end
          end
        ) matches
      end

    ) compatible_pairs;
  !count
(* end of func generate_compatible_edits *)
]

let mkfilt getlab is_x nd =
  try
    is_x (getlab nd)
  with
    Not_found -> false


let is_def nd = B.is_def nd#data#binding
let is_non_local_def nd = B.is_non_local_def nd#data#binding
let is_use nd = B.is_use nd#data#binding
let get_bid nd = B.get_bid nd#data#binding
let get_bid_opt nd = B.get_bid_opt nd#data#binding

let get_bid_name tree bid =
  try
    tree#find_name_for_bid bid
  with _ -> "?"

let null_boundary_key = Comparison.null_boundary_key
let is_mapped_boundary_key = Comparison.is_mapped_boundary_key

[%%capture_path
let is_uniq_child pnd nd =
  let b =
    try
      let pos = Sourcecode.get_logical_pos ?strict:(Some true) nd in
      match Sourcecode.get_logical_nth_child pnd pos with
      | [|_|] -> true
      | _ -> false
    with _ ->
      pnd#initial_nchildren = 1

  in
  [%debug_log "%a -> %B" nups nd b];
  b
]

let has_uniq_path rt nd =
  let b =
    try
      let prev = ref nd in
      nd#iter_initial_ancestor_nodes
        (fun n ->
          if not (is_uniq_child n !prev) then
            raise Abort;
          if n == rt then
            raise Exit;
          prev := n
        );
      true
    with
    | Abort -> false
    | Exit -> true
  in
  (*[%debug_log "%a (rt=%a) -> %B" nups nd nups rt b]*)
  b

[%%capture_path
let has_uniq_paths rt1 rt2 n1 n2 =
  let b = has_uniq_path rt1 n1 && has_uniq_path rt2 n2 in
  [%debug_log "(%a-%a) %a-%a -> %B" nups rt1 nups rt2 nups n1 nups n2 b];
  b
]

[%%capture_path
let collect_use_renames ?(filt=fun _ _ -> true) cenv nmapping edits is_possible_rename = begin

  let freq_tbl = Hashtbl.create 0 in
  let bonus_tbl = Hashtbl.create 0 in

  let _use_rename_tbl1 = Hashtbl.create 0 in
  let _use_rename_tbl2 = Hashtbl.create 0 in

  let free_freq_tbl = Hashtbl.create 0 in
  let free_bonus_tbl = Hashtbl.create 0 in

  let _free_rename_tbl1 = Hashtbl.create 0 in
  let _free_rename_tbl2 = Hashtbl.create 0 in

  (*let get_orig_name n = try n#data#get_orig_name with _ -> n#data#get_name in*)
  let get_orig_name n = Comparison.get_orig_name n in

  let add_use_rename ?(force=false) ?(bonus=1) ?(strip=false) node1 node2 bid1 bid2 =
    [%debug_log "force=%B bonus=%d strip=%B" force bonus strip];
    let name1 = if strip then Comparison.get_orig_name node1 else node1#data#get_name in
    let name2 = if strip then Comparison.get_orig_name node2 else node2#data#get_name in
    [%debug_log "adding %a -> %a (\"%s\" -> \"%s\")" BID.ps bid1 BID.ps bid2 name1 name2];
    let add tbl bkey bi1 bi2 =
      let bi_tbl =
        try
          Hashtbl.find tbl bkey
        with
          Not_found ->
            let t = Hashtbl.create 0 in
            Hashtbl.add tbl bkey t;
            t
      in
      try
        let bs = Hashtbl.find bi_tbl bi1 in
        if not (List.mem bi2 bs) then
          Hashtbl.replace bi_tbl bi1 (bi2::bs)
      with
        Not_found -> Hashtbl.add bi_tbl bi1 [bi2]
    in
    if
      force ||
      is_possible_rename cenv node1 node2 bid1 bid2(*!20240324! &&
      let find_nearest_anc_stmt =
        Sourcecode.find_nearest_p_ancestor_node (fun n -> n#data#is_statement)
      in
      not (
       try
         let stmt1 = find_nearest_anc_stmt node1 in
         let stmt2 = find_nearest_anc_stmt node2 in
         nmapping#find stmt1 == stmt2 &&
         let has_stmt_anc = Misc.has_p_ancestor (fun x -> x#data#is_statement) in
         not (has_stmt_anc stmt1) && not (has_stmt_anc stmt2) &&
         stmt1#initial_parent#initial_nchildren = 1 &&
         stmt2#initial_parent#initial_nchildren = 1
       with _ -> false
      )*)
    then begin
      let boundary_key = cenv#get_boundary_key node1 node2 in
      add _use_rename_tbl1 boundary_key bid1 bid2;
      add _use_rename_tbl2 boundary_key bid2 bid1;
      [%debug_log "added"];
      let k = bid1, bid2 in
      if
        force ||
        not node1#data#is_order_insensitive && not node2#data#is_order_insensitive &&
        (
         try
           let pnd1 = node1#initial_parent in
           let pnd2 = node2#initial_parent in
           (
            not pnd1#data#is_order_insensitive && not pnd2#data#is_order_insensitive ||
            is_uniq_child pnd1 node1 && is_uniq_child pnd2 node2 ||
            pnd1#initial_nchildren = 1 && pnd1#initial_nchildren = 1
           ) &&
           nmapping#find pnd1 == pnd2 &&
           let ppnd1 = pnd1#initial_parent in
           let ppnd2 = pnd2#initial_parent in
           (
            not ppnd1#data#is_order_insensitive && not ppnd2#data#is_order_insensitive ||
            is_uniq_child ppnd1 pnd1 && is_uniq_child ppnd2 pnd2 ||
            ppnd1#initial_nchildren = 1 && ppnd1#initial_nchildren = 1
           ) &&
           nmapping#find ppnd1 == ppnd2
         with
           _ -> false
        ) ||
        try
          let tree1 = cenv#tree1 in
          let tree2 = cenv#tree2 in
          let find_nearest_anc_stmt =
            Sourcecode.find_nearest_p_ancestor_node (fun n -> n#data#is_statement)
          in
          match cenv#find_ancestor_pairs_of_same_category false node1 node2 with
          | (_, _, anc1, anc2, _, _)::_ when begin
              [%debug_log "anc: %s - %s" anc1#data#to_string anc2#data#to_string];
              anc1#data#eq anc2#data &&
              let stmt1 = find_nearest_anc_stmt node1 in
              let stmt2 = find_nearest_anc_stmt node2 in
              stmt1#data#_anonymized_label = stmt2#data#_anonymized_label &&
              tree1#is_initial_ancestor stmt1 anc1 &&
              tree2#is_initial_ancestor stmt2 anc2
          end -> begin
            let def1 = tree1#search_node_by_uid (B.get_uid node1#data#binding) in
            let def2 = tree2#search_node_by_uid (B.get_uid node2#data#binding) in
            [%debug_log "def: %s - %s" def1#data#to_string def2#data#to_string];
            not (try
              let def1' = nmapping#find def1 in
              def1' != def2 && def1#data#eq def1'#data
            with _ -> false) &&
            not (try
              let def2' = nmapping#inv_find def2 in
              def2' != def1 && def2#data#eq def2'#data
            with _ -> false)
          end
          | _ -> false
        with
          _ -> false
      then begin
        [%debug_log "@"];
        Hashtbl.replace bonus_tbl k bonus
      end;
      try
        let freq, nm1, nm2 = Hashtbl.find freq_tbl k in
        [%debug_log "nm1=\"%s\" nm2=\"%s\"" nm1 nm2];
        assert (nm1 = name1 && nm2 = name2);
        Hashtbl.replace freq_tbl k (freq + 1, name1, name2)
      with
        Not_found -> Hashtbl.add freq_tbl k (1, name1, name2)
    end
    else begin
      [%debug_log "not added"];
    end
  in

  let add_free_rename node1 node2 =
    let name1 = get_orig_name node1 in
    let name2 = get_orig_name node2 in
    [%debug_log "adding \"%s\" -> \"%s\"" name1 name2];
    let add tbl nm1 nm2 =
      try
        let nms = Hashtbl.find tbl nm1 in
        if not (List.mem nm2 nms) then
          Hashtbl.replace tbl nm1 (nm2::nms)
      with
        Not_found -> Hashtbl.add tbl nm1 [nm2]
    in
    if
      is_possible_rename cenv node1 node2 BID.dummy BID.dummy(*!20240324! &&
      not (cenv#has_match1 node1) && not (cenv#has_match2 node2)*)
    then begin
      add _free_rename_tbl1 name1 name2;
      add _free_rename_tbl2 name2 name1;
      [%debug_log "added"];
      let k = name1, name2 in
      if
        not node1#data#is_order_insensitive && not node2#data#is_order_insensitive &&
        try
          let pnd1 = node1#initial_parent in
          let pnd2 = node2#initial_parent in
          not pnd1#data#is_order_insensitive && not pnd2#data#is_order_insensitive &&
          nmapping#find pnd1 == pnd2 &&
          let ppnd1 = pnd1#initial_parent in
          let ppnd2 = pnd2#initial_parent in
          not ppnd1#data#is_order_insensitive && not ppnd2#data#is_order_insensitive &&
          nmapping#find ppnd1 = ppnd2
        with
          _ -> false
      then
        Hashtbl.replace free_bonus_tbl k 1;
      try
        let freq = Hashtbl.find free_freq_tbl k in
        Hashtbl.replace free_freq_tbl k (freq + 1)
      with
        Not_found -> Hashtbl.add free_freq_tbl k 1
    end
    else begin
      [%debug_log "not added"];
    end
  in

  let has_stmt_anc = Misc.has_p_ancestor (fun x -> x#data#is_statement) in
  let has_uniq_subtree_match n1 n2 =
    let b =
      cenv#in_subtree_matches n1 n2 ||
      n1#data#subtree_equals n2#data &&
      match n1#data#_digest with
      | Some d -> begin
          try
            match cenv#multiple_subtree_matches#find d with
            | [], _, _ | _, [], _ -> false
            | [x1,_], [x2,_], _ -> x1 == n1 && x2 == n2
            | xl1, xl2, _ when has_stmt_anc n1 && has_stmt_anc n2 -> begin
                let filt1 (n, _) = nmapping#mem_dom n in
                let filt2 (n, _) = nmapping#mem_cod n in
                match List.filter filt1 xl1, List.filter filt2 xl2 with
                | [x1,_], [x2,_] -> x1 == n1 && x2 == n2
                | _ -> false
            end
            | _ -> false
          with _ -> false
      end
      | None -> false
    in
    [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
    b
  in

  edits#iter_relabels
    (function
      | Relabel(_, (info1, _), (info2, _)) as rel -> begin
          let _ = rel in
          [%debug_log "checking %s" (Editop.to_string rel)];
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          if filt nd1 nd2 then begin
            if is_use nd1 && is_use nd2 then begin
              try
                add_use_rename nd1 nd2 (get_bid nd1) (get_bid nd2)
              with
                Not_found -> assert false
            end
            else if
              not (is_def nd1) && not (is_def nd2) &&
              nd1#data#is_named_orig && nd2#data#is_named_orig
            then begin
              try
                add_free_rename nd1 nd2
              with Not_found -> ()
            end
            else if
              is_def nd1 && is_def nd2 &&
              match nd1#initial_children, nd2#initial_children with
              | [|c1|], [|c2|] -> has_uniq_subtree_match c1 c2
              | _ -> begin
                  try
                    nd1#initial_parent#data#is_ntuple && nd2#initial_parent#data#is_ntuple &&
                    let bn1 = Comparison.get_bn nd1 in
                    let bn2 = Comparison.get_bn nd2 in
                    bn1#data#is_named_orig && bn2#data#is_named_orig &&
                    nmapping#find bn1 == bn2
                  with
                    _ -> false
              end
            then begin
              let bonus = 2 in
              try
                add_use_rename ~force:true ~bonus ~strip:true nd1 nd2 (get_bid nd1) (get_bid nd2)
              with
                Not_found -> assert false
            end
            (*else if
              is_def nd1 && is_def nd2 &&
              match nd1#initial_children, nd2#initial_children with
              | [|c1|], [|c2|] -> begin
                  (
                   c1#data#_digest <> None && c1#data#subtree_equals c2#data ||
                   c1#data#eq c2#data
                  ) &&
                  try
                    let pnd1 = nd1#initial_parent in
                    let pnd2 = nd2#initial_parent in
                    nmapping#find pnd1 = pnd2 &&
                    is_uniq_child pnd1 nd1 && is_uniq_child pnd2 nd2
                  with _ -> false
              end
              | _ -> false
            then begin
              let bonus = 1 in
              try
                add_use_rename ~force:true ~bonus ~strip:true nd1 nd2 (get_bid nd1) (get_bid nd2)
              with
                Not_found -> assert false
            end*)
            else if
              nd1#data#is_named && nd2#data#is_named &&
              try
                nd1#initial_parent#data#is_sequence &&
                nd2#initial_parent#data#is_sequence
              with _ -> false
            then begin
              try
                let pos1 = nd1#initial_pos in
                let pos2 = nd2#initial_pos in
                [%debug_log "pos1=%d pos2=%d" pos1 pos2];
                let siblings1 = nd1#initial_parent#initial_children in
                let siblings2 = nd2#initial_parent#initial_children in
                if
                  try
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
                then begin
                  let nm1 = Comparison.get_orig_name nd1 in
                  let nm2 = Comparison.get_orig_name nd2 in
                  cenv#add_rename_pat (nm1, nm2)
                end
              with
                _ -> ()
            end
          end
          else if nd1#data#is_named_orig && nd2#data#is_named_orig then begin
            match nd1#initial_children, nd2#initial_children with
            | [|c1|], [|c2|] when begin
                not (cenv#has_match1 nd1) && not (cenv#has_match2 nd2) &&
                cenv#has_uniq_match c1 c2
            end -> begin
              let nm1 = Comparison.get_orig_name nd1 in
              let nm2 = Comparison.get_orig_name nd2 in
              cenv#add_rename_pat (nm1, nm2)
            end
            | _ -> ()
          end
      end
      | _ -> assert false
    );
  (*!20240205!nmapping#iter
    (fun n1 n2 ->
      [%debug_log "checking %a-%a" nups n1 nups n2];
      if filt n1 n2 then begin
        if is_use n1 && is_use n2 then begin
          try
            add_use_rename n1 n2 (get_bid n1) (get_bid n2)
          with
            Not_found -> assert false
        end
        else if
          not (is_def n1) && not (is_def n2) &&
          n1#data#is_named_orig && n2#data#is_named_orig
        then begin
          add_free_rename n1 n2
        end
      end
    );*)

  Hashtbl.iter
    (fun (bi1, bi2 as k) bonus ->
      let _ = bi1 in
      let _ = bi2 in
      try
        let c, name1, name2 = Hashtbl.find freq_tbl k in
        [%debug_log "adding bonus: (%a(\"%s\"),%a(\"%s\")) -> %d+%d"
          BID.ps bi1 (get_bid_name cenv#tree1 bi1) BID.ps bi2 (get_bid_name cenv#tree2 bi2) c bonus];
        Hashtbl.replace freq_tbl k (c + bonus, name1, name2)
      with
        Not_found -> ()
    ) bonus_tbl;

  Hashtbl.iter
    (fun (nm1, nm2 as k) bonus ->
      let _ = nm1 in
      let _ = nm2 in
      try
        let c = Hashtbl.find free_freq_tbl k in
        [%debug_log "adding bonus: (\"%s\",\"%s\") -> %d+%d" nm1 nm2 c bonus];
        Hashtbl.replace free_freq_tbl k (c + bonus)
      with
        Not_found -> ()
    ) free_bonus_tbl;

  begin %debug_block
    [%debug_log "* use rename freq.:"];
    Hashtbl.iter
      (fun (bi1, bi2) (freq, nm1, nm2) ->
        [%debug_log " (%a, %a) -> %3d (\"%s\" -> \"%s\")" BID.ps bi1 BID.ps bi2 freq nm1 nm2]
      ) freq_tbl;
    [%debug_log "* free rename freq.:"];
    Hashtbl.iter
      (fun (nm1, nm2) freq ->
        [%debug_log "(\"%s\"->\"%s\") -> %d" nm1 nm2 freq]
      ) free_freq_tbl
  end;

  freq_tbl, _use_rename_tbl1, _use_rename_tbl2, free_freq_tbl, _free_rename_tbl1, _free_rename_tbl2
end
]

[%%capture_path
(* rectify_renames assumes that edit seq. contains correct renames of USEs *)
let rectify_renames_u
    ?(handle_weak=true)
    ?(trust_moved_non_renames=true)
    options
    (cenv : (node_t, tree_t) Comparison.c)
    nmapping
    edits
    (filters : (node_t -> bool) array)
    =
  [%debug_log "START! (handle_weak=%B,trust_moved_non_renames=%B)" handle_weak trust_moved_non_renames];

  let tree1 = (cenv#tree1 : tree_t) in
  let tree2 = (cenv#tree2 : tree_t) in

  (* collect def/use mapping (not relabeled) *)
  let non_rename_bid_tbl1 = Hashtbl.create 0 in (* bid -> bool * bool *)
  let non_rename_bid_tbl2 = Hashtbl.create 0 in
  let set_tbl setter tbl bid =
    try
      let d, u = Hashtbl.find tbl bid in
      Hashtbl.replace tbl bid (setter (Some (d, u)))
    with
      Not_found -> Hashtbl.add tbl bid (setter None)
  in
  let set_tbl_def = set_tbl (function Some (_, u) -> true, u | None -> true, false) in
  let set_tbl_use = set_tbl (function Some (d, _) -> d, true | None -> false, true) in

  let non_rename_bid_map1 = Hashtbl.create 0 in
  let non_rename_bid_map2 = Hashtbl.create 0 in

  let non_rename_bid_map_find1 bi1 =
    let bi2 = Hashtbl.find non_rename_bid_map1 bi1 in
    [%debug_log "%a -> %a" BID.ps bi1 BID.ps bi2];
    bi2
  in
  let non_rename_bid_map_find2 bi2 =
    let bi1 = Hashtbl.find non_rename_bid_map2 bi2 in
    [%debug_log "%a <- %a" BID.ps bi1 BID.ps bi2];
    bi1
  in

  nmapping#iter
    (fun n1 n2 ->
      [%debug_log "non_rename: checking %a-%a" nups n1 nups n2];
      let context_cond =
        (try nmapping#find n1#initial_parent == n2#initial_parent with _ -> false) &&
        (trust_moved_non_renames || not (edits#mem_mov12 n1 n2))
      in
      [%debug_log "context_cond=%B" context_cond];
      if context_cond then
      try
        let bi1 = get_bid n1 in
        let bi2 = get_bid n2 in
        if n1#data#eq n2#data then begin

          let name = try n1#data#get_name with _ -> "" in
          let _ = name in

          if (*is_non_local_def*)is_def n1 && (*is_non_local_def*)is_def n2 then begin
            set_tbl_def non_rename_bid_tbl1 bi1;
            set_tbl_def non_rename_bid_tbl2 bi2;
            Hashtbl.add non_rename_bid_map1 bi1 bi2;
            Hashtbl.add non_rename_bid_map2 bi2 bi1;

            [%debug_log "non_rename (def): %a-%a (%s)" BID.ps bi1 BID.ps bi2 name];
          end
          else if is_use n1 && is_use n2 then begin
            set_tbl_use non_rename_bid_tbl1 bi1;
            set_tbl_use non_rename_bid_tbl2 bi2;
            Hashtbl.add non_rename_bid_map1 bi1 bi2;
            Hashtbl.add non_rename_bid_map2 bi2 bi1;

            [%debug_log "non_rename (use): %a-%a (%s)" BID.ps bi1 BID.ps bi2 name];
          end

        end
      with
        Not_found -> ()
    );

  let non_rename tbl bi =
    let b =
      try
        match Hashtbl.find tbl bi with
        | true, true -> true
        | _ -> false
      with
        Not_found -> false
    in
    [%debug_log "%a -> %B" BID.ps bi b];
    b
  in

  (* non-rename can be rename e.g. fortran: variable-name -> array-element *)
  let is_possible_rename (cenv : (node_t, tree_t) Comparison.c) node1 node2 bi1 bi2 =

    let parent_cond, context_cond =
      try
        let pnd1 = node1#initial_parent in
        let pnd2 = node2#initial_parent in
        let c_cond =
          try nmapping#find pnd1 == pnd2 with _ -> false
        in
        let p_cond =
          let pbi1_opt = get_bid_opt pnd1 in
          let pbi2_opt = get_bid_opt pnd2 in
          match pbi1_opt, pbi2_opt with
          | Some (*pbi1*)_, Some (*pbi2*)_ -> true(*bi1 = pbi1 && bi2 = pbi2*)
          | Some _, None | None, Some _ -> false
          | None, None -> true
        in
        p_cond, c_cond
      with
        Otree.Parent_not_found _ -> true, true
    in
    [%debug_log "%a-%a (%a-%a): parent_cond=%B context_cond=%B"
      nups node1 nups node2 BID.ps bi1 BID.ps bi2 parent_cond context_cond];

    if parent_cond then
      let same_name() =
        let b =
          try
            node1#data#get_name = node2#data#get_name &&
            node1#data#get_category <> node2#data#get_category
          with
            _ -> false
        in
        [%debug_log "%B" b];
        b
      in
      let parent_mapped() =
        let b =
          try
            let p1 = node1#initial_parent in
            let p2 = node2#initial_parent in
            nmapping#find p1 == p2 &&
            let p1_eq_p2 = p1#data#eq p2#data in
            p1_eq_p2 && (p1#data#is_sequence || has_uniq_paths p1 p2 node1 node2) ||
            not p1_eq_p2 && p1#data#is_named && p2#data#is_named &&
            not (edits#mem_mov12 p1 p2)
          with
            _ -> false
        in
        [%debug_log "%B" b];
        b
      in
      let b =
        let has_conflict =
          context_cond &&
          (*(non_rename non_rename_bid_tbl1 bi1 || non_rename non_rename_bid_tbl2 bi2)*)
          (non_rename non_rename_bid_tbl1 bi1 &&
           not (
           try
             List.mem bi2 (cenv#tree2#find_mapped_bids (non_rename_bid_map_find1 bi1))
           with _ -> false
           )
          ) ||
          (non_rename non_rename_bid_tbl2 bi2 &&
           not (
           try
             List.mem bi1 (cenv#tree1#find_mapped_bids (non_rename_bid_map_find2 bi2))
           with _ -> false
           )
          )
        in
        if has_conflict then
          [%debug_log "%a-%a: conflicts with exactly matched pair" BID.ps bi1 BID.ps bi2];
        not has_conflict || same_name() || parent_mapped()
      in
      if not b then
        [%debug_log "%a-%a: conflicts with exactly matched pair" BID.ps bi1 BID.ps bi2];
      b
    else
      false
  in

  let has_nearest_mapped_ancestor_upto_boundary n1 n2 =
    [%debug_log "%a-%a" nups n1 nups n2];
    let moveon_ n = not n#data#is_boundary && (n#data#is_named || n#data#is_primary) in
    let find_anc = Sourcecode.find_nearest_mapped_ancestor_node ~moveon_ in
    let b =
      try
        let an1 = find_anc nmapping#mem_dom n1 in
        let an2 = find_anc nmapping#mem_cod n2 in
        let an1' = nmapping#find an1 in
        [%debug_log "%a->%a" nups an1 nups an1'];
        an1' == an2 &&
        (
         (try n1#initial_parent == an1 with _ -> false) ||
         (try n2#initial_parent == an2 with _ -> false)
        )
        (*&&
        (an1#data#eq an2#data(* || an1#data#_stripped_label = an2#data#_stripped_label*))*)
      with _ -> false
    in
    [%debug_log "%B" b];
    b
  in

  (* collect use/free renames *)
  let freq_tbl, _use_rename_tbl1, _use_rename_tbl2,
    free_freq_tbl, _free_rename_tbl1, _free_rename_tbl2
      =
    let filt n1 n2 =
      let b =
        not (Misc.is_cross_boundary nmapping n1 n2) &&
        (
        (
         try
           let p1' = nmapping#find n1#initial_parent in
           p1' == n2#initial_parent ||
           n1#data#_anonymized_label = n2#data#_anonymized_label &&
           p1' == n2#initial_parent#initial_parent
         with _ -> false
        ) ||
        n1#data#_anonymized_label = n2#data#_anonymized_label &&
        (
         (try
           let p2' = nmapping#inv_find n2#initial_parent in
           (*p2' == n1#initial_parent#initial_parent*)
           Misc.has_p_ancestor ~moveon:(fun x -> not x#data#is_boundary) ((==) p2') n1
          with _ -> false
         ) ||
         has_nearest_mapped_ancestor_upto_boundary n1 n2
        )
        )
      in
      [%debug_log "%a-%a: %B" nups n1 nups n2 b];
      b
    in
    collect_use_renames ~filt cenv nmapping edits is_possible_rename
  in
  let get_freq bi1 bi2 =
    let freq, _, _ = Hashtbl.find freq_tbl (bi1, bi2) in
    freq
  in

  (* select use renames *)
  let selected_renames1 = ref [] in
  let selected_renames2 = ref [] in

  let weak_selected_renames1 = ref [] in
  let weak_selected_renames2 = ref [] in

  let conflicting_bids1 = ref [] in
  let conflicting_bids2 = ref [] in

  let loser_tbl = Hashtbl.create 0 in

  let sel_freq max bi1 bi2 =
    try
      let freq = get_freq bi1 bi2 in
      if freq > max then
        freq
      else
        max
    with
      Not_found -> assert false
  in

  let boundary_key_to_string = Comparison.boundary_key_to_string in
  ignore boundary_key_to_string;

  let has_use_rename_cache = Misc.Tbl2.create() in
  let has_use_rename n1 n2 =
    try
      let b = Misc.Tbl2.find has_use_rename_cache n1 n2 in
      [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
      b
    with Not_found ->

    [%debug_log "%a-%a" nups n1 nups n2];
    let has_use1 ?(bkey_opt=None) bi1 bi2 =
      try
        [%debug_log "bids: %a-%a" BID.ps bi1 BID.ps bi2];
        let bkey =
          match bkey_opt with
          | Some k -> k
          | None ->
              let def1 = tree1#find_def_for_bid bi1 in
              let def2 = tree2#find_def_for_bid bi2 in
              [%debug_log "defs: %a-%a" nups def1 nups def2];
              cenv#get_boundary_key def1 def2
        in
        let tbl = Hashtbl.find _use_rename_tbl1 bkey in
        let bs = Hashtbl.find tbl bi1 in
        List.mem bi2 bs
      with _ -> false
    in
    let has_use2 ?(bkey_opt=None) bi1 bi2 =
      try
        [%debug_log "bids: %a-%a" BID.ps bi1 BID.ps bi2];
        let bkey =
          match bkey_opt with
          | Some k -> k
          | None ->
              let def1 = tree1#find_def_for_bid bi1 in
              let def2 = tree2#find_def_for_bid bi2 in
              [%debug_log "defs: %a-%a" nups def1 nups def2];
              cenv#get_boundary_key def1 def2
        in
        let tbl = Hashtbl.find _use_rename_tbl2 bkey in
        let bs = Hashtbl.find tbl bi2 in
        List.mem bi1 bs
      with _ -> false
    in
    let b =
      try
        let bi1 = get_bid n1 in
        let bi2 = get_bid n2 in
        has_use1 ~bkey_opt:(Some (cenv#get_boundary_key n1 n2)) bi1 bi2 ||
        List.exists (fun bi1' -> bi1' <> bi1 && has_use1 bi1' bi2) (tree1#find_mapped_bids bi1) ||
        List.exists (fun bi2' -> bi2' <> bi2 && has_use2 bi1 bi2') (tree2#find_mapped_bids bi2)
      with
        _ -> false
    in
    Misc.Tbl2.add has_use_rename_cache n1 n2 b;
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b
  in
  cenv#set_has_use_rename has_use_rename;

  let _use_rename_tbl1_ = Hashtbl.create 0 in
  let _use_rename_tbl2_ = Hashtbl.create 0 in
  let add_ tbl bi bs_sel_max_freq =
    let bs, sel, max_freq = bs_sel_max_freq in
    try
      let _bs, _sel, _max_freq = Hashtbl.find tbl bi in
      let bs_ = Xlist.union bs _bs in
      let sel_ = Xlist.union sel _sel in
      Hashtbl.replace tbl bi (bs_, sel_, max _max_freq max_freq)
    with Not_found -> Hashtbl.add tbl bi bs_sel_max_freq
  in
  Hashtbl.iter
    (fun boundary_key tbl ->
      let _ = boundary_key in
      [%debug_log "boundary_key=%s" (boundary_key_to_string boundary_key)];
      Hashtbl.iter
        (fun bi1 bs ->
          [%debug_log "* selecting from: %a(\"%s\") -> [%s]"
            BID.ps bi1 (get_bid_name tree1 bi1)
            (Xlist.to_string
               (fun bi2 ->
                 Printf.sprintf "%a(\"%s\")" BID.ps bi2 (get_bid_name tree2 bi2)) ";" bs)];
          let max_freq = List.fold_left (fun max bi2 -> sel_freq max bi1 bi2) 0 bs in
          [%debug_log "  max freq.: %d" max_freq];

          let selected = List.filter (fun bi2 -> get_freq bi1 bi2 = max_freq) bs in
          [%debug_log "  selected: %a(\"%s\") -> [%s]"
            BID.ps bi1 (get_bid_name tree1 bi1)
            (Xlist.to_string
               (fun bi2 ->
                 Printf.sprintf "%a(\"%s\")" BID.ps bi2 (get_bid_name tree2 bi2)) ";" selected)];
          add_ _use_rename_tbl1_ bi1 (bs, selected, max_freq)
        ) tbl
    ) _use_rename_tbl1;

  Hashtbl.iter
    (fun boundary_key tbl ->
      let _ = boundary_key in
      [%debug_log "boundary_key=%s" (boundary_key_to_string boundary_key)];
      Hashtbl.iter
        (fun bi2 bs ->
          [%debug_log "* selecting from: [%s] <- %a(\"%s\")"
            (Xlist.to_string
               (fun bi1 ->
                 Printf.sprintf "%a(\"%s\")" BID.ps bi1 (get_bid_name tree1 bi1)) ";" bs)
            BID.ps bi2 (get_bid_name tree2 bi2)];
          let max_freq = List.fold_left (fun max bi1 -> sel_freq max bi1 bi2) 0 bs in
          [%debug_log "  max freq.: %d" max_freq];

          let selected = List.filter (fun bi1 -> get_freq bi1 bi2 = max_freq) bs in
          [%debug_log "  selected: [%s] <- %a(\"%s\")"
            (Xlist.to_string
               (fun bi1 ->
                 Printf.sprintf "%a(\"%s\")" BID.ps bi1 (get_bid_name tree1 bi1)) ";" selected)
            BID.ps bi2 (get_bid_name tree2 bi2)];
          add_ _use_rename_tbl2_ bi2 (bs, selected, max_freq)
        ) tbl
    ) _use_rename_tbl2;

  Hashtbl.iter
    (fun bi1 (bs, selected, max_freq) ->
      [%debug_log "%a -> [%s] (max_freq=%d)" BID.ps bi1 (Xlist.to_string BID.to_string ";" selected)
        max_freq];
      match selected with
      | []   -> assert false
      | [bi2] -> begin
          if handle_weak || max_freq > 1 then begin
            [%debug_log "added"];
            selected_renames1 := (bi1, bi2) :: !selected_renames1
          end;
          if handle_weak && max_freq = 1 then begin
            [%debug_log "added (weak)"];
            weak_selected_renames1 := (bi1, bi2) :: !weak_selected_renames1
          end;
          List.iter
            (fun bi ->
              if bi != bi2 then
                Hashtbl.add loser_tbl (bi1, bi) true
            ) bs
      end
      | _ -> conflicting_bids2 := selected @ !conflicting_bids2
    ) _use_rename_tbl1_;

  Hashtbl.iter
    (fun bi2 (bs, selected, max_freq) ->
      [%debug_log "[%s] <- %a (max_freq=%d)" (Xlist.to_string BID.to_string ";" selected) BID.ps bi2
        max_freq];
      match selected with
      | []   -> assert false
      | [bi1] -> begin
          if handle_weak || max_freq > 1 then begin
            [%debug_log "added"];
            selected_renames2 := (bi1, bi2) :: !selected_renames2
          end;
          if handle_weak && max_freq = 1 then begin
            [%debug_log "added (weak)"];
            weak_selected_renames2 := (bi1, bi2) :: !weak_selected_renames2
          end;
          List.iter
            (fun bi ->
              if bi != bi1 then
                Hashtbl.add loser_tbl (bi, bi2) true
            ) bs
      end
      | _ -> conflicting_bids1 := selected @ !conflicting_bids1
    ) _use_rename_tbl2_;

  [%debug_log "  conflicting_bids1: %s" (Xlist.to_string BID.to_string ";" !conflicting_bids1)];
  [%debug_log "  conflicting_bids2: %s" (Xlist.to_string BID.to_string ";" !conflicting_bids2)];

  let tree1 = cenv#tree1 in
  let tree2 = cenv#tree2 in

  let selected_renames =
    List.filter
      (fun ((bi1, bi2) as bp) ->
        let no_conflicts1 = not (List.mem bi1 !conflicting_bids1) in
        let no_conflicts2 = not (List.mem bi2 !conflicting_bids2) in
        begin
         try
           let freq, nm1, nm2 = Hashtbl.find freq_tbl bp in
           [%debug_log "%a-%a \"%s\"-\"%s\" %d" BID.ps bi1 BID.ps bi2 nm1 nm2 freq];
           if freq > 1 && (no_conflicts1 || no_conflicts2) then begin
             cenv#add_rename_pat (nm1, nm2);
             List.iter
               (fun bi1_ ->
                 try
                   let nm1_ = tree1#find_name_for_bid bi1_ in
                   [%debug_log "bi1_=%a nm1_=\"%s\"" BID.ps bi1_ nm1_];
                   cenv#add_rename_pat (nm1_, nm2)
                 with
                   _ -> ()
               ) (tree1#find_mapped_bids bi1);
             List.iter
               (fun bi2_ ->
                 try
                   let nm2_ = tree2#find_name_for_bid bi2_ in
                   [%debug_log "bi2_=%a nm2_=\"%s\"" BID.ps bi2_ nm2_];
                   cenv#add_rename_pat (nm1, nm2_)
                 with
                   _ -> ()
               ) (tree2#find_mapped_bids bi2)
           end
          with _ -> ()
        end;
        not (Hashtbl.mem loser_tbl (bi1, bi2)) && no_conflicts1 && no_conflicts2
      ) (Xlist.union !selected_renames1 !selected_renames2)
  in

  let weak_selected_renames =
    Xlist.intersection selected_renames
      (Xlist.union !weak_selected_renames1 !weak_selected_renames2)
  in
  let weak_selected_renames_from, weak_selected_renames_to =
    List.split weak_selected_renames
  in

  (* select free renames *)
  let selected_free_renames1 = ref [] in
  let selected_free_renames2 = ref [] in

  (*let weak_selected_free_renames1 = ref [] in
  let weak_selected_free_renames2 = ref [] in*)

  let conflicting_nms1 = ref [] in
  let conflicting_nms2 = ref [] in

  let free_loser_tbl = Hashtbl.create 0 in

  let get_free_freq nm1 nm2 =
    let freq = Hashtbl.find free_freq_tbl (nm1, nm2) in
    freq
  in

  let sel_free_freq max bi1 bi2 =
    try
      let freq = get_free_freq bi1 bi2 in
      if freq > max then
        freq
      else
        max
    with
      Not_found -> assert false
  in

  Hashtbl.iter
    (fun nm1 nms ->
      [%debug_log "* selecting from: %s -> [%s]" nm1 (Xlist.to_string Fun.id ";" nms)];
      let max_freq = List.fold_left (fun max nm2 -> sel_free_freq max nm1 nm2) 0 nms in
      [%debug_log "  max freq.: %d" max_freq];
      let selected = List.filter (fun nm2 -> max_freq = get_free_freq nm1 nm2) nms in
      [%debug_log "  selected: %s -> [%s]" nm1 (Xlist.to_string Fun.id ";" selected)];
      match selected with
      | []   -> assert false
      | [nm2] -> begin
          if handle_weak || max_freq > 1 then
            selected_free_renames1 := (nm1, nm2) :: !selected_free_renames1;
          (*if handle_weak && max_freq = 1 then
            weak_selected_free_renames1 := (nm1, nm2) :: !weak_selected_free_renames1;*)
          List.iter
            (fun nm ->
              if nm != nm2 then
                Hashtbl.add free_loser_tbl (nm1, nm) true
            ) nms
      end
      | _ -> conflicting_nms2 := nms @ !conflicting_nms2
    ) _free_rename_tbl1;

  Hashtbl.iter
    (fun nm2 nms ->
      [%debug_log "* selecting from: [%s] <- %s" (Xlist.to_string Fun.id ";" nms) nm2];
      let max_freq = List.fold_left (fun max nm1 -> sel_free_freq max nm1 nm2) 0 nms in
      [%debug_log "  max freq.: %d" max_freq];
      let selected = List.filter (fun nm1 -> max_freq = get_free_freq nm1 nm2) nms in
      [%debug_log "  selected: [%s] <- %s" (Xlist.to_string Fun.id ";" selected) nm2];
      match selected with
      | []   -> assert false
      | [nm1] -> begin
          if max_freq > 1 || handle_weak then
            selected_free_renames2 := (nm1, nm2) :: !selected_free_renames2;
          (*if max_freq = 1 && handle_weak then
            weak_selected_free_renames2 := (nm1, nm2) :: !weak_selected_free_renames2;*)
          List.iter
            (fun nm ->
              if nm != nm1 then
                Hashtbl.add free_loser_tbl (nm, nm2) true
            ) nms
      end
      | _ -> conflicting_nms1 := nms @ !conflicting_nms1
    ) _free_rename_tbl2;

  [%debug_log "  conflicting_nms1: %s" (Xlist.to_string Fun.id ";" !conflicting_nms1)];
  [%debug_log "  conflicting_nms2: %s" (Xlist.to_string Fun.id ";" !conflicting_nms2)];

  let selected_free_renames =
    List.filter
      (fun ((nm1, nm2) as nmp) ->
        let no_conflicts1 = not (List.mem nm1 !conflicting_nms1) in
        let no_conflicts2 = not (List.mem nm2 !conflicting_nms2) in
        begin
         try
           let freq = Hashtbl.find free_freq_tbl nmp in
           [%debug_log "\"%s\"-\"%s\" %d" nm1 nm2 freq];
           if (freq > 1 || nm1 = nm2) && (no_conflicts1 || no_conflicts2) then
             cenv#add_rename_pat nmp
          with _ -> ()
        end;
        not (Hashtbl.mem free_loser_tbl nmp) && no_conflicts1 && no_conflicts2
      ) (Xlist.union !selected_free_renames1 !selected_free_renames2)
  in

  (*let weak_selected_free_renames =
    Xlist.intersection selected_free_renames
      (Xlist.union !weak_selected_free_renames1 !weak_selected_free_renames2)
  in*)

  begin %debug_block
    [%debug_log "* selected use renames:"];
    List.iter
      (fun (bi1, bi2) ->
        [%debug_log " %a -> %a (\"%s\" -> \"%s\")" BID.ps bi1 BID.ps bi2
          (get_bid_name tree1 bi1) (get_bid_name tree2 bi2)]
      ) selected_renames;
    [%debug_log "* weakly selected use renames:"];
    List.iter
      (fun (bi1, bi2) ->
        [%debug_log " %a -> %a (\"%s\" -> \"%s\")" BID.ps bi1 BID.ps bi2
          (get_bid_name tree1 bi1) (get_bid_name tree2 bi2)]
      ) weak_selected_renames;
    [%debug_log "* selected free renames:"];
    List.iter
      (fun (nm1, nm2) ->
        [%debug_log " \"%s\" -> \"%s\"" nm1 nm2]
      ) selected_free_renames;
    (*[%debug_log "* weakly selected free renames:"];
    List.iter
      (fun (nm1, nm2) ->
        [%debug_log " \"%s\" -> \"%s\"" nm1 nm2]
      ) weak_selected_free_renames*)
  end;

  begin
    [%debug_log "checking rename patterns..."];
    let rename_pat_tbl = Hashtbl.create 0 in
    List.iter
      (fun l ->
        List.iter
          (fun bp ->
            try
              let freq, nm1, nm2 = Hashtbl.find freq_tbl bp in
              let nmp = nm1, nm2 in
              try
                let c = Hashtbl.find rename_pat_tbl nmp in
                Hashtbl.replace rename_pat_tbl nmp (c+freq)
              with
                Not_found -> Hashtbl.add rename_pat_tbl nmp freq
            with
              _ -> ()
          ) l
      ) [selected_renames(*; weak_selected_renames*)];
    List.iter
      (fun l ->
        List.iter
          (fun nmp ->
            try
              let freq = Hashtbl.find free_freq_tbl nmp in
              try
                let c = Hashtbl.find rename_pat_tbl nmp in
                Hashtbl.replace rename_pat_tbl nmp (c+freq)
              with
                Not_found -> Hashtbl.add rename_pat_tbl nmp freq
            with
              _ -> ()
          ) l
      ) [selected_free_renames(*; weak_selected_free_renames*)];
    Hashtbl.iter
      (fun ((nm1, nm2) as nmp) c ->
        let _ = nm1 in
        let _ = nm2 in
        [%debug_log "\"%s\"->\"%s\" %d" nm1 nm2 c];
        if c > 1 then
          cenv#add_rename_pat nmp
      ) rename_pat_tbl;
    [%debug_log "done."]
  end;

  cenv#finalize_rename_pat();

  let rename_tbl1 = Hashtbl.create 0 in
  let rename_tbl2 = Hashtbl.create 0 in
  List.iter
    (fun (bi1, bi2) ->
      Hashtbl.add rename_tbl1 bi1 bi2;
      Hashtbl.add rename_tbl2 bi2 bi1;
    ) selected_renames;

  let is_good_relabel nd1 nd2 =
    [%debug_log "%a-%a" nups nd1 nups nd2];
    try
      let chk n1 n2 =
        n1#data#relabel_allowed n2#data &&
        try
          nmapping#find n1 == n2
        with
          Not_found -> not (nmapping#mem_cod n2)
      in
      let pnd1 = nd1#initial_parent in
      let pnd2 = nd2#initial_parent in

      let parent_cond = chk pnd1 pnd2 in

      let chka a1 a2 =
        let l1 = Array.to_list a1 in
        let l2 = Array.to_list a2 in
        List.for_all2 chk l1 l2
      in
      let children_cond =
        let ca1 = nd1#initial_children in
        let ca2 = nd2#initial_children in
        let sz1 = Array.length ca1 in
        let sz2 = Array.length ca2 in
        [%debug_log "sz1=%d sz2=%d" sz1 sz2];
        if sz1 = sz2 then
          if sz1 = 0 then
            let a1 = pnd1#initial_children in
            let a2 = pnd2#initial_children in
            let asz1 = Array.length a1 in
            let asz2 = Array.length a2 in
            [%debug_log "asz1=%d asz2=%d" asz1 asz2];
            if asz1 = asz2 then
              chka a1 a2
            else if asz1 = 1 || asz2 = 1 then
              true
            else
              (*false*)
              try
                Array.iter
                  (fun s1 ->
                    if
                      s1 != nd1 &&
                      Array.exists (fun s2 -> s2 != nd2 && chk s1 s2) a2
                    then
                      raise Exit
                  ) a1;
                false
              with
                Exit -> true
          else
            chka ca1 ca2
        (*else if sz1 = 0 || sz2 = 0 then
          true!!!NG!!!*)
        else if
          is_def nd1 && is_def nd2 &&
          (sz1 = 0 && sz2 = 1 || sz1 = 1 && sz2 = 0)
        then
          true
        else
          false
      in
      [%debug_log "parent_cond=%B children_cond=%B" parent_cond children_cond];
      nd1#data#relabel_allowed nd2#data && parent_cond && children_cond
    with
      Otree.Parent_not_found _ -> false
  in

  let is_incompatible nd1 nd2 =
    let pnd1 = nd1#initial_parent in
    let pnd2 = nd2#initial_parent in
    let context_cond = try nmapping#find pnd1 == pnd2 with _ -> false in
    [%debug_log "%a-%a context_cond=%B" nups nd1 nups nd2 context_cond];
    (*let is_stable = not (edits#mem_mov12 nd1 nd2) in
    [%debug_log "%a-%a is_stable=%B" nups nd1 nups nd2 is_stable];*)

    let same_name =
      try
        nd1#data#get_name = nd2#data#get_name && nd1#data#get_category <> nd2#data#get_category
      with
        _ -> false
    in
    let bi1_opt, non_rename1, bi1'_opt =
      try
        let bi1 = get_bid nd1 in
        [%debug_log "bi1=%a" BID.ps bi1];
        let non_rename1 = non_rename non_rename_bid_tbl1 bi1 in
        [%debug_log "non_rename1=%B" non_rename1];
        try
          let bi1' = Hashtbl.find rename_tbl1 bi1 in
          [%debug_log "bi1'=%a" BID.ps bi1'];
          Some bi1, non_rename1, Some bi1'
        with
          Not_found -> Some bi1, non_rename1, None
      with
        Not_found -> None, false, None
    in
    let bi2_opt, non_rename2, bi2'_opt =
      try
        let bi2 = get_bid nd2 in
        [%debug_log "bi2=%a" BID.ps bi2];
        let non_rename2 = non_rename non_rename_bid_tbl2 bi2 in
        [%debug_log "non_rename2=%B" non_rename2];
        try
          let bi2' = Hashtbl.find rename_tbl2 bi2 in
          [%debug_log "bi2'=%a" BID.ps bi2'];
          Some bi2, non_rename2, Some bi2'
        with
          Not_found -> Some bi2, non_rename2, None
      with
        Not_found -> None, false, None
    in
    let b, by_non_renames =
      let context_cond_ = context_cond(* || is_stable*) in
      match bi1_opt, bi2_opt with
      | Some bi1, Some bi2 -> begin
          [%debug_log "bi1=%a bi2=%a" BID.ps bi1 BID.ps bi2];
          if non_rename1 && non_rename2 && not same_name then begin
            [%debug_log "@"];
            true, true
          end
          else if (non_rename1 || non_rename2) && not same_name then
            context_cond_, true
          (*!20240521!else if
            context_cond_ && List.mem (bi1, bi2) selected_renames
          then
            false, false*)
          else if
            context_cond_ &&
            not non_rename1 && not non_rename2 &&
            match bi1'_opt, bi2'_opt with
            | Some bi1', Some bi2' -> bi1' = bi2 && bi2' = bi1
            | _ -> false
          then
            false, false
          else
            context_cond_ &&
            (
             not (List.mem bi1 weak_selected_renames_from) &&
             not (List.mem bi2 weak_selected_renames_to)
            )(* &&
            (
              (match bi1'_opt with Some bi1' -> bi2 <> bi1' | None -> false) ||
              (match bi2'_opt with Some bi2' -> bi1 <> bi2' | None -> false)
            )*), false
      end
      | Some _, None when nd2#data#is_literal -> false, false
      | None, Some _ when nd1#data#is_literal -> false, false

      | Some bi1, None ->
          let _ = bi1 in
          [%debug_log "bi1=%a bi2=None" BID.ps bi1];
          context_cond_ &&
          (non_rename1 || (match bi1'_opt with Some _ -> true | None -> false)), non_rename1

      | None, Some bi2 ->
          let _ = bi2 in
          [%debug_log "bi1=None bi2=%a" BID.ps bi2];
          context_cond_ &&
          (non_rename2 || (match bi2'_opt with Some _ -> true | None -> false)), non_rename2

      | None, None ->
          false, false
    in
    [%debug_log "%a-%a: b=%B by_non_renames=%B" nups nd1 nups nd2 b by_non_renames];
    b, by_non_renames
  in (* is_incompatible *)


  let is_incompatible_def n1 n2 =
    let b =
      is_def n1 && is_def n2 &&
      try
        let bi1 = get_bid n1 in
        let bi2 = get_bid n2 in
        Hashtbl.find rename_tbl1 bi1 <> bi2
      with
        Not_found -> false
    in
    [%debug_log "%s-%s --> %B" n1#data#to_string n2#data#to_string b];
    b
  in (* is_incompatible_def *)
  (*let is_incompatible_use n1 n2 =
    let b =
      B.is_use n1#data#binding && B.is_use n2#data#binding &&
      try
        let bi1 = get_bid n1 in
        let bi2 = get_bid n2 in
        Hashtbl.find rename_tbl1 bi1 <> bi2
      with
        Not_found -> true
    in
    [%debug_log "%s-%s --> %B" n1#data#to_string n2#data#to_string b];
    b
  in (* is_incompatible_use *)*)

  [%debug_log "* finding incompatible relabels..."];

  let to_be_removed = ref [] in

  let remove_from_rename_tbls n1 n2 =
    try
      let bi1 = get_bid n1 in
      let bi2 = get_bid n2 in
      [%debug_log "%a-%a" BID.ps bi1 BID.ps bi2];
      if try Hashtbl.find rename_tbl1 bi1 = bi2 with _ -> false then
        Hashtbl.remove rename_tbl1 bi1;
      if try Hashtbl.find rename_tbl2 bi2 = bi1 with _ -> false then
        Hashtbl.remove rename_tbl2 bi2
    with _ -> ()
  in

  let good1 = Xset.create 0 in
  let good2 = Xset.create 0 in

  edits#iter_relabels (* find incompatible relabels *)
    (function
      | Relabel(_, (info1, _), (info2, _)) as rel -> begin
          let _ = rel in
          [%debug_log "finding incompatible relabels: checking %a-%a"
            nups (Info.get_node info1) nups (Info.get_node info2)];

          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          let incompat, by_non_renames = is_incompatible nd1 nd2 in
          if incompat then begin
            [%debug_log "incompatible relabel%s: %s"
              (if by_non_renames then "[by non-renames]" else "") (Editop.to_string rel)];
            let is_good = is_good_relabel nd1 nd2 in
            if is_good then begin
              if
                nd1#data#is_order_insensitive && nd2#data#is_order_insensitive &&
                nd1#initial_nchildren = 0 && nd2#initial_nchildren = 0
              ||
                is_incompatible_def nd1 nd2
              then begin
                [%debug_log "not so good relabel: %a-%a" nups nd1 nups nd2];
                to_be_removed := (nd1, nd2, by_non_renames) :: !to_be_removed;
                remove_from_rename_tbls nd1 nd2
              end
              else begin
                [%debug_log "good relabel"];
                if is_use nd1 && is_use nd2 then begin
                  Xset.add good1 nd1;
                  Xset.add good2 nd2
                end
              end
            end
            else begin
              [%debug_log "bad relabel: %a-%a" nups nd1 nups nd2];
              to_be_removed := (nd1, nd2, by_non_renames) :: !to_be_removed;
              remove_from_rename_tbls nd1 nd2
            end
          end
          (*else if is_incompatible_use nd1 nd2 then begin
            [%debug_log "incompatible relabel (USE): %s" (Editop.to_string rel)];
            to_be_removed := (nd1, nd2, by_non_renames) :: !to_be_removed;
            remove_from_rename_tbls nd1 nd2
          end*)
          (*else if is_incompatible_def nd1 nd2 then begin
            [%debug_log "incompatible relabel (DEF): %s" (Editop.to_string rel)];
            to_be_removed := (nd1, nd2, by_non_renames) :: !to_be_removed;
          end*)
      end
      | _ -> assert false
    );

  [%debug_log "* removing incompatible relabels and mappings..."];

  remove_relabels_and_mapping cenv edits nmapping !to_be_removed;

  [%debug_log "* finding compatible pairs..."];

  let cands_pair_tbl = Hashtbl.create 0 in (* (bid * bid) -> node list * node list *)

  let subtree_eq n1 n2 =
    let b = n1#data#_digest <> None && n1#data#subtree_equals n2#data in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b
  in

  let check_tbl1 nd =
    [%debug_log "%a" nups nd];
    if not (Xset.mem good1 nd) then
      let bid = get_bid nd in
      [%debug_log "bid=%a" BID.ps bid];
      if
        Hashtbl.mem rename_tbl1 bid &&
        not
          (
           is_def nd &&
           non_rename non_rename_bid_tbl1 bid &&
           subtree_eq nd (nmapping#find nd)
          )
      then begin
        let bid_ = Hashtbl.find rename_tbl1 bid in
        [%debug_log "%a -> %a" BID.ps bid BID.ps bid_];
        let key = bid, bid_ in
        try
          let cands1, cands2 = Hashtbl.find cands_pair_tbl key in
          if not (List.memq nd cands1) then
            Hashtbl.replace cands_pair_tbl key ((nd::cands1), cands2)
        with
          Not_found ->
            Hashtbl.add cands_pair_tbl key ([nd], [])
      end
  in
  let check_tbl2 nd =
    [%debug_log "%a" nups nd];
    if not (Xset.mem good2 nd) then
      let bid = get_bid nd in
      [%debug_log "bid=%a" BID.ps bid];
      if
        Hashtbl.mem rename_tbl2 bid &&
        not
          (
           is_def nd &&
           non_rename non_rename_bid_tbl2 bid &&
           subtree_eq (nmapping#inv_find nd) nd
          )
      then begin
        let _bid = Hashtbl.find rename_tbl2 bid in
        [%debug_log "%a -> %a" BID.ps _bid BID.ps bid];
        let key = _bid, bid in
        try
          let cands1, cands2 = Hashtbl.find cands_pair_tbl key in
          if not (List.memq nd cands2) then
            Hashtbl.replace cands_pair_tbl key (cands1, (nd::cands2))
        with
          Not_found ->
            Hashtbl.add cands_pair_tbl key ([], [nd])
      end
  in
  let check check_tbl info =
    let nd = Info.get_node info in
    Array.iter
      (fun filt ->
        try
          if filt nd then
            check_tbl nd
        with
          Not_found -> ()
      ) filters
  in

  edits#iter_deletes
    (function
      | Delete(_, info, _) -> check check_tbl1 info
      | _ -> assert false
    );
  edits#iter_inserts
    (function
      | Insert(_, info, _) -> check check_tbl2 info
      | _ -> assert false
    );
  edits#iter_relabels
    (function
      | Relabel(_, (info1, _), (info2, _)) -> begin
          check check_tbl1 info1;
          check check_tbl2 info2
      end
      | _ -> assert false
    );
  nmapping#iter
    (fun n1 n2 ->
      Array.iter
        (fun filt ->
          try
            if filt n1 && filt n2 then begin
              check_tbl1 n1;
              check_tbl2 n2
            end
          with
            Not_found -> ()
        ) filters
    );

  begin %debug_block
    [%debug_log "cands pair table:"];
    Hashtbl.iter
      (fun (bid1, bid2) (cands1, cands2) ->
        [%debug_log "  (%a,%a) [%a]-[%a]" BID.ps bid1 BID.ps bid2 nugsps cands1 nugsps cands2]
      ) cands_pair_tbl
  end;

  (* select compatible pairs *)
  let compatible_pairs = ref [] in
  Hashtbl.iter
    (fun (bid1, bid2) (cands1, cands2) ->
      let _ = bid1 in
      let _ = bid2 in
      [%debug_log "%a-%a: ncands1=%d ncands2=%d"
        BID.ps bid1 BID.ps bid2 (List.length cands1) (List.length cands2)];
      let filt n1 n2 =
        (n1#data#eq n2#data || n1#data#relabel_allowed n2#data) &&
        let is_def1 = is_def n1 in
        let is_def2 = is_def n2 in
        let is_use1 = is_use n1 in
        let is_use2 = is_use n2 in
        is_def1 && is_def2 || is_use1 && is_use2 ||
        not is_def1 && not is_def2 && not is_use1 && not is_use2
      in
      compatible_pairs := (combine_node_lists ~filt cenv nmapping cands1 cands2) @ !compatible_pairs

    ) cands_pair_tbl;

  begin %debug_block
    List.iter
      (fun (n1, n2) ->
        [%debug_log "compatible_pair: %a-%a (%a-%a)"
          nups n1 nups n2 GI.ps n1#gindex GI.ps n2#gindex]
      )
      (List.fast_sort
         (fun (n1, _) (n2, _) -> Stdlib.compare n1#gindex n2#gindex)
         !compatible_pairs);
     Hashtbl.iter (fun b1 b2 -> [%debug_log "rename_tbl1: %a->%a" BID.ps b1 BID.ps b2]) rename_tbl1;
     Hashtbl.iter (fun b2 b1 -> [%debug_log "rename_tbl2: %a<-%a" BID.ps b1 BID.ps b2]) rename_tbl2
  end;

  (*[%debug_log "* generating compatible edits..."];
  let nrels =
    generate_compatible_edits options cenv nmapping edits
      !compatible_pairs is_incompatible
  in
  [%debug_log "* %d relabels generated." nrels];*)

  [%debug_log "* locking relabels..."];

  edits#iter_relabels (* lock relabels *)
    (function
      | Relabel(_, (info1, _), (info2, _)) -> begin
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in

          [%debug_log "relabel %a-%a (%a-%a)" nups nd1 nups nd2 GI.ps nd1#gindex GI.ps nd2#gindex];

          let is_final () =
            let b =
              (try
                match cenv#multiple_node_matches#find nd1#data#_label with
                | [_], [_] -> true
                | ns11, ns12 -> begin
                    let _ = ns11 in
                    let _ = ns12 in
                    [%debug_log "ns11=[%a] ns12=[%a]" nsps ns11 nsps ns12];
                    false
                end
              with
                _ -> true) &&
              (try
                match cenv#multiple_node_matches#find nd2#data#_label with
                | [_], [_] -> true
                | ns21, ns22 -> begin
                    let _ = ns21 in
                    let _ = ns22 in
                    [%debug_log "ns21=[%a] ns22=[%a]" nsps ns21 nsps ns22];
                    false
                end
              with
                _ -> true)
            in
            [%debug_log "%B" b];
            b
          in

          let use_flag = is_use nd1 && is_use nd2 in
          let def_flag = is_def nd1 && is_def nd2 in

          [%debug_log "use_flag=%B def_flag=%B" use_flag def_flag];

          if
            use_flag ||
            (def_flag &&
             (
              nd1#data#_anonymized_label = nd2#data#_anonymized_label ||
              B.is_local_def nd1#data#binding = B.is_local_def nd2#data#binding
             )
            )
          then begin
            let bid1 = get_bid nd1 in
            let bid2 = get_bid nd2 in
            [%debug_log "%s vs %s" (B.to_string nd1#data#binding) (B.to_string nd2#data#binding)];
            try
              let bid1' = Hashtbl.find rename_tbl1 bid1 in
              let lock, final =
                if bid1' = bid2 then
                  match Hashtbl.find cands_pair_tbl (bid1, bid2) with
                  | [], _ | _, [] -> false, false
                  | [n1], [n2] -> begin
                      [%debug_log "nds1=[%a] nds2=[%a]" nups n1 nups n2];
                      if
                        use_flag && is_use n1 && is_use n2 ||
                        def_flag && is_def n1 && is_def n2
                      then
                        true, is_final()
                      else
                        false, false
                  end
                  | nds1, nds2 -> begin
                      [%debug_log "nds1=[%a] nds2=[%a]" nsps nds1 nsps nds2];
                      let b =
                        is_final() &&
                        if use_flag then
                          let uses1 = List.filter is_use nds1 in
                          let uses2 = List.filter is_use nds2 in
                          [%debug_log "uses1=[%a] uses2=[%a]" nsps uses1 nsps uses2];
                          match uses1, uses2 with
                          | [_], [_] -> true
                          | _ -> false
                        else if def_flag then
                          let defs1 = List.filter is_def nds1 in
                          let defs2 = List.filter is_def nds2 in
                          [%debug_log "defs1=[%a] defs2=[%a]" nsps defs1 nsps defs2];
                          match defs1, defs2 with
                          | [_], [_] -> true
                          | _ -> false
                        else
                          false
                      in
                      b, b
                  end
                else
                  false, false
              in
              [%debug_log "lock=%B final=%B" lock final];
              if lock then begin
                lock_mapping tree1 tree2 nmapping nd1 nd2;
                if final then
                  nmapping#finalize_mapping nd1 nd2
              end
            with
              Not_found -> ()
          end

      end
      | _ -> assert false
    );

  [%debug_log "* generating compatible edits..."];
  let nrels =
    generate_compatible_edits options cenv nmapping edits
      !compatible_pairs is_incompatible
  in
  [%debug_log "* %d relabels generated." nrels];

  List.iter
    (fun (n1, n2) ->
      [%debug_log "%s - %s" n1#data#to_string n2#data#to_string];
      nmapping#add_starting_pair_for_glueing (n1, n2)
    ) !compatible_pairs;

(*
  let rename_tbl1 = Hashtbl.create 0 in
  let rename_tbl2 = Hashtbl.create 0 in
  edits#iter_relabels
    (function
      | Relabel(_, (u1, info1, ex1), (u2, info2, ex2)) -> begin
          let n1 = Info.get_node info1 in
          let n2 = Info.get_node info2 in
          try
            let bi1 = get_bid n1 in
            let bi2 = get_bid n2 in
            [%debug_log "adding %a-%a" BID.ps bi1 BID.ps bi2];
            Hashtbl.add rename_tbl1 bi1 bi2;
            Hashtbl.add rename_tbl2 bi2 bi1
          with
            Not_found -> ()
      end
      | _ -> assert false
    );
*)
  cenv#set_is_possible_rename
    (fun ?(strict=false) n1 n2 ->
      [%debug_log "is_possible_rename: strict=%B %a-%a" strict nups n1 nups n2];
      let bi1_opt = try Some (get_bid n1) with Not_found -> None in
      let bi2_opt = try Some (get_bid n2) with Not_found -> None in
      match bi1_opt, bi2_opt with
      | Some bi1, Some bi2 -> begin
          [%debug_log "bi1=%a bi2=%a" BID.ps bi1 BID.ps bi2];
          if Hashtbl.mem rename_tbl1 bi1 then begin
            let bi1' = Hashtbl.find rename_tbl1 bi1 in
            [%debug_log "%a->%a" BID.ps bi1 BID.ps bi1'];
            bi1' = bi2 ||
            (not strict || not (Hashtbl.mem rename_tbl2 bi2)) && is_possible_rename cenv n1 n2 bi1 bi2
          end
          else if Hashtbl.mem rename_tbl2 bi2 then begin
            let bi2' = Hashtbl.find rename_tbl2 bi2 in
            [%debug_log "%a<-%a" BID.ps bi2' BID.ps bi2];
            bi2' = bi1 ||
            (not strict || not (Hashtbl.mem rename_tbl1 bi1)) && is_possible_rename cenv n1 n2 bi1 bi2
          end
          else
            is_possible_rename cenv n1 n2 bi1 bi2
      end
      | Some bi1, None -> begin
          [%debug_log "bi1=%a" BID.ps bi1];
          (*not strict || !!!NG!!!*)
          not (non_rename non_rename_bid_tbl1 bi1) && not (Hashtbl.mem rename_tbl1 bi1) ||
          is_possible_rename cenv n1 n2 bi1 BID.dummy
      end
      | None, Some bi2 -> begin
          [%debug_log "bi2=%a" BID.ps bi2];
          (*not strict || !!!NG!!!*)
          not (non_rename non_rename_bid_tbl2 bi2) && not (Hashtbl.mem rename_tbl2 bi2) ||
          is_possible_rename cenv n1 n2 BID.dummy bi2
      end
      | None, None -> true
    );


  [%debug_log "FINISHED!"];

  nrels > 0

(* end of func rectify_renames_u *)
]

[%%capture_path
let rectify_renames_d
    options
    (cenv : (node_t, tree_t) Comparison.c)
    nmapping
    edits
    =
  let rrlv = options#rename_rectification_level in
  let strict_flag = rrlv >= 3 in
  let cands_thresh = 128 in

  [%debug_log "START! (rrlv=%d, strict_flag=%B, cands_thresh=%d)"
    rrlv strict_flag cands_thresh];

  let def_pair_list = ref [] in

  let def_bid_tbl1 = Hashtbl.create 0 in
  let def_bid_tbl2 = Hashtbl.create 0 in

  let def_use_tbl1 = Nodetbl.create 0 in
  let def_use_tbl2 = Nodetbl.create 0 in

  let visited1 = Xset.create 0 in

  let non_rename_bids1 = Xset.create 0 in
  let non_rename_bids2 = Xset.create 0 in

  let tbl_add tbl def use =
    try
      let ul = Nodetbl.find tbl def in
      Nodetbl.replace tbl def (use::ul)
    with
      Not_found -> Nodetbl.add tbl def [use]
  in

  (*edits#iter_relabels
    (function
      | Relabel(_, (info1, _), (info2, _)) -> begin
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          if is_def nd1 && is_def nd2 then begin
            def_pair_list := (nd1, nd2) :: !def_pair_list;
            Hashtbl.add def_bid_tbl1 (get_bid nd1) nd1;
            Hashtbl.add def_bid_tbl2 (get_bid nd2) nd2
          end
      end
      | _ -> assert false
    );*)
  nmapping#iter
    (fun nd1 nd2 ->
      if
        not nd1#data#is_common && not nd2#data#is_common &&
        is_def nd1 && is_def nd2
      then begin
        def_pair_list := (nd1, nd2) :: !def_pair_list;
        let bid1 = get_bid nd1 in
        let bid2 = get_bid nd2 in
        Hashtbl.add def_bid_tbl1 bid1 nd1;
        Hashtbl.add def_bid_tbl2 bid2 nd2;
        [%debug_log "def_bid_tbl1: %a -> %a" nups nd1 BID.ps bid1];
        [%debug_log "def_bid_tbl2: %a -> %a" nups nd2 BID.ps bid2];
        if not (edits#mem12 nd1 nd2) then begin
          [%debug_log "non rename def mapping: %a-%a" nps nd1 nps nd2];
          Xset.add non_rename_bids1 bid1;
          Xset.add non_rename_bids2 bid2
        end
      end
    );
  [%debug_log "@"];
  edits#iter_deletes
    (function
      | Delete(_, info1, _) -> begin
          let nd1 = Info.get_node info1 in
          if is_def nd1 then begin
            let bid1 = get_bid nd1 in
            [%debug_log "def_bid_tbl1: %a -> %a" nups nd1 BID.ps bid1];
            Hashtbl.add def_bid_tbl1 bid1 nd1
          end
      end
      | _ -> ()
    );
  edits#iter_inserts
    (function
      | Insert(_, info2, _) -> begin
          let nd2 = Info.get_node info2 in
          if is_def nd2 then begin
            let bid2 = get_bid nd2 in
            [%debug_log "def_bid_tbl2: %a -> %a" nups nd2 BID.ps bid2];
            Hashtbl.add def_bid_tbl2 bid2 nd2
          end
      end
      | _ -> assert false
    );
  [%debug_log "@"];
  edits#iter_relabels
    (function
      | Relabel(_, (info1, _), (info2, _)) -> begin
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          if is_use nd1 && is_use nd2 then begin
            let bid1 = get_bid nd1 in
            let bid2 = get_bid nd2 in
            [%debug_log "%a(%a)-%a(%a)" nups nd1 BID.ps bid1 nups nd2 BID.ps bid2];
            begin
              try
                let def1 = Hashtbl.find def_bid_tbl1 bid1 in
                [%debug_log "def_use_tbl1: %a -> %a" nups def1 nups nd1];
                tbl_add def_use_tbl1 def1 nd1;
                Xset.add visited1 nd1
              with
                Not_found -> ()
            end;
            begin
              try
                let def2 = Hashtbl.find def_bid_tbl2 bid2 in
                [%debug_log "def_use_tbl2: %a -> %a" nups def2 nups nd2];
                tbl_add def_use_tbl2 def2 nd2;
              with
                Not_found -> ()
            end
          end
      end
      | _ -> assert false
    );
  edits#iter_deletes
    (function
      | Delete(_, info1, _) -> begin
          let nd1 = Info.get_node info1 in
          if is_use nd1 then begin
            let bid1 = get_bid nd1 in
            try
              let def1 = Hashtbl.find def_bid_tbl1 bid1 in
              tbl_add def_use_tbl1 def1 nd1;
              Xset.add visited1 nd1
            with
              Not_found -> ()
          end
      end
      | _ -> assert false
    );
  edits#iter_inserts
    (function
      | Insert(_, info2, _) -> begin
          let nd2 = Info.get_node info2 in
          if is_use nd2 then begin
            let bid2 = get_bid nd2 in
            try
              let def2 = Hashtbl.find def_bid_tbl2 bid2 in
              tbl_add def_use_tbl2 def2 nd2
            with
              Not_found -> ()
          end
      end
      | _ -> assert false
    );
  edits#iter_moves
    (function
      | Move(_, _, (info1, _), (info2, _)) -> begin
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          if is_use nd1 && is_use nd2 then begin
            let bid1 = get_bid nd1 in
            let bid2 = get_bid nd2 in
            begin
              try
                let def1 = Hashtbl.find def_bid_tbl1 bid1 in
                tbl_add def_use_tbl1 def1 nd1;
                Xset.add visited1 nd1
              with
                Not_found -> ()
            end;
            begin
              try
                let def2 = Hashtbl.find def_bid_tbl2 bid2 in
                tbl_add def_use_tbl2 def2 nd2;
              with
                Not_found -> ()
            end
          end
      end
      | _ -> assert false
    );
  [%debug_log "@"];
  let find_def tree def_bid_tbl bid =
    [%debug_log "%a" BID.ps bid];
    let def =
      try
        Hashtbl.find def_bid_tbl bid
      with _ -> tree#find_def_for_bid bid
    in
    [%debug_log "def=%a" nups def];
    def
  in
  [%debug_log "@"];
  nmapping#iter
    (fun nd1 nd2 ->
      if not (Xset.mem visited1 nd1) then begin
        if is_use nd1 then begin
          try
            let bid1 = get_bid nd1 in
            let def1 = find_def cenv#tree1 def_bid_tbl1 bid1 in
            [%debug_log "def_use_tbl1: %a -> %a" nups def1 nups nd1];
            tbl_add def_use_tbl1 def1 nd1
          with
            Not_found -> ()
        end;
        if is_use nd2 then begin
          try
            let bid2 = get_bid nd2 in
            let def2 = find_def cenv#tree2 def_bid_tbl2 bid2 in
            [%debug_log "def_use_tbl2: %a -> %a" nups def2 nups nd2];
            tbl_add def_use_tbl2 def2 nd2
          with
            Not_found -> ()
        end
      end
    );
  let get_use_list1 def1 = try Nodetbl.find def_use_tbl1 def1 with _ -> [] in
  let get_use_list2 def2 = try Nodetbl.find def_use_tbl2 def2 with _ -> [] in
  [%debug_log "@"];
  let def_bid_map1 = Hashtbl.create 0 in
  let def_bid_map2 = Hashtbl.create 0 in
  let pairs_to_be_removed = ref [] in
  let to_be_mapped = ref [] in
  List.iter
    (fun (def1, def2) ->
      [%debug_log "[def rename] %a-%a" nps def1 nps def2];
      let bid1 = get_bid def1 in
      let bid2 = get_bid def2 in
      [%debug_log "             %a-%a" BID.ps bid1 BID.ps bid2];

      let use_rename_count = ref 0 in
      let delete_list = ref [] in
      let insert_list = ref [] in
      let conflicting_mapping_list1 = ref [] in
      let conflicting_mapping_list2 = ref [] in
      let use_renames1 = ref [] in
      let use_renames2 = ref [] in

      let use_list1 = get_use_list1 def1 in
      let use_list1 = List.fast_sort (fun x y -> Stdlib.compare y#gindex x#gindex) use_list1 in
      List.iter
        (fun use1 ->
          try
            let use1' = nmapping#find use1 in
            let bid1' = get_bid use1' in
            if bid1' = bid2 then begin
              [%debug_log "use rename: %a-%a" nps use1 nps use1'];
              use_renames1 := use1 :: !use_renames1;
              use_renames2 := use1' :: !use_renames2;
              incr use_rename_count
            end
            else begin
              [%debug_log "use mapping1: %a-%a" nps use1 nps use1'];
              [%debug_log "            : %a-%a" BID.ps bid1 BID.ps bid1'];
              conflicting_mapping_list1 := (use1, use1') :: !conflicting_mapping_list1
            end
          with Not_found -> begin
            [%debug_log "use delete: %a" nps use1];
            delete_list := use1 :: !delete_list
          end
        ) use_list1;

      let use_list2 = get_use_list2 def2 in
      let use_list2 = List.fast_sort (fun x y -> Stdlib.compare y#gindex x#gindex) use_list2 in
      List.iter
        (fun use2 ->
          try
            let use2' = nmapping#inv_find use2 in
            let bid2' = get_bid use2' in
            if bid2' <> bid1 then begin
              [%debug_log "use mapping2: %a-%a" nps use2' nps use2];
              [%debug_log "            : %a-%a" BID.ps bid2' BID.ps bid2];
              conflicting_mapping_list2 := (use2', use2) :: !conflicting_mapping_list2
            end
          with Not_found -> begin
            [%debug_log "use insert: %a" nps use2];
            insert_list := use2 :: !insert_list
          end
        ) use_list2;

      let use_delete_count = List.length !delete_list in
      let use_insert_count = List.length !insert_list in
      let conflicting_use_mapping_count1 = List.length !conflicting_mapping_list1 in
      let conflicting_use_mapping_count2 = List.length !conflicting_mapping_list2 in

      [%debug_log "use_rename_count=%d" !use_rename_count];
      [%debug_log "use_delete_count=%d use_insert_count=%d" use_delete_count use_insert_count];
      [%debug_log "conflicting_use_mapping_count1=%d" conflicting_use_mapping_count1];
      [%debug_log "conflicting_use_mapping_count2=%d" conflicting_use_mapping_count2];

      let local_def_flag = B.is_local_def def1#data#binding && B.is_local_def def2#data#binding in
      [%debug_log "local_def_flag=%B" local_def_flag];

      let compatible_scope_flag = Misc.is_scope_compatible nmapping def1 def2 in
      [%debug_log "compatible_scope_flag=%B" compatible_scope_flag];

      let non_rename_def_cand1 = ref None in
      let non_rename_def_cand2 = ref None in

      let is_bad_def =
        (*Comparison.get_orig_name def1 <> Comparison.get_orig_name def2 &&*)
        List.exists
          (fun x -> x > 0)
          [!use_rename_count; use_delete_count; use_insert_count;
           conflicting_use_mapping_count1; conflicting_use_mapping_count2
          ] &&
        (
         Comparison.get_orig_name def1 <> Comparison.get_orig_name def2 &&
         !use_rename_count = 0 &&
         (use_delete_count + conflicting_use_mapping_count1)
           * (use_insert_count + conflicting_use_mapping_count2) = 0
        ||
         (*!use_rename_count > 0 &&*)
         (
          (match !conflicting_mapping_list1 with
          | [] -> false
          | ((n1, n2)::_ as pl) -> begin
              let b =
                let name1 = Comparison.get_orig_name n1 in
                Comparison.get_orig_name n2 = name1 &&
                not
                  (
                   Misc.is_cross_boundary nmapping n1 n2 ||
                   local_def_flag &&
                   (
                    compatible_scope_flag ||
                    Misc.is_cross_scope nmapping n1 n2
                   )
                  ) &&
                let bi2 = get_bid n2 in
                List.for_all
                  (fun (_, y) ->
                    if Comparison.get_orig_name y = name1 && get_bid y = bi2 then begin
                      begin
                        try
                          let def2' = cenv#tree2#search_node_by_uid (B.get_uid y#data#binding) in
                          non_rename_def_cand2 := Some def2'
                        with
                          _ -> ()
                      end;
                      true
                    end
                    else
                      false
                  ) pl
              in
              [%debug_log "b=%B" b];
              b
          end) ||
          (match !conflicting_mapping_list2 with
          | [] -> false
          | ((n1, n2)::_ as pl) -> begin
              let b =
                let name2 = Comparison.get_orig_name n2 in
                Comparison.get_orig_name n1 = name2 &&
                not
                  (
                   Misc.is_cross_boundary nmapping n1 n2 ||
                   local_def_flag &&
                   (
                    compatible_scope_flag ||
                    Misc.is_cross_scope nmapping n1 n2
                   )
                  ) &&
                let bi1 = get_bid n1 in
                List.for_all
                  (fun (x, _) ->
                    if Comparison.get_orig_name x = name2 && get_bid x = bi1 then begin
                      begin
                        try
                          let def1' = cenv#tree1#search_node_by_uid (B.get_uid x#data#binding) in
                          non_rename_def_cand1 := Some def1'
                        with
                          _ -> ()
                      end;
                      true
                    end
                    else
                      false
                  ) pl
              in
              [%debug_log "b=%B" b];
              b
          end)
         )
        )
      in
      [%debug_log "is_bad_def=%B" is_bad_def];
      if is_bad_def then begin
        [%debug_log "added to pairs_to_be_removed: %a-%a" nups def1 nups def2];
        pairs_to_be_removed := (def1, def2, true) :: !pairs_to_be_removed;
        begin
          try
            let pdef1 = def1#initial_parent in
            if not (pdef1#data#is_sequence || pdef1#data#is_ntuple) then begin
              let pdef2 = def2#initial_parent in
              if nmapping#find pdef1 == pdef2 then begin
                [%debug_log "added to pairs_to_be_removed: %a-%a" nups pdef1 nups pdef2];
                pairs_to_be_removed := (pdef1, pdef2, true) :: !pairs_to_be_removed;
              end
            end
          with _ -> ()
        end;
        List.iter2
          (fun n1 n2 ->
            [%debug_log "added to pairs_to_be_removed: %a-%a" nups n1 nups n2];
            pairs_to_be_removed := (n1, n2, strict_flag) :: !pairs_to_be_removed
          ) !use_renames1 !use_renames2;

        match !non_rename_def_cand1, !non_rename_def_cand2 with
        | None, Some def2' -> begin
            to_be_mapped := ([def1], [def2']) :: !to_be_mapped;
            to_be_mapped := (get_use_list1 def1, get_use_list2 def2') :: !to_be_mapped
        end
        | Some def1', None -> begin
            to_be_mapped := ([def1'], [def2]) :: !to_be_mapped;
            to_be_mapped := (get_use_list1 def1', get_use_list2 def2) :: !to_be_mapped
        end
        | _ -> ()
      end
      else begin (* is good def pair *)
        let conflicting_mapping_list1_, conflicting_mapping_list2_ =
          let filt =
            List.filter
              (fun (n1, n2) ->
                let b =
                  not (Misc.is_cross_boundary nmapping n1 n2) &&
                  (strict_flag ||
                  try
                    nmapping#find n1#initial_parent != n2#initial_parent
                  with _ -> true)
                in
                [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
                b
              )
          in
          filt !conflicting_mapping_list1, filt !conflicting_mapping_list2
        in
        List.iter
          (fun ((*i*)_, pl) ->
            List.iter
              (fun (n1, n2) ->
                [%debug_log "%a-%a" nups n1 nups n2];
                let strict_flag_ =
                  strict_flag(* ||
                  try
                    if i = 1 then begin
                      let bi2 = get_bid n2 in
                      [%debug_log "%a -> %a" nups n2 BID.ps bi2];
                      let def2 = find_def cenv#tree2 def_bid_tbl2 bi2 in
                      let b = nmapping#mem_cod def2 in
                      [%debug_log "%B" b];
                      b
                    end
                    else if i = 2 then begin
                      let bi1 = get_bid n1 in
                      [%debug_log "%a -> %a" nups n1 BID.ps bi1];
                      let def1 = find_def cenv#tree1 def_bid_tbl1 bi1 in
                      let b = nmapping#mem_dom def1 in
                      [%debug_log "%B" b];
                      b
                    end
                    else
                      assert false
                  with
                    _ -> true*)
                in
                [%debug_log "strict_flag=%B strict_flag_=%B" strict_flag strict_flag_];
                [%debug_log "added to pairs_to_be_removed: %a-%a" nups n1 nups n2];
                pairs_to_be_removed := (n1, n2, strict_flag_) :: !pairs_to_be_removed
              ) pl
          ) [1,conflicting_mapping_list1_; 2,conflicting_mapping_list2_];

        let nds1, _ = List.split conflicting_mapping_list1_ in
        let _, nds2 = List.split conflicting_mapping_list2_ in
        let nds1_ = !delete_list @ nds1 in
        let nds2_ = !insert_list @ nds2 in
        let nds1__, nds2__ =
          if
            B.is_local_def def1#data#binding && B.is_local_def def2#data#binding &&
            (nds1_ <> [] || nds2_ <> [])
          then begin
            List.iter2
              (fun n1 n2 ->
                let strict_flag_ =
                  strict_flag
                in
                [%debug_log "added to pairs_to_be_removed: %a-%a" nups n1 nups n2];
                pairs_to_be_removed := (n1, n2, strict_flag_) :: !pairs_to_be_removed
              ) !use_renames1 !use_renames2;
            !use_renames1 @ nds1_, !use_renames2 @ nds2_
          end
          else
            nds1_, nds2_
        in
        [%debug_log "nds1__=[%a]" nsps nds1__];
        [%debug_log "nds2__=[%a]" nsps nds2__];
        if nds1__ <> [] && nds2__ <> [] then
          to_be_mapped := (nds1__, nds2__) :: !to_be_mapped;

        Hashtbl.add def_bid_map1 bid1 bid2;
        Hashtbl.add def_bid_map2 bid2 bid1
      end

    )
    (List.fast_sort
       (fun (x, _) (y, _) -> Stdlib.compare x#gindex y#gindex)
       !def_pair_list);

  [%debug_log "* removing renames and mappings..."];

  remove_relabels_and_mapping cenv edits nmapping !pairs_to_be_removed;

  [%debug_log "* finding compatible pairs..."];

  let compatible_pairs = ref [] in
  List.iter
    (fun (cands1, cands2) ->
      [%debug_log "cands1=[%a]" nsps cands1];
      [%debug_log "cands2=[%a]" nsps cands2];
      let ncands1 = List.length cands1 in
      let ncands2 = List.length cands2 in
      [%debug_log "ncands1=%d ncands2=%d" ncands1 ncands2];
      if ncands1 > cands_thresh || ncands2 > cands_thresh then begin
        let get_ofs n = n#data#src_loc.Loc.start_offset in
        let cmp n0 n1 = Stdlib.compare (get_ofs n0) (get_ofs n1) in
        let sorted_cands1 = List.fast_sort cmp cands1 in
        let sorted_cands2 = List.fast_sort cmp cands2 in
        let rec comb l1 l2 =
          match l1, l2 with
          | [], _ | _, [] -> []
          | x1::tl1, x2::tl2 -> (x1, x2)::(comb tl1 tl2)
        in
        compatible_pairs := (comb sorted_cands1 sorted_cands2) @ !compatible_pairs
      end
      else
        compatible_pairs := (combine_node_lists cenv nmapping cands1 cands2) @ !compatible_pairs
    ) !to_be_mapped;

  begin %debug_block
    List.iter
      (fun (n1, n2) ->
        [%debug_log "compatible pair: %a-%a" nps n1 nps n2]
      )
      (List.fast_sort
         (fun (n1, _) (n2, _) -> Stdlib.compare n1#gindex n2#gindex)
         !compatible_pairs)
  end;

  [%debug_log "* generating compatible edits..."];
  let nrels =
    generate_compatible_edits options cenv nmapping edits
      !compatible_pairs (fun _ _ -> false, false)
  in
  let _ = nrels in
  [%debug_log "* %d relabels generated." nrels];

  List.iter
    (fun (n1, n2) ->
      nmapping#add_starting_pair_for_glueing (n1, n2)
    ) !compatible_pairs;

  let local_bad_pairs = Xset.create 0 in
  List.iter
    (fun (n1, n2, strict) ->
      if strict then
        Xset.add local_bad_pairs (n1, n2)
    ) !pairs_to_be_removed;

  let is_possible_rename = cenv#_is_possible_rename in
  cenv#set_is_possible_rename
    (fun ?(strict=false) n1 n2 ->
      [%debug_log "is_possible_rename: strict=%B %a-%a" strict nups n1 nups n2];
      let b =
        not (Xset.mem local_bad_pairs (n1, n2)) &&
        is_possible_rename ?strict:(Some strict) n1 n2 &&
        (
         not strict_flag ||
         (try
           let bi1 = get_bid n1 in
           [%debug_log "bi1=%a" BID.ps bi1];
           not (Xset.mem non_rename_bids1 bi1)
         with
           _ -> true) &&
         (try
           let bi2 = get_bid n2 in
           [%debug_log "bi2=%a" BID.ps bi2];
           not (Xset.mem non_rename_bids2 bi2)
         with
           _ -> true)
        )
      in
      [%debug_log "%B" b];
      b
    );

  cenv#set_def_bid_map1 def_bid_map1;
  cenv#set_def_bid_map2 def_bid_map2;
  cenv#set_def_use_tbl1 def_use_tbl1;
  cenv#set_def_use_tbl2 def_use_tbl2;

  [%debug_log "FINISHED!"]

(* end of rectify_renames_d *)
]
