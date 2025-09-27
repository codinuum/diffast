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
(* postprocessing.ml *)

[%%prepare_logger]

module Xarray = Diffast_misc.Xarray
module Xset = Diffast_misc.Xset
module Xstring = Diffast_misc.Xstring
module Xprint = Diffast_misc.Xprint
module HIS = Diffast_misc.HIS
module UID = Diffast_misc.UID
module GI  = Diffast_misc.GIndex
module Otree = Diffast_misc.Otree
module Mapping = Diffast_misc.Mapping
module ZS = Diffast_misc.ZS
module MID = Moveid
module B   = Diffast_misc.Binding
module BID = B.ID
module Nodetbl = Node.Tbl

open Misc

let is_use n = B.is_use n#data#binding
let get_def_node tree n = tree#search_node_by_uid (B.get_uid n#data#binding)
let is_local_def n = B.is_local_def n#data#binding


[%%capture_path
module F (Label : Spec.LABEL_T) = struct

  exception Abort
  exception Break
  exception Found
  exception Certain

  type node_t = Spec.node_t
  type tree_t = Spec.tree_t

  let get_orig_name = Comparison.get_orig_name

  let is_ghost_node = Triple.is_ghost_ast_node

  let getlab nd = (Obj.obj nd#data#_label : Label.t)

  let get_bn = get_p_ancestor (fun x -> x#data#is_boundary)

  let can_be_keyroot tree nd =
    let initial_ancestors = tree#initial_ancestor_nodes nd in

    [%debug_log "initial ancestors of %a: [%a]" nups nd nsps initial_ancestors];

    let d = List.length initial_ancestors in
    let dcond = d >= Label.keyroot_depth_min in
    let prohibited = Label.cannot_be_keyroot nd in
    let b = dcond && not prohibited in

    [%debug_log "%a -> %B (depth=%d,prohibited=%B)" nups nd b d prohibited];
    b


  let printf = Printf.printf
  let sprintf = Printf.sprintf

  let mkinfo = Info.make

  let _is_map (*tree1*)_ (*tree2*)_ nmapping n1 n2 =
    let b =
      try nmapping#find n1 == n2 with _ -> false
    in
    [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
    b

  let pmap_add pmap n v =
    try
      let vs = Nodetbl.find pmap n in
      if not (List.mem v vs) then
        Nodetbl.replace pmap n (v::vs)
    with Not_found -> Nodetbl.add pmap n [v]


  let left_to_right (*tree*)_ node1 node2 =
    Stdlib.compare node1#gindex node2#gindex


  let estimate_cost_of_move = Comparison.estimate_cost_of_move


  let detect_permutation mid_gen cenv pruned base_edits edits pmap =

    let select_compatible_pairs pair_nth_weight_list =
      let pair_weight_list =
        List.map (fun (n1, n2, _, sz) -> (n1, n2, sz)) pair_nth_weight_list
      in
      let compat, incompat = cenv#select_compatible_pairs pair_weight_list in

      List.iter
        (fun (n1, n2, _) ->
          if base_edits#mem_mov12 n1 n2 then
            [%debug_log "already exists in base_edits: %a-%a" nups n1 nups n2]
          else begin
          pruned#set_kind n1 n2 Pruned.Migratory;
          let info1 = mkinfo n1 in
          let info2 = mkinfo n2 in
          try
            match edits#find_mov12 n1 n2 with
            | Edit.Move (m, k, _, _) -> begin
                let _ = m in
                if !k <> Edit.Mpermutation then begin
                  [%debug_log "kind changed: %a: %s -> %s (select_compatible_pairs)" MID.ps !m
                    (Edit.move_kind_to_string !k) (Edit.move_kind_to_string Edit.Mpermutation)];
                  k := Edit.Mpermutation
                end
            end
            | _ -> assert false
          with
            Not_found -> begin
              edits#add_edit
                (Edit.make_move_permutation (mid_gen#gen) info1 info2);
              [%debug_log "added permutation %a -> %a" nups n1 nups n2]
            end
          end
        ) incompat;

      List.map (fun (n1, n2, sz) -> (n1, n2, ref 0, sz)) compat
    in

    Nodetbl.iter
      (fun nd vs ->
        let _ = nd in

        [%debug_log "%a %s" nups nd
          (Xlist.to_string
             (fun (nd1, nd2, nth, sz) ->
               sprintf "<%a-%a(%dth,sz:%a)>" nups nd1 nups nd2 !nth Comparison.wps sz)
             "" vs)];

        let vs = select_compatible_pairs vs in

        let len = List.length vs in
        if len > 1 then begin

          let sorted1 =
            List.stable_sort
              (fun (n1, _, _, _) (n2, _, _, _) ->
                left_to_right cenv#tree1 n1 n2
              ) vs
          in
          ignore (List.fold_left (fun c (_, _, nth, _) -> nth := c; c + 1) 0 sorted1);
          let a1 = Array.make len 0 in
          Array.iteri (fun i _ -> a1.(i) <- i) a1;

          let sorted2 =
            List.stable_sort
              (fun (_, n1, _, _) (_, n2, _, _) ->
                left_to_right cenv#tree2 n1 n2) vs
          in
          let a2 = Array.make len 0 in
          ignore (List.fold_left (fun c (_, _, nth, _) -> a2.(c) <- !nth; c + 1) 0 sorted2);


          begin %debug_block
            [%debug_log "%a %s" nups nd
              (Xlist.to_string
                 (fun (nd1, nd2, nth, sz) ->
                   sprintf "<%a-%a(%dth,sz:%a)>" nups nd1 nups nd2 !nth Comparison.wps sz)
                 "" (List.rev vs))];
            [%debug_log "a1 = [%s]" (Xarray.to_string string_of_int " " a1)];
            [%debug_log "a2 = [%s]" (Xarray.to_string string_of_int " " a2)];
          end;


          let moved =
            if a1 = a2 then
              []
            else
              let weight_list =
                List.map (fun (_, _, _, sz) -> Comparison.weight_to_int sz) sorted1
              in
(*
              let get_weight _ j _ =
                try
                  List.nth weight_list a2.(j)
                with _ -> assert false
              in
              let del =
                let res = HCS.Int.compute get_weight a1 a2 in
                res.HCS.Int.del
              in
*)
              let get_weight i j _ =
                try
                  (List.nth weight_list a2.(j), -i)
                with _ -> assert false
              in
              let del =
                let res = HIS.IntInt.compute get_weight a1 a2 in
                let r1, _ = List.split res in
                List.filter (fun i -> not (List.mem i r1)) (Xlist.range len)
              in
(*
              if not (Xlist.subtract del del' = [] && Xlist.subtract del' del = []) then begin
                Xprint.message "a1=[%s]" (Xarray.to_string string_of_int "," a1);
                Xprint.message "a2=[%s]" (Xarray.to_string string_of_int "," a2);
                Xprint.message "cost: [%s]" (Xlist.to_string string_of_int "," weight_list);
                Xprint.message "del=[%s]" (Xlist.to_string string_of_int "," del);
                Xprint.message "del'=[%s]" (Xlist.to_string string_of_int "," del');
              end;
*)
              del

(*
              let _, rel, del, _ = Adiff.adiff a1 a2 in
              let rel1, _ = List.split rel in
              rel1 @ del
*)
          in

          [%debug_log "moved (cost considered): [%s]" (Xlist.to_string string_of_int ";" moved)];

          List.iter
            (fun (nd1, nd2, nth, _) ->
              [%debug_log "%a-%a %d-th" nups nd1 nups nd2 !nth];
              if List.mem !nth moved then begin
                let ok =
                  not (base_edits#mem_mov12 nd1 nd2) &&
                  let eds = edits#find12 nd1 nd2 in
                  match eds with
                  | [] -> true
                  | [Edit.Move(m, kind, (i1, _), (i2, _)) as ed]
                  | [Edit.Move(m, kind, (i1, _), (i2, _)) as ed;
                     Edit.Relabel _]
                  | [Edit.Relabel _;
                     Edit.Move(m, kind, (i1, _), (i2, _)) as ed] -> begin
                       let _ = m in
                       let n1 = Info.get_node i1 in
                       let n2 = Info.get_node i2 in
                       assert (n1 == nd1 && n2 = nd2);
                       if !kind = Edit.Mpermutation then begin

                         [%debug_log "already have %s" (Edit.to_string ed)];

                         false
                       end
                       else if !kind = Edit.Modd then begin

                         [%debug_log "already have %s" (Edit.to_string ed)];

                         pruned#set_kind nd1 nd2 Pruned.Migratory;

                         [%debug_log "kind changed: %a: %s -> %s (detect_permutation)"
                           MID.ps !m
                            (Edit.move_kind_to_string !kind)
                            (Edit.move_kind_to_string Edit.Mpermutation)];

                         kind := Edit.Mpermutation;
                         false
                       end
                       else begin
                         edits#remove_edit ed;
                         true
                       end
                     end
                  | [_] -> true
                  | _ -> assert false
                in
                if ok then begin
                  pruned#set_kind nd1 nd2 Pruned.Migratory;
                  let info1 = mkinfo nd1 in
                  let info2 = mkinfo nd2 in
                  edits#add_edit
                    (Edit.make_move_permutation (mid_gen#gen) info1 info2);

                  [%debug_log "added permutation %a -> %a" nups nd1 nups nd2]
                end
              end
              else begin
                try
                  let ed = edits#find_mov12 nd1 nd2 in
                  edits#remove_edit ed
                with
                  Not_found -> ()
              end
            ) vs
        end
      ) pmap
  (* end of func detect_permutation *)



  let is_pseudo_match nd1 nd2 =
    try
      nd1#data#_anonymized2_label = nd2#data#_anonymized2_label &&
      nd1#data#get_name = nd2#data#get_name
    with
      Not_found -> false


  let check_relabel options ?(exact=false) ?(matches=[]) (*tree1*)_ (*tree2*)_ nd1 nd2 nmapping =
    let parent_cond =
      let p1 = nd1#has_initial_parent in
      let p2 = nd2#has_initial_parent in
      if p1 && p2 then
        let pnd1 = nd1#initial_parent in
        let pnd2 = nd2#initial_parent in
        try
          let pnd1' = nmapping#find pnd1 in
          if pnd1' == pnd2 then
            pnd1#data#eq pnd2#data || pnd1#data#relabel_allowed pnd2#data
          else
            false
        with
          Not_found ->
            List.mem (pnd1, pnd2) matches
      else
        if (not p1) && (not p2) then
          true
        else
          false
    in

    let children1 = nd1#initial_children in
    let children2 = nd2#initial_children in
(*
    let pseudo_match = is_pseudo_match nd1 nd2 in

    let to_be_exact = exact && not pseudo_match in
*)
    let children_cond =
      let nchildren1 = Array.length children1 in
      let nchildren2 = Array.length children2 in

      if nchildren1 = 0 || nchildren2 = 0 then
        true

      else begin
        let sum_nchildren = nchildren1 + nchildren2 in
        if sum_nchildren = 0 then
(*      to_be_exact *) true

        else
          let nmapped =
            Array.fold_left
              (fun count n ->
                try
                  let n' = nmapping#find n in
                  if Array.memq n' children2 then
                    if
                      (* n#data#eq n'#data *)
                      n#data#_anonymized2_label = n'#data#_anonymized2_label
                    then
                      count + 1
                    else
                      count
                  else
                    count
                with
                  Not_found -> count
              ) 0 children1
          in
          let r = (float (nmapped * 2)) /. (float sum_nchildren) in
          [%debug_log "%f (pp_relabel_criteria=%f)" r options#pp_relabel_criteria];
          r >= options#pp_relabel_criteria
      end
    in

    let result =
      if (* to_be_exact *) exact then
        parent_cond && children_cond
      else
        parent_cond || children_cond
    in

(*
    [%debug_log "[exact=%B] %a-%a: pseudo_match:%B parent_cond:%B children_cond:%B --> %B"
      exact nups nd1 nups nd2 pseudo_match parent_cond children_cond result];
*)

    [%debug_log "[exact=%B] %a-%a: parent_cond:%B children_cond:%B --> %B"
      exact nups nd1 nups nd2 parent_cond children_cond result];

    result
  (* end of func check_relabel *)


  let generate_moves options cenv pruned edits nmapping subtree_matches =
    let tree1 = cenv#tree1 in
    let tree2 = cenv#tree2 in

    let mid_gen = options#moveid_generator in

    begin %debug_block
      nmapping#print_status;
    end;

    let extra_edits = new Edit.seq options in
    let pmap = Nodetbl.create 0 in

    let is_mapped1 = nmapping#mem_dom in
    let is_mapped2 = nmapping#mem_cod in

    let possible_move_tbl = Hashtbl.create 0 in
    let add_possible_move key b thunk =
      let v = (b, thunk) in
      try
        let vl = Hashtbl.find possible_move_tbl key in
        Hashtbl.replace possible_move_tbl key (v::vl)
      with Not_found ->
        Hashtbl.add possible_move_tbl key [v]
    in

    let check an1 an2 =
(*
      let moderate_nchildren_threshold = options#moderate_nchildren_threshold in
      let moderate_nchildren = moderate_nchildren ~threshold:moderate_nchildren_threshold in

      if (moderate_nchildren an1) && (moderate_nchildren an2) then begin (* we ignore too many children *)
*)
        let c1 =
          Sourcecode.find_nearest_mapped_descendant_nodes is_mapped1 an1
        in
        let c2 =
          Sourcecode.find_nearest_mapped_descendant_nodes is_mapped2 an2
        in

        let c2' = ref [] in

        [%debug_log "checking %a{%a} - %a{%a}" nups an1 nsps c1 nups an2 nsps c2];

        let total_cost = ref 0 in

        let maps =
          Xlist.union
            (List.map (fun n1 -> n1, nmapping#find n1) c1)
            (List.map (fun n2 -> nmapping#inv_find n2, n2) c2)
        in
        let is_odd_map n1 n2 asz =

          [%debug_log "%a-%a: maps: [%s]" nups n1 nups n2
            (Xlist.to_string (fun (n1, n2) -> (UID.to_string n1#uid)^"-"^(UID.to_string n2#uid)) ";" maps)];

          let incompat =
            List.filter
              (fun (n1', n2') ->
(*
                (Node_mapping._is_incompatible tree1 tree2 n1 n2 n1' n2') &&
*)
                n1' != n1 && n2' != n2 &&
                (cenv#is_crossing_or_incompatible n1 n2 n1' n2')

              ) maps
          in

          [%debug_log "incompatible maps: [%s]"
            (Xlist.to_string
               (fun (n1, n2) -> (UID.to_string n1#uid)^"-"^(UID.to_string n2#uid)) ";" incompat)];

          if incompat = [] then
            false

          else
            let cost =
              let incompat' =
                List.map
                  (fun (n1, n2) ->
                    let w =
                      Comparison.weight_of_int (estimate_cost_of_move tree1 tree2 nmapping n1 n2)
                    in
                    (n1, n2, w)
                  ) incompat
              in
              let incompat'', _ = cenv#select_compatible_pairs incompat' in
              List.fold_left (fun sum (_, _, sz) -> sum + Comparison.weight_to_int sz) 0 incompat''
            in

            let b = asz <= cost in

            begin %debug_block
              [%debug_log "%a-%a --> %B (asz=%d, cost=%d)" nups n1 nups n2 b asz cost];
            end;

            b
        in (* is_odd_map *)

        let chk eds n n' =
          [%debug_log "%a-%a" nups n nups n'];
          match eds#find12 n n' with
          | [] -> true
          | [Edit.Move(_, _, _, _) as ed]
          | [Edit.Relabel _;Edit.Move(_, _, _, _) as ed]
          | [Edit.Move(_, _, _, _) as ed;Edit.Relabel _] ->
              let _ = ed in
              [%debug_log "already exists: %s" (Edit.to_string ed)];

              false
          | [_] -> true
          | _ -> assert false
        in
        let add_move ?(odd=false) nd nd' =
          let mkmv =
            if odd then
              Edit.make_move_odd
            else
              Edit.make_move
          in
          if chk extra_edits nd nd' && chk edits nd nd' then
            let ed = mkmv (mid_gen#gen) (mkinfo nd) (mkinfo nd') in
            [%debug_log "adding %s" (Editop.to_string ed)];
            extra_edits#add_edit ed
        in
        List.iter
          (fun nd ->

            [%debug_log "nearest mapped descendant of %a ---> %a" nups an1 nups nd];

            let nd' = nmapping#find nd in

            if List.memq nd' c2 then begin (* may be a permutation *)

              let asz = estimate_cost_of_move tree1 tree2 nmapping nd nd' in

              total_cost := !total_cost + asz;

              if is_odd_map nd nd' asz (* EXPERIMENTAL!!! *) then begin (* odd move *)
                add_move ~odd:true nd nd'
              end;

              c2' := nd' :: !c2';

              [%debug_log "may be a permutation: (%a) %a-%a" nups an1 nups nd nups nd'];

              pmap_add pmap an1 (nd, nd', ref 0, Comparison.weight_of_int asz);
              [%debug_log "map added"]

            end
            else begin (* normal move *)
              add_move nd nd'
            end
          ) c1;

        List.iter
          (fun nd' ->
            if not (List.memq nd' !c2') then begin

              [%debug_log "descendant of %a ---> %a" nups an2 nups nd'];

              let nd = nmapping#inv_find nd' in
              add_move nd nd'
            end
          ) c2;

        if an1#data#is_statement && an2#data#is_statement then begin
          try
            let bn1, bn2 = get_bn an1, get_bn an2 in

            let bgi1, bgi2 = bn1#gindex, bn2#gindex in
            let blgi1 = (tree1#initial_leftmost bn1)#gindex in
            let blgi2 = (tree2#initial_leftmost bn2)#gindex in

            let gi1, gi2 = an1#gindex, an2#gindex in
            let lgi1 = (tree1#initial_leftmost an1)#gindex in
            let lgi2 = (tree2#initial_leftmost an2)#gindex in

            let is_desc lgi gi n =
              let g = n#gindex in
              lgi <= g && g <= gi
            in
            let in_bn1 = is_desc blgi1 bgi1 in
            let in_bn2 = is_desc blgi2 bgi2 in

            let is_desc1 = is_desc lgi1 gi1 in
            let is_desc2 = is_desc lgi2 gi2 in

            let size1 = ref 0 in
            let size2 = ref 0 in
            let csize12 = ref 0 in

            let stmts1 = ref [] in
            let stmts2 = ref [] in

            let ncstmts12 = ref 0 in

            Xset.iter
              (fun (rn1, rn2, sz) ->
                (*if
                  try
                    rn1#initial_parent = an1 && rn2#initial_parent = an2
                  with _ -> false
                then begin
                end;*)

                if in_bn1 rn1 && in_bn2 rn2 then begin
                  let cond1 = is_desc1 rn1 in
                  let cond2 = is_desc2 rn2 in

                  if cond1 && cond2 then begin
                    [%debug_log "%a--%a (%d): %a [%a]-[%a]"
                      nups rn1 nups rn2 sz labps rn1 locps rn1 locps rn2];
                    if rn1#initial_parent == an1 && rn2#initial_parent == an2 then begin
                      csize12 := !csize12 + sz;
                      if rn1#data#is_statement then
                        incr ncstmts12
                    end
                  end
                  else if cond1 && not cond2 && rn2#gindex > gi2 then begin
                    [%debug_log "%a->%a (%d): %a [%a]-[%a]"
                      nups rn1 nups rn2 sz labps rn1 locps rn1 locps rn2];
                    size1 := !size1 + sz;
                    if rn1#data#is_statement then
                      stmts1 := rn1 :: !stmts1
                  end
                  else if not cond1 && cond2 && rn1#gindex > gi1 then begin
                    [%debug_log "%a<-%a (%d): %a [%a]-[%a]"
                      nups rn1 nups rn2 sz labps rn1 locps rn1 locps rn2];
                    size2 := !size2 + sz;
                    if rn2#data#is_statement then
                      stmts2 := rn2 :: !stmts2
                  end
                end
              ) subtree_matches;

            let nstmts1 = List.length !stmts1 in
            let nstmts2 = List.length !stmts2 in

            [%debug_log "an1=%a an2=%a: size of matched subtrees: %d (%d stmts) or %d (%d stmts) (total_cost: %d)"
              nups an1 nups an2 !size1 nstmts1 !size2 nstmts2 !total_cost];
            [%debug_log "size of matched child subtrees: %d (%d stmts)" !csize12 !ncstmts12];

            let size =
              if !size1 > !size2 && nstmts1 > 0 then
                !size1
              else if !size2 > !size1 && nstmts2 > 0 then
                !size2
              else
                0
            in
            [%debug_log "size->%d" size];

            if size > !total_cost then begin
              let cmp n0 n1 = compare n0#gindex n1#gindex in
              let stmts1 = List.fast_sort cmp !stmts1 in
              let stmts2 = List.fast_sort cmp !stmts2 in

              if !csize12 > 1 then
                add_possible_move (stmts1, stmts2) false (fun () -> ())
              else begin
                [%debug_log "possible move: %a [%a]-[%a]" labps an1 locps an1 locps an2];
                let thunk () = add_move an1 an2 in
                add_possible_move (stmts1, stmts2) true thunk
              end
            end

          with
            _ -> ()
        end;

(*      end (* we ignore huge arrays *) *)

    in (* end of func check *)

(*    nmapping#iter_unsettled check; *)
    nmapping#iter check;

    Hashtbl.iter
      (fun _ vl ->
        if List.for_all (fun (b, _) -> b) vl then begin
          [%debug_log "!!!!! adding possible moves..."];
          List.iter (fun (_, thunk) -> thunk()) vl;
          [%debug_log "!!!!! possible moves added"];
        end
      ) possible_move_tbl;

    let c = extra_edits#get_nedits in
    let _ = c in

    begin %debug_block
      [%debug_log "%d edits generated" c];
      extra_edits#iter
        (fun ed -> [%debug_log "%s" (Editop.to_string ed)]);
      [%debug_log "detecting permutations..."];
    end;

    detect_permutation mid_gen cenv pruned edits extra_edits pmap;

    [%debug_log "%d edits generated (permutatioin)" (extra_edits#get_nedits - c)];

    (*if options#no_moves_flag then begin
      extra_edits#iter_moves
        (function
          | Edit.Move(_, _, (u1, inf1, ex1), (u2, inf2, ex2)) as mov -> begin
              let del = Edit.Delete(false, u1, inf1, ex1) in
              let ins = Edit.Insert(false, u2, inf2, ex2) in
              ignore (nmapping#remove u1 u2);
              List.iter
                (fun ed ->
                  [%debug_log "adding %s" (Editop.to_string ed)];
                  edits#add_edit ed
                ) [del; ins];
              try
                match edits#find_rel12 u1 u2 with
                | Edit.Relabel _ as rel -> edits#remove_edit rel;
                | _ -> assert false
              with
                Not_found -> ()
          end
          | _ -> assert false
        )
    end
    else*)
      (*edits#add_edits extra_edits*)
    extra_edits#iter
      (function
        | Edit.Move(mid, _, (info1, _), (info2, _)) as mov -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            begin
              try
                let del = edits#find_del nd1 in
                edits#remove_edit del
              with _ -> ()
            end;
            begin
              try
                let ins = edits#find_ins nd2 in
                edits#remove_edit ins
              with _ -> ()
            end;
            edits#add_edit mov
        end
        | _ -> ()
      )
  (* end of func generate_moves *)


  let make_move_region_tbl tree1 tree2 edits =
    let mtbl = Hashtbl.create 0 in (* mid -> (leftmost gi * top gi * leftmost gi * top gi) *)
    edits#iter_moves
      (function
        | Edit.Move(mid, _, (info1, _), (info2, _)) -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            let gi1 = nd1#gindex in
            let gi2 = nd2#gindex in
            let lgi1 = (tree1#initial_leftmost nd1)#gindex in
            let lgi2 = (tree2#initial_leftmost nd2)#gindex in
            [%debug_log "move region: %a: (%a,%a)-(%a,%a) (%a-%a)" MID.ps !mid
              gps lgi1 gps gi1 gps lgi2 gps gi2 nps nd1 nps nd2];
            try
              let _, g1, _, g2 = Hashtbl.find mtbl !mid in
              if lgi1 <= g1 && g1 < gi1 && lgi2 <= g2 && g2 < gi2 then
                Hashtbl.replace mtbl !mid (lgi1, gi1, lgi2, gi2)
            with
              Not_found ->
                Hashtbl.add mtbl !mid (lgi1, gi1, lgi2, gi2)
        end
        | _ -> assert false
      );
    begin %debug_block
      [%debug_log "final move_region_tbl:"];
      let l =
        Hashtbl.fold (fun m (lmg1, g1, lmg2, g2) l -> (m, lmg1, g1, lmg2, g2)::l) mtbl []
      in
      let cmp (_, _, g1, _, _) (_, _, g2, _, _) = compare g1 g2 in
      List.iter
        (fun (m, lmg1, g1, lmg2, g2) ->
           let n1 = tree1#search_node_by_gindex g1 in
           let n2 = tree2#search_node_by_gindex g2 in
           [%debug_log "move region: %a -> (%a,%a)-(%a,%a) (%a-%a)"
             MID.ps m gps lmg1 gps g1 gps lmg2 gps g2 nps n1 nps n2]
        ) (List.fast_sort cmp l)
    end;

    mtbl

  let make_move_member_tbl edits =
    let tbl = Hashtbl.create 0 in
    edits#iter_moves
      (function
        | Edit.Move(mid, _, (info1, _), (info2, _)) -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            try
              let pl = Hashtbl.find tbl !mid in
              Hashtbl.replace tbl !mid ((nd1, nd2)::pl)
            with
              Not_found -> Hashtbl.add tbl !mid [nd1, nd2]
        end
        | _ -> assert false
      );
    tbl

  let make_parent_move_tbl cenv move_region_tbl edits =

    let mem_tbl = make_move_member_tbl edits in

    let mem_move_tbl = Hashtbl.create 0 in
    edits#iter_moves
      (function
        | Edit.Move(mid, _, _, _) -> begin
            if not (Hashtbl.mem mem_move_tbl !mid) then
              Hashtbl.add mem_move_tbl !mid [!mid]
        end
        | _ -> assert false
      );

    let parent_move_tbl = Hashtbl.create 0 in

    let move_list =
      List.fast_sort
        (fun (_, _, g1, _, _) (_, _, g2, _, _) -> Stdlib.compare g1 g2)
        (Hashtbl.fold
           (fun m (lmg1, g1, lmg2, g2) l ->
             (m, lmg1, g1, lmg2, g2)::l
           ) move_region_tbl [])
    in
    edits#iter_moves_bottomup
      (function
        | Edit.Move(mid, kind, (info1, _), (info2, _)) -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            let gi1 = nd1#gindex in
            let gi2 = nd2#gindex in
            [%debug_log "mid=%a (%a, %a)" MID.ps !mid gps gi1 gps gi2];
            try
              List.iter
                (fun (m, lmg1, g1, lmg2, g2) ->
                  [%debug_log "m=%a (%a-%a, %a-%a)" MID.ps m gps lmg1 gps g1 gps lmg2 gps g2];
                  if
                    !mid <> m &&
                    lmg1 <= gi1 && gi1 < g1 &&
                    lmg2 <= gi2 && gi2 < g2 &&
                    let b =
                      !kind <> Edit.Mpermutation ||
                      try
                        let ml = Hashtbl.find mem_move_tbl m in
                        List.for_all
                          (fun m ->
                            let pl = try Hashtbl.find mem_tbl m with _ -> [] in
                            List.for_all
                              (fun (n1, n2) ->
                                not (cenv#is_crossing_or_incompatible nd1 nd2 n1 n2)
                              ) pl
                          ) ml
                      with
                        Not_found -> true
                    in
                    [%debug_log "b=%B" b];
                    if not b then
                      raise Exit;
                    b
                  then begin
                    [%debug_log "parent move of %a --> %a" MID.ps !mid MID.ps m];
                    begin
                      try
                        let ml = Hashtbl.find mem_move_tbl m in
                        if not (List.mem !mid ml) then
                          Hashtbl.replace mem_move_tbl m (!mid::ml)
                      with
                        Not_found -> ()
                    end;
                    begin
                      try
                        let (pm, pg1, _) = Hashtbl.find parent_move_tbl !mid in
                        if pm <> m && g1 <= pg1 (* && g2 <= pg2 *) then
                          Hashtbl.replace parent_move_tbl !mid (m, g1, g2)
                      with
                        Not_found -> Hashtbl.add parent_move_tbl !mid (m, g1, g2)
                    end
                  end
                ) move_list
            with
              Exit -> ()
        end
        | _ -> assert false
      );
    if true then begin
      [%debug_log "checking parent_move_tbl..."];
      let to_be_removed = ref [] in
      Hashtbl.iter
        (fun m (pm, pg1, pg2) ->
          let _ = pg1 in
          let _ = pg2 in
          [%debug_log "%a -> %a: %a-%a" MID.ps m MID.ps pm gps pg1 gps pg2];
          let mem_pair_list = Hashtbl.find mem_tbl m in
          let parent_mem_pair_list = ref [] in
          if List.length mem_pair_list = 1 then begin
            let ok1 = ref false in
            let ok2 = ref false in
            List.iter
              (fun (n1, n2) ->
                [%debug_log "n1=%a" nps n1];
                [%debug_log "n2=%a" nps n2];
                begin
                  try
                    let def1 = get_def_node cenv#tree1 n1 in
                    [%debug_log "def1=%a" nps def1];
                    parent_mem_pair_list := Hashtbl.find mem_tbl pm;
                    [%debug_log "|parent_mem_pair_list|=%d" (List.length !parent_mem_pair_list)];
                    List.iter
                      (fun (pn1, _) ->
                        [%debug_log "pn1=%a" nups pn1];
                        if pn1 == def1 then
                          raise Found
                      ) !parent_mem_pair_list
                  with
                  | Found -> ok1 := true
                  | _ ->
                      if
                        n1#data#is_statement || n1#data#is_op
                      then
                        ok1 := true
                end;
                if !ok1 then begin
                  try
                    let def2 = get_def_node cenv#tree2 n2 in
                    [%debug_log "def2=%a" nps def2];
                    if !parent_mem_pair_list = [] then begin
                      parent_mem_pair_list := Hashtbl.find mem_tbl pm;
                      [%debug_log "|parent_mem_pair_list|=%d" (List.length !parent_mem_pair_list)];
                    end;
                    List.iter
                      (fun (_, pn2) ->
                        [%debug_log "pn2=%a" nups pn2];
                        if pn2 == def2 then
                          raise Found
                      ) !parent_mem_pair_list
                  with
                  | Found -> ok2 := true
                  |  _ ->
                      if
                        n2#data#is_statement || n2#data#is_op
                      then
                        ok2 := true
                end;
                if
                  (not !ok1 || not !ok2) &&
                  n1#data#is_named_orig &&
                  n2#data#is_named_orig
                then begin
                  if !parent_mem_pair_list = [] then begin
                    parent_mem_pair_list := try Hashtbl.find mem_tbl pm with _ -> []
                  end;
                  match !parent_mem_pair_list with
                  | [pn1, pn2] -> begin
                      [%debug_log "pn1=%a pn2=%a" nups pn1 nups pn2];
                      ok1 := pn1#data#is_named && n1#initial_parent == pn1;
                      ok2 := pn2#data#is_named && n2#initial_parent == pn2
                  end
                  | _ -> ()
                end;
                [%debug_log "ok1=%B ok1=%B" !ok1 !ok2];
                if not !ok1 || not !ok2 then begin
                  [%debug_log "to be removed: %a -> %a" MID.ps m MID.ps pm];
                  to_be_removed := m :: !to_be_removed
                end
              ) mem_pair_list
          end
        ) parent_move_tbl;
      List.iter (Hashtbl.remove parent_move_tbl) !to_be_removed
    end;
    begin %debug_block
      [%debug_log "final parent_move_tbl:"];
      Hashtbl.iter
        (fun m (pm, pg1, pg2) ->
          [%debug_log "%a -> %a: %a-%a" MID.ps m MID.ps pm gps pg1 gps pg2]
        ) parent_move_tbl
    end;
    parent_move_tbl

  let make_child_move_tbl parent_move_tbl =
    let tbl = Hashtbl.create 0 in
    Hashtbl.iter
      (fun mid (parent_mid, _, _) ->
        try
          let ms = Hashtbl.find tbl parent_mid in
          if not (List.mem mid ms) then
            Hashtbl.replace tbl parent_mid (mid::ms)
        with
          Not_found -> Hashtbl.add tbl parent_mid [mid]
      ) parent_move_tbl;
    tbl

  (* grouping moves *)
  let group_moves options tree1 tree2 edits nmapping =

    [%debug_log "* GROUPING MOVES:"];

    let mid_gen() =
      let mid = options#moveid_generator#gen in
      [%debug_log "%a" MID.ps mid];
      mid
    in

    let mid_chg_tbl = Hashtbl.create 0 in

    let get_mid n =
      try
        match edits#find_mov1 n with
        | Edit.Move(id, _, _, _) -> Some !id
        | _ -> None
      with
        Not_found -> None
    in

    let rec gen_moves movid kind nd =

      [%debug_log "(%a, %s): scanning (%a)%s..."
        MID.ps movid (Edit.move_kind_to_string kind) nups nd nd#data#to_string];

      let movid, kind =
        let moveon x =
          match get_mid x with
          | Some id -> id = movid
          | _ -> true
        in
        try
          Sourcecode.scan_ancestors ~moveon nd
            (fun a ->
              [%debug_log "a=%a" nups a];
              match get_mid a with
              | Some id when id = movid ->
                  [%debug_log "found: %a" MID.ps id];
                  raise Exit
              | _ -> ()
            );
          let nm = edits#get_nmoves_of_move_id movid in
          [%debug_log "num moved nodes of %a: %d" MID.ps movid nm];
          if nm > 0 then begin
            let movid' = mid_gen() in
            [%debug_log "%a -> %a" MID.ps movid MID.ps movid'];
            movid', Edit.Mnormal
          end
          else
            movid, kind
        with
          Exit -> movid, kind
      in

      let moveon = ref true in

      let chk eds =
        match eds#find1 nd with
        | [] ->
            [%debug_log "edit not found: %a" nups nd];
            true

        | [Edit.Move(id, k, _, _)]
        | [Edit.Move(id, k, _, _); Edit.Relabel _]
        | [Edit.Relabel _;Edit.Move(id, k, _, _)] ->
            moveon := !id = movid;

            if not !moveon then begin
              [%debug_log "found: another move (%a)" MID.ps !id];
              if !k = Edit.Modd then begin

                [%debug_log "%a --> %a" MID.ps !id MID.ps movid];

                Hashtbl.replace mid_chg_tbl !id movid;

                moveon := true
              end
            end;

            false

        | [Edit.Relabel _] ->
            [%debug_log "found: relabel"];
            true

        | [ed] -> begin
            let _ = ed in
            [%debug_log "found: another edit: %s" (Edit.to_string ed)];
            false
        end
        | eds -> begin
            let _ = eds in
            [%debug_log "%d conflicting edits found:\n%s"
              (List.length eds) (Xlist.to_string Edit.to_string "\n" eds)];
            assert false
        end

      in (* end of func chk *)

      let addmov nd1 =
        try
          let nd2 = nmapping#find nd1 in

          [%debug_log "adding: (%a)%s - (%a)%s"
            nups nd1 nd1#data#to_string nups nd2 nd2#data#to_string];

          try
            match edits#find_mov12 nd1 nd2 with
            | Edit.Move(id, _, (i1, _), (i2, _)) ->
                let n1 = Info.get_node i1 in
                let n2 = Info.get_node i2 in
                if nd1 == n1 && nd2 == n2 then begin
                  [%debug_log "%a --> %a" MID.ps !id MID.ps movid];
                  id := movid
                end
                else
                  assert false
            | _ -> assert false
          with
            Not_found ->
              let info1, info2 = mkinfo nd1, mkinfo nd2 in
              edits#add_edit (Edit._make_move movid kind info1 info2)
        with
          Not_found ->
            [%debug_log "not mapped"];
            edits#add_edit (Edit.make_delete nd1)
      in

      if chk edits then begin (* mapped (have no edit other than relabel) *)
          addmov nd
      end;

      if !moveon then begin
        let is_frontier =
          try
            let nd' = nmapping#find nd in

            let ca = nd#initial_children in
            let ca' = nd'#initial_children in

            let is_crossing_or_incompatible x x' y y' =
              Comparison.is_crossing x x' y y' ||
              Node_mapping._is_incompatible tree1 tree2 x x' y y'
            in

            (*let has_crossing_mapped_anc n n' =
              let moveon x = x != nd in
              let b =
                has_p_ancestor ~moveon
                  (fun x ->
                    try
                      let x' = nmapping#find x in
                      is_crossing_or_incompatible n n' x x'
                    with _ -> false
                  ) n
              in
              [%debug_log "%a\n %a --> %B" nps n nps n' b];
              b
            in
            let has_crossing_mapped_anc' n' n =
              let moveon x' = x' != nd' in
              let b =
                has_p_ancestor ~moveon
                  (fun x' ->
                    try
                      let x = nmapping#inv_find x' in
                      is_crossing_or_incompatible n n' x x'
                    with _ -> false
                  ) n'
              in
              [%debug_log "%a\n %a --> %B" nps n' nps n b];
              b
            in*)
            let find_mappings_below n _ =
              let ml = ref [] in
              tree1#fast_scan_whole_initial_subtree n
                (fun x ->
                  try
                    let x' = nmapping#find x in
                    ml := (x, x') :: !ml
                  with _ -> ()
                );
              !ml
            in
            let has_crossing_mapped_desc ?(strict=false) ?(excludes=[]) n n' =
              [%debug_log "strict=%B" strict];
              let mappings = find_mappings_below n n' in
              let b =
                has_p_descendant
                  (fun x ->
                    (not strict || x#initial_parent != n) &&
                    try
                      let x' = nmapping#find x in
                      not (List.mem (x, x') excludes) &&
                      (not strict || x'#initial_parent != n') &&
                      (
                       is_crossing_or_incompatible n n' x x' ||
                       List.exists
                         (fun (y, y') ->
                           is_crossing_or_incompatible x x' y y'
                         ) mappings
                      )
                    with _ -> false
                  ) n
              in
              [%debug_log "%a\n %a --> %B" nps n nps n' b];
              b
            in
            let has_crossing_mapped_desc' n' n =
              let mappings = find_mappings_below n n' in
              let b =
                has_p_descendant
                  (fun x' ->
                    try
                      let x = nmapping#inv_find x' in
                      is_crossing_or_incompatible n n' x x' ||
                      List.exists
                        (fun (y, y') ->
                          is_crossing_or_incompatible x x' y y'
                        ) mappings
                    with _ -> false
                  ) n'
              in
              [%debug_log "%a\n %a --> %B" nps n' nps n b];
              b
            in
            [%debug_log "nd=%a" nps nd];
            [%debug_log "nd'=%a" nps nd'];

            let st_has_crossing_mapped_desc =
              let cache = ref None in
              let f x x' =
                match !cache with
                | Some b -> b
                | None ->
                    let strict = true in
                    let excludes = [x, x'] in
                    let b = has_crossing_mapped_desc ~strict ~excludes nd nd' in
                    cache := Some b;
                    b
              in
              f
            in
            let check_st_flag =
              not (nd#data#is_sequence && nd'#data#is_sequence) &&
              not (nd#data#is_statement && nd'#data#is_statement)
            in
            [%debug_log "check_st_flag=%B" check_st_flag];

            Array.exists
              (fun n ->
                try
                  let n' = nmapping#find n in
                  let b =
                    if n'#initial_parent == nd' then
                      false
                    else if not (tree2#is_initial_ancestor nd' n') then
                      true
                    else if has_crossing_mapped_desc' n' n then
                      true
                    else if check_st_flag then
                      st_has_crossing_mapped_desc n n'
                    else
                      false
                  in
                  [%debug_log "%a -> %a (%B)" nups n nups n' b];
                  b
                with
                  Not_found -> false
              ) ca
          ||
            Array.exists
              (fun n' ->
                try
                  let n = nmapping#inv_find n' in
                  let b =
                    if n#initial_parent == nd then
                      false
                    else if not (tree1#is_initial_ancestor nd n) then
                      true
                    else if has_crossing_mapped_desc n n' then
                      true
                    else if check_st_flag then
                      st_has_crossing_mapped_desc n n'
                    else
                      false
                  in
                  [%debug_log "%a <- %a (%B)" nups n nups n' b];
                  b
                with
                  Not_found -> false
              ) ca'

          with
            Not_found -> false
        in
        [%debug_log "is_frontier --> %B" is_frontier];
        let genmov =
          if is_frontier then (* cf. regression:java/Tar.java: 384L-397L --> 459L-472L *)
            fun n -> gen_moves (mid_gen()) Edit.Mnormal n
          else
            gen_moves movid kind
        in
        Array.iter genmov nd#initial_children

      end

    in (* end of func gen_moves *)

    edits#iter_moves_bottomup
      (function
        | Edit.Move(mid, kind, (info1, _), _) as ed -> begin
            let _ = ed in
            [%debug_log "checking move: %s" (Edit.to_string ed)];
            let nd1 = Info.get_node info1 in
            Array.iter (gen_moves !mid !kind) nd1#initial_children
        end
        | _ -> assert false
      );

    mid_chg_tbl

  (* end of func group_moves *)


  let find_keyroots
      options
      ?(relax=false)
      ?(ignore_sequence=false)
      ?(filt=fun _ _ -> true)
      (tree1 : tree_t)
      (tree2 : tree_t)
      (nmapping : node_t Node_mapping.c)
      =
    let cands = ref [] in

    nmapping#iter_unsettled
      (fun nd1 nd2 ->

        if filt nd1 nd2 then begin

          [%debug_log "checking %a-%a" nups nd1 nups nd2];

          let moveon =
            (not ignore_sequence || not nd1#data#is_sequence)
              &&
            (relax && nd1#data#_anonymized_label = nd2#data#_anonymized_label ||
            not relax && nd1#data#eq nd2#data)
          in

          if moveon then begin

            try
              if can_be_keyroot tree1 nd1 && can_be_keyroot tree2 nd2 then begin

                let chn1 = nd1#initial_children in
                let chn2 = nd2#initial_children in

                [%debug_log "chn1: [%a]" naps chn1];
                [%debug_log "chn2: [%a]" naps chn2];

                let cond =
                  Array.exists
                    (fun n ->
                      try
                        let n' = nmapping#find n in
                        [%debug_log "%a -> %a" nups n nups n'];
                        not (Array.memq n' chn2)
                      with
                        Not_found -> true
                    ) chn1
                ||
                  Array.exists
                    (fun n ->
                      try
                        let n' = nmapping#inv_find n in
                        [%debug_log "%a <- %a" nups n' nups n];
                        not (Array.memq n' chn1)
                      with
                        Not_found -> true
                    ) chn2
                in
                if cond then begin
                  [%debug_log " -> candidate"];
                  cands := (nd1, nd2)::!cands;
                end
              end
            with
              Not_found -> ()
          end
        end
      );

    begin %debug_block
      List.iter
        (fun (n1, n2) ->
          [%debug_log "cands: %a(size=%d) - %a(size=%d)"
            nups n1 (tree1#whole_initial_subtree_size n1)
            nups n2 (tree2#whole_initial_subtree_size n2)]
        ) !cands;
    end;

    let (*cands_large*)_, cands_moderate =
      let thresh = options#match_algo_threshold in
      List.partition
        (fun (n1, n2) ->
          tree1#whole_initial_subtree_size n1 > thresh ||
          tree2#whole_initial_subtree_size n2 > thresh
         ) !cands
    in

    let finalize cnds =
      List.filter
        (fun (nd1, nd2) ->
          let b =
            not
              (
               List.exists
                 (fun (n1, n2) ->
                   let x =
                     not (n1#data#is_sequence && n1 == nd1#initial_parent) &&
                     not (n2#data#is_sequence && n2 == nd2#initial_parent) &&
                     tree1#is_initial_ancestor n1 nd1 && tree2#is_initial_ancestor n2 nd2
                   in
                   if x then
                     [%debug_log "%a-%a is contained in %a-%a"
                       nups nd1 nups nd2 nups n1 nups n2];
                   x
                 ) cnds
              )
          in
          b
        ) cnds
    in

    let fin_cands_large = finalize !cands (* cands_large *) in
    let fin_cands_moderate = finalize cands_moderate in

    begin %debug_block
      List.iter
        (fun (n1, n2) ->
          [%debug_log "large: %a(size=%d) - %a(size=%d)"
            nups n1 (tree1#whole_initial_subtree_size n1)
            nups n2 (tree2#whole_initial_subtree_size n2)];
        ) fin_cands_large;
      List.iter
        (fun (n1, n2) ->
          [%debug_log "moderate: %a(size=%d) - %a(size=%d)"
            nups n1 (tree1#whole_initial_subtree_size n1)
            nups n2 (tree2#whole_initial_subtree_size n2)]
        ) fin_cands_moderate;
    end;

    fin_cands_large, fin_cands_moderate
  (* end of func find_keyroots *)


  let is_odd_relabel ?(exact=false)
      (tree1 : tree_t)
      (tree2 : tree_t)
      (nmapping : node_t Node_mapping.c)
      nd1 nd2
      =
    [%debug_log "%a-%a" nups nd1 nups nd2];

    let weak_equal =
      nd1#data#eq nd2#data ||
      nd1#data#has_non_trivial_tid && nd2#data#has_non_trivial_tid &&
      (
       nd1#data#anonymized_label = nd2#data#anonymized_label ||
       nd1#data#anonymized2_label = nd2#data#anonymized2_label
      )
    in
    [%debug_log "weak_equal=%B" weak_equal];

    if not exact && weak_equal then
      false
    else

    let allowed = nd1#data#relabel_allowed nd2#data in
    [%debug_log "allowed=%B" allowed];

    if not allowed then
      false
    else

    (* check ancestors *)
    let is_odd_anc =
      try
        let an1 = Sourcecode.find_nearest_mapped_ancestor_node nmapping#mem_dom nd1 in
        let an2 = Sourcecode.find_nearest_mapped_ancestor_node nmapping#mem_cod nd2 in
        (try
          let an1' = nmapping#find an1 in
          [%debug_log "%a->%a" nups an1 nups an1'];
          an1' != an2
        with _ -> false) ||
        (try
          let an2' = nmapping#inv_find an2 in
          [%debug_log "%a<-%a" nups an2' nups an2];
          an2' != an1
        with _ -> false)
      with
        _ -> false
    in
    [%debug_log "is_odd_anc=%B" is_odd_anc];

    (* check descendants *)
    let ds1 = Sourcecode.find_nearest_mapped_descendant_nodes nmapping#mem_dom nd1 in
    let ds2 = Sourcecode.find_nearest_mapped_descendant_nodes nmapping#mem_cod nd2 in

    let exists_in_subtree nd tree rt =
      try
        tree#fast_scan_whole_initial_subtree rt
          (fun n ->
            if nd#data#eq n#data then
              raise Exit
          );
        false
      with
        Exit -> true
    in

    let is_odd_desc =
      (List.exists
         (fun dn ->
           let dn' = nmapping#find dn in

           [%debug_log "\tmapped descendant of %a: %a (-> %a)" nups nd1 nups dn nups dn'];

           let dn_exists_in_nd2tree = exists_in_subtree dn tree2 nd2 in

           if
             not dn_exists_in_nd2tree &&
             dn#data#is_named_orig &&
             dn#data#eq dn'#data &&
             (not (tree2#initial_subtree_mem nd2 dn'))
           then begin

             [%debug_log "\todd mapping: %a-%a" nups nd1 nups nd2];

             true
           end
           else
             false
         ) ds1)
    ||
      (List.exists
         (fun dn ->
           let dn' = nmapping#inv_find dn in

           [%debug_log "\tmapped descendant of %a: %a (-> %a)" nups nd2 nups dn nups dn'];

           let dn_exists_in_nd1tree = exists_in_subtree dn tree1 nd1 in

           if
             not dn_exists_in_nd1tree &&
             dn#data#is_named_orig &&
             dn#data#eq dn'#data &&
             (not (tree1#initial_subtree_mem nd1 dn'))
           then begin

             [%debug_log "\todd mapping: %a-%a" nups nd1 nups nd2];

             true
           end
           else
             false
         ) ds2)
    in
    [%debug_log "is_odd_desc=%B" is_odd_desc];

(*
    let not_absurd =
      allowed && (check_relabel options ~exact tree1 tree2 nd1 nd2 nmapping)
    in

    [%debug_log "not_absurd=%B" not_absurd];

    let is_odd1 = not not_absurd in
*)
(*    is_odd_desc || is_odd1 *)
    (*let same_name =
      nd1#data#is_named_orig && nd2#data#is_named_orig &&
      get_orig_name nd1 = get_orig_name nd2
    in
    [%debug_log "same_name=%B" same_name];*)

    let b0 =
      if exact then
        is_odd_desc && is_odd_anc(* && not same_name*)
      else
        (is_odd_desc || is_odd_anc)(* && not same_name*)
    in
    let b = b0(* || (not allowed)*) in
    [%debug_log "%a-%a --> %B" nups nd1 nups nd2 b];
    b
  (* end of func is_odd_relabel *)


(*
  let estimate_subtree_similarity tree1 tree2 nd1 nd2 =
    let getsz t n = t#whole_initial_subtree_size n in
    let t1 = new Tree.c nd1 false in
    let t2 = new Tree.c nd2 false in
    let m, em, r = Treediff.fast_match_trees t1 t2 in
    let nmapped =
      List.fold_left
        (fun s (n1, n2) ->
          s +
          (if n1#is_leaf then getsz tree1 n1 else 1) +
          (if n2#is_leaf then getsz tree2 n2 else 1)
        ) 0 (m @ em @ r)
    in
    (float (nmapped + nmapped)) /. (float ((getsz tree1 nd1) + (getsz tree2 nd2)))
*)


  let eliminate_enclaves
      options
      (cenv : (node_t, tree_t) Comparison.c)
      keyroots
      (tree1 : tree_t)
      (tree2 : tree_t)
      (nmapping : node_t Node_mapping.c)
      (ref_nmapping : node_t Node_mapping.c)
      =
    [%debug_log "** ELIMINATING ENCLAVES...\n"];

    let new_pairs1 = Nodetbl.create 0 in
    let new_pairs2 = Nodetbl.create 0 in

    let new_pairs_add (nd1, nd2) =
      [%debug_log "%a-%a" nups nd1 nups nd2];
      try
        let nd1' = Nodetbl.find new_pairs1 nd1 in
        if nd1' == nd2 then
          ()
        else
          if nd1#data#eq nd2#data && not (nd1#data#eq nd1'#data) then begin
            Nodetbl.remove new_pairs1 nd1;
            raise Not_found
          end
          else
            [%debug_log "! conflict with %a-%a, not added!" nups nd1 nups nd1'];
      with
        Not_found ->
          try
            let nd2' = Nodetbl.find new_pairs2 nd2 in
            if nd2' == nd1 then
              ()
            else
              if nd1#data#eq nd2#data && not (nd2#data#eq nd2'#data) then begin
                Nodetbl.remove new_pairs2 nd2;
                raise Not_found
              end
              else
              [%debug_log "! conflict with %a-%a, not added!" nups nd2' nups nd2];
          with
            Not_found ->
              Nodetbl.add new_pairs1 nd1 nd2;
              Nodetbl.add new_pairs2 nd2 nd1
    in
(*
    let new_pairs_remove (nd1, nd2) =
      [%debug_log "removing %a-%a" nups nd1 nups nd2];
      Nodetbl.remove new_pairs1 nd1;
      Nodetbl.remove new_pairs2 nd2;
    in
*)

    let new_pairs_mem1 nd1 = Nodetbl.mem new_pairs1 nd1 in
    let new_pairs_mem2 nd2 = Nodetbl.mem new_pairs2 nd2 in

    let add_enclave nd1 nd2 =
      [%debug_log "%a-%a" nups nd1 nups nd2];

      if not (nmapping#is_locked_node nd1 || nmapping#is_locked_node nd2) then
        if
          nmapping#mem_settled nd1 ||
          nmapping#mem_cod_settled nd2
        then (* impossible? *)
          [%debug_log "settled mapping exists, aborted"]
        else
          new_pairs_add (nd1, nd2)
      else
        [%debug_log "locked pair: %a-%a" nups nd1 nups nd2]
    in


    let find_enclaves nd1 nd2 =
      begin %debug_block
        [%debug_log "finding enclaves of %a-%a (%a-%a)" nups nd1 nups nd2 ngps nd1 ngps nd2];
      end;

      let otree = tree1#make_subtree_from_node nd1 in
      let ntree = tree2#make_subtree_from_node nd2 in
      nd1#hide_parent;
      nd2#hide_parent;

(*
      begin %debug_block
        [%debug_log "|T1(root:%a)|=%d |T2(root:%a)|=%d"
          nups nd1 otree#size nups nd2 ntree#size];

        [%debug_log "T1:\n%s" otree#to_string];
        [%debug_log "T2:\n%s" ntree#to_string];
      end;
*)
      let osize = otree#size in
      let nsize = ntree#size in
      if osize > 1 && nsize > 1 then begin

        let matches, extra_matches, relabels =
          if
            osize > options#match_algo_threshold ||
            nsize > options#match_algo_threshold
          then
            Treediff.fast_match_trees otree ntree ref_nmapping
          else
            let check_relabels =
              if
                nd1#data#is_boundary && nd2#data#is_boundary ||
                nd1#data#is_block && nd2#data#is_block
              then
                let r = float (min osize nsize) /. float (max osize nsize) in
                [%debug_log "r=%f" r];
                r > 0.8
              else
                true
            in
            [%debug_log "check_relabels=%B %s-%s" check_relabels
              nd1#data#to_string nd2#data#to_string];
            Treediff.match_trees cenv otree ntree ~check_relabels nmapping ref_nmapping
        in

        let matches_ = matches in
(*
  let matches_ = (* does not override mapping because matches are not so reliable, especially in case of permutation *)
  List.filter
  (fun (nd1, nd2) ->
  not (
  (nmapping#mem_dom nd1 && not (nmapping#mem_dom_weak nd1)) ||
  (nmapping#mem_cod nd2 && not (nmapping#mem_cod_weak nd2)))
  ) matches
  in
 *)

        begin %debug_block
          let cmp (n1, _) (n2, _) = Stdlib.compare n1#gindex n2#gindex in
          List.iter
            (fun (n1, n2) ->
              [%debug_log "match (filtered): %a-%a (%a-%a)" nups n1 nups n2 ngps n1 ngps n2]
            ) matches_;
          List.iter
            (fun (n1, n2) ->
              [%debug_log "match (filtered:gindex): %a-%a" ngps n1 ngps n2]
            ) (List.fast_sort cmp matches_);
        end;

        let extra_matches_ = (* does not override _strict_ mapping because extra matches are not so reliable *)
          List.filter
            (fun (nd1, nd2) ->
              let conflict1 =
                try
                  let nd1' = nmapping#find nd1 in
                  nd1#data#eq nd1'#data
                with
                  Not_found -> false
              in
              let conflict2 =
                try
                  let nd2' = nmapping#inv_find nd2 in
                  nd2#data#eq nd2'#data
                with
                  Not_found -> false
              in
              not (conflict1 || conflict2)
            ) extra_matches
        in

        begin %debug_block
          let cmp (n1, _) (n2, _) = Stdlib.compare n1#gindex n2#gindex in
          List.iter
            (fun (n1, n2) ->
              [%debug_log "extra_match (filtered): %a-%a (%a-%a)" nups n1 nups n2 ngps n1 ngps n2]
            ) extra_matches_;
          List.iter
            (fun (n1, n2) ->
              [%debug_log "extra_match (filtered:gindex): %a-%a" ngps n1 ngps n2]
            ) (List.fast_sort cmp extra_matches_);
        end;

        let temp_nmapping = new Node_mapping.c cenv in
        ignore (temp_nmapping#merge nmapping);

        let to_be_removed = ref [] in

        let matches_and_extra_matches = matches_ @ extra_matches_ in

        List.iter
          (fun (nd1, nd2) ->
            let score = ref (-1.0) in
            let cond1 =
              try
                let nd1' = temp_nmapping#find nd1 in
                if nd1' != nd2 then

                  if next_to_each_other nd2 nd1' then begin
                    to_be_removed := (nd1, nd1') :: !to_be_removed;
                    true
                  end
                  else begin

                  score := cenv#get_adjacency_score nd1 nd2;
                  let score' = cenv#get_adjacency_score nd1 nd1' in
                  if !score >= score' then begin
                    to_be_removed := (nd1, nd1') :: !to_be_removed;
                    true
                  end
                  else begin
                    to_be_removed := (nd1, nd2) :: !to_be_removed;
                    false
                  end

                  end
                else
                  false
              with
                Not_found -> true
            in
            let cond2 =
              try
                let nd2' = temp_nmapping#inv_find nd2 in
                if nd2' != nd1 then

                  if next_to_each_other nd1 nd2' then begin
                    to_be_removed := (nd2', nd2) :: !to_be_removed;
                    true
                  end
                  else begin

                  if !score < 0.0 then
                    score := cenv#get_adjacency_score nd1 nd2;
                  let score' = cenv#get_adjacency_score nd2' nd2 in
                  if !score >= score' then begin
                    to_be_removed := (nd2', nd2) :: !to_be_removed;
                    true
                  end
                  else begin
                    to_be_removed := (nd1, nd2) :: !to_be_removed;
                    false
                  end

                  end
                else
                  false
              with
                Not_found -> true
            in

            if cond1 && cond2 then
              ignore (temp_nmapping#add_unsettled nd1 nd2)

          ) matches_and_extra_matches;


        let matches_and_extra_matches_ =
          List.filter (fun (n1, n2) -> not (List.mem (n1, n2) !to_be_removed)) matches_and_extra_matches
        in

        begin %debug_block
          List.iter
            (fun (n1, n2) ->
              [%debug_log "matches_and_extra_matches_: %a-%a (%a-%a)" nups n1 nups n2 ngps n1 ngps n2]
            ) matches_and_extra_matches_;
        end;

        let relabels_checked =
          List.filter
            (fun (nd1, nd2) ->
              not (is_odd_relabel ~exact:true tree1 tree2 temp_nmapping nd1 nd2)
            ) relabels
        in
        begin %debug_block
          List.iter
            (fun (n1, n2) ->
              [%debug_log "relabels_checked: %a-%a (%a-%a)" nups n1 nups n2 ngps n1 ngps n2]
            ) relabels_checked
        end;

        let relabels_ = (* does not override mapping because relabels are not so reliable *)
          List.filter
            (fun (nd1, nd2) ->
              [%debug_log "filtering relabel: %a-%a" nups nd1 nups nd2];

(*(nd1#data#is_named_orig && nd2#data#is_named_orig && nd1#data#get_name = nd2#data#get_name) ||*)

              let conflict1 = nmapping#mem_dom nd1 && nmapping#find nd1 != nd2 in
              let conflict2 = nmapping#mem_cod nd2 && nmapping#inv_find nd2 != nd1 in

              [%debug_log "conflict1:%B conflict2:%B" conflict1 conflict2];

              let ncross = ref (-1) in
              let adj = ref (-1.0) in

              let cond0 =
                if conflict1 || conflict2 then

                  let ok1, _, remover1 =
                    if conflict1 then
                      try
                        let nd1' = nmapping#find nd1 in

                        [%debug_log "relabel: %a-%a conflicts with %a-%a"
                          nups nd1 nups nd2 nups nd1 nups nd1'];

                        if nmapping#is_stable_pair nd1 nd1' then begin
                          [%debug_log "relabel: %a-%a: stable" nups nd1 nups nd1'];
                          false, None, (fun () -> ())
                        end
                        else
                          let alab1 = nd1#data#_anonymized3_label in
                          [%debug_log "alab1=%s alab1'=%s alab2=%s" nd1#data#anonymized3_label
                            nd1'#data#anonymized3_label nd2#data#anonymized3_label];
                          if
                            nd1'#data#_anonymized3_label = alab1 &&
                            nd2#data#_anonymized3_label <> alab1 && not (nd1#data#relabel_allowed nd2#data)
                          then begin
                            [%debug_log "relabel: %a-%a: anonymized3 label match (%s)"
                              nups nd1 nups nd1' nd1#data#anonymized3_label];
                            false, None, (fun () -> ())
                          end
                          else

                          let b = ref false in
                          let dnc = ref None in
                          cenv#compare_mappings nmapping
                            nd1 nd1' (fun d _ _ -> dnc := d)
                            nd1 nd2 ~ncrossing_new:ncross ~adjacency_new:adj
                            (fun d _ _ -> b := true; dnc := d);
                          !b, !dnc, (fun () -> ignore (nmapping#remove nd1 nd1'))
                      with
                        Not_found -> assert false
                    else
                      true, None, (fun () -> ())
                  in
                  let ok2, _, remover2 =
                    if conflict2 then
                      try
                        let nd2' = nmapping#inv_find nd2 in
                        [%debug_log "relabel: %a-%a conflicts with %a-%a"
                          nups nd1 nups nd2 nups nd2' nups nd2];
                        if nmapping#is_stable_pair nd2' nd2 then begin
                          [%debug_log "relabel: %a-%a: stable" nups nd2' nups nd2];
                          false, None, (fun () -> ())
                        end
                        else
                          let b = ref false in
                          let dnc = ref None in
                          cenv#compare_mappings nmapping
                            nd2' nd2 (fun d _ _ -> dnc := d)
                            nd1 nd2 ~ncrossing_new:ncross ~adjacency_new:adj
                            (fun d _ _ -> b := true; dnc := d);
                          !b, !dnc, (fun () -> ignore (nmapping#remove nd2' nd2))
                      with
                        Not_found -> assert false
                    else
                      true, None, (fun () -> ())
                  in
                  let b =
                    (ok1 && ok2) (* ||
               (ok1 && not ok2 && match dnc1, dnc2 with Some d1, Some d2 -> d1 > d2 | _ -> false) ||
               (not ok1 && ok2 && match dnc1, dnc2 with Some d1, Some d2 -> d1 < d2 | _ -> false) *)
                  in
                  if b then begin
                    remover1();
                    remover2()
                  end;
                  b

                else
                  true
              in (* cond0 *)
              [%debug_log "cond0=%B" cond0];

              cond0 &&
              try
                let pnd1 = nd1#initial_parent in
                let pnd2 = nd2#initial_parent in
                try
                  let pnd1' = nmapping#find pnd1 in

                  [%debug_log "parent nmapping: %a -> %a" nups pnd1 nups pnd1'];

                  pnd1' == pnd2

                with Not_found ->
                  let parent_cond =
                    try
                      (List.assq pnd1 relabels_checked) == pnd2
                    with Not_found ->
                      (List.assq pnd1 matches_and_extra_matches_) == pnd2
                  in
                  (*let parent_cond =
                    let pl = relabels_checked @ matches_and_extra_matches_ in
                    (try
                      (List.assq pnd1 pl) == pnd2
                    with _ ->
                      let pred1 x =
                        try
                          (List.assq x pl) == pnd2
                        with _ -> false
                      in
                      has_p_ancestor pred1 pnd1
                    ) ||
                    (try
                      (inv_assq pnd2 pl) == pnd1
                    with _ ->
                      let pred2 x =
                        try
                          (inv_assq x pl) == pnd1
                        with _ -> false
                      in
                      has_p_ancestor pred2 pnd2)
                  in*)
                  [%debug_log "parent_cond=%B" parent_cond];

(*
                    let n_nodes_of_same_cat nodes nd =
                      let alab = nd#data#_anonymized_label in
                      List.fold_left
                        (fun count al ->
                          if alab = al then
                            count + 1
                          else
                            count
                        ) 0 (List.map (fun n -> n#data#_anonymized_label) nodes)
                    in
                    let n_nodes_of_same_cat1 =
                      n_nodes_of_same_cat (Array.to_list pnd1#initial_children) nd1
                    in
                    let n_nodes_of_same_cat2 =
                      n_nodes_of_same_cat (Array.to_list pnd2#initial_children) nd2
                    in
                    let cat_cond =
                      n_nodes_of_same_cat1 = 1 && n_nodes_of_same_cat2 = 1
                    in

                    begin %debug_block
                      [%debug_log "relabel: %a-%a (parent: %a-%a, num of children of same category not matched: %d-%d)"
                        nups nd1 nups nd2
                        nups pnd1 nups pnd2
                        n_nodes_of_same_cat1 n_nodes_of_same_cat2];
                      [%debug_log "parent_cond:%B cat_cond:%B --> filtered:%B" parent_cond cat_cond (not cond)];
                    end;

*)
                    let n_nodes_of_same_cat_not_matched =
                      let cs1 = Array.to_list pnd1#initial_children in
                      let cs2 = Array.to_list pnd2#initial_children in
                      let alab1 = nd1#data#_anonymized_label in
                      let alab2 = nd2#data#_anonymized_label in
                      let filt alab n = n#data#_anonymized_label = alab in
                      let to_array x = Array.of_list (List.map (fun n -> n#data#_label) x) in
                      let a1 = to_array (List.filter (filt alab1) cs1) in
                      let a2 = to_array (List.filter (filt alab2) cs2) in
                      let mat, _, _, _ = Adiff.adiff a1 a2 in
                      (Array.length a1) + (Array.length a2) - ((List.length mat) * 2)
                    in
                    [%debug_log "n_nodes_of_same_cat_not_matched=%d" n_nodes_of_same_cat_not_matched];

                    let cat_cond = n_nodes_of_same_cat_not_matched = 2 in

                    let cond = parent_cond && cat_cond in
begin %debug_block
  [%debug_log "relabel: %a-%a (parent: %a-%a, num of children of same category not matched: %d)"
               nups nd1 nups nd2 nups pnd1 nups pnd2 n_nodes_of_same_cat_not_matched];
  [%debug_log "parent_cond:%B cat_cond:%B --> filtered:%B" parent_cond cat_cond (not cond)];
end;
                    cond
              with
              | Otree.Parent_not_found _
              | Not_found -> begin
                  try
                    let moveon_ n = not n#data#is_boundary in
                    let find_anc = Sourcecode.find_nearest_mapped_ancestor_node ~moveon_ in
                    let an1 = find_anc nmapping#mem_dom nd1 in
                    let an2 = find_anc nmapping#mem_cod nd2 in
                    [%debug_log "nd1=%s" nd1#data#to_string];
                    [%debug_log "nd2=%s" nd2#data#to_string];
                    [%debug_log "an1=%s" an1#data#to_string];
                    [%debug_log "an2=%s" an2#data#to_string];
                    (an1#data#eq an2#data(* ||
                     an1#data#_stripped_label = an2#data#_stripped_label*)
                    ) &&
                    (
                     an1 == nd1#initial_parent
                    ||
                     an2 == nd2#initial_parent
                    ||
                     (is_use nd1 || nd1#data#has_non_trivial_value) &&
                     nd1#data#anonymized_label = nd2#data#anonymized_label
                    ) &&
                    try
                      let an1' = nmapping#find an1 in
                      [%debug_log "%a->%a" nups an1 nups an1'];
                      let b = an1' == an2 in
                      [%debug_log "%B" b];
                      b
                    with Not_found -> begin
                      let b =
                        try
                          (List.assq an1 relabels_checked) == an2
                        with Not_found ->
                          try
                            (List.assq an1 matches_and_extra_matches_) == an2
                          with Not_found -> false
                      in
                      [%debug_log "%B" b];
                      b
                    end
                  with _ -> false
              end
            ) (List.fast_sort (fun (n0, _) (n1, _) -> Stdlib.compare n1#gindex n0#gindex) relabels)
        in

        begin %debug_block
          List.iter
            (fun (n1, n2) ->
              [%debug_log "relabels (filtered): %a-%a" nups n1 nups n2]
            ) relabels_;
        end;

        let get_digest tree n =
          let d_opt = n#data#_digest in
          let res =
            if d_opt = None then
              if n#initial_nchildren > 0 then
                Some (tree#initial_subtree_digest n)
              else
                None
            else
              d_opt
          in
          res
        in

        List.iter (* for isos and moves *)
          (fun (nd1, nd2) ->

            [%debug_log "checking <%a-%a>" nups nd1 nups nd2];

            let adj = cenv#get_adjacency_score nd1 nd2 in

            [%debug_log " adjacency=%f" adj];

            if adj > 0.0 then begin

              let nprox = nmapping#get_proximity ~extra:new_pairs1 nd1 nd2 in

              let prox = nprox#primary_prox in

              [%debug_log " proximity=%d" prox];

              let passed1 =
                try
                  let n2 = nmapping#find nd1 in

                  if n2 == nd2 then
                    raise Found;

                  if not (nd1#data#eq n2#data) && nd1#data#eq nd2#data then
                    raise Not_found;

                  let nprox_before1 = nmapping#get_proximity nd1 n2 in

                  let prox_before1 = nprox_before1#primary_prox in

                  [%debug_log " proximity (before:%a->%a)=%d" nups nd1 nups n2 prox_before1];

                  let cond =
                    if prox > prox_before1 then
                      if nprox#low_confidence then
                        let pn1, pn2 = nprox#primary_pivot in
                        let pn_b1, pn_b2 = nprox_before1#primary_pivot in
                        let a = cenv#get_adjacency_score pn1 pn2 in
                        let a_b = cenv#get_adjacency_score pn_b1 pn_b2 in
                        if a >= a_b then
                          true
                        else
                          let prox2 = nprox#secondary_prox in

                          [%debug_log " secondary_prox(%a,%a)=%d" nups nd1 nups nd2 prox2];

                          if prox2 > prox_before1 then
                            true
                          else if prox2 = prox_before1 then begin
                            let adj_before1 = cenv#get_adjacency_score nd1 n2 in

                            [%debug_log " adjacency(before:%a->%a)=%f" nups nd1 nups n2 adj_before1];

                            adj > adj_before1
                          end
                          else
                            false
                      else
                        true
                    else if prox = prox_before1 then begin
                      let adj_before1 = cenv#get_adjacency_score nd1 n2 in

                      [%debug_log " adjacency(before:%a->%a)=%f" nups nd1 nups n2 adj_before1];

                      adj > adj_before1
                    end
                    else
                      false
                  in

                  cond && n2 != nd2

                with Not_found -> true | Found -> false
              in
              let passed2 =
                try
                  let n1 = nmapping#inv_find nd2 in

                  if n1 == nd1 then
                    raise Found;

                  if not (nd2#data#eq n1#data) && nd1#data#eq nd2#data then
                    raise Not_found;

                  let nprox_before2 = nmapping#get_proximity n1 nd2 in
                  let prox_before2 = nprox_before2#primary_prox in

                  [%debug_log " proximity (before:%a<-%a)=%d" nups n1 nups nd2 prox_before2];

                  let cond =
                    if prox > prox_before2 then
                      if nprox#low_confidence then
                        let pn1, pn2 = nprox#primary_pivot in
                        let pn_b1, pn_b2 = nprox_before2#primary_pivot in
                        let a = cenv#get_adjacency_score pn1 pn2 in
                        let a_b = cenv#get_adjacency_score pn_b1 pn_b2 in
                        if a >= a_b then
                          true
                        else
                          let prox2 = nprox#secondary_prox in

                          [%debug_log " secondary_prox (%a,%a)=%d" nups nd1 nups nd2 prox2];

                          if prox2 > prox_before2 then
                            true
                          else if prox2 = prox_before2 then begin
                            let adj_before2 = cenv#get_adjacency_score n1 nd2 in

                            [%debug_log " adjacency (before:%a<-%a)=%f" nups n1 nups nd2 adj_before2];

                            adj > adj_before2
                          end
                          else
                            false
                      else
                        true
                    else if prox = prox_before2 then begin
                      let adj_before2 = cenv#get_adjacency_score n1 nd2 in

                      [%debug_log " adjacency (before:%a<-%a)=%f" nups n1 nups nd2 adj_before2];

                      adj > adj_before2
                    end
                    else
                      false
                  in

                  cond && n1 != nd1

                with Not_found -> true | Found -> false
              in
              if passed1 && passed2 then begin
                add_enclave nd1 nd2;
                let d1 = get_digest tree1 nd1 in
                let d2 = get_digest tree2 nd2 in
                if d1 = d2 && d1 <> None then begin
                  begin %debug_block
                      begin
                        match d1 with
                        | Some d -> begin
                            [%debug_log "d1=(Some %s)" (Digest.to_hex d)];
                            [%debug_log "nd1: %s" nd1#to_string];
                            [%debug_log "nd1 (initial): %s" nd1#initial_to_string];
                        end
                        | None -> ()
                      end;
                      begin
                        match d2 with
                        | Some d -> begin
                            [%debug_log "d2=(Some %s)" (Digest.to_hex d)];
                            [%debug_log "nd2: %s" nd2#to_string];
                            [%debug_log "nd2 (initial): %s" nd2#initial_to_string];
                        end
                        | None -> ()
                      end;
                  end;
                  let l1 = ref [] in
                  let l2 = ref [] in
                  tree1#fast_scan_whole_initial_subtree nd1 (fun n -> l1 := n :: !l1);
                  tree2#fast_scan_whole_initial_subtree nd2 (fun n -> l2 := n :: !l2);
                  List.iter2
                    (fun n1 n2 ->
                      if not (nmapping#is_locked_node n1 || nmapping#is_locked_node n2) then
                        new_pairs_add (n1, n2)
                      else
                        [%debug_log "locked pair: %a-%a" nups n1 nups n2]
                    ) !l1 !l2
                end
              end

            end
          ) (matches_and_extra_matches_ @ relabels_ );
      end; (* if otree#size > 1 && ntree#size > 1 *)

      nd1#unhide_parent;
      nd2#unhide_parent;

    in (* end of func find_enclaves *)

    let reduced_mapping_list = nmapping#get_reduced_mapping_list() in
    let has_crossing_or_incompatible_mapping rt1 (*rt2*)_ =
      let has_crossing_or_incompatible_mapping nd1 nd2 =
        List.exists
          (function
            | (n1, n2)::_ -> begin
                n1 != nd1 && n2 != nd2 &&
                let b =
	          Node_mapping.is_crossing nd1 nd2 n1 n2 ||
                  Node_mapping.is_incompatible tree1 tree2 nd1 nd2 n1 n2
                in
                if b then
                  [%debug_log "%s-%s is crossing or incompatible with %s-%s"
                    nd1#data#to_string nd2#data#to_string
                    n1#data#to_string n2#data#to_string];
                b
            end
            | _ -> assert false
          ) reduced_mapping_list
      in
      let b =
        try
          tree1#fast_scan_whole_initial_subtree rt1
            (fun nd ->
              try
                let nd' = nmapping#find nd in
                if
                  has_crossing_or_incompatible_mapping nd nd'
                then
                  raise Exit
              with
                Not_found -> ()
            );
          false
        with
          Exit -> true
      in
      [%debug_log "%B" b];
      b
    in
    let keyroots_ =
      List.filter
        (fun (n1, n2) ->
          not (n1#data#is_boundary && not n2#data#is_boundary) ||
          has_crossing_or_incompatible_mapping n1 n2
        ) keyroots
    in
    let nkeyroots = List.length keyroots in
    let nkeyroots_ = List.length keyroots_ in
    [%debug_log "keyroots: %d -> %d" nkeyroots nkeyroots_];
    if nkeyroots > nkeyroots_ then
      Xprint.verbose options#verbose_flag
        "  number of key node pairs reduced from %d to %d" nkeyroots nkeyroots_;

    let sorted_keyroots =
      List.fast_sort
        (fun (n1, _) (n2, _) -> Stdlib.compare n1#gindex n2#gindex)
        keyroots_
    in
    Xprint.verbose options#verbose_flag
      "  finding enclaves from %d key node pairs..." (List.length sorted_keyroots);

    List.iter (fun (nd1, nd2) -> find_enclaves nd1 nd2) sorted_keyroots;

    Xprint.verbose options#verbose_flag "  %d found" (Nodetbl.length new_pairs1);

    begin %debug_block
      let new_pairs_list() =
        Nodetbl.fold (fun n1 n2 l -> (n1, n2)::l) new_pairs1 []
      in
      [%debug_log "enclaves: [\n%s\n]\n"
        (Xlist.to_string
           (fun (n1, n2) ->
             sprintf "%a-%a" nups n1 nups n2) "\n" (new_pairs_list()))];
    end;

    if options#trust_tree_matcher_flag then begin

      [%debug_log "removing old mappings..."];

      nmapping#filter (* removing old mappings *)
        (fun n1 n2 ->
          let b = not (new_pairs_mem1 n1 || new_pairs_mem2 n2) in
          if not b then
            [%debug_log "removing: %a-%a" nups n1 nups n2];
          b
        );

      [%debug_log "done."]; (* removing old mappings *)

      [%debug_log "adding new mappings..."];

      Nodetbl.iter
        (fun n1 n2 ->
          ignore (nmapping#add_unsettled n1 n2);

          [%debug_log " %a-%a ---> added" nups n1 nups n2]

        ) new_pairs1;

      [%debug_log "done."]

    end;

    [%debug_log "finished."]
  (* end of func eliminate_enclaves *)




  let eliminate_odd_relabels
      (tree1 : tree_t)
      (tree2 : tree_t)
      (nmapping : node_t Node_mapping.c)
      =
    [%debug_log "* ELIMINATING ODD RELABELS..."];

    nmapping#filter
      (fun nd1 nd2 ->

        [%debug_log "checking %a-%a" nups nd1 nups nd2];

        if not (nd1#data#eq nd2#data) then begin

          [%debug_log " -> relabel"];

          let is_odd = is_odd_relabel tree1 tree2 nmapping nd1 nd2 in

          if is_odd then
            [%debug_log "odd relabel: %a -- %a" nps nd1 nps nd2];

          not is_odd
        end
        else
          true
      );

    [%debug_log "ODD RELABELS ELIMINATED."]
  (* end of func eliminate_odd_relabels *)


  let is_crossing_with_untouched edits nmapping
      ?(full_scan=false)
      ?(mask=[])
      ?(incompatible_only=false)
      ?(weak=false)
      =
    edits#is_crossing_with_untouched
      ?full_scan:(Some full_scan)
      ?mask:(Some mask)
      ?incompatible_only:(Some incompatible_only)
      ?weak:(Some weak)
      nmapping


  let has_crossing_descendant tree1 tree2 nmapping nd1 nd2 =
    let b =
      try
        let pnd1 = nd1#initial_parent in
        let pnd2 = nd2#initial_parent in
        (
         try
           tree1#fast_scan_whole_initial_subtree nd1
             (fun n ->
               if n != nd1 then
                 try
                   let n' = nmapping#find n in
                   if
                     n' != nd2 &&
                     not (tree2#is_initial_ancestor nd2 n') &&
                     tree2#is_initial_ancestor pnd2 n'
                   then begin
                     [%debug_log "found: %a->%a" nups n nups n'];
                     raise Exit
                   end
                 with
                   Not_found -> ()
             );
           false
         with
           Exit -> true
        ) ||
        (
         try
           tree2#fast_scan_whole_initial_subtree nd2
             (fun n ->
               if n != nd2 then
                 try
                   let n' = nmapping#inv_find n in
                   if
                     n' != nd1 &&
                     not (tree1#is_initial_ancestor nd1 n') &&
                     tree1#is_initial_ancestor pnd1 n'
                   then begin
                     [%debug_log "found: %a<-%a" nups n' nups n];
                     raise Exit
                   end
                 with
                   Not_found -> ()
             );
           false
         with
           Exit -> true
        )
      with _ -> false
    in
    [%debug_log "%a-%a --> %B" nups nd1 nups nd2 b];
    b

  (*let has_mapped_descendant tree1 tree2 nmapping nd1 nd2 =
    let b =
      (
       try
         tree1#fast_scan_whole_initial_subtree nd1
           (fun n ->
             try
               let n' = nmapping#find n in
               if
                 tree2#is_initial_ancestor nd2 n'
               then
                 raise Exit
             with
               Not_found -> ()
           );
         false
       with
         Exit -> true
      ) ||
      (
       try
         tree2#fast_scan_whole_initial_subtree nd2
           (fun n ->
             try
               let n' = nmapping#inv_find n in
               if
                 tree1#is_initial_ancestor nd1 n'
               then
                 raise Exit
             with
               Not_found -> ()
           );
         false
       with
         Exit -> true
      )
    in
    [%debug_log "%a-%a --> %B" nups nd1 nups nd2 b];
    b*)

  let is_extendable_move tree1 tree2 nmapping n1 n2 =
    [%debug_log "n1=%a" nps n1];
    [%debug_log "n2=%a" nps n2];
    let has_crossing_descendant = has_crossing_descendant tree1 tree2 nmapping in
    let b =
      try
        let pn1 = n1#initial_parent in
        let pn2 = n2#initial_parent in
        [%debug_log "pn1=%a" nps pn1];
        [%debug_log "pn2=%a" nps pn2];
        let na1 = pn1#initial_children in
        let na2 = pn2#initial_children in
        let nna1 = Array.length na1 in
        let nna2 = Array.length na2 in
        [%debug_log "nna1=%d nna2=%d" nna1 nna2];
        nna1 = 1 && nna2 = 1 ||
        let lpos1 = Sourcecode.get_logical_pos n1 in
        let lpos2 = Sourcecode.get_logical_pos n2 in
        [%debug_log "lpos1=%d lpos2=%d" lpos1 lpos2];
        lpos1 = lpos2 &&
        let is_crossing_with_sibling =
          Array.exists
            (fun x1 ->
              x1 != n1 &&
              try
                let x2 = nmapping#find x1 in
                x2#initial_parent == pn2 &&
                Node_mapping.is_crossing n1 n2 x1 x2
              with
                _ -> false
            ) pn1#initial_children
        in
        [%debug_log "is_crossing_with_sibling=%B" is_crossing_with_sibling];
        not is_crossing_with_sibling &&
        (
         not (has_crossing_descendant n1 n2) &&
         let p1 = n1#initial_pos in
         let p2 = n2#initial_pos in
         [%debug_log "p1=%d p2=%d" p1 p2];
         (
          try
            let _n1 = na1.(p1-1) in
            let _n2 = na2.(p2-1) in
            [%debug_log "_n1=%a _n2=%a" nups _n1 nups _n2];
            not (has_crossing_descendant _n1 _n2)
          with _ -> false
         ) ||
         (
          try
            let n1_ = na1.(p1+1) in
            let n2_ = na2.(p2+1) in
            [%debug_log "n1_=%a n2_=%a" nups n1_ nups n2_];
            not (has_crossing_descendant n1_ n2_)
          with _ -> false
         )
        )
      with _ -> false
    in
    [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
    b


  let cmp_node_pairs ?(reverse=false) (n10, n20) (n11, n21) =
    let gi10, gi11 = n10#gindex, n11#gindex in
    let c =
      if reverse then
        Stdlib.compare gi11 gi10
      else
        Stdlib.compare gi10 gi11
    in
    if c = 0 then
      let gi20, gi21 = n20#gindex, n21#gindex in
      if reverse then
        Stdlib.compare gi21 gi20
      else
        Stdlib.compare gi20 gi21
    else
      c

  let sort_node_pairs ?(reverse=false) = List.fast_sort (cmp_node_pairs ~reverse)


 (*
  * glueing deletes and inserts
  *)
  let glue_deletes_and_inserts
      ?(first=false)
      ?(record_conflicted_pairs=false)
      options
      (cenv : (node_t, tree_t) Comparison.c)
      (tree1 : tree_t)
      (tree2 : tree_t)
      ?(override=false)
      ?(no_mapping_override=false)
      ?(no_moves=false)
      ?(last=false)
      ?(is_move=(fun _ _ -> false))
      ?(extend_move=(fun _ _ -> failwith "extend_move"))
      ?(add_move=(fun _ _ -> failwith "add_move"))
      ?(downward=false)
      ?(glue_filt=(fun _ _ -> true : node_t -> node_t -> bool))
      ?(use_binding_info=false)
      ?(rely_on_binding_info=false)
      ?(rely_on_context=false)
      ?(ignore_common=false)
      ?(edits_opt=None)
      (nmapping : node_t Node_mapping.c)
      (ref_nmapping : node_t Node_mapping.c)
      =
    Xprint.verbose options#verbose_flag "glueing deletes and inserts...";

    let _ = last in

    let shifted_nodes1 = Xset.create 0 in
    let shifted_nodes2 = Xset.create 0 in
    let shift_node1 n1 = Xset.add shifted_nodes1 n1 in
    let shift_node2 n2 = Xset.add shifted_nodes2 n2 in
    let is_shifted_node1 n1 = Xset.mem shifted_nodes1 n1 in
    let is_shifted_node2 n2 = Xset.mem shifted_nodes2 n2 in

    let is_possible_rename n1 n2 =
      let b = cenv#is_possible_rename ~strict:rely_on_binding_info n1 n2 in
      [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
      b
    in

    let check_context =
      if rely_on_context then
        fun n1 n2 ->
          let chk nmap =
            let chk_ca n ca =
              let alab = Obj.obj n#data#_anonymized_label in
              [%debug_log "n=%a alab=%s" nups n (Label.to_string alab)];
              let cl = List.filter (fun c -> c#data#_anonymized_label = alab) (Array.to_list ca) in
              match cl with
              | [_] -> true
              | _ -> false
            in
            let pn1 = n1#initial_parent in
            let pn2 = n2#initial_parent in
            (*((try nmap pn1 == pn2 with _ -> false) ||
            (try nmap pn1#initial_parent == pn2#initial_parent with _ -> false))*)
            (
             (try nmap pn1 == pn2 with _ -> false) ||
             (try nmap pn1#initial_parent == pn2#initial_parent with _ -> false) ||
             (try
               let ppn1 = pn1#initial_parent in
               chk_ca n1 pn1#initial_children && nmap ppn1 = pn2
             with _ -> false) ||
             (try
               let ppn2 = pn2#initial_parent in
               chk_ca n2 pn2#initial_children && nmap pn1 == ppn2
             with _ -> false)
             (*has_p_ancestor (fun x -> try nmap pn1 == x with _ -> false) n2 ||
             has_p_ancestor (fun x -> try nmap x == pn2 with _ -> false) n1 ||
             Array.exists
              (fun s1 ->
                s1 != n1 &&
                try
                  (nmap s1)#initial_parent == pn2
                with _ -> false
              ) pn1#initial_children*)
            )
              &&
            (n1#initial_nchildren = 0 && n2#initial_nchildren = 0 ||
            Array.exists
              (fun c1 ->
                try
                  (nmap c1)#initial_parent == n2
                with _ -> false
              ) n1#initial_children)
          in
          let b = chk nmapping#find(* || chk ref_nmapping#find*) in
          [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
          b
      else
        fun _ _ -> false
    in

    let relabel_allowed n1 n2 =
      (n1#data#relabel_allowed n2#data) &&
      (not use_binding_info || is_possible_rename n1 n2 || check_context n1 n2)
    in

    let bad_pairs = cenv#bad_pairs in

    begin %debug_block
      [%debug_log "START: first=%B record_conflicted_pairs=%B" first record_conflicted_pairs];
      [%debug_log "       override=%B no_mapping_override=%B" override no_mapping_override];
      [%debug_log "       no_moves=%B downward=%B use_binding_info=%B rely_on_binding_info=%B"
                        no_moves downward use_binding_info rely_on_binding_info];
      [%debug_log "       rely_on_context=%B ignore_common=%B last=%B"
                        rely_on_context ignore_common last];
      if not (Xset.is_empty bad_pairs) then begin
        Xset.iter
          (fun (n1, n2) ->
            [%debug_log "bad_pair: <%a-%a>" nups n1 nups n2]
          ) bad_pairs
      end;
      Nodetbl.iter
        (fun n1 n2 ->
          [%debug_log "stable_pair: %a-%a [%a]-[%a] %a" nups n1 nups n2 locps n1 locps n2 labps n1]
        ) nmapping#stable_pairs;
      [%debug_log "nmapping:\n%s\n" nmapping#to_string];
      (*[%debug_log "nmapping (gindex):\n%s\n" nmapping#to_string_gid];*)
    end;

    let is_bad_pair =
      let has_no_use_rename n1 n2 =
        let b =
          not (n1#data#eq n2#data) &&
          is_local_def n1 && is_local_def n2 &&
          not (cenv#has_use_rename n1 n2) &&
          let bid1 = Edit.get_bid n1 in
          let bid2 = Edit.get_bid n2 in
          try
            match cenv#get_use1 bid1, cenv#get_use2 bid2 with
            | [], [] -> false
            | [u1], [u2] -> begin
                [%debug_log "%a %a" nups u1 nups u2];
                not (u1#data#relabel_allowed u2#data)
            end
            | nl1, nl2 -> begin
                [%debug_log "{%a} {%a}" nsps nl1 nsps nl2];
                true
            end
          with _ -> true
        in
        [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
        b
      in
      let has_uniq_desc_match n1 n2 =
        let b =
          has_p_descendant
            (fun x1 ->
              try
                let x1' = nmapping#find x1 in
                tree2#is_initial_ancestor n2 x1' &&
                cenv#has_uniq_match x1 x1'
              with _ -> false
            ) n1
        in
        [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
        b
      in
      if ignore_common then
        fun n1 n2 ->
          let b =
            (
             (n1#data#is_common || n2#data#is_common) &&
             try
               let pn1 = n1#initial_parent in
               let pn2 = n2#initial_parent in
               pn1#data#is_sequence && pn2#data#is_sequence &&
               (pn1#initial_nchildren > 1 || pn2#initial_nchildren > 1) &&
               (not (n1#data#eq n2#data) || is_cross_boundary nmapping n1 n2) &&
               not (has_uniq_desc_match n1 n2)
             with _ -> false
            )
          ||
            Xset.mem bad_pairs (n1, n2)
          ||
            (try cenv#is_scope_breaking_mapping nmapping n1 n2 with Failure _ -> false)
          ||
            has_no_use_rename n1 n2
          in
          [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
          b
      else
        fun n1 n2 ->
          let b =
            Xset.mem bad_pairs (n1, n2)
          ||
            (
             try
               cenv#is_scope_breaking_mapping nmapping n1 n2 &&
               (
                try
                  let def1 = get_def_node cenv#tree1 n1 in
                  let def2 = get_def_node cenv#tree2 n2 in
                  [%debug_log "def1=%a" nps def1];
                  [%debug_log "def2=%a" nps def2];
                  not (is_local_def def1 && is_local_def def2) ||
                  nmapping#mem_dom def1 && nmapping#mem_cod def2
                with _ -> true
               )
             with Failure _ -> false
            )
          ||
            has_no_use_rename n1 n2
          ||
            (
             match edits_opt with
             | None -> false
             | Some edits ->
                 n1#data#is_named && n2#data#is_named && is_odd_relabel tree1 tree2 nmapping n1 n2 &&
                 is_crossing_with_untouched edits nmapping n1 n2
            )
          in
          [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
          b
    in (* is_bad_pair *)

    let starting_pairs =
      List.fold_left
       (fun l ((n1, n2) as np) ->
         if is_bad_pair n1 n2 then
           l
         else begin
           np::l
         end
       ) [] nmapping#starting_pairs_for_glueing
    in

    let is_mapped_pair n1 n2 =
      let b = nmapping#mem_dom n1 || nmapping#mem_cod n2 in
      [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
      b
    in
    (*let get_mapping u1 u2 =
      let u1', u2' =
        if nmapping#mem_dom u1 then
          u1, nmapping#find u1
        else if nmapping#mem_cod u2 then
          nmapping#inv_find u2, u2
        else
          raise Not_found
      in
      [%debug_log "%a-%a --> %a-%a" ups u1 ups u2 ups u1' ups u2'];
      u1', u2'
    in*)

    let can_override n1 n2 n1' n2' = (* n1-n2 beats n1'-n2' *)
      let b =
      try
        let pn1 = n1#initial_parent in
        let pn2 = n2#initial_parent in
        let pn1' = n1'#initial_parent in
        let pn2' = n2'#initial_parent in
        (*let ppn1 = pn1#initial_parent in
        let ppn2 = pn2#initial_parent in
        let ppn1' = pn1'#initial_parent in
        let ppn2' = pn2'#initial_parent in*)
        n1#data#is_named && n2#data#is_named &&
        not n1#data#is_named_orig && not n2#data#is_named_orig &&
        pn1#data#is_named_orig && pn2#data#is_named_orig &&
        pn1#initial_nchildren = 1 && pn2#initial_nchildren = 1 &&
        n1#data#eq n2#data &&
        is_mapped_pair pn1 pn2 &&
        pn1#data#eq pn2#data &&
        (*ppn1#data#is_named && ppn2#data#is_named && ppn1#data#eq ppn2#data &&*)
        not
          (
           n1'#data#is_named && n2'#data#is_named &&
           not n1'#data#is_named_orig && not n2'#data#is_named_orig &&
           pn1'#data#is_named_orig && pn2'#data#is_named_orig &&
           pn1'#initial_nchildren = 1 && pn2'#initial_nchildren = 1 &&
           n1'#data#eq n2'#data &&
           is_mapped_pair pn1' pn2' &&
           pn1'#data#eq pn2'#data(* &&
           ppn1'#data#is_named && ppn2'#data#is_named && ppn1'#data#eq pn2'#data*)
          )
      with
        _ -> false
      in
      if b then begin
        [%debug_log "%a-%a (%s-%s)" nups n1 nups n2
          (Loc.to_string n1#data#src_loc) (Loc.to_string n2#data#src_loc)];
        (*Printf.printf "! can_override: %s\n" n1#to_string*)
      end;
      b
    in

    let conflicted_pairs = Xset.create 0 in

    let calc_bonus nd1 nd2 =
      if nd1#data#is_anonymous || nd2#data#is_anonymous then
        if nd1#data#subtree_equals nd2#data then
          2
        else
          if nd1#data#eq nd2#data then
            1
          else
            0
      else
        if nd1#data#eq nd2#data then
          2
        else
          0
    in

    let default_score_up = 2 in
    let default_score_down = 1 in

    let get_scoring ?(base=(default_score_up,default_score_down)) n1 n2 =
      let s_up, s_down = base in
      let s =
        if nmapping#is_stable_pair n1 n2 then
          s_up + 3, s_down + 3
        else
          if n1#data#eq n2#data then
            if n1#path#equals n2#path then
              s_up + 2, s_down + 2
            else
              s_up + 1, s_down + 1

          else if n1#data#_anonymized_label = n2#data#_anonymized_label then
            if n1#path#equals n2#path then
              s_up + 2, s_down + 2
            else
              s_up + 1, s_down + 1

          else if relabel_allowed n1 n2 then
            if n1#path#equals n2#path then
              s_up + 2, s_down + 2
            else
              s_up + 1, s_down + 1

          else
            s_up, s_down
      in
      [%debug_log "%a-%a -> (%d,%d)" nups n1 nups n2 (fst s) (snd s)];
      s
    in
    let are_parents_mapped nd1 nd2 =
      let b =
        try
          let pnd1 = nd1#initial_parent in
          let pnd2 = nd2#initial_parent in
          nmapping#find pnd1 == pnd2 &&
          let ppnd1 = pnd1#initial_parent in
          let ppnd2 = pnd2#initial_parent in
          nmapping#find ppnd1 == ppnd2
        with
          _ -> false
      in
      [%debug_log "%a-%a --> %B" nups nd1 nups nd2 b];
      b
    in

    tree1#init; tree2#init;

    let reg_deferred_op, do_deferred_op, has_deferred_op =
      let deferred_op_tbl = Hashtbl.create 0 in
      let reg npair f = Hashtbl.add deferred_op_tbl npair f in
      let do_ npair =
        try
          let f = Hashtbl.find deferred_op_tbl npair in
          f()
        with
          _ -> ()
      in
      reg, do_, Hashtbl.mem deferred_op_tbl
    in

    let cands = ref ([] : ((node_t * node_t) * int ref) list) in

    let add_cand context nd1 nd2 score =
      let _ = context in

      if is_bad_pair nd1 nd2 then
        [%debug_log "bad pair: %a-%a" nups nd1 nups nd2]
(*
      else if not ((nd1#data#eq nd2#data) || is_possible_rename nd1 nd2) then
        [%debug_log "not possible rename: %a-%a" nups nd1 nups nd2]
*)
      else if no_mapping_override && is_mapped_pair nd1 nd2 then
        [%debug_log "each is mapped: %a->*, *<-%a" nups nd1 nups nd2]

      else if
        no_moves && (is_move nd1 nd2)
        (* && (not last || nd1#initial_nchildren > 0 && nd2#initial_nchildren > 0)*)
      &&
        let parents_mapped = are_parents_mapped nd1 nd2 in
        if
          parents_mapped &&
          (
           (*not nd1#data#is_order_insensitive && not nd2#data#is_order_insensitive &&*)
           (*not nd1#data#is_sequence && not nd2#data#is_sequence &&
           not nd1#data#is_ntuple && not nd2#data#is_ntuple &&*)
           is_extendable_move tree1 tree2 nmapping nd1 nd2
          )
        then begin
          [%debug_log "@"];
          try
            reg_deferred_op (nd1, nd2) (extend_move nd1 nd2);
            false
          with
            _ -> true
        end
        else if
          parents_mapped &&
          nd1#data#is_order_insensitive && nd2#data#is_order_insensitive &&
          not nd1#data#is_boundary && not nd2#data#is_boundary &&
          not (is_move nd1#initial_parent nd2#initial_parent)
        then begin
          [%debug_log "@"];
          reg_deferred_op (nd1, nd2) (add_move nd1 nd2);
          false
        end
        else if
          try
            has_deferred_op (nd1#initial_parent, nd2#initial_parent)
          with _ -> false
        then begin
          [%debug_log "@"];
          reg_deferred_op (nd1, nd2) (add_move nd1 nd2);
          false
        end
        else begin
          [%debug_log "@"];
          true
        end
      then
        [%debug_log "move: %a-%a" nups nd1 nups nd2]

      else if not (glue_filt nd1 nd2) then
        [%debug_log "filtered: %a-%a" nups nd1 nups nd2]

      else begin

        begin %debug_block
          [%debug_log "@"];
          let pr n =
            try
              let key = nmapping#key_of_locked_node n in
              [%debug_log "%a is locked (key=%s)" nups n
                (Key.to_string ~opr:(fun o -> Label.to_string (Obj.obj o)) key)]
            with
              Not_found -> ()
          in
          pr nd1;
          pr nd2;
        end;

        let check n =
          try
            let key = nmapping#key_of_locked_node n in
            (key = Key.make_pair_key nd1 nd2), Some key
          with
            Not_found -> true, None
        in

        let nd1_ok, key1_opt = check nd1 in
        let nd2_ok, key2_opt = check nd2 in

        [%debug_log "nd1_ok=%B nd2_ok=%B" nd1_ok nd2_ok];

        let can_add =
          nd1_ok && nd2_ok &&
          (match key1_opt, key2_opt with
          | Some key1, Some key2 -> key1 = key2
          | _ -> true) &&
          (try
            let nd1' = nmapping#find nd1 in
            let b = nd1' == nd2 || not (nmapping#is_locked_mapping nd1 nd1') in
            if not b then
              [%debug_log "!!!!!!!! %a->%a" nups nd1 nups nd1'];
            b
          with _ -> true) &&
          (try
            let nd2' = nmapping#inv_find nd2 in
            let b = nd2' == nd1 || not (nmapping#is_locked_mapping nd2' nd2) in
            if not b then
              [%debug_log "!!!!!!!! %a<-%a" nups nd2' nups nd2];
            b
          with _ -> true)
        in

        if can_add then begin
          (*let score =
            if
              Array.exists
                (fun c1 ->
                  Array.exists
                    (fun c2 ->
                      cenv#has_uniq_subtree_match c1 c2
                    ) nd2#initial_children
                ) nd1#initial_children
            then begin
              let score_ = score + 1 in
              [%debug_log "score: %d -> %d" score score_];
              score_
            end
            else
              score
          in*)

          begin %debug_block
            [%debug_log "[%s]: adding %a -> %a (score=%d)" context nups nd1 nups nd2 score];
            [%debug_log "[%s]:        %a    %a" context ngps nd1 ngps nd2];
          end;

          try
            let s = List.assoc (nd1, nd2) !cands in
            s := max !s score
          with
            Not_found -> cands := ((nd1, nd2), ref score)::!cands
        end

      end

    in (* add_cand *)

    let is_cand n1 n2 =
      let b = List.mem_assoc (n1, n2) !cands in
      [%debug_log "%a-%a -> %B" nups n1 nups n2 b];
      b
    in

    let scanned_up   = Nodetbl.create 0 in
    let scanned_down = Nodetbl.create 0 in
    let scanned_up_add (nd1, nd2)   = Nodetbl.add scanned_up nd1 nd2 in
    let scanned_down_add (nd1, nd2) = Nodetbl.add scanned_down nd1 nd2 in
    let scanned_up_mem (nd1, nd2) =
      try
        let nds = Nodetbl.find_all scanned_up nd1 in
        List.memq nd2 nds
      with
        Not_found -> false
    in
    let scanned_down_mem (nd1, nd2) =
      try
        let nds = Nodetbl.find_all scanned_down nd1 in
        List.memq nd2 nds
      with
        Not_found -> false
    in

    let rec scan_up ?(reflex=false) (score_up, score_down) nd1 nd2 =

      if is_bad_pair nd1 nd2 then
        [%debug_log "bad pair: %a-%a" nups nd1 nups nd2]

      else if scanned_up_mem (nd1, nd2) then begin
        [%debug_log "already scanned up: %a-%a" nups nd1 nups nd2]

      end
      else begin
        scanned_up_add (nd1, nd2);

        [%debug_log "[override=%B] (%d,%d): %a-%a"
          override score_up score_down nups nd1 nups nd2];

        if nd1#has_initial_parent && nd2#has_initial_parent then begin

          let pnd1 = nd1#initial_parent in
          let pnd2 = nd2#initial_parent in

          [%debug_log "\tparents: %a-%a" nups pnd1 nups pnd2];

          if is_bad_pair pnd1 pnd2 then
            [%debug_log "bad pair: %a-%a" nups pnd1 nups pnd2]

          else begin

            let already_mapped =
              if (nmapping#mem_dom pnd1) || (nmapping#mem_cod pnd2) then
                try
                  let pnd1' = nmapping#find pnd1 in
                  Some (pnd1, pnd1')
                with
                  Not_found ->
                    let pnd2' = nmapping#inv_find pnd2 in
                    Some (pnd2', pnd2)
              else
                None
            in

            begin %debug_block
            match already_mapped with
            | None -> [%debug_log "\tnot mapped yet"]
            | Some (n1, n2) ->
                let nmapped1 = nmapped_of_subtree1 n1 in
                let nnodes1 = tree1#whole_initial_subtree_size n1 in
                let nmapped2 = nmapped_of_subtree2 n2 in
                let nnodes2 = tree2#whole_initial_subtree_size n2 in
                (*
                  [%debug_log "\tnmapping: %a(%d/%d) -> %a(%d/%d) (subtree sim.: %f)"
                  nups n1 nmapped1 nnodes1
                  nups n2 nmapped2 nnodes2
                  (estimate_subtree_similarity tree1 tree2 n1 n2)];
                 *)
                [%debug_log "\tnmapping: %a(%d/%d) -> %a(%d/%d)"
                  nups n1 nmapped1 nnodes1
                  nups n2 nmapped2 nnodes2];
            end;

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

            let label_match_score = cenv#eval_label_match pnd1 pnd2 in

            let anc_sim = cenv#get_ancestors_similarity pnd1 pnd2 in

            let continue, is_cand =
              match already_mapped with
              | None -> true, true
              | Some (n1, n2) ->
                  [%debug_log "%a-%a" nups n1 nups n2];
                  let lms = cenv#eval_label_match n1 n2 in
                  let asim = cenv#get_ancestors_similarity n1 n2 in

                  [%debug_log "label match score: %d --> %d" lms label_match_score];
                  [%debug_log "ancestors similarity: %f --> %f" asim anc_sim];

                  let lcond =
                    if override then
                      lms <= label_match_score
                    else
                      lms < label_match_score
                  in
                  let acond =
                    if override then
                      asim <= anc_sim
                    else
                      asim < anc_sim
                  in
                  let ccond =
                    tree1#is_initial_ancestor pnd1 n1 || tree2#is_initial_ancestor pnd2 n2 ||
                    has_same_subtree n1 n2 ||
                    cenv#has_uniq_match nd1 nd2
                  in
                  [%debug_log "lcond=%B acond=%B ccond=%B" lcond acond ccond];
                  let cont, cand = (lcond || acond || ccond), (lcond || ccond) in
                  if not cont && not cand then
                    let b =
                      lms = label_match_score && asim >= 1.0 && anc_sim < 1.0 &&
                      n1#data#is_op && n2#data#is_op && pnd1#data#is_op && pnd2#data#is_op &&
                      cenv#check_op_mappings_m nmapping n1 n2 pnd1 pnd2
                    in
                    if b then
                      [%debug_log "!!!!!!!! %a - %a" nps pnd1 nps pnd2];
                    b, b
                  else
                    cont, cand
            in (* let continue, is_cand *)

            [%debug_log "continue=%B is_cand=%B" continue is_cand];

            if continue then begin

              [%debug_log "\tglue cand (scan_up): %a-%a" nups pnd1 nups pnd2];

              let bonus, is_ok =
                if pnd1#data#equals pnd2#data then
                  calc_bonus pnd1 pnd2,
                  true
                else
                  label_match_score,
                  relabel_allowed pnd1 pnd2
              in
              if is_ok then begin

                if is_cand || reflex then begin
                  [%debug_log "base score: %d, bonus: %d" score_up bonus];

                  let score = score_up + bonus in
                  add_cand "scan_up" pnd1 pnd2 score
                end;

                scan_up (score_up, score_down) pnd1 pnd2;

                if not options#simple_glue_flag && is_cand then
(*            let scoring = get_scoring nd1 nd2 in *)
                  scan_down (* scoring *) (score_up, score_down) pnd1 pnd2
                  (* cf. ieee1394_transactions.c 481L packet -> 481L packet *)
              end
              else
(*            check_upper_boundary (score_up, score_down) pnd1 pnd2 *)
                if not options#simple_glue_flag then
                  check_until_upper_boundary (score_up, score_down) pnd1 pnd2

            end (* of if continue *)

          end (* of if not (is_bad_pair pnd1 pnd2) *)

        end (* of if (nd1#has_initial_parent && nd2#has_initial_parent) *)

      end (* of if scanned_up_mem (nd1, nd2) *)
    (* end of func scan_up *)


    and check_until_upper_boundary (score_up, score_down) nd1 nd2 =

      [%debug_log "checking %a-%a" nups nd1 nups nd2];

      let boundary = ref None in
      begin
        try
          nd1#iter_initial_ancestor_nodes
            (fun n1 ->
              try
                let n1' = nmapping#find n1 in
                if tree2#is_initial_ancestor n1' nd2 then begin
                  boundary := Some (n1, n1');
                  raise Break
                end
              with
                Not_found -> ()
            )
        with
          Break -> ()
      end;
      begin
        match !boundary with
        | None -> [%debug_log "no boundary"]
        | Some (bn1, bn2) ->
            [%debug_log "boundary: %a-%a" nups bn1 nups bn2];

            let alab1 = nd1#data#_anonymized2_label in
            let alab2 = nd2#data#_anonymized2_label in
            let cand1 = ref None in
            let cand2 = ref None in
            begin
              try
                nd2#iter_initial_ancestor_nodes
                  (fun n2 ->
                    if n2 == bn2 then
                      raise Break
                    else
                      if not (nmapping#mem_cod n2) then
                        if n2#data#_anonymized2_label = alab1 then begin
                          cand1 := Some (nd1, n2);
                          raise Break
                        end
                  )
              with
                Break -> ()
            end;
            begin
              try
                nd1#iter_initial_ancestor_nodes
                  (fun n1 ->
                    if n1 == bn1 then
                      raise Break
                    else
                      if not (nmapping#mem n1) then
                        if n1#data#_anonymized2_label = alab2 then begin
                          cand2 := Some (n1, nd2);
                          raise Break
                        end
                  )
              with
                Break -> ()
            end;

            let continue n1 n2 =

              if is_bad_pair n1 n2 then
                [%debug_log "bad pair: %a-%a" nups n1 nups n2]

              else
                let bonus, is_ok =
                  if n1#data#equals n2#data then
                    calc_bonus n1 n2, true
                  else
                    cenv#eval_label_match n1 n2, relabel_allowed n1 n2
                in
                if is_ok then begin

                  [%debug_log "base score: %d, bonus: %d" score_up bonus];

                  let score = score_up + bonus in
                  add_cand "check_until_upper_boundary" n1 n2 score;

(*                let scoring = get_scoring n1 n2 in *)
                  (*scan_down ~recur:false (score_up, score_down) n1 n2;*)
                  scan_up (* scoring *) (score_up, score_down) n1 n2
                end
            in (* func continue *)

            begin %debug_block
              let f = function
                | None -> "None"
                | Some (n1, n2) -> sprintf "%a-%a" nups n1 nups n2
              in
              [%debug_log "cand1: %s" (f !cand1)];
              [%debug_log "cand2: %s" (f !cand2)];
            end;

            match !cand1, !cand2 with
            | None, None -> ()
            | Some (n1, n2), None | None, Some (n1, n2) -> continue n1 n2
            | Some (n11, n12), Some (n21, n22) ->
                if n11 == n21 && n12 == n22 then
                  continue n11 n12
                else if n11 == n21 && next_to_each_other n12 n22 then
                  continue n11 n12
                else if n12 == n22 && next_to_each_other n11 n21 then
                  continue n11 n12
                else
                  let score1 = cenv#get_adjacency_score n11 n12 in
                  let score2 = cenv#get_adjacency_score n21 n22 in
                  if score1 >= score2 then
                    continue n11 n12

                  else
                    continue n21 n22
      end
    (* end of check_until_upper_boundary *)


    and nmapped_of_subtree ?(exclude_root=false) tree mem nd =
      let c = ref 0 in
      let f =
        if exclude_root then
          (fun n -> if n != nd && mem n then incr c)
        else
          (fun n -> if mem n then incr c)
      in
      tree#fast_scan_whole_initial_subtree nd f;
      !c

    and nmapped_of_subtree1 ?(exclude_root=false) nd =
      nmapped_of_subtree ~exclude_root tree1 nmapping#mem_dom nd

    and nmapped_of_subtree2 ?(exclude_root=false) nd =
      nmapped_of_subtree ~exclude_root tree2 nmapping#mem_cod nd

    and scan_down
        ?(recur=true)
        ?(hardoverride=false)
        ?(force_treediff=false)
        (score_up, score_down)
        nd1 nd2
        =

      if not (nd1#is_valid && nd2#is_valid) then
        [%debug_log "invalid node: %a-%a" nups nd1 nups nd2]

      else if is_bad_pair nd1 nd2 then
        [%debug_log "bad pair: %a-%a" nups nd1 nups nd2]

      else if scanned_down_mem (nd1, nd2) then begin
        [%debug_log "already scanned down: %a-%a" nups nd1 nups nd2]
      end
      else begin
        scanned_down_add (nd1, nd2);

        begin %debug_block
          [%debug_log "[hardoverride=%B:override=%B] (%d,%d): %a[%s] -"
            hardoverride override score_up score_down nups nd1
            (Xarray.to_string
              (fun n -> UID.to_string n#uid) ";" nd1#initial_children)];
          [%debug_log "[hardoverride=%B:override=%B] (%d,%d): %a[%s]"
            hardoverride override score_up score_down nups nd2
            (Xarray.to_string
              (fun n -> UID.to_string n#uid) ";" nd2#initial_children)];
        end;

        let has_uniq_paths = Edit.has_uniq_paths nd1 nd2 in

        (* mapped subtree members (but sub-root) *)
        let nmapped1 = nmapped_of_subtree1 ~exclude_root:true nd1 in
        let nmapped2 = nmapped_of_subtree2 ~exclude_root:true nd2 in

        let nmembers1 = tree1#whole_initial_subtree_size nd1 in
        let nmembers2 = tree2#whole_initial_subtree_size nd2 in

        let mapped_ratio1 = (float nmapped1) /. (float nmembers1) in
        let mapped_ratio2 = (float nmapped2) /. (float nmembers2) in

        begin %debug_block
          [%debug_log "%a: mapped subtree members (%d/%d=%f)"
            nups nd1 nmapped1 nmembers1 mapped_ratio1];
          [%debug_log "%a: mapped subtree members (%d/%d=%f)"
            nups nd2 nmapped2 nmembers2 mapped_ratio2];
        end;

        let all_subtree_members_not_mapped = nmapped1 = 0 && nmapped2 = 0 in

        if all_subtree_members_not_mapped then
          [%debug_log "all subtree members not mapped"];

        let size_cond =
          (nmembers1 > 1 || nmembers2 > 1) &&
          (float (min nmembers1 nmembers2)) /. (float (max nmembers1 nmembers2)) > 0.1 &&
          (nmembers1 < options#match_algo_threshold) && (nmembers2 < options#match_algo_threshold)
        in
        [%debug_log "size_cond=%B" size_cond];

        let go_down_cond =
          match nd1#initial_children, nd2#initial_children with
          | [|_|], [|_|] -> nd1#data#eq nd2#data
          | _ -> false
        in
        [%debug_log "go_down_cond=%B" go_down_cond];

        let ca1, ca2 = nd1#initial_children, nd2#initial_children in

        let subtree_not_mapped =
          (nmapped1 = 0 || nmapped2 = 0) && max mapped_ratio1 mapped_ratio2 < 0.3
        in
        [%debug_log "subtree_not_mapped=%B" subtree_not_mapped];

        let has_better_desc_match n1 n2 =
          let b =
            (
             n1#data#is_named || n1#data#has_non_trivial_value ||
             n2#data#is_named || n2#data#has_non_trivial_value
            ) &&
            (*(
             n1#initial_nchildren = 0 &&
             (n1#data#is_named || n1#data#has_non_trivial_value)
            ||
             n2#initial_nchildren = 0 &&
             (n2#data#is_named || n2#data#has_non_trivial_value)
            ) &&*)
            let alab1 = n1#data#anonymized_label in
            let alab2 = n2#data#anonymized_label in
            alab1 <> alab2 &&
            (
             has_p_descendant
               (fun x1 ->
                 x1#data#eq n2#data
               ||
                 (try cenv#is_rename_pat (get_orig_name x1, get_orig_name n2) with _ -> false)
               ||
                 (*x1#data#has_non_trivial_value && *)x1#data#anonymized_label = alab2
               ) n1
            ||
             has_p_descendant
               (fun x2 ->
                 n1#data#eq x2#data
               ||
                 (try cenv#is_rename_pat (get_orig_name n1, get_orig_name x2) with _ -> false)
               ||
                 (*x2#data#has_non_trivial_value && *)alab1 = x2#data#anonymized_label
               ) n2
            )
          in
          [%debug_log "%a-%a --> %B" nups n1 nups n2 b];
          if b then
            [%debug_log "@@@@@"];
          b
        in

        let use_treediff_cond =
          size_cond &&
          (
           all_subtree_members_not_mapped ||
           subtree_not_mapped ||
           force_treediff ||
           cenv#child_has_use_rename nd1 nd2 ||
           has_better_desc_match nd1 nd2
          ) &&
          (not go_down_cond)
        in
        [%debug_log "use_treediff_cond=%B" use_treediff_cond];

        if use_treediff_cond then begin (* use tree diff *)

          if force_treediff then
            [%debug_log "force_treediff=true"];

          let subtree1 = tree1#make_subtree_from_node nd1 in
          let subtree2 = tree2#make_subtree_from_node nd2 in

          nd1#hide_parent;
          nd2#hide_parent;

          let subroot1 = subtree1#root in
          let subroot2 = subtree2#root in

          let matches, extra_matches, relabels =
            let partially_mapped = not all_subtree_members_not_mapped && subtree_not_mapped in
            Treediff.match_trees cenv ~partially_mapped ~root_check:false
              subtree1 subtree2 nmapping ref_nmapping
          in

          let pseudo_matches =
            List.filter (fun (n1, n2) -> is_pseudo_match n1 n2) relabels
          in

          let nrelabels = List.length relabels in

          begin %debug_block
            let nmatches = List.length matches in
            let nextra_matches = List.length extra_matches in
            [%debug_log "(by tree diff): match:%d extra_match:%d relabels:%d"
              nmatches nextra_matches nrelabels];
          end;

          let conv = conv_subtree_node_pairs tree1 tree2 in

          let amatches, aextra_matches, arelabels =
            if nrelabels > 0 then
              let nds_left_named1, nds_left_named2 =
                List.split (matches @ extra_matches @ pseudo_matches)
              in
              try
                let atree1 =
                  subtree1#make_anonymized2_subtree_copy ~nds_left_named:nds_left_named1 subroot1
                in
                let atree2 =
                  subtree2#make_anonymized2_subtree_copy ~nds_left_named:nds_left_named2 subroot2
                in

                [%debug_log "anonymized trees: |T1(root:%a)|=%d |T2(root:%a)|=%d"
                  nups nd1 atree1#size nups nd2 atree2#size];

                let acenv = new Comparison.c options atree1 atree2 in

                let m, em, r =
                  Treediff.match_trees acenv ~root_check:false atree1 atree2
                    (new Node_mapping.c acenv) (new Node_mapping.c acenv)
                in

                conv m, conv em, conv r

              with
                Invalid_argument msg ->
                  Xprint.error "%s" msg;
                  assert false

            else (* nrelabels = 0 *)
              matches, extra_matches, []
          in

          let arelabels = (* ??? *)
            List.filter
              (fun (n1, n2) ->
                [%debug_log "%a-%a" nps n1 nps n2];
                check_relabel options ~exact:true ~matches:amatches tree1 tree2 n1 n2 nmapping
              ) arelabels
          in

          let no_cands_found = ref true in

          List.iter
            (fun matches ->
              List.iter
                (fun (n1, n2) ->
                  let bonus, is_ok =
                    if n1#data#equals n2#data then
                      calc_bonus n1 n2, true
                    else
                      cenv#eval_label_match n1 n2, relabel_allowed n1 n2
                  in
                  if is_ok then begin
                    no_cands_found := false;

                    [%debug_log "! glue cand (scan_down: by tree diff): %a-%a" nups n1 nups n2];

                    let base =
                      if has_uniq_paths n1 n2(* is_unique_pair n1 n2 *) then
                        score_up
                      else
                        score_down
                    in

                    [%debug_log "base score: %d, bonus: %d" base bonus];

                    let score = base + bonus in
                    add_cand "tree diff on subtrees" n1 n2 score
                  end

                ) matches
            ) [amatches; aextra_matches; arelabels];

          [%debug_log "no_cands_found=%B" !no_cands_found];

          if !no_cands_found then begin
            let (*matches*)_, (*extra_matches*)_, relabels =
              Treediff.match_trees cenv
                ~root_check:false ~semantic:true subtree1 subtree2 nmapping ref_nmapping
            in
            let relabels =
              List.filter
                (fun (n1, n2) ->
                  check_relabel options ~exact:false tree1 tree2 n1 n2 nmapping
                ) relabels
            in
            List.iter
              (fun (n1, n2) ->
                let bonus, is_ok = cenv#eval_label_match n1 n2, relabel_allowed n1 n2 in
                if is_ok then begin
                  [%debug_log "! glue cand (scan_down: by tree diff): %a-%a" nups n1 nups n2];
                  let base =
                    if has_uniq_paths n1 n2(* is_unique_pair n1 n2 *) then
                      score_up
                    else
                      score_down
                  in
                  [%debug_log "base score: %d, bonus: %d" base bonus];
                  let score = base + bonus in
                  add_cand "weak tree diff on subtrees" n1 n2 score
                end
              ) relabels
          end;

          nd1#unhide_parent;
          nd2#unhide_parent;

        end (* of if the sizes of subtrees are moderate... *)
        else begin (* tree diff not used or no cands found *)

          let cld1, cld2 =
            let idxs = ref [] in
            let cond =
              if (Array.length ca1) = (Array.length ca2) then begin
                (*if not no_moves then begin
                  let all_named_and_ordered =
                    let is_named_and_ordered x = x#data#is_named && not x#data#is_order_insensitive in
                    Array.for_all is_named_and_ordered ca1 &&
                    Array.for_all is_named_and_ordered ca2
                  in
                  [%debug_log "all_named_and_orderred=%B" all_named_and_ordered];
                  if all_named_and_ordered then begin
                    let cmp n1 n2 = compare n1#data#label n2#data#label in
                    Array.fast_sort cmp ca1;
                    Array.fast_sort cmp ca2;
                  end
                end;*)
                try
                  Array.iteri
                    (fun i n1 ->
                      let n2 = ca2.(i) in
                      if n1#data#_anonymized_label = n2#data#_anonymized_label then begin
                        let not_mapped() =
                          (not (nmapping#mem_dom n1)) && (not (nmapping#mem_cod n2))
                        in
                        if
                          n1#data#eq n2#data || not_mapped()(* ||
                          try n1#initial_parent#data#eq n2#initial_parent#data with _ -> false*)
                        then
                          idxs := i :: !idxs
                      end
                      else
                        raise Break
                    ) ca1;
                  true
                with
                  Break -> false
              end
              else
                false
            in
            [%debug_log "cond=%B" cond];
            if cond && (not (override || hardoverride)) then begin
              List.fold_left
                (fun (l1, l2) i ->
                  ca1.(i)::l1, ca2.(i)::l2
                ) ([], []) !idxs
            end
            else
              let _cld1 =
                if override || hardoverride then
                  Array.to_list ca1
                else
                  List.filter
                    (fun n1 ->
                      try
                        let n2 = nmapping#find n1 in
                        not (n1#data#eq n2#data)
                      with
                        Not_found -> true
                    ) (Array.to_list ca1)
              in
              let _cld2 =
                if override || hardoverride then
                  Array.to_list ca2
                else
                  List.filter
                    (fun n2 ->
                      try
                        let n1 = nmapping#inv_find n2 in
                        not (n1#data#eq n2#data)
                      with
                        Not_found -> true
                    ) (Array.to_list ca2)
              in
              _cld1, _cld2
          in

          let cld1, cld2 =
            let f l =
              List.filter
                (fun n ->
                  let locked = nmapping#is_locked_node n in
                  if locked then
                    [%debug_log "%a is locked" nups n];
                  not locked
                ) l
            in
            (f cld1, f cld2)
          in

          begin %debug_block
            let ltos tree nmapped_of_subtree l =
              Xlist.to_string
                (fun n ->
                  sprintf "%a(%d/%d)"
                    nups n (nmapped_of_subtree n) (tree#whole_initial_subtree_size n)
                ) ";" l
            in
            let ltos1 = ltos tree1 nmapped_of_subtree1 in
            let ltos2 = ltos tree2 nmapped_of_subtree2 in
            [%debug_log "filtered: %a[%s] -" nups nd1 (ltos1 cld1)];
            [%debug_log "filtered: %a[%s]" nups nd2 (ltos2 cld2)];
            let ltos l = Xlist.to_string (fun n -> n#data#label) ";" l in
            [%debug_log "filtered (label): %a[%s] -" nups nd1 (ltos cld1)];
            [%debug_log "filtered (label): %a[%s]" nups nd2 (ltos cld2)];
          end;

          let cld1a = Array.of_list cld1 in
          let cld2a = Array.of_list cld2 in

          let len1 = Array.length cld1a in
          let len2 = Array.length cld2a in


          let occur_tbl1 = Hashtbl.create 0 in
          let occur_tbl2 = Hashtbl.create 0 in
          let occur_tbl_add tbl k v =
            try
              let l = Hashtbl.find tbl k in
              Hashtbl.replace tbl k (v::l)
            with
              Not_found -> Hashtbl.add tbl k [v]
          in
          let occur_tbl_create tbl clda =
            let prev, count =
              Array.fold_left
                (fun (prev, count) (alab, alab_str) ->
                  match prev with
                  | None -> (Some (alab, alab_str), 1)
                  | Some (p, pstr) ->
                      let _ = pstr in
                      if p = alab then
                        (prev, count + 1)

                      else begin
                        occur_tbl_add tbl p count;

                        [%debug_log "  alab count: %s -> %d" pstr count];

                        (Some (alab, alab_str), 1)
                      end

                )
                (None, 0)
                (Array.map (fun n -> n#data#_anonymized_label, n#data#anonymized_label) clda)
            in
            match prev with
            | Some (p, pstr) -> begin
                let _ = pstr in
                occur_tbl_add tbl p count;
                [%debug_log "  alab count: %s -> %d" pstr count];
            end
            | _ -> ()
          in
          occur_tbl_create occur_tbl1 cld1a;
          [%debug_log "  ---"];
          occur_tbl_create occur_tbl2 cld2a;

          let has_different_repetition_pattern() =
            let b =
              let xs = ref [] in
              Hashtbl.iter
                (fun alab2 counts2 ->
                  try
                    let counts1 = Hashtbl.find occur_tbl1 alab2 in
                    if counts1 <> counts2 then
                      xs := alab2 :: !xs
                  with
                    Not_found -> ()
                ) occur_tbl2;
              List.exists
                (fun alab ->
                  let filt n = not n#is_leaf && n#data#_anonymized_label = alab in
                  Array.exists filt cld1a || Array.exists filt cld2a
                ) !xs
            in
            [%debug_log "has_different_repetition_pattern: %B" b];
            b
          in

          let chk_anon3 clda =
            let s = Xset.create 0 in
            try
              Array.iter
                (fun n ->
                  let alab = n#data#_anonymized3_label in
                  if Xset.mem s alab then
                    raise Exit
                  else
                    Xset.add s alab
                ) clda;
              true
            with
              Exit -> false
          in
          let anon3_all_once() =
            let b =
              len1 > 0 && len2 > 0 &&
              chk_anon3 cld1a && chk_anon3 cld2a
            in
            [%debug_log "anon3_all_once: %B" b];
            b
          in

          let _cands =
            match cld1a, cld2a with
            | [||], _ | _, [||] -> []
            | _ ->
                let use_similarity = len1 <> len2 && (has_different_repetition_pattern()) in

                [%debug_log "use_similarity: %B" use_similarity];

                if use_similarity then
                  let f0 = Array.map (fun n -> n#data#_label, n#data#_digest) in
                  let cldd1 = f0 cld1a in
                  let cldd2 = f0 cld2a in

                  let mat, _, _, _ = Adiff.adiff cldd1 cldd2 in

                  begin %debug_block
                    [%debug_log "mat:"];
                    List.iter
                      (fun (i, j) ->
                        [%debug_log "%a - %a" nps cld1a.(i) nps cld2a.(j)]
                      ) mat
                  end;

                  let mat1, mat2 = List.split mat in
                  let f1 m cldd =
                    Array.iteri
                      (fun i (l, _) -> if not (List.mem i m) then cldd.(i) <- (l, None)) cldd
                  in
                  f1 mat1 cldd1;
                  f1 mat2 cldd2;

                  let get_weight i j _ =
                    cenv#get_similarity_score cld1a.(i) cld2a.(j)
                  in

                  let mat' = HIS.Float.compute get_weight cldd1 cldd2 in

                  begin %debug_block
                    [%debug_log "mat':"];
                    List.iter
                      (fun (i, j) ->
                        [%debug_log "%a - %a" nps cld1a.(i) nps cld2a.(j)]
                      ) mat'
                  end;

                  let mat1', mat2' = List.split mat' in
                  let f2 m m' clda cldd =
                    Array.iteri
                      (fun i (_, _) ->
                        if not (List.mem i m || List.mem i m') then
                          cldd.(i) <- ((clda.(i))#data#_anonymized2_label, None)
                      ) cldd
                  in
                  f2 mat1 mat1' cld1a cldd1;
                  f2 mat2 mat2' cld2a cldd2;

                  begin %debug_block
                    let a2s =
                      Xarray.to_string (fun (lab, _) -> Label.to_string (Obj.obj lab : Label.t)) ";"
                    in
                    [%debug_log "cldd1: [%s]" (a2s cldd1)];
                    [%debug_log "cldd2: [%s]" (a2s cldd2)]
                  end;

                  let mat'' = HIS.Float.compute get_weight cldd1 cldd2 in

                  List.map (fun (i, j) -> cld1a.(i), cld2a.(j)) mat''

                else (* similarity not used *)

                  let get_extra_matches _del _ins m =
                    let m_tbl = Nodetbl.create 0 in
                    List.iter (fun (i, j) -> Nodetbl.add m_tbl cld1a.(i) cld2a.(j)) m;
                    let del = List.map (fun i -> cld1a.(i)) _del in
                    let ins = List.map (fun j -> cld2a.(j)) _ins in
                    Treediff.find_glue_cands ~simple:true tree1 tree2 del ins m_tbl
                  in

                  let f0 = Array.map (fun n -> n#data#_label, n#data#_digest) in
                  let cldd1 = f0 cld1a in
                  let cldd2 = f0 cld2a in

                  let digest_to_str = function
                    | None -> ""
                    | Some d -> Digest.to_hex d
                  in
                  let _ = digest_to_str in

                  begin %debug_block
                    Array.iteri
                      (fun _ (l, d) ->
                        [%debug_log "cldd1: %s(%s)" (Label.to_string (Obj.obj l)) (digest_to_str d)]
                      ) cldd1;
                    Array.iteri
                      (fun _ (l, d) ->
                        [%debug_log "cldd2: %s(%s)" (Label.to_string (Obj.obj l)) (digest_to_str d)]
                      ) cldd2;
                  end;

                  let mat, _, del, ins = Adiff.adiff cldd1 cldd2 in

                  let exm = get_extra_matches del ins mat in

                  let mat1, mat2 = List.split mat in
                  let f1 m cldd =
                    Array.iteri
                      (fun i (l, _) -> if not (List.mem i m) then cldd.(i) <- (l, None)) cldd
                  in
                  f1 mat1 cldd1;
                  f1 mat2 cldd2;

                  begin %debug_block
                    [%debug_log "mat: [%s]"
                      (Xlist.to_string (fun (i, j) -> sprintf "(%d,%d)" i j) ";" mat)];
                    Array.iteri
                      (fun _ (l, d) ->
                        [%debug_log "cldd1: %s(%s)" (Label.to_string (Obj.obj l)) (digest_to_str d)]
                      ) cldd1;
                    Array.iteri
                    (fun _ (l, d) ->
                      [%debug_log "cldd2: %s(%s)" (Label.to_string (Obj.obj l)) (digest_to_str d)]
                    ) cldd2;
                  end;

                  let mat', _, _, _ = Adiff.adiff cldd1 cldd2 in

                  let mat1', mat2' = List.split mat' in
                  (*let a3_flag = not (is_move nd1 nd2) && no_moves in*)
                  let a3_flag = nd1#data#is_boundary && nd2#data#is_boundary && anon3_all_once() in
                  [%debug_log "a3_flag=%B" a3_flag];
                  let f2 m m' cldd clda =
                    Array.iteri
                      (fun i (_, _) ->
                        if not (List.mem i m || List.mem i m') then
                          let a =
                            let ci = clda.(i) in
                            if a3_flag && ci#data#is_sequence then
                              ci#data#_anonymized3_label
                            else
                              ci#data#_anonymized2_label
                          in
                          cldd.(i) <- (a, None)
                      ) cldd
                  in
                  f2 mat1 mat1' cldd1 cld1a;
                  f2 mat2 mat2' cldd2 cld2a;

                  begin %debug_block
                    [%debug_log "mat': [%s]"
                    (Xlist.to_string (fun (i, j) -> sprintf "(%d,%d)" i j) ";" mat')];
                    Array.iteri
                      (fun _ (l, d) ->
                        [%debug_log "cldd1: %s(%s)" (Label.to_string (Obj.obj l)) (digest_to_str d)]
                      ) cldd1;
                    Array.iteri
                      (fun _ (l, d) ->
                        [%debug_log "cldd2: %s(%s)" (Label.to_string (Obj.obj l)) (digest_to_str d)]
                      ) cldd2;
                  end;

                  let mat'', _, _, _ = Adiff.adiff cldd1 cldd2 in
                  let nps'' = List.rev_map (fun (i, j) -> cld1a.(i), cld2a.(j)) mat'' in
                  List.rev_append nps'' (List.filter (fun x -> not (List.mem x nps'')) exm)

          in (* _cands *)


          begin %debug_block
            [%debug_log "_cands:"];
          List.iter
            (fun (n1, n2) ->
              [%debug_log "%a - %a" nps n1 nps n2]
            ) _cands;
          end;

          let match_ratio =
            let n = Xlist.min [List.length cld1; List.length cld2] in
            if n = 0 then
              1.0
            else
              (float (List.length _cands)) /. (float n)
          in

          [%debug_log "match_ratio=%f" match_ratio];

          let cands =
            let clda1 = Array.map (fun n -> n#data#_anonymized2_label) cld1a in
            let clda2 = Array.map (fun n -> n#data#_anonymized2_label) cld2a in
            let repetition_free a =
              try
                Array.iteri
                  (fun i lab ->
                    try
                      if lab = a.(i+1) then
                        raise Found
                    with
                      Invalid_argument _ -> ()
                  ) a;
                true
              with
                Found -> false
            in
            let is_reliable =
              (repetition_free clda1) && (repetition_free clda2)
            in

            if is_reliable && match_ratio < options#pp_anonymized_match_threshold then begin
              [%debug_log "trying to match anonymized labels... (match ratio: %f, thresh=%f)"
                match_ratio options#pp_anonymized_match_threshold];

              let mat, rel, _, _ = Adiff.adiff clda1 clda2 in
              List.map (fun (i, j) -> cld1a.(i), cld2a.(j)) (mat @ rel)
            end
            else
              _cands
          in (* cands *)

          let to_be_focused = cands = [] && match_ratio = 0.0 in

          let cands =
            if to_be_focused then begin

              [%debug_log "  focusing on %a-%a" nups nd1 nups nd2];

              let gi1, gi2 = nd1#gindex, nd2#gindex in
              let lgi1 = (tree1#initial_leftmost nd1)#gindex in
              let lgi2 = (tree2#initial_leftmost nd2)#gindex in
              let found_st = ref [] in
              begin
                let filt lgi gi (n, _) =
                  let g = n#gindex in
                  lgi <= g && g <= gi
                in
                try
                  cenv#multiple_subtree_matches#iter
                    (fun (_, ndmems1, ndmems2, sz) ->
                      let _ = sz in
                      let ndmems1' = List.filter (filt lgi1 gi1) ndmems1 in
                      let ndmems2' = List.filter (filt lgi2 gi2) ndmems2 in
                      match ndmems1', ndmems2' with
                      | [n1, _], [n2, _] ->
                          let found1, found2 = List.split !found_st in
                          let sub1 =
                            List.exists (fun fd1 -> tree1#initial_subtree_mem fd1 n1) found1
                          in
                          let sub2 =
                            List.exists (fun fd2 -> tree2#initial_subtree_mem fd2 n2) found2
                          in
                          if not sub1 && not sub2 then begin
                            [%debug_log "  subtree pair of size %d found: %a-%a" sz nups n1 nups n2];
                            found_st := (n1, n2) :: !found_st
                          end
                      | _ -> ()
                    )
                with
                  Not_found -> ()
              end;
              let found_st1, found_st2 = List.split !found_st in
              let issub1 n1 = List.exists (fun fd1 -> tree1#initial_subtree_mem fd1 n1) found_st1 in
              let issub2 n2 = List.exists (fun fd2 -> tree2#initial_subtree_mem fd2 n2) found_st2 in
              let found = ref [] in
              begin
                let filt lgi gi n =
                  let g = n#gindex in
                  lgi <= g && g <= gi
                in
                try
                  let multiple_node_matches = cenv#multiple_node_matches in
                  multiple_node_matches#iter
                    (fun (_lab, ns1, ns2) ->
                      let ns1' = List.filter (filt lgi1 gi1) ns1 in
                      let ns2' = List.filter (filt lgi2 gi2) ns2 in
                      match ns1', ns2' with
                      | [n1], [n2] -> begin
                          if
                            not (List.mem (n1, n2) !found) && not (issub1 n1) && not (issub2 n2)
                          then begin
                            [%debug_log "  node pair found: %a-%a" nups n1 nups n2];
                            found := (n1, n2) :: !found;
                            try
                              let pn1 = n1#initial_parent in
                              let pn2 = n2#initial_parent in
                              if
                                not (nmapping#mem_dom pn1) && not (nmapping#mem_cod pn2) &&
                                (pn1#data#eq pn2#data || relabel_allowed pn1 pn2)
                              then begin
                                [%debug_log "  parent node pair added: %a-%a" nups pn1 nups pn2];
                                found := (pn1, pn2) :: !found
                              end
                            with
                              _ -> ()
                          end
                      end
                      | _ -> ()
                    )
                with
                  Not_found -> ()
              end;
              !found_st @ !found
            end
            else
              cands
          in (* cands *)


          (* checking conflicts *)

          [%debug_log "checking conflicts..."];

          let already_mapped_pairs = ref [] in

          let may_be_renamed n1 n2 =
            let b =
              try
                n1#data#is_named && n2#data#is_named &&
                let nm1 = get_orig_name n1 in
                let nm2 = get_orig_name n2 in
                cenv#is_rename_pat (nm1, nm2)
              with _ -> false
            in
            [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
            b
          in

          let cands =
            Xlist.filter_map
              (fun (n1, n2) ->

                let get d sorted ca n =
                  try
                    if sorted then
                      let pos, found =
                        Array.fold_left
                          (fun ((i, found) as a) c ->
                            if found then
                              a
                            else if c == n then
                              i + d, true
                            else
                              i + 1, found
                          ) (0, false) ca
                      in
                      if found then begin
                        let sib = ca.(pos) in
                        [%debug_log "%a: (%d) -> %a" nups n d nups sib];
                        Some sib
                      end
                      else
                        None
                    else
                      let sib = ca.(n#initial_pos + d) in
                      [%debug_log "%a: (%d) -> %a" nups n d nups sib];
                      Some sib
                  with
                    _ -> None
                in
                let get_left = get (-1) in
                let get_right = get 1 in
                let is_mapped ?(weak=false) n1_opt n2_opt =
                  let b =
                    match n1_opt, n2_opt with
                    | None, None -> weak
                    | Some n1, Some n2 -> begin
                        try
                          nmapping#find n1 == n2
                        with _ -> false
                    end
                    | _ -> false
                  in
                  begin %debug_block
                    let n_opt_to_str = function
                      | Some n -> UID.to_string n#uid
                      | None -> "None"
                    in
                    if b then
                      [%debug_log "mapped: %s -> %s" (n_opt_to_str n1_opt) (n_opt_to_str n2_opt)];
                  end;
                  b
                in
                let is_stable n1 n2 =
                  [%debug_log "%a-%a" nups n1 nups n2];
                  let cond0 =
                    try
                      let ca1 = n1#initial_parent#initial_children in
                      let ca2 = n2#initial_parent#initial_children in
                      let left = is_mapped (get_left false ca1 n1) (get_left false ca2 n2) in
                      let right = is_mapped (get_right false ca1 n1) (get_right false ca2 n2) in
                      [%debug_log "left=%B right=%B" left right];
                      left && right ||
                      (left || right) && n1#data#equals n2#data
                    with
                      _ -> false
                  in
                  [%debug_log "cond0=%B" cond0];
                  let cond1 () =
                    let b =
                      n1#data#eq n2#data &&
                      try
                        let p1 = n1#initial_parent in
                        let p2 = n2#initial_parent in
                        p1#data#eq p2#data &&
                        p1#initial_nchildren > 1 && p2#initial_nchildren > 1 &&
                        is_mapped (Some p1) (Some p2) &&
                        let ca1 = Array.copy p1#initial_children in
                        let ca2 = Array.copy p2#initial_children in

                        begin %debug_block
                          let a2s ca =
                            Xlist.to_string (fun x -> x#data#label) "; " (Array.to_list ca)
                          in
                          [%debug_log "ca1: [%s]" (a2s ca1)];
                          [%debug_log "ca2: [%s]" (a2s ca2)]
                        end;

                        List.iter
                            (Array.fast_sort (fun x1 x2 -> compare x1#data#label x2#data#label))
                            [ca1; ca2];

                        begin %debug_block
                          let a2s ca =
                            Xlist.to_string (fun x -> x#data#label) "; " (Array.to_list ca)
                          in
                          [%debug_log "ca1: -> [%s]" (a2s ca1)];
                          [%debug_log "ca2: -> [%s]" (a2s ca2)]
                        end;

                        is_mapped ~weak:true (get_left true ca1 n1) (get_left true ca2 n2) &&
                        is_mapped ~weak:true (get_right true ca1 n1) (get_right true ca2 n2)
                      with _ -> false
                    in
                    if b then
                      [%debug_log "!!!!!!!! %B" b];
                    b
                  in
                  let b = cond0 || cond1() in
                  [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
                  b
                in

                if hardoverride then begin
                  [%debug_log "hardoverride"];
                  Some (n1, n2, true)
                end
                else if
                  n1#data#is_order_insensitive && n2#data#is_order_insensitive &&
                  n1#initial_nchildren = 0 && n2#initial_nchildren = 0 &&
                  not (is_stable n1 n2)
                then begin
                  [%debug_log "not so good mapping: %a-%a" nups n1 nups n2];
                  if n1#initial_nchildren > 0 || n2#initial_nchildren > 0 then
                    None
                  else
                    try
                      match cenv#multiple_node_matches#find n1#data#_label with
                      | [], _ | _, [] -> None
                      | [x1], ns2 when x1 == n1 -> begin
                          List.fold_left
                            (fun opt x2 ->
                              match opt with
                              | None ->
                                  if x2 != n2 && is_stable x1 x2 then begin
                                    [%debug_log "better mapping found: %a-%a" nps x1 nps x2];
                                    Some (x1, x2, true)
                                  end
                                  else
                                    None
                              | x -> x
                            ) None ns2
                      end
                      | ns1, [x2] when x2 == n2 -> begin
                          List.fold_left
                            (fun opt x1 ->
                              match opt with
                              | None ->
                                  if x1 != n1 && is_stable x1 x2 then begin
                                    [%debug_log "better mapping found: %a-%a" nps x1 nps x2];
                                    Some (x1, x2, true)
                                  end
                                  else
                                    None
                              | x -> x
                            ) None ns1
                      end
                      | _ when begin
                          if n1#data#is_named && n2#data#is_named then
                            cenv#is_rename_pat (get_orig_name n1, get_orig_name n2)
                          else
                            try
                              let p1 = n1#initial_parent in
                              let p2 = n2#initial_parent in
                              cenv#is_rename_pat (get_orig_name p1, get_orig_name p2)
                            with
                              _ -> false
                      end -> Some (n1, n2, false)
                      | _ -> None
                    with
                      _ -> None
                end
                else begin
                  let score = ref (-1.0) in
                  let ncross = ref (-1) in

                  let defeated1 = ref false in
                  let defeated2 = ref false in

                  let already_mapped1 = ref false in
                  let already_mapped2 = ref false in

                  let has_def_sibling n =
                    try
                      Array.exists
                        (fun c -> B.is_def c#data#binding) n#initial_parent#initial_children
                    with _ -> false
                  in

                  let cond1, dnc1(*, padj1*) =
                    try
                      let n1' = nmapping#find n1 in

                      if n1' != n2 then begin

                        [%debug_log "%a-%a conflicts with %a-%a"
                          nups n1 nups n2 nups n1 nups n1'];

                        if
                          not (nmapping#is_final_mapping n1 n2) &&
                          nmapping#is_final_mapping n1 n1'
                        then
                          false, None
                        else if
                          n1#data#is_named_orig &&
                          n1'#data#is_named_orig &&
                          n1#data#eq n1'#data &&
                          not (n1#data#eq n2#data) &&
                          not (is_cross_boundary nmapping n1 n1')
                        then
                          false, None(*, None*)
                        else if
                          n1#data#eq n1'#data &&
                          n1#data#eq n2#data &&
                          not n1#data#is_named && not n1'#data#is_named &&
                          has_def_sibling n1 && has_def_sibling n1' &&
                          try
                            nmapping#find n1#initial_parent == n1'#initial_parent
                          with _ -> false
                        then begin
                          [%debug_log "%s -> %s, %s"
                            n1#data#to_string n2#data#to_string n1'#data#to_string];
                          false, None
                        end

                        (*!20240324!else if
                          n1#data#eq n1'#data &&
                          n1#data#eq n2#data &&
                          n1#data#is_named && n2#data#is_named &&
                          try
                            let p1 = n1#initial_parent in
                            let p2 = n2#initial_parent in
                            p1#data#is_boundary && p1#data#is_named_orig &&
                            p1#data#eq p2#data &&
                            nmapping#find p1 == p2
                          with _ -> false
                        then begin
                          [%debug_log "%s -> %s, %s"
                            n1#data#to_string n2#data#to_string n1'#data#to_string];
                          true, None
                        end*)

                        else if can_override n1 n2 n1 n1' then begin
                          true, None(*, None*)
                        end
                        else
                          let b = ref false in
                          let dnc = ref None in
                          cenv#compare_mappings nmapping
                            ~override ~bonus_self:true ~bonus_parent:true
                            n1 n1' (fun d _ _ -> dnc := d)
                            n1 n2 ~ncrossing_new:ncross ~adjacency_new:score
                            (fun d _ _ ->
                              b := true;
                              dnc := d;
                              defeated1 := true;
                            );
                          !b, !dnc(*,
                          let p1 = n1#initial_parent in
                          let b =
                            cenv#get_adjacency_score p1 n1'#initial_parent <
                            cenv#get_adjacency_score p1 n2#initial_parent
                          in
                          [%debug_log "padj1=%B" b];
                          Some b*)
                      end
                      else begin
                        already_mapped1 := true;
                        false, None(*, None*)
                      end
                    with
                      Not_found -> true, None(*, None*)
                  in
                  let cond2, dnc2(*, padj2*) =
                    try
                      let n2' = nmapping#inv_find n2 in

                      if n2' != n1 then begin

                        [%debug_log "%a-%a conflicts with %a-%a"
                          nups n1 nups n2 nups n2' nups n2];

                        if
                          not (nmapping#is_final_mapping n1 n2) &&
                          nmapping#is_final_mapping n2' n2
                        then
                          false, None
                        else if
                          n2#data#is_named_orig &&
                          n2'#data#is_named_orig &&
                          n2#data#eq n2'#data &&
                          not (n1#data#eq n2#data) &&
                          not (is_cross_boundary nmapping n2' n2)
                        then
                          false, None(*, None*)
                        else if
                          n2#data#eq n2'#data &&
                          n1#data#eq n2#data &&
                          not n2'#data#is_named && not n2#data#is_named &&
                          has_def_sibling n2' && has_def_sibling n2 &&
                          try
                            nmapping#find n2'#initial_parent == n2#initial_parent
                          with _ -> false
                        then begin
                          [%debug_log "%s, %s -> %s"
                            n1#data#to_string n2'#data#to_string n2#data#to_string];
                          false, None
                        end

                        (*!20240324!else if
                          n2#data#eq n2'#data &&
                          n1#data#eq n2#data &&
                          n1#data#is_named && n2#data#is_named &&
                          try
                            let p1 = n1#initial_parent in
                            let p2 = n2#initial_parent in
                            p1#data#is_boundary && p1#data#is_named_orig &&
                            p1#data#eq p2#data &&
                            nmapping#find p1 == p2
                          with _ -> false
                        then begin
                          [%debug_log "%s, %s -> %s"
                            n1#data#to_string n2'#data#to_string n2#data#to_string];
                          true, None
                        end*)

                        else if can_override n1 n2 n2' n2 then begin
                          true, None(*, None*)
                        end
                        else
                          let b = ref false in
                          let dnc = ref None in
                          cenv#compare_mappings nmapping
                            ~override ~bonus_self:true ~bonus_parent:true
                            n2' n2 (fun d _ _ -> dnc := d)
                            n1 n2 ~ncrossing_new:ncross ~adjacency_new:score
                            (fun d _ _ ->
                              b := true;
                              dnc := d;
                              defeated2 := true;
                            );
                          !b, !dnc(*,
                          let p2 = n2#initial_parent in
                          let b =
                            cenv#get_adjacency_score n2'#initial_parent p2 <
                            cenv#get_adjacency_score n1#initial_parent p2
                          in
                          [%debug_log "padj2=%B" b];
                          Some b*)
                      end
                      else begin
                        already_mapped2 := true;
                        false, None(*, None*)
                      end
                    with
                      Not_found -> true, None(*, None*)
                  in
                  if !already_mapped1 && !already_mapped2 then
                    already_mapped_pairs := (n1, n2) :: !already_mapped_pairs;

                  let cond_p =
                    try
                      let pn1 = n1#initial_parent in
                      let pn2 = n2#initial_parent in
                      (
                       is_cand pn1 pn2
                      (*||
                       try
                         is_mapped_pair pn1 pn2 && pn1#data#eq pn2#data
                       with _ -> false*)
                      ) &&
                      (
                       (try
                         pn1#data#get_name = n1#data#get_name &&
                         pn2#data#get_name = n2#data#get_name
                       ||
                         pn1#data#eq pn2#data &&
                         Comparison.get_stripped_name pn1 = Comparison.get_stripped_name n1 &&
                         Comparison.get_stripped_name pn2 = Comparison.get_stripped_name n2
                       with _ -> false) ||
                       (try
                         n1#data#is_named_orig && n1#data#eq n2#data &&
                         cenv#is_rename_pat (pn1#data#get_stripped_name, pn2#data#get_stripped_name)
                       with _ -> false)
                      )
                    with
                    | Not_found
                    | Otree.Parent_not_found _ -> false
                  in

                  let c0 = cond1 && cond2 in

                  (*!20240205!let has_nearest_mapped_same_name_ancestor_upto_boundary n1 n2 =
                    [%debug_log "%a-%a" nups n1 nups n2];
                    let moveon_ n = not n#data#is_boundary in
                    let find_anc = Sourcecode.find_nearest_mapped_ancestor_node ~moveon_ in
                    let b =
                      try
                        let an1 = find_anc nmapping#mem_dom n1 in
                        let an2 = find_anc nmapping#mem_cod n2 in
                        let an1' = nmapping#find an1 in
                        [%debug_log "%a->%a" nups an1 nups an1'];
                        an1' == an2 &&
                        (try an1#data#get_name = an2#data#get_name with _ -> false) ||
                        an1#data#_stripped_label = an2#data#_stripped_label
                      with _ -> false
                    in
                    [%debug_log "%B" b];
                    b
                  in*)

                  let c1 =
                    n1#data#_digest = n2#data#_digest(* ||
                    (not n1#data#is_named_orig && not n2#data#is_named_orig &&
                     n1#data#anonymized_label = n2#data#anonymized_label)*)
                    (*!20240205!n1#data#_digest = n2#data#_digest ||
                    n1#data#eq n2#data &&
                    has_nearest_mapped_same_name_ancestor_upto_boundary n1 n2*)
                  in
                  let c2 =
                    cond1 && not cond2 &&
                    match dnc1, dnc2 with
                    | Some d1, Some d2 -> d1 > d2
                    (*| _ when not n1#data#is_named_orig && not n2#data#is_named_orig ->
                        padj2 = Some true*)
                    | _ ->
                        (*false*)may_be_renamed n1 n2(*!20240205! ||
                        n1#data#_stripped_label = n2#data#_stripped_label ||
                        try n1#data#get_name = n2#data#get_name with _ -> false*)
                  in
                  let c3 =
                    not cond1 && cond2 &&
                    match dnc1, dnc2 with
                    | Some d1, Some d2 -> d1 < d2
                    (*| _ when not n1#data#is_named_orig && not n2#data#is_named_orig ->
                        padj1 = Some true*)
                    | _ ->
                        (*false*)may_be_renamed n1 n2(*!20240205! ||
                        n1#data#_stripped_label = n2#data#_stripped_label ||
                        try n1#data#get_name = n2#data#get_name with _ -> false*)
                  in

                  let cond = cond_p || c0 || (c1 && (c2 || c3)) in

                  begin %debug_block
                    let dnc_to_str = function
                      | Some d -> string_of_int d
                      | None -> "-"
                    in
                    [%debug_log "%a-%a->cond_p:%B cond1:%B cond2:%B c0:%B c1:%B c2:%B c3:%B dnc1:%s dnc2:%s --> %B"
                      nups n1 nups n2 cond_p cond1 cond2 c0 c1 c2 c3 (dnc_to_str dnc1) (dnc_to_str dnc2) cond];
                  end;

                  if cond then
                    Some (n1, n2, !defeated1 && !defeated2)
                  else
                    None

                end (* of if hardoverride else *)

              ) cands
          in (* cands *)

          let cands =
            List.map
              (fun ((n1, n2, defeated) as triple) ->
                [%debug_log "<%a-%a%s>" nups n1 nups n2 (if defeated then "(defeated)" else "")];
                if n1#data#anonymized_label <> n2#data#anonymized_label then
                  if n1#initial_nchildren = 0 && n2#initial_nchildren = 1 then
                    let c2 = n2#initial_children.(0) in
                    if n1#data#eq c2#data then begin
                      [%debug_log " -> <%a-%a%s>" nups n1 nups c2 (if defeated then "(defeated)" else "")];
                      shift_node2 c2;
                      n1, c2, defeated
                    end
                    else
                      triple
                  else if n1#initial_nchildren = 1 && n2#initial_nchildren = 1 then
                    let c1 = n1#initial_children.(0) in
                    if c1#data#eq n2#data then begin
                      [%debug_log " -> <%a-%a%s>" nups c1 nups n2 (if defeated then "(defeated)" else "")];
                      shift_node1 c1;
                      c1, n2, defeated
                    end
                    else
                      triple
                  else
                    triple
                else
                  triple
              ) cands
          in

          [%debug_log "cands: %s"
            (String.concat ""
               (List.map
                  (fun (n1, n2, defeated) ->
                    sprintf "<%a-%a%s>" nups n1 nups n2 (if defeated then "(defeated)" else "")
                  ) cands))];

          [%debug_log "already mapped pairs (no conflict): %s"
            (String.concat ""
               (List.map
                  (fun (n1, n2) ->
                    sprintf "<%a-%a>" nups n1 nups n2
                  ) !already_mapped_pairs))];

          if cands = [] then begin
            let cld1_all_not_mapped = List.filter (fun n -> (nmapped_of_subtree1 n) = 0) cld1 in
            let cld2_all_not_mapped = List.filter (fun n -> (nmapped_of_subtree2 n) = 0) cld2 in
            match cld1_all_not_mapped, cld2_all_not_mapped with
            | [n1], [n2] -> if recur then scan_down (score_up, score_down) n1 n2
            | _ -> (* () *)
                List.iter (* experimental *)
                  (fun (n1, n2) ->
                    let cond =
                      (not (n1#initial_children = [||]) || not (n2#initial_children = [||])) &&
(*                      (n1#data#eq n2#data) && *)
                      (try
                        let _ns1, _ns2 = cenv#multiple_node_matches#find n1#data#_label in
                        let ns1 = List.filter (fun n -> not (nmapping#mem_dom n)) _ns1 in
                        let ns2 = List.filter (fun n -> not (nmapping#mem_cod n)) _ns2 in
                        [%debug_log "ns1: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" ns1)];
                        [%debug_log "ns2: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" ns2)];
                        match ns1, ns2 with
                        | [], [] | [_], [_] -> true
                        | _ -> false
                      with
                        Not_found -> true
                      )(* ||
                      n1#initial_nchildren = 1 && n2#initial_nchildren = 1 &&
                      (not (nmapping#mem_dom n1#initial_children.(0)) ||
                      not (nmapping#mem_cod n2#initial_children.(0)))*)
                    in
                    if cond && recur then
                      scan_down (score_up, score_down) n1 n2
                  ) !already_mapped_pairs
          end
          else begin
            List.iter
              (fun (cnd1, cnd2, defeated) ->

                [%debug_log "glue cand (scan_down): %a-%a" nups cnd1 nups cnd2];

                let bonus, is_ok =
                  if cnd1#data#equals cnd2#data then
                    calc_bonus cnd1 cnd2, true
                  else
                    cenv#eval_label_match cnd1 cnd2, relabel_allowed cnd1 cnd2
                in
                if is_ok then begin
                  let base =
                    if has_uniq_paths cnd1 cnd2(* is_unique_pair cnd1 cnd2 *) then
                      score_up
                    else
                      score_down
                  in

                  [%debug_log "base score: %d, bonus: %d" base bonus];

                  let score = base + bonus(* + (if defeated then 1 else 0)*) in

                  if cnd1#data#subtree_equals cnd2#data then begin
                    let nds1 = ref [] in
                    let nds2 = ref [] in
                    tree1#fast_scan_whole_initial_subtree cnd1 (fun n -> nds1 := n::!nds1);
                    tree2#fast_scan_whole_initial_subtree cnd2 (fun n -> nds2 := n::!nds2);
                    List.iter2
                      (fun n1 n2 ->
                        add_cand "no tree diff" n1 n2 score
                      ) !nds1 !nds2;
                    if cnd1#initial_nchildren > 0 then
                      scan_up ~reflex:true (score_up, score_down)
                        cnd1#initial_children.(0) cnd2#initial_children.(0)
                  end
                  else begin
                    add_cand "no tree diff" cnd1 cnd2 score;
                    if
                      (cnd1#initial_nchildren = 0 && cnd2#initial_nchildren = 0) (* ||
                                                                                    to_be_focused *)
                    then
                      scan_up ~reflex:true (score_up, score_down) cnd1 cnd2
                    else if recur then
                      scan_down ~hardoverride:defeated (score_up, score_down) cnd1 cnd2
                  end
                end
              ) cands;

            if (* override *) true then
              let cands1, cands2, _ = Xlist.split3 cands in
              match Xlist.subtractq cld1 cands1, Xlist.subtractq cld2 cands2 with
              | [n1], [n2] when recur ->
                  if nmapped_of_subtree1 n1 = 0 || nmapped_of_subtree2 n2 = 0 then
                    scan_down ~force_treediff:true (score_up, score_down) n1 n2
              | _ -> ()
          end

        end (* of tree diff not used *)

      end (* not scanned yet *)

    in (* end of func scan_down *)

    nmapping#print_status;


(*    cenv#compare_mappings_cache_begin; *)

    (*let starting_pairs =
      List.fold_left
       (fun l (n1, n2) ->
         if is_bad_pair n1 n2 then
           l
         else
           (n1, n2)::l
       ) [] nmapping#starting_pairs_for_glueing
    in*)

    let upward_only =
      if options#simple_glue_flag then
        true
      else
        false
    in
    (*let starting_pairs =
      if not options#simple_glue_flag then
        starting_pairs
      else if starting_pairs = [] then begin
        let s_up = Xset.create 0 in
        let s_down = Xset.create 0 in
        nmapping#iter_unsettled
          (fun n1 n2 ->
            (*if
              not (n1#data#is_named_orig && n1#data#anonymized2_label = n2#data#anonymized2_label)
            then
              let _ = () in*)
              Xset.add s_up n1;
            (*let f = ref (fun () -> ()) in
            begin
              try
                Xset.iter
                  (fun x ->
                    if tree1#is_initial_ancestor x n1 then begin
                      f := (fun () -> Xset.remove s_up x; Xset.add s_up n1);
                      raise Exit
                    end
                    else if tree1#is_initial_ancestor n1 x then
                      raise Exit
                  ) s_up;
                Xset.add s_up n1
              with
                Exit -> (!f)()
            end;*)

            if downward then
              Xset.add s_down n1
              (*let f = ref (fun () -> ()) in
              begin
                try
                  Xset.iter
                    (fun x ->
                      if tree1#is_initial_ancestor n1 x then begin
                        f := (fun () -> Xset.remove s_down x; Xset.add s_down n1);
                        raise Exit
                      end
                      else if tree1#is_initial_ancestor x n1 then
                        raise Exit
                    ) s_down;
                  Xset.add s_down n1
                with
                  Exit -> (!f)()
              end;*)
          );
        Xprint.verbose options#verbose_flag "starting pairs for upward glueing: %d" (Xset.length s_up);
        Xprint.verbose options#verbose_flag "starting pairs for downward glueing: %d" (Xset.length s_down);
        (*Xprint.verbose options#verbose_flag "for down: %d" (Xset.length s_down);*)
        let l = ref [] in
        nmapping#iter_unsettled
          (fun n1 n2 ->
            if Xset.mem s_up n1 || (downward && Xset.mem s_down n1) then
              l := (n1, n2) :: !l
          );
        !l
      end
      else
        starting_pairs
    in*)
    Xprint.verbose options#verbose_flag
      "%d starting_pairs, upward_only=%B" (List.length starting_pairs) upward_only;
(*
    let starting_pairs =
      List.fast_sort
        (fun (n10, n20) (n11, n21) ->
          let gi10, gi11 = n10#gindex, n11#gindex in
          let c = Stdlib.compare gi10 gi11 in
          if c = 0 then
            let gi20, gi21 = n20#gindex, n21#gindex in
            Stdlib.compare gi20 gi21
          else
            c
        ) starting_pairs
    in
*)
    let has_dels_and_inss () =
      let reduced_mapping_list = nmapping#get_reduced_mapping_list() in
      let has_crossing_or_incompatible_mapping nd1 nd2 =
        List.exists
          (function
            | (n1, n2)::_ -> begin
                n1 != nd1 && n2 != nd2 &&
	        Node_mapping.is_crossing nd1 nd2 n1 n2 ||
                Node_mapping.is_incompatible tree1 tree2 nd1 nd2 n1 n2
            end
            | _ -> assert false
          ) reduced_mapping_list
      in
      let has_dels =
        try
          tree1#fast_scan_whole_initial
            (fun nd ->
              try
                let nd' = nmapping#find nd in
                if
                  (*not (nd#data#eq nd'#data)*)
                  has_crossing_or_incompatible_mapping nd nd'
                then
                  raise Exit
              with
                Not_found -> raise Exit
            );
          false
        with
          Exit -> true
      in
      let has_inss =
        try
          tree2#fast_scan_whole_initial
            (fun nd ->
              if not (nmapping#mem_cod nd) then
                raise Exit
            );
          false
        with
          Exit -> true
      in
      [%debug_log "has_dels=%B has_inss=%B" has_dels has_inss];
      let b = has_dels && has_inss in
      [%debug_log "%B" b];
      Xprint.verbose options#verbose_flag "has_dels=%B has_inss=%B" has_dels has_inss;
      b
    in

    nmapping#set_starting_pairs_for_glueing starting_pairs;

    if starting_pairs = [] then begin

      if has_dels_and_inss() then begin

      nmapping#iter_unsettled (*_sorted Stdlib.compare *)
        (fun n1 n2 ->
          let s = get_scoring n1 n2 in
          scan_up s n1 n2;
          if first || not upward_only then
            scan_down s n1 n2
        );
      nmapping#iter_settled_roots_sorted cmp_node_pairs
        (fun n1 n2 ->
          let s = get_scoring n1 n2 in
          scan_up s n1 n2)

      end

    end
    else begin

      begin %debug_block
        List.iter
          (fun (n1, n2) -> [%debug_log "starting_pair: %a-%a" nups n1 nups n2])
          starting_pairs;

        let starting_node_pairs =
          List.fast_sort (fun (n1, _) (n2, _) -> Stdlib.compare n1#gindex n2#gindex)
            starting_pairs
        in
        List.iter
          (fun (n1, n2) ->
            [%debug_log "starting_pair (gindex): %a-%a" ngps n1 ngps n2]
          ) starting_node_pairs;
      end;

      List.iter
        (fun (n1, n2) ->
          let s = get_scoring n1 n2 in
          if not downward then
            scan_up s n1 n2;
          if not upward_only || downward then
            scan_down s n1 n2
        ) starting_pairs

    end;

    let sorted_cands =
      List.fast_sort (fun (_, s1) (_, s2) -> compare !s2 !s1) !cands
    in

    begin %debug_block
      [%debug_log "%d CANDIDATES (sorted by score):" (List.length sorted_cands)];
      List.iter
        (fun ((nd1, nd2), score) ->
          [%debug_log "%a-%a (score=%d)" nups nd1 nups nd2 !score]
        ) sorted_cands;
    end;


    (* solving conflict *)

    let score_tbl = Hashtbl.create 0 in
    let tbl1 = Hashtbl.create 0 in
    let tbl2 = Hashtbl.create 0 in

    let tbl_add t n =
      try
        let c = Hashtbl.find t n in
        Hashtbl.replace t n (c + 1)
      with Not_found ->
        Hashtbl.add t n 1
    in
    let get_count t n =
      try
        Hashtbl.find t n
      with
        Not_found -> 0
    in

    List.iter
      (fun ((n1, n2) as up, x) ->
        tbl_add tbl1 n1;
        tbl_add tbl2 n2;
        Hashtbl.add score_tbl up x
      ) sorted_cands;

    let get_parent_pair_adj_gi (n1, n2) =
      let p1 = n1#initial_parent in
      let p2 = n2#initial_parent in
      let adj = cenv#get_adjacency_score p1 p2 in
      (p1, p2), adj, (p1#gindex, p2#gindex)
    in
    let get_score up = Hashtbl.find score_tbl up in

    let conflicting_cands, good_cands =
      List.fold_left
        (fun (conflicting, good) ((n1, n2), s) ->
          if (get_count tbl1 n1) > 1 || (get_count tbl2 n2) > 1 then
            ((n1, n2), !s)::conflicting, good
          else
            conflicting, ((n1, n2), !s)::good;

        ) ([], []) sorted_cands
    in

    begin %debug_block
      [%debug_log "%d GOOD CANDIDATES (no conflicts):" (List.length good_cands)];
      List.iter
        (fun ((nd1, nd2), s) ->
          [%debug_log "%a-%a (score=%d)" nups nd1 nups nd2 s]
        ) good_cands;
    end;

    let rec cmp_score ?(top=true) (up1, (s1, adj1, gip1)) (up2, (s2, adj2, gip2)) =
      let c1 = Stdlib.compare s2 s1 in
      if c1 = 0 then
        let c2 = Stdlib.compare adj2 adj1 in
        if c2 = 0 then
          try
            if not top then begin
              (*let gi11, gi12 = gip1 in
              let gi21, gi22 = gip2 in
              let n11 = tree1#search_node_by_gindex gi11 in
              let n21 = tree1#search_node_by_gindex gi21 in
              let n12 = tree2#search_node_by_gindex gi12 in
              let n22 = tree2#search_node_by_gindex gi22 in
              let ncrossing_old = ref (-1) in
              let ncrossing_new = ref (-1) in
              let b = ref 0 in
              cenv#compare_mappings nmapping ~force_prefer_crossing_count:true
                n11 n12 (fun _ _ _ -> b := 1)
                n21 n22 (fun _ _ _ -> b := -1);
              !b???NG???*)
              raise Exit;
            end
            else
            let pup1, adj1, pgi1 = get_parent_pair_adj_gi up1 in
            let pup2, adj2, pgi2 = get_parent_pair_adj_gi up2 in
            let ps1 = get_score pup1 in
            let ps2 = get_score pup2 in
            cmp_score ~top:false (pup1, (!ps1, adj1, pgi1)) (pup2, (!ps2, adj2, pgi2))
          with
            _ -> Stdlib.compare gip2 gip1
        else
          c2
      else
        c1
    in

    let sorted_conflicting_cands =
      let l =
        List.map
          (fun ((n1, n2), s) ->
            if record_conflicted_pairs then
              Xset.add conflicted_pairs (n1, n2);
            let adj = cenv#get_adjacency_score n1 n2 in
            (*let s = if is_cross_boundary nmapping n1 n2 then s / 2 else s in*)
            (*let s =
              try
                let p1 = n1#initial_parent in
                let p2 = n2#initial_parent in
                if p1#initial_nchildren = 1 && p2#initial_nchildren = 1 then
                  let p_score = get_score (p1, p2) in
                  let s' = min s !p_score in
                  if s <> s' then
                    [%debug_log "!!!!!! %a-%a: %d -> %d" nups n1 nups n2 s s'];
                  s'
                else
                  s
              with _ -> s
            in*)
            ((n1, n2), (s, adj, (n1#gindex, n2#gindex)))
          ) conflicting_cands
      in
      List.fast_sort cmp_score l
    in

    begin %debug_block
      [%debug_log "%d CONFLICTING CANDIDATES (sorted by score, adjacency, and gindexes):"
        (List.length sorted_conflicting_cands)];
      List.iter
      (fun ((nd1, nd2), (s, adj, (gi1, gi2))) ->
        [%debug_log "%a-%a (%d, %f, (%a-%a))" nups nd1 nups nd2 s adj gps gi1 gps gi2]
      ) sorted_conflicting_cands;
    end;

    Hashtbl.clear tbl1;
    Hashtbl.clear tbl2;

    let _nmap = Hashtbl.create 0 in
    let _is_mapped n1 n2 =
      try
        Hashtbl.find _nmap n1 == n2
      with
        _ -> false
    in
    let _set1 = Xset.create 0 in
    let _set2 = Xset.create 0 in
    let _are_named_orig n1 n2 = n1#data#is_named_orig && n2#data#is_named_orig in

    let resolved_cands, unresolved_cands =
      List.partition
        (fun ((n1, n2), (_, _, _)) ->
          [%debug_log "%a-%a" nups n1 nups n2];
          if (get_count tbl1 n1) = 0 && (get_count tbl2 n2) = 0 then begin
            if
              not (Xset.mem _set1 n1) && not (Xset.mem _set2 n2)
            ||
              not (options#dump_delta_flag || options#conservative_flag) &&
              _are_named_orig n1 n2
            ||
              _is_mapped n1 n2
            then begin
              tbl_add tbl1 n1;
              tbl_add tbl2 n2;

              Hashtbl.add _nmap n1 n2;
              begin
                try
                  let p1 = n1#initial_parent in
                  let p2 = n2#initial_parent in
                  Xset.add _set1 p1;
                  Xset.add _set2 p2;
                  Hashtbl.add _nmap p1 p2;
                with
                  _ -> ()
              end;
              true
            end
            else
              false
          end
          else
            false
        ) sorted_conflicting_cands
    in
    let additionally_resolved_cands =
      List.filter
        (fun ((n1, n2), (_, _, _)) ->
          if (get_count tbl1 n1) = 0 && (get_count tbl2 n2) = 0 then begin
            try
              _is_mapped n1 n2 &&
              _is_mapped n1#initial_parent n2#initial_parent
            with
              _ -> false
          end
          else
            false
        ) unresolved_cands
    in

    begin %debug_block
      [%debug_log "%d CANDIDATES (resolved):" (List.length resolved_cands)];
      List.iter
      (fun ((nd1, nd2), (s, adj, (gi1, gi2))) ->
          [%debug_log "%a-%a (%d, %f, (%a-%a))" nups nd1 nups nd2 s adj gps gi1 gps gi2]
        ) resolved_cands;
      [%debug_log "%d CANDIDATES (additionally resolved):" (List.length additionally_resolved_cands)];
      List.iter
        (fun ((nd1, nd2), (s, adj, (gi1, gi2))) ->
          [%debug_log "%a-%a (%d, %f, (%a-%a))" nups nd1 nups nd2 s adj gps gi1 gps gi2]
        ) additionally_resolved_cands;
    end;

    let resolved_cands = resolved_cands @ additionally_resolved_cands in

    let good_cands = List.map (fun (p, _) -> p) good_cands in
    let resolved_cands = List.map (fun (p, _) -> p) resolved_cands in

    let final_cands = good_cands @ resolved_cands in

    begin %debug_block
      [%debug_log "%d CANDIDATES (final):" (List.length final_cands)];
      List.iter (fun (n1, n2) -> [%debug_log "%a-%a" nups n1 nups n2]) final_cands;
    end;


    let removed_pairs = ref [] in
    let added_pairs = ref [] in

    let is_crossing_with_added n1 n2 =
      let b =
        try
          List.iter
            (fun (n1', n2') ->
              if cenv#is_crossing_or_incompatible n1 n2 n1' n2' then begin
                [%debug_log "found: %a-%a [%a]-[%a] %a" nups n1' nups n2'
                  locps n1' locps n2' labps n1'];
                raise Exit
              end
            ) !added_pairs;
          false
        with
          Exit -> true
      in
      [%debug_log "%a %a -> %B" nups n1 nups n2 b];
      b
    in

    let failed_cands = ref [] in

    let add_mappings =
    List.iter (* add mappings *)
      (fun (nd1, nd2) ->

        [%debug_log "adding %a-%a" nups nd1 nups nd2];

        if nmapping#has_mapping nd1 nd2 then begin
          [%debug_log "already in mapping: %a-%a" nups nd1 nups nd2]
        end
        else
          let to_be_removed = ref [] in
          let ncross = ref (-1) in
          let adj = ref (-1.0) in

          let can_add1, dnc1, padj1 =
            try
              let n2 = nmapping#find nd1 in
              if n2 != nd2 then begin

                [%debug_log "conflict: %a->%a" nups nd1 nups n2];

                if nmapping#is_final_mapping nd1 n2 then begin
                  [%debug_log "         --> final"];
                  false, None, None
                end
                else if no_moves && nmapping#is_stable_pair nd1 n2 then begin
                  [%debug_log "         --> stable"];
                  false, None, None
                end
                else if can_override nd1 nd2 nd1 n2 then begin
                  to_be_removed := (nd1, n2) :: !to_be_removed;
                  true, None, None
                end
                else begin
                  to_be_removed := (nd1, n2) :: !to_be_removed;
                  let b = ref false in
                  let dnc = ref None in
                  let force = ref false in
                  let nd1_ = if is_shifted_node1 nd1 then nd1#initial_parent else nd1 in
                  cenv#compare_mappings nmapping ~override
                    nd1_ n2 (fun d _ frc -> dnc := d; force := frc)
                    nd1_ nd2 ~ncrossing_new:ncross ~adjacency_new:adj
                    (fun d _ frc ->
                      b := true;
                      dnc := d;
                      force := frc
                    );
                  [%debug_log "force=%B" !force];
                  !b, !dnc,
                  if !force then None else
                  if tree2#is_initial_ancestor n2 nd2 || tree2#is_initial_ancestor nd2 n2 then
                    None
                  else
                  let p1 = nd1#initial_parent in
                  let b =
                    if
                      is_cross_boundary nmapping p1 n2#initial_parent &&
                      not (is_cross_boundary nmapping p1 nd2#initial_parent)
                    then
                      true
                    else if
                      is_cross_boundary nmapping p1 nd2#initial_parent &&
                      not (is_cross_boundary nmapping p1 n2#initial_parent)
                    then
                      false
                    else
                      (*if Comparison.next_to_each_other n2#initial_parent nd2#initial_parent then
                        false
                      else!!!NG!!!*)
                        cenv#get_adjacency_score p1 n2#initial_parent <
                        cenv#get_adjacency_score p1 nd2#initial_parent
                  in
                  [%debug_log "padj1=%B" b];
                  Some b
                end
              end
              else (* n2 == nd2 *)
                false, None, None
            with
              Not_found ->
                let b =
                  not no_moves ||
                  not (is_crossing_with_added nd1 nd2)
                in
                b, None, None
          in
          let can_add2, dnc2, padj2 =
            try
              let n1 = nmapping#inv_find nd2 in
              if n1 != nd1 then begin

                [%debug_log "conflict: %a<-%a" nups n1 nups nd2];

                if nmapping#is_final_mapping n1 nd2 then begin
                  [%debug_log "         --> final"];
                  false, None, None
                end
                else if no_moves && nmapping#is_stable_pair n1 nd2 then begin
                  [%debug_log "         --> stable"];
                  false, None, None
                end
                else if can_override nd1 nd2 n1 nd2 then begin
                  to_be_removed := (n1, nd2) :: !to_be_removed;
                  true, None, None
                end
                else begin
                  to_be_removed := (n1, nd2) :: !to_be_removed;
                  let b = ref false in
                  let dnc = ref None in
                  let force = ref false in
                  let nd2_ = if is_shifted_node2 nd2 then nd2#initial_parent else nd2 in
                  cenv#compare_mappings nmapping ~override
                    n1 nd2_ (fun d _ frc -> dnc := d; force := frc)
                    nd1 nd2_ ~ncrossing_new:ncross ~adjacency_new:adj
                    (fun d _ frc ->
                      b := true;
                      dnc := d;
                      force := frc
                    );
                  [%debug_log "force=%B" !force];
                  !b, !dnc,
                  if !force then None else
                  if tree1#is_initial_ancestor n1 nd1 || tree1#is_initial_ancestor nd1 n1 then
                    None
                  else
                  let p2 = nd2#initial_parent in
                  let b =
                    if
                      is_cross_boundary nmapping n1#initial_parent p2 &&
                      not (is_cross_boundary nmapping nd1#initial_parent p2)
                    then
                      true
                    else if
                      is_cross_boundary nmapping nd1#initial_parent p2 &&
                      not (is_cross_boundary nmapping n1#initial_parent p2)
                    then
                      false
                    else
                      (*if Comparison.next_to_each_other n1#initial_parent nd1#initial_parent then
                        false
                      else!!!NG!!!*)
                        cenv#get_adjacency_score n1#initial_parent p2 <
                        cenv#get_adjacency_score nd1#initial_parent p2
                  in
                  [%debug_log "padj2=%B" b];
                  Some b
                end
              end
              else (* n1 == nd1 *)
                false, None, None
            with
              Not_found ->
                let b =
                  not no_moves ||
                  not (is_crossing_with_added nd1 nd2)
                in
                b, None, None
          in
          begin %debug_block
            let dnc_to_str = function
              | Some d -> string_of_int d
              | None -> "-"
            in
            [%debug_log "can_add1=%B can_add2=%B dnc1:%s dnc2:%s"
              can_add1 can_add2 (dnc_to_str dnc1) (dnc_to_str dnc2)];
          end;
          if
            (can_add1 && can_add2) ||
            (
             (
              nd1#data#_digest = nd2#data#_digest ||
              (
               not nd1#data#is_named_orig && not nd2#data#is_named_orig &&
               (*not nd1#data#has_non_trivial_value && not nd2#data#has_non_trivial_value &&!!!NG!!!*)
               nd1#data#_anonymized_label = nd2#data#_anonymized_label
              )
             ) &&
             (
              (can_add1 && not can_add2 &&
               let _ = [%debug_log "@"] in
               match dnc1, dnc2 with
               | Some d1, Some d2 -> d1 > d2
               | None, Some _ -> padj2 = Some true
               | _ when not nd1#data#is_named_orig && not nd2#data#is_named_orig ->
                   padj2 = Some true
               (*| _ when not nd1#data#has_non_trivial_value && not nd2#data#has_non_trivial_value ->
                   padj2 = Some true!!!NG!!!*)
               | _ -> false
              ) ||
              (not can_add1 && can_add2 &&
               let _ = [%debug_log "@"] in
               match dnc1, dnc2 with
               | Some d1, Some d2 -> d1 < d2
               | Some _, None -> padj1 = Some true
               | _ when not nd1#data#is_named_orig && not nd2#data#is_named_orig ->
                   padj1 = Some true
               (*| _ when not nd1#data#has_non_trivial_value && not nd2#data#has_non_trivial_value ->
                   padj1 = Some true!!!NG!!!*)
               | _ -> false
              )
             )
            )
          then begin
            List.iter
              (fun ((n1, n2) as n1_n2) ->
                if n1 != nd1 || n2 != nd2 then begin
                  if nmapping#remove n1 n2 then begin
                    removed_pairs := n1_n2 :: !removed_pairs;
                    if List.mem n1_n2 !added_pairs then
                      added_pairs := Xlist.subtract !added_pairs [n1_n2];
                    [%debug_log "removed %a-%a" nups n1 nups n2];
                  end
                end
              ) !to_be_removed;
            ignore (nmapping#add_unsettled nd1 nd2);
            do_deferred_op (nd1, nd2);

            (*removed_pairs := !to_be_removed @ !removed_pairs;*)
            added_pairs := (nd1, nd2) :: !added_pairs;

            [%debug_log "added %a-%a (%a-%a)" nups nd1 nups nd2 ngps nd1 ngps nd2];
          end
          else begin
            failed_cands := (nd1, nd2) :: !failed_cands
          end;

      )
    in
    add_mappings final_cands;

    begin %debug_block
      [%debug_log "%d CANDIDATES FAILED:" (List.length !failed_cands)];
      List.iter (fun (n1, n2) -> [%debug_log "%a-%a" nups n1 nups n2]) !failed_cands;
    end;

    let extra_cands = ref [] in
    let failed_nds1, failed_nds2 = List.split !failed_cands in
    let added_nds1, added_nds2 = List.split !added_pairs in
    let added_nds1 = Xset.from_list added_nds1 in
    let added_nds2 = Xset.from_list added_nds2 in
    let nds1 = Xset.create 0 in
    let nds2 = Xset.create 0 in
    List.iter
      (fun (((n1, n2) as n1_n2), (_, _, _)) ->
        if
          not (Xset.mem nds1 n1) && not (Xset.mem nds2 n2) &&
          not (List.mem n1_n2 !removed_pairs) &&
          not (Xset.mem added_nds1 n1) && not (Xset.mem added_nds2 n2)
        then
          if n1#data#is_sequence && n2#data#is_sequence then begin
            let mem1 = List.memq n1 failed_nds1 in
            let mem2 = List.memq n2 failed_nds2 in
            if mem1 || mem2 then begin
              if mem1 then
                Xset.add nds1 n1;
              if mem2 then
                Xset.add nds2 n2;
              extra_cands := (n1, n2) :: !extra_cands
            end
          end
      ) unresolved_cands;

    begin %debug_block
      [%debug_log "%d EXTRA CANDIDATES:" (List.length !extra_cands)];
      List.iter (fun (n1, n2) -> [%debug_log "%a-%a" nups n1 nups n2]) !extra_cands;
    end;

    add_mappings !extra_cands;

(*    cenv#compare_mappings_cache_end; *)

    begin %debug_block
      [%debug_log "nmapping:\n%s\n" nmapping#to_string];
      List.iter
        (fun (name, pairs) ->
          List.iter
            (fun (n1, n2) ->
              [%debug_log "%s: %a-%a (%a-%a)" name nups n1 nups n2 ngps n1 ngps n2]
            ) pairs
        ) [("removed_pair", !removed_pairs); ("added_pair", !added_pairs)]
    end;

    Xprint.verbose options#verbose_flag "glueing completed.";

    !removed_pairs, !added_pairs, conflicted_pairs
  (* end of func glue_deletes_and_inserts *)


  let sync_edits
      options
      ?(is_mov=fun _ _ -> false, None)
      ?(check_conflicts=false)
      cenv edits removed_pairs added_pairs
      =
    let mid_gen = options#moveid_generator in

    [%debug_log "* REMOVING EDITS..."];

    let to_be_added1 = Xset.create 0 in
    let to_be_added2 = Xset.create 0 in
    List.iter
      (fun (n1, n2) ->
        [%debug_log "checking %a-%a" nups n1 nups n2];
        let eds = edits#find12 n1 n2 in
        begin %debug_block
          List.iter (fun ed -> [%debug_log "removing %s" (Edit.to_string ed)]) eds
        end;
        if eds = [] then begin
          [%debug_log "none found"];
        end
        else begin
          List.iter edits#remove_edit eds;
        end;
        Xset.add to_be_added1 n1;
        Xset.add to_be_added2 n2
      ) removed_pairs;

    List.iter
      (fun (n1, n2) ->
        Xset.remove to_be_added1 n1;
        Xset.remove to_be_added2 n2
      ) added_pairs;

    [%debug_log "* ADDING EDITS..."];

    Xset.iter
      (fun n1 ->
        let del = Edit.make_delete n1 in
        [%debug_log "adding %s" (Edit.to_string del)];
        edits#add_edit del;
      ) to_be_added1;
    Xset.iter
      (fun n2 ->
        let ins = Edit.make_insert n2 in
        [%debug_log "adding %s" (Edit.to_string ins)];
        edits#add_edit ins
      ) to_be_added2;

    let pending_pairs = ref [] in

    List.iter
      (fun (n1, n2) ->
        [%debug_log "checking %a-%a" nups n1 nups n2];
        begin
          try
            let del = edits#find_del n1 in
            [%debug_log "removing %s" (Edit.to_string del)];
            edits#remove_edit del
          with
            Not_found -> ()
        end;
        begin
          try
            let ins = edits#find_ins n2 in
            [%debug_log "removing %s" (Edit.to_string ins)];
            edits#remove_edit ins;
          with
            Not_found -> ()
        end;
        if not (n1#data#eq n2#data) then
          edits#add_edit (Edit.make_relabel n1 n2);

        if edits#mem_mov12 n1 n2 then
          ()
        else
          let b, mid_opt = is_mov n1 n2 in
          [%debug_log "is_mov: %a-%a --> %B" nups n1 nups n2 b];
          if b then begin
            let info1, info2 = mkinfo n1, mkinfo n2 in
            let mid =
              match mid_opt with
              | Some mid -> mid
              | _ -> mid_gen#gen
            in
            edits#add_edit (Edit.make_move_permutation mid info1 info2);
          end
          else if check_conflicts then
            pending_pairs := (n1, n2) :: !pending_pairs

      ) added_pairs;

    if check_conflicts then begin
      let a = Array.of_list !pending_pairs in
      let len = Array.length a in
      let ca = Array.make len 0 in
      let li = len - 1 in
      let conflicts = ref [] in
      for i = 0 to li do
        let (n1, n2) as p = a.(i) in
        for j = i + 1 to li do
          let (n1', n2') as p' = a.(j) in
          let b = cenv#is_crossing_or_incompatible n1 n2 n1' n2' in
          [%debug_log "conflicts: (%a,%a) vs (%a,%a) --> %B"
            nups n1 nups n2 nups n1' nups n2' b];
          if b then begin
            conflicts := (p, p') :: !conflicts;
            ca.(i) <- ca.(i) + 1;
            ca.(j) <- ca.(j) + 1;
          end
        done
      done;
      let cpl = List.combine (Array.to_list ca) !pending_pairs in
      let cpl = List.fast_sort (fun (c0, _) (c1, _) -> compare c1 c0) cpl in
      [%debug_log "cpl=[%s]"
        (String.concat ""
           (List.map
              (fun (c,(n1,n2)) -> sprintf "<%d,(%a,%a)>" c nups n1 nups n2) cpl))];
      let movs = ref [] in
      if !conflicts <> [] then begin
        try
          List.iter
            (fun (_, p) ->

              conflicts :=
                List.fold_left
                  (fun l (p0, p1) ->
                    if p == p0 || p == p1 then
                      l
                    else
                      (p0, p1)::l
                  ) [] !conflicts;

              movs := p :: !movs;

              if !conflicts = [] then
                raise Exit

            ) cpl
        with
          Exit -> ()
      end;
      [%debug_log "movs=[%s]"
        (String.concat ", "
           (List.map
              (fun (n1,n2) -> sprintf "(%a,%a)" nups n1 nups n2) !movs))];

      List.iter
        (fun (n1, n2) ->
          let info1, info2 = mkinfo n1, mkinfo n2 in
          let mid = mid_gen#gen in
          edits#add_edit (Edit.make_move_permutation mid info1 info2);
        ) !movs
    end
  (* end of func sync_edits *)

  let generate_edits ?(simple=false)
      options
      lang
      (cenv : (node_t, tree_t) Comparison.c)
      pruned
      edits
      (nmapping : node_t Node_mapping.c)
      =
    let tree1 = cenv#tree1 in
    let tree2 = cenv#tree2 in

    [%debug_log "simple=%B" simple];

    [%debug_log "nmapping:\n%s\n" nmapping#to_string];
    (*[%debug_log "nmapping (gindex):\n%s\n" nmapping#to_string_gid];*)


    (* generate deletes and relabels *)
    tree1#fast_scan_whole_initial
      (fun nd ->
        [%debug_log "scanning %a" nups nd];
        try
          let nd' = nmapping#find nd in
          if not (nd#data#eq nd'#data) then begin
            let rel = Edit.make_relabel nd nd' in
            [%debug_log "%s" (Edit.to_string rel)];
            edits#add_edit rel
          end
        with
          Not_found ->
            let del = Edit.make_delete nd in
            [%debug_log "%s" (Edit.to_string del)];
            edits#add_edit del
      );
    (* generate inserts *)
    tree2#fast_scan_whole_initial
      (fun nd ->
        [%debug_log "scanning %a" nups nd];

        if not (nmapping#mem_cod nd) then begin
          let ins = Edit.make_insert nd in
          [%debug_log "%s" (Edit.to_string ins)];
          edits#add_edit ins
        end
        else
          [%debug_log "%a <- %a" nups (nmapping#inv_find nd) nups nd]
      );

(*
    let ndeletes = edits#get_ndeletes in
    let ninserts = edits#get_ninserts in
    [%debug_log "[0] edits: del:%d ins:%d rel:%d" ndeletes ninserts edits#get_nrelabels];

    if not options#no_glue_flag && (ndeletes = 0 || ninserts = 0) then begin
      if options#verbose_flag then begin
        let s =
          if ndeletes = 0 then
            "deletes"
          else if ninserts = 0 then
            "inserts"
          else
            assert false
        in
        Xprint.verbose true "no %s found. glueing disabled." s;
      end;
      options#set_no_glue_flag
    end;
*)
    let sync_edits ?(check_conflicts=false) = sync_edits options ~check_conflicts cenv edits in

    if not simple then begin
      begin
        match lang#elaborate_edits with
        | Some f ->

            [%debug_log "nmapping:\n%s\n" nmapping#to_string];
            (*[%debug_log "nmapping (gindex):\n%s\n" nmapping#to_string_gid];*)

            f options cenv nmapping edits;
(*
  [%debug_log "[1] edits: del:%d ins:%d rel:%d"
  edits#get_ndeletes edits#get_ninserts edits#get_nrelabels];
 *)
            [%debug_log "nmapping:\n%s\n" nmapping#to_string];

            let removed_pairs, added_pairs = cenv#elaborate_nmapping nmapping in

            nmapping#add_starting_pairs_for_glueing added_pairs;

            sync_edits removed_pairs added_pairs;
(*
  [%debug_log "[2] edits: del:%d ins:%d rel:%d"
  edits#get_ndeletes edits#get_ninserts edits#get_nrelabels];
 *)
if not options#no_glue_flag then begin
            [%debug_log "@"];
            (*let prev_use_mapping_comparison_cache = cenv#use_mapping_comparison_cache in
            if prev_use_mapping_comparison_cache then
              cenv#clear_use_mapping_comparison_cache;*)
            let removed_pairs, added_pairs, (*conflicted_pairs*)_ =
              glue_deletes_and_inserts options cenv tree1 tree2
                ~override:true ~no_moves:options#no_moves_flag ~use_binding_info:true
                ~ignore_common:true
                ~edits_opt:(Some edits)
                nmapping (new Node_mapping.c cenv)
            in
            sync_edits ~check_conflicts:true removed_pairs added_pairs;
            (*if prev_use_mapping_comparison_cache then
              cenv#set_use_mapping_comparison_cache*)
end;
(*
  [%debug_log "[3] edits: del:%d ins:%d rel:%d"
  edits#get_ndeletes edits#get_ninserts edits#get_nrelabels];
 *)
        | None -> ()
      end;

      let removed_pairs, added_pairs =
        cenv#elaborate_nmapping ~multi:true ~multi_node:true nmapping
      in
      nmapping#set_starting_pairs_for_glueing added_pairs;

      sync_edits removed_pairs added_pairs;

if not options#no_glue_flag then begin
      [%debug_log "@"];
      let use_binding_info = lang#elaborate_edits <> None in
      let removed_pairs, added_pairs, (*conflicted_pairs*)_ =
        glue_deletes_and_inserts options cenv tree1 tree2
          ~no_moves:options#no_moves_flag
          ~use_binding_info(* ~rely_on_binding_info:use_binding_info*)
          ~edits_opt:(Some edits)
          nmapping (new Node_mapping.c cenv)
      in
      sync_edits removed_pairs added_pairs;

end;

      if options#rename_rectification_level >= 2 then begin
        Edit.rectify_renames_d options cenv nmapping edits
      end

    end;

    generate_moves options cenv pruned edits nmapping cenv#subtree_matches
  (* end of func generate_edits *)



  let postprocess
      options
      (cenv : (node_t, tree_t) Comparison.c)
      (*tree1*)_
      (*tree2*)_
      (nmapping : node_t Node_mapping.c)
      pruned
      ref_nmapping
      =
    let tree1 = cenv#tree1 in
    let tree2 = cenv#tree2 in

    let aborted1, aborted2 = pruned#aborted1, pruned#aborted2 in
    let para_iso1, para_iso2 = pruned#para_iso1, pruned#para_iso2 in

    (* recover pruned nodes other than settled isos
     * and expands all collapsed nodes
     *)

    let filter_para_iso tree aborted para_iso =

      [%debug_log "size of para_iso: %d"
        (List.length para_iso)];

      List.filter
        (fun nd ->
          let lm = tree#initial_leftmost nd in
          let contain_aborted =
            List.exists
              (fun n ->
                let ngi = n#gindex in
                lm#gindex <= ngi && ngi <= nd#gindex
              ) aborted
          in

          if contain_aborted then
            [%debug_log "(%a): contains aborted subtree" nups nd];

          contain_aborted
        ) para_iso
    in (* end of func filter_para_iso *)

    let expand_substances para_iso =
      List.concat_map
        (fun nd ->
          if nd#in_path then begin
            let s = nd#get_substances in
            [%debug_log "in_path: %a -> [%s]"
              nups nd
              (Xlist.to_string (fun nd -> UID.to_string nd#uid) ";" s)];
            s
          end
          else [nd]
        ) para_iso
    in

    let para_iso1 =
      expand_substances
        (filter_para_iso tree1 aborted1 para_iso1)
    in
    let para_iso2 =
      expand_substances
        (filter_para_iso tree2 aborted2 para_iso2)
    in

    begin %debug_block
      [%debug_log "para_iso1: [%s]"
        (Xlist.to_string (fun nd -> UID.to_string nd#uid) ";" para_iso1)];
      [%debug_log "aborted1: [%s]"
        (Xlist.to_string (fun nd -> UID.to_string nd#uid) ";" aborted1)];
      [%debug_log "para_iso2: [%s]"
        (Xlist.to_string (fun nd -> UID.to_string nd#uid) ";" para_iso2)];
      [%debug_log "aborted2: [%s]"
        (Xlist.to_string (fun nd -> UID.to_string nd#uid) ";" aborted2)];
    end;

    let filt1 nd = List.memq nd aborted1 || List.memq nd para_iso1 in
    let filt2 nd = List.memq nd aborted2 || List.memq nd para_iso2 in
    tree1#recover_filtered filt1;
    tree2#recover_filtered filt2;

    let (* is_expanded1a *) _ = (tree1#expand_all : node_t -> bool) in
    let (* is_expanded2a *) _ = (tree2#expand_all : node_t -> bool) in

    begin %debug_block
      [%debug_log "* BEFORE POSTPROCESSING(EE,RE,GLUE) *\n"];
      [%debug_log "nmapping:\n%s\n" nmapping#to_string];
      [%debug_log "T1:\n%s\n" tree1#to_string];
      [%debug_log "T2:\n%s\n" tree2#to_string];
    end;


    (*
     * eliminate enclaves
     *)
    if not options#no_enclave_elim_flag then begin
      Xprint.verbose options#verbose_flag "  eliminating enclaves...";

      let _ = cenv#elaborate_nmapping nmapping in

(*      check_toplevel tree1 tree2 nmapping; *)

      [%debug_log "nmapping:\n%s" nmapping#to_string];
      (*[%debug_log "nmapping (gindex):\n%s" nmapping#to_string_gid]*);


      let keyroots_large, keyroots_moderate =
        find_keyroots options tree1 tree2 nmapping
      in
      let keyroots =
        List.fast_sort (fun (n1, _) (n2, _) -> Stdlib.compare n2#gindex n1#gindex)
          (if options#lower_ee_flag then
            keyroots_moderate
          else
            keyroots_large)
      in

      begin %debug_block
        List.iter
          (fun (n1, n2) ->
            [%debug_log "keyroot pair: %a(size=%d) - %a(size=%d)"
              nups n1 (tree1#whole_initial_subtree_size n1)
              nups n2 (tree2#whole_initial_subtree_size n2)]
          ) keyroots;
      end;

      eliminate_enclaves options cenv keyroots tree1 tree2 nmapping ref_nmapping;

      Xprint.verbose options#verbose_flag "  enclaves eliminated."

    end;

    let (* is_expanded1b *) _ = (tree1#recover_and_expand : node_t -> bool) in
    let (* is_expanded2b *) _ = (tree2#recover_and_expand : node_t -> bool) in

(*
    let is_expanded1 nd = is_expanded1a nd || is_expanded1b nd in
    let is_expanded2 nd = is_expanded2a nd || is_expanded2b nd in
*)

    (*
     * eliminate odd relabels
     *)
    if not options#no_odd_relabel_elim_flag then begin
      Xprint.verbose options#verbose_flag "  eliminating odd relabels...";
      eliminate_odd_relabels tree1 tree2 nmapping;
      Xprint.verbose options#verbose_flag "  odd relabels eliminated."
    end;

    begin %debug_block
      [%debug_log "* BEFORE GLUEING *"];
      [%debug_log "nmapping:\n%s\n" nmapping#to_string];
      (*[%debug_log "nmapping (gindex):%s" nmapping#to_string_gid];*)
      [%debug_log "T1:\n%s" tree1#to_string];
      [%debug_log "\nT2:\n%s" tree2#to_string];
    end;

    let _ = cenv#elaborate_nmapping(* ~multi:true ~multi_node:true*) nmapping in

(*
      [%debug_log "nmapping (gindex):\n%s" (nmapping#to_string_gid tree1 tree2)];
*)

    (*
     * glue deleted nodes and inserted nodes
     *)
    if not options#no_glue_flag then begin
      [%debug_log "@"];
      let _, added_pairs, conflicted_pairs =
        glue_deletes_and_inserts
          ~first:true ~record_conflicted_pairs:true ~ignore_common:true
          options cenv tree1 tree2 nmapping ref_nmapping
      in
      [%debug_log "|conflicted_pairs|=%d" (Xset.length conflicted_pairs)];
      let starting_pairs =
        List.iter (Xset.add conflicted_pairs) added_pairs;
        Xset.to_list conflicted_pairs
      in

      let starting_pairs = sort_node_pairs starting_pairs in

      nmapping#add_starting_pairs_for_glueing starting_pairs;
    end
  (* end of func postprocess *)


  type edtag = Edel | Eins | Erel | Emov
  let edtag_to_string = function
    | Edel -> "del" | Eins -> "ins" | Erel -> "rel" | Emov -> "mov"


  let eliminate_odd_relabels options tree1 tree2 edits nmapping =
    [%debug_log "ELIMINATING ODD RELABELS AGAIN..."];

    let permutation_pairs =
      let l = ref [] in
      edits#iter_moves
        (function
          | Edit.Move(_, kind, (info1, _), (info2, _)) ->
              if !kind = Edit.Mpermutation then
                let nd1 = Info.get_node info1 in
                let nd2 = Info.get_node info2 in
                l := (nd1, nd2)::!l

          | _ -> assert false
        );
      !l
    in

    let get_crossing_pairs (nd1, nd2) =
      List.filter
        (fun (n1, n2) ->
(*        n1#data#eq n2#data && *)
          (nd1#gindex - n1#gindex) * (nd2#gindex - n2#gindex) < 0
        ) permutation_pairs
    in

    let odd_pairs = ref [] in
    let add_odd (n1, n2) =
      odd_pairs := (n1, n2) :: !odd_pairs
    in

    edits#iter_relabels
      (function
        | Edit.Relabel(_, (info1, _), (info2, _)) -> begin
            let n1 = Info.get_node info1 in
            let n2 = Info.get_node info2 in

            [%debug_log "checking %a-%a" nups n1 nups n2];

            if (nmapping#is_locked_node n1 && nmapping#is_locked_node n2) then
              [%debug_log " -> locked"]

            else
              try
                match edits#find_mov12 n1 n2 with
                | Edit.Move(_, kind, _, _) ->

                    let permu_cond =
                      if !kind = Edit.Mpermutation then
                        let crossing_pairs = get_crossing_pairs (n1, n2) in
(*
                          [%debug_log "crossing_pairs: [%s]"
                            (String.concat ";"
                               (List.map
                                  (fun (_n1, _n2) ->
                                    sprintf "<%a-%a>" nups _n1 nups _n2) crossing_pairs))];
*)

                        let lconv l = (Obj.obj l : Label.t) in
                        let alab1 = n1#data#_anonymized_label in
                        let alab2 = n2#data#_anonymized_label in
                        let alabp = lconv alab1, lconv alab2 in
                        (List.exists
                           (fun (_n1, _n2) -> not (_n1#data#eq _n2#data))
                           crossing_pairs
                        ) &&
                        ((* alab1 <> alab2 *) not (Label.relabel_allowed alabp) ||
                        List.exists
                          (fun (_n1, _n2) ->
                            _n1#data#_anonymized_label = alab1 || _n2#data#_anonymized_label = alab2)
                          crossing_pairs)
                      else
                        false
                    in
                    [%debug_log "permu_cond:%B" permu_cond];

                    if
                      permu_cond &&
                      (*not (check_relabel options tree1 tree2 n1 n2 nmapping)*)
                      is_odd_relabel ~exact:true tree1 tree2 nmapping n1 n2
                    then begin

                      [%debug_log "odd relabel: %a-%a" nups n1 nups n2];

                      add_odd (n1, n2)
                    end

                | _ -> assert false
              with
                Not_found -> ()

        end
        | _ -> assert false
      );

    let odd_pairs_tbl = Hashtbl.create 0 in
    List.iter
      (fun n1_n2 -> Hashtbl.add odd_pairs_tbl n1_n2 true)
      !odd_pairs;

    let odd_move_tbl = Hashtbl.create 0 in
    edits#filter
      (function
        | Edit.Relabel(_, (i1, _), (i2, _)) -> begin
            let n1 = Info.get_node i1 in
            let n2 = Info.get_node i2 in
            not (Hashtbl.mem odd_pairs_tbl (n1, n2))
        end
        | Edit.Move(mid, _, (i1, _), (i2, _)) -> begin
            let n1 = Info.get_node i1 in
            let n2 = Info.get_node i2 in
            let is_odd = Hashtbl.mem odd_pairs_tbl (n1, n2) in
            if is_odd then begin
              try
                let n1', n2' = Hashtbl.find odd_move_tbl !mid in
                if n1' != n1 || n2' != n2 then
                  raise Not_found
              with
                Not_found ->
                  Hashtbl.add odd_move_tbl !mid (n1, n2);
                  [%debug_log "odd move: %a %a-%a" MID.ps !mid nups n1 nups n2]
            end;
            not is_odd
        end

        | _ -> true
      );

    let mid_conv_tbl = Hashtbl.create 0 in
    let mid_gen() = options#moveid_generator#gen in
    let is_odd_mid m = Hashtbl.mem odd_move_tbl m in
    edits#iter_moves_topdown
      (function
        | Edit.Move(mid, _, (i1, _), (i2, _)) when is_odd_mid !mid -> begin
            [%debug_log "checking %a" MID.ps !mid];
            let orig_mid = !mid in
            try
              List.iter
                (fun (on1, on2) ->
                  let n1 = Info.get_node i1 in
                  let n2 = Info.get_node i2 in
                  if tree1#is_initial_ancestor on1 n1 && tree2#is_initial_ancestor on2 n2 then begin
                    let cands =
                      try Hashtbl.find mid_conv_tbl !mid with _ -> []
                    in
                    List.iter
                      (fun (mid', x1, x2) ->
                        if
                          tree1#is_initial_ancestor x1 n1 && tree2#is_initial_ancestor x2 n2
                        then begin
                          [%debug_log "%a-%a: %a -> %a" nups n1 nups n2 MID.ps !mid MID.ps mid'];
                          mid := mid'
                        end
                      ) cands;
                    if !mid = orig_mid then begin
                      let mid' = mid_gen() in
                      begin
                        try
                          Hashtbl.replace mid_conv_tbl
                            orig_mid ((mid', n1, n2)::(Hashtbl.find mid_conv_tbl orig_mid))
                        with
                          Not_found -> Hashtbl.add mid_conv_tbl orig_mid [(mid', n1, n2)]
                      end;
                      [%debug_log "%a-%a: %a -> %a" nups n1 nups n2 MID.ps !mid MID.ps mid'];
                      mid := mid'
                    end
                  end
                ) (Hashtbl.find_all odd_move_tbl !mid)
            with
              Not_found -> ()
        end
        | _ -> ()
      );

    List.iter
      (fun (nd1, nd2) ->
        edits#add_edit (Edit.make_delete nd1);
        edits#add_edit (Edit.make_insert nd2)
      ) !odd_pairs;

    nmapping#filter
      (fun n1 n2 ->
        not (Hashtbl.mem odd_pairs_tbl (n1, n2))
      );

    [%debug_log "* ODD RELABELS ELIMINATED *\n"];

    odd_move_tbl
  (* end of func eliminate_odd_relabels *)


  class mid_data (mid : Editop.move_id) (w : float) (nd : Spec.node_t) = object
    inherit Otree.data
    val mutable weight = w
    method mid = mid
    method node = nd
    method weight = weight
    method set_weight w = weight <- w

    method equals mdat = mid = mdat#mid
    method to_rep = MID.to_raw mid
    method to_string = sprintf "%a(%f)" MID.ps mid weight
    method to_elem_data = "", [], ""
  end



  (* handle movrels *)
  let handle_movrels
      options cenv
      tree1 tree2
      edits
      nmapping
      parent_move_tbl
      child_move_tbl
      =
    begin %debug_block
      Hashtbl.iter
        (fun m ms ->
          [%debug_log "child_move_tbl: %a -> [%s]" MID.ps m (Xlist.to_string MID.to_string ";" ms)]
        ) child_move_tbl;
    end;

    [%debug_log "EDITS BEFORE handle_movrels:\n%s" edits#to_string_gid];
    [%debug_log "nmapping:\n%s" nmapping#to_string];
    (*[%debug_log "nmapping (gindex):\n%s" nmapping#to_string_gid];*)

    [%debug_log "handling movrels..."];


    let suggested_pairs = Xset.create 0 in

    (*!20240205!let check n1 n2 =
      let b =
        not
          (try
            let n1' = nmapping#find n1 in
            n1' == n2 || nmapping#is_final_mapping n1 n1'
          with _ -> false) &&
        not
          (try
            let n2' = nmapping#inv_find n2 in
            n2' == n1 || nmapping#is_final_mapping n2' n2
          with _ -> false)
      in
      [%debug_log "%a-%a -> %B" nups n1 nups n2 b];
      b
    in*)

    if options#no_movrels_flag then begin (* eliminate ALL movrels *)
      [%debug_log "removing ALL movrels..."];
      edits#iter_moves
        (function
          | Edit.Move(_, _, (info1, ex1), (info2, ex2)) as mov -> begin
              try
                let nd1 = Info.get_node info1 in
                let nd2 = Info.get_node info2 in
                match edits#find_rel12 nd1 nd2 with
                | Edit.Relabel _ as rel ->
                    let _ = nmapping#remove nd1 nd2 in
                    edits#remove_edit mov;
                    edits#remove_edit rel;
                    edits#add_edit (Edit.Delete(false, info1, ex1));
                    edits#add_edit (Edit.Insert(false, info2, ex2));
                    cenv#add_bad_pair nd1 nd2
                | _ -> assert false
              with
                Not_found -> ()
          end
          | _ -> assert false
        )
    end
    else begin
      let count_mapped tree mem nd =
        let c = ref 0 in
        tree#fast_scan_whole_initial_subtree nd
          (fun n -> if mem n then incr c);
        !c
      in
      let mtbl = Hashtbl.create 0 in (* mid -> (top node * top node) set *)
      edits#iter_moves
        (function
          | Edit.Move(mid, _, (info1, _), (info2, _)) -> begin
              let nd1 = Info.get_node info1 in
              let nd2 = Info.get_node info2 in
              try
                let _top_pairs = Hashtbl.find mtbl !mid in
                let anc_flag = ref false in
                Xset.iter
                  (function (n1, n2) as p ->
                    if
                      tree1#is_initial_ancestor nd1 n1 &&
                      tree2#is_initial_ancestor nd2 n2
                    then begin
                      anc_flag := true;
                      Xset.remove _top_pairs p
                    end
                    else if
                      tree1#is_initial_ancestor n1 nd1 &&
                      tree2#is_initial_ancestor n2 nd2
                    then begin
                      ()
                    end
                    else
                      anc_flag := true
                  ) _top_pairs;

                if !anc_flag then
                  Xset.add _top_pairs (nd1, nd2);

              with
                Not_found ->
                  let s = Xset.create 0 in
                  Xset.add s (nd1, nd2);
                  Hashtbl.add mtbl !mid s
          end
          | _ -> assert false
        );

      begin %debug_block
        [%debug_log "mtbl:"];
        let l = ref [] in
        Hashtbl.iter
          (fun mid s ->
            Xset.iter
              (fun (n1, n2) ->
                l := (mid, n1, n2) :: !l
              ) s
          ) mtbl;
        List.iter
          (fun (mid, n1, n2) ->
            [%debug_log "%a: %a-%a (%a-%a)" MID.ps mid ngps n1 ngps n2 nups n1 nups n2]
          )
          (List.fast_sort
             (fun (_, n1, _) (_, n2, _) ->
               Stdlib.compare n1#gindex n2#gindex)
             !l);
      end;

(* !!!
      let is_possible_rename node1 node2 bid1 bid2 =
        let parent_cond =
          try
            let pnd1 = node1#initial_parent in
            let pnd2 = node2#initial_parent in

            let mcond =
              try
                nmapping#find pnd1 == pnd2
              with
                Not_found -> false
            in

            let pbi1_opt = Edit.get_bid_opt pnd1 in
            let pbi2_opt = Edit.get_bid_opt pnd2 in
            match pbi1_opt, pbi2_opt with
            | Some pbi1, Some pbi2 -> mcond && bid1 = pbi1 && bid2 = pbi2
            | Some _, None | None, Some _ -> false
            | None, None -> mcond
          with
            Otree.Parent_not_found _ -> true
        in
        [%debug_log "%a-%a (%a-%a): parent_cond -> %B"
          nups node1 nups node2 Binding.ID.ps bid1 Binding.ID.ps bid2 parent_cond];

        parent_cond && node1#data#relabel_allowed node2#data
      in
      let _ = Edit.collect_use_renames edits is_possible_rename in
*)

      let stbl = Hashtbl.create 0 in (* mid -> (stability * movrel ratio * nmoved * nmapped1 * nmapped2) *)

      let bad_value = (0.0, 0.0, 0, 0, 0) in
      let set_to_bad mid =
        Hashtbl.add stbl mid bad_value
      in
      let is_bad_mid mid =
        try
          Hashtbl.find stbl mid = bad_value
        with
          Not_found -> false
      in

      Hashtbl.iter
        (fun mid s ->
          [%debug_log "mid=%a" MID.ps mid];
          Xset.iter
            (fun (nd1, nd2) ->
              let is_bad =
                try
                  let pnd1 = nd1#initial_parent in
                  let pnd2 = nd2#initial_parent in

                  if pnd1#data#is_sequence && pnd2#data#is_sequence then
                    false
                  else
                    let pnd1' = nmapping#find pnd1 in

                    if pnd1' == pnd2 then
                      false
                    else begin
                      match edits#find12 pnd1 pnd1' with
                      | [] -> true
                      | _ -> begin
                          let pnd2' = nmapping#inv_find pnd2 in
                          if pnd2' == pnd1 then
                            false
                          else
                            match edits#find12 pnd2' pnd2 with
                            | [] -> true
                            | _ -> false
                      end
                    end
                with
                | Otree.Parent_not_found _
                | Not_found -> false
              in
              if is_bad then begin
                [%debug_log "%a --> BAD" MID.ps mid];
                set_to_bad mid
              end
            ) s
        ) mtbl;


      (* !!! *)
      edits#iter_moves_bottomup
        (function
          | Edit.Move(mid, _, (info1, _), (info2, _)) -> begin
              if not (is_bad_mid !mid) then
                try
                  let nd1 = Info.get_node info1 in
                  let nd2 = Info.get_node info2 in
                  let _ = edits#find_rel12 nd1 nd2 in
                  let bid1 = Edit.get_bid nd1 in
                  let bid2 = Edit.get_bid nd2 in
                  [%debug_log "%a -> %a" BID.ps bid1 BID.ps bid2];
                  let _use1 = cenv#get_use1 bid1 in
                  let _use2 = cenv#get_use2 bid2 in
                  let alab1 = nd1#data#_anonymized2_label in
                  let alab2 = nd2#data#_anonymized2_label in
                  let filt alab nd n =
                    n#data#_anonymized2_label = alab && n != nd
                  in
                  let use1 = List.filter (filt alab1 nd1) _use1 in
                  let use2 = List.filter (filt alab2 nd2) _use2 in

                  begin %debug_block
                    let nl_to_s = Xlist.to_string (fun n -> UID.to_string n#uid) ";" in
                    [%debug_log "use1=[%s]" (nl_to_s use1)];
                    [%debug_log "use2=[%s]" (nl_to_s use2)];
                  end;

                  let is_mov1 =
                    edits#is_crossing_with_untouched
                      ?full_scan:None ?mask:None ?incompatible_only:None ?weak:None
                      nmapping
                  in
                  let is_mov2 n1 n2 = is_mov1 n2 n1 in

                  let find is_mov nd use =
                    let rec doit = function
                      | [] -> raise Not_found
                      | n::rest ->
                          if is_mov nd n then
                            doit rest
                          else
                            n
                    in
                    doit use
                  in
                  let is_bad1 =
                    try
                      let nd1' = find is_mov1 nd1 use2 in
                      [%debug_log "non move pair found: %a-%a" nups nd1 nups nd1'];
                      (*!20240205!if check nd1 nd1' then*)
                        Xset.add suggested_pairs (nd1, nd1');
                      try
                        let nd1'' = nmapping#inv_find nd1' in
                        let b = edits#mem_mov12 nd1'' nd1' in
                        if b then begin
                          let m = edits#find_mid12 nd1'' nd1' in
                          if not (is_bad_mid m) then begin
                            [%debug_log "%a --> BAD" MID.ps m];
                            set_to_bad m
                          end
                        end;
                        begin %debug_block
                          let k = if b then "movrel:" else "relabel:" in
                          [%debug_log "conflicts with %s%a-%a" k nups nd1'' nups nd1'];
                        end;
                        b
                      with
                        Not_found -> false
                    with
                      Not_found -> false
                  in
                  let is_bad2 =
                    try
                      let nd2' = find is_mov2 nd2 use1 in
                      [%debug_log "non move pair found: %a-%a" nups nd2' nups nd2];
                      (*!20240205!if check nd2' nd2 then*)
                        Xset.add suggested_pairs (nd2', nd2);
                      try
                        let nd2'' = nmapping#find nd2' in
                        let b = edits#mem_mov12 nd2' nd2'' in
                        if b then begin
                          let m = edits#find_mid12 nd2' nd2'' in
                          if not (is_bad_mid m) then begin
                            [%debug_log "%a --> BAD" MID.ps m];
                            set_to_bad m
                          end
                        end;
                        begin %debug_block
                          let k = if b then "movrel:" else "relabel:" in
                          [%debug_log "conflicts with %s%a-%a" k nups nd2' nups nd2''];
                        end;
                        b
                      with
                        Not_found -> false
                    with
                      Not_found -> false
                  in
                  if is_bad1 || is_bad2 then begin
                    [%debug_log "%a --> BAD" MID.ps !mid];
                    set_to_bad !mid
                  end

                with
                  Not_found -> ()
          end
          | _ -> assert false
        );


      edits#iter_moves_bottomup
        (function
          | Edit.Move(mid, kind, (info1, ex1), (info2, ex2)) as mov -> begin
(*
              let same_kind = nd1#data#_anonymized_label = nd2#data#_anonymized_label in
*)
              [%debug_log "checking: %s" (Editop.to_string mov)];

              try
                let nd1 = Info.get_node info1 in
                let nd2 = Info.get_node info2 in

                if (nmapping#is_locked_node nd1) && (nmapping#is_locked_node nd2) then begin
                  [%debug_log "locked mapping: %a-%a" nups nd1 nups nd2];

                  if is_bad_mid !mid then begin
                    [%debug_log "bad mid: %a" MID.ps !mid];
                    nmapping#unlock_node nd1;
                    nmapping#unlock_node nd2
                  end
                  else
                    raise Not_found
                end;

                let rel = edits#find_rel12 nd1 nd2 in

                let stability, ratio, nmoved, (*nmapped1*)_, (*nmapped2*)_ =
                  (*try
                    Hashtbl.find stbl !mid
                  with
                    Not_found ->*)
                      let parent_moves =
                        try
                          let (pm, _, _) = Hashtbl.find parent_move_tbl !mid in
                          [pm]
                        with
                          Not_found -> []
                      in
                      let sibling_moves =
                        List.fold_left
                          (fun l pm ->
                            try
                              let cms = Hashtbl.find child_move_tbl pm in
                              Xlist.union l (Xlist.subtract cms [!mid])
                            with
                              Not_found -> l
                          ) [] parent_moves
                      in
                      let child_moves =
                        try
                          Hashtbl.find child_move_tbl !mid
                        with
                          Not_found -> []
                      in

                      begin %debug_block
                        [%debug_log "parent moves of %a --> [%s]" MID.ps !mid
                          (Xlist.to_string MID.to_string ";" parent_moves)];
                        [%debug_log "sibling moves of %a --> [%s]" MID.ps !mid
                          (Xlist.to_string MID.to_string ";" sibling_moves)];
                        [%debug_log "child moves of %a --> [%s]" MID.ps !mid
                          (Xlist.to_string MID.to_string ";" child_moves)];
                      end;

                      let strip s =
                        Xstring.strip  ~strs:["\""] s
                      in
                      let get_lcss_len str1 str2 = (* length of longest common sub-string *)
                        let s1 = strip str1 in
                        let s2 = strip str2 in
                        let m, _, _, _ =
                          Adiff.adiff (Xstring.to_char_array s1) (Xstring.to_char_array s2)
                        in
                        let len = List.length m in
                        [%debug_log "\"%s\"(%d) vs \"%s\"(%d) -> %d"
                          s1 (String.length s1) s2 (String.length s2) len];
                        len
                      in
                      let is_string n = Label.is_string_literal (getlab n) in
                      let get_value n = Label.get_value (getlab n) in

                      let surrounding_moves = parent_moves @ sibling_moves @ child_moves in

                      let stable =
                        if surrounding_moves = [] then
                          (try
                            let p1 = nd1#initial_parent in
                            let p2 = nd2#initial_parent in
                            (nmapping#find p1 == p2) &&
                            (not (edits#mem_mov12 p1 p2) && !kind <> Edit.Mpermutation(* ||
                            try edits#find_mid12 p1 p2 = !mid with _ -> false*))
                          with
                            _ -> false)
                        ||
                          let is_stable1 n =
                            match edits#find1 n with
                            | [] | [Edit.Relabel _] -> true
                            | _ -> false
                          in
                          let is_stable2 n =
                            match edits#find2 n with
                            | [] | [Edit.Relabel _] -> true
                            | _ -> false
                          in
                          try
                            let an1 = get_p_ancestor is_stable1 nd1 in
                            let an2 = get_p_ancestor is_stable2 nd2 in
                            [%debug_log "an1=%a" nps an1];
                            [%debug_log "an2=%a" nps an2];
                            nmapping#find an1 == an2
                          with
                            _ -> false
                        else
                          false
                      in

                      if stable then begin
                        [%debug_log "stable relabel"];
                        1.0, 1.0, 1, 2, 2
                      end
                      else begin
                        let t0 = ref 0 in
                        let c, t =
                          List.fold_left
                            (fun (c, t) m ->

                              let c'_ex = ref 0 in
                              let c' =
                                edits#get_nmoves_of_move_id_filt
                                  (fun n1 n2 ->
                                    if is_string n1 && is_string n2 then begin
                                      c'_ex := !c'_ex + 2 * (get_lcss_len (get_value n1) (get_value n2));
                                      false
                                    end
                                    else
                                      n1#data#eq n2#data
                                  ) m
                              in

                              let t'_ex = ref 0 in
                              let t' =
                                edits#get_nmoves_of_move_id_filt
                                  (fun n1 n2 ->
                                    incr t0;
                                    if is_string n1 && is_string n2 then begin
                                      t'_ex := !t'_ex + (String.length (get_value n1)) + (String.length (get_value n2));
                                      false
                                    end
                                    else
                                      true
                                  ) m
                              in
                              (c + c' + !c'_ex, t + t' + !t'_ex)
                            ) (0, 0) (!mid :: surrounding_moves)
                        in

                        let stability = (float c) /. (float t) in
                        let n_mapped1, n_mapped2 =
                          try
                            let topl = Xset.to_list (Hashtbl.find mtbl !mid) in

                            [%debug_log "top nodes of %a %a-%a: %s" MID.ps !mid nups nd1 nups nd2
                              (Xlist.to_string (fun (n1, n2) -> sprintf "(%a,%a)" nups n1 nups n2) ";" topl)];

                            List.fold_left
                              (fun (c1, c2) (n1, n2) ->
                                let c1' = count_mapped tree1 nmapping#mem_dom n1 in
                                let c2' = count_mapped tree2 nmapping#mem_cod n2 in
                                c1 + c1', c2 + c2'
                              ) (0, 0) topl
                          with
                            Not_found -> assert false
                        in

                        let ratio = (float (!t0 * 2)) /. (float (n_mapped1 + n_mapped2)) in

                        [%debug_log "stability: (num of exact matches)/(num of moved): %a --> %d/%d=%f"
                          MID.ps !mid c t stability];
                        [%debug_log "num of mapped nodes: %d - %d" n_mapped1 n_mapped2];
                        [%debug_log "movrel ratio: (num of moved)/(num of mapped): %f/%f=%f"
                          (float (!t0 * 2)) (float (n_mapped1 + n_mapped2)) ratio];

                        Hashtbl.add stbl !mid (stability, ratio, t, n_mapped1, n_mapped2);
                        stability, ratio, t, n_mapped1, n_mapped2
                      end
                in (* end of let stability, ratio, nmoved, nmapped1, nmapped2 *)

                let bad_movrel =
                  not (nmapping#is_final_mapping nd1 nd2) &&
                  (try nd1#data#get_orig_name <> nd2#data#get_orig_name with _ -> true) &&
                  stability <= options#movrel_stability_threshold &&
                  (
                   ratio <= options#movrel_ratio_threshold ||
                   nmoved = 1(* || nmapped1 = 1 || nmapped2 = 1 *)
                  ) &&
                  not (cenv#has_use_rename nd1 nd2 || cenv#child_has_use_rename nd1 nd2)
                in

                [%debug_log "stability:%f <= %f --> %B" stability options#movrel_stability_threshold
                  (stability <= options#movrel_stability_threshold)];
                [%debug_log "ratio:%f <= %f --> %B"
                  ratio options#movrel_ratio_threshold (ratio <= options#movrel_ratio_threshold)];
                [%debug_log "nmoved:%d = 1 --> %B" nmoved (nmoved=1)];

                if bad_movrel then begin

                  [%debug_log "removing unstable movrel: %s" (Editop.to_string rel)];

                  let _ = nmapping#remove nd1 nd2 in
                  edits#remove_edit mov;
                  edits#remove_edit rel;
                  edits#add_edit (Edit.Delete(false, info1, ex1));
                  edits#add_edit (Edit.Insert(false, info2, ex2));
                  cenv#add_bad_pair nd1 nd2
                end

              with
                Not_found -> ()
          end
          | _ -> assert false
        )
    end;
    [%debug_log "movrel handling finished"];
    suggested_pairs
  (* end of handle_movrels *)

  let get_subtree_similarity tree1 tree2 nmap nd1 nd2 =
    let sz1 = tree1#whole_initial_subtree_size nd1 in
    let sz2 = tree2#whole_initial_subtree_size nd2 in
    let mapped_node_count = ref 0 in
    tree1#scan_whole_initial_subtree nd1
      (fun n1 ->
        try
          let n2 = nmap n1 in
          if tree2#initial_subtree_mem nd2 n2 && n1#data#equals n2#data then
            incr mapped_node_count
        with
          Not_found -> ()
      );
    let sim = 2.0 *. (float !mapped_node_count) /. (float (sz1 + sz2)) in
    (*[%debug_log "%a-%a -> %f" nps nd1 nps nd2 sim];*)
    sim

  let find_nearest_anc_stmt = Sourcecode.find_nearest_p_ancestor_node (fun n -> n#data#is_statement)

  type upairs_kind =
    | LocalVariableInliningOrExtraction
    | StableContext

  (* eliminate small move of unnamed entities *)
  let decompose_moves cenv tree1 tree2
      ?(force=false)
      ?(weak=false)
      ?(thresh=0.1)
      is_xxx_pair (*options*)_ edits nmapping size_limit =
    ignore thresh;

    [%debug_log "weak=%B size_limit=%d" weak size_limit];

    let is_map = _is_map tree1 tree2 nmapping in
    let is_stable_map n1 n2 =
      let b =
        (try nmapping#find n1 == n2 with _ -> false) &&
        not (edits#mem_mov12 n1 n2)
      in
      [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
      b
    in
    let is_stable1 n =
      match edits#find1 n with
      | []
      | [Edit.Relabel _] -> true
      | _ -> false
    in
    let is_stable2 n =
      match edits#find2 n with
      | []
      | [Edit.Relabel _] -> true
      | _ -> false
    in
    let is_mov1 n =
      let b = edits#mem_mov1 n in
      [%debug_log "%a -> %B" nps n b];
      b
    in
    let is_mov2 n =
      let b = edits#mem_mov2 n in
      [%debug_log "%a -> %B" nps n b];
      b
    in
    let is_del n =
      let b = edits#mem_del n in
      if b then
        [%debug_log "%a -> %B" nps n b];
      b
    in
    let is_ins n =
      let b = edits#mem_ins n in
      if b then
        [%debug_log "%a -> %B" nps n b];
      b
    in
    let node_eq n1 n2 = n1#data#eq n2#data in

    let has_same_digest n1 n2 =
      let b =
      match n1#data#_digest with
      | Some d1 -> begin
          match n2#data#_digest with
          | Some d2 -> d2 = d1
          | None -> node_eq n1 n2
      end
      | _ -> false
      in
      [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
      b
    in
    let exists_uniq_match =
      List.exists
        (function
          | Edit.Move(_, _, (info1, _), (info2, _)) -> begin
              let nd1 = Info.get_node info1 in
              let nd2 = Info.get_node info2 in
              cenv#has_uniq_match nd1 nd2
          end
          | _ -> false
        )
    in
    let surrounded_by is_xxx n =
      let check_lr x =
        try
          let ca = x#initial_parent#initial_children in
          let nca = Array.length ca in
          let l = x#initial_pos <= 0 || is_xxx ca.(x#initial_pos - 1) in
          let r = x#initial_pos >= nca - 1 || is_xxx ca.(x#initial_pos + 1) in
          l && r
        with _ -> false
      in
      let b =
        try
          check_lr n && check_lr n#initial_parent && check_lr n#initial_parent#initial_parent
        with _ -> false
      in
      [%debug_log "%a -> %B" nps n b];
      b
    in
    (*let check_parent n1 n2 =
      try
        let p1 = n1#initial_parent in
        let p2 = nmapping#find p1 in
        n2#initial_parent != p2 ||
        match edits#find12 p1 p2 with
        | [] | [Edit.Relabel _] -> false
        | _ -> true
      with
        Not_found ->
          try
            let a1 = get_p_ancestor is_stable1 n1 in
            let a2 = get_p_ancestor is_stable2 n2 in
            [%debug_log "n1=%a, n2=%a: a1=%a, a2=%a"
              nups n1 nups n2 nups a1 nups a2];
            nmapping#find a1 != a2
          with
            Not_found -> true
    in*)
    let sz_tbl = Hashtbl.create 0 in
    edits#iter_moves
      (function
        | Edit.Move(mid, kind, (info1, _), (info2, _)) as mov -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            let gi1 = nd1#gindex in
            let gi2 = nd2#gindex in
            let sz, esz, tsz, k, r1, r2, ml =
              try
                let _sz, _esz, _tsz, _k, _r1, _r2, _ml = (Hashtbl.find sz_tbl !mid) in
                let k, r1, r2 =
                  if gi1 > _r1#gindex && gi2 > _r2#gindex then
                    !kind, nd1, nd2
                  else
                    _k, _r1, _r2
                in
                let sz =
                  if
                    (node_eq nd1 nd2(* ||
                    match nd1#data#orig_lab_opt, nd2#data#orig_lab_opt with
                    | Some o1, Some o2 -> o1 = o2
                    | _ -> false*)
                    ) &&
                    nd1#data#is_named_orig
                  then
                    _sz + 1
                  else
                    _sz
                in
                let esz =
                  if node_eq nd1 nd2 then
                    _esz + 1
                  else
                    _esz
                in
                sz, esz, _tsz+1, k, r1, r2, mov::_ml
              with
                Not_found ->
                  (if
                    (node_eq nd1 nd2(* ||
                    match nd1#data#orig_lab_opt, nd2#data#orig_lab_opt with
                    | Some o1, Some o2 -> o1 = o2
                    | _ -> false*)
                    ) &&
                    nd1#data#is_named_orig
                  then
                    1
                  else
                    0),
                  (if node_eq nd1 nd2 then 1 else 0),
                  1, !kind, nd1, nd2, [mov]
            in
            match ml with
            | [_] when begin
                not r1#data#is_common && not r2#data#is_common &&
                (r1#data#is_named || r1#data#has_non_trivial_value) &&
                (r2#data#is_named || r2#data#has_non_trivial_value) &&
                not
                  (
                   tsz = 1 &&
                   r1#data#is_sequence && r2#data#is_sequence &&
                   r1#data#is_named && r2#data#is_named &&
                   try
                     let pr1 = r1#initial_parent in
                     let pr2 = r2#initial_parent in
                     not (is_map pr1 pr2) &&
                     pr1#data#get_stripped_name = r1#data#get_stripped_name &&
                     pr2#data#get_stripped_name = r2#data#get_stripped_name
                   with _ -> false
                  ) &&
                cenv#multiple_node_matches#is_uniq_match r1 r2
            end -> ()
            | _ -> Hashtbl.replace sz_tbl !mid (sz, esz, tsz, k, r1, r2, ml)
        end
        | _ -> assert false
      );

    let mid_tbl = Hashtbl.create 0 in
    let sz_list =
      let l =
        Hashtbl.fold
          (fun mid ((_, _, _, _, rt1, rt2, _) as x) l ->
            Hashtbl.add mid_tbl rt1 (mid, rt2);
            (mid, x)::l
          ) sz_tbl []
      in
      let cmp (_, (_, _, _, _, n1, _, _)) (_, (_, _, _, _, n2, _, _)) =
        compare n2#gindex n1#gindex
      in
      List.sort cmp l
    in

    let move_density_tbl = Hashtbl.create 0 in
    List.iter
      (fun (mid, (_, _, tsz, _, rt1, rt2, _)) ->
        let _tsz = ref tsz in
        let _st_sz1 = ref 0 in
        tree1#scan_whole_initial_subtree rt1
          (fun n1 ->
            incr _st_sz1;
            try
              let m, n2 = Hashtbl.find mid_tbl n1 in
              if tree2#is_initial_ancestor rt2 n2 then begin
                let _, s, _, _, _, _, _ = Hashtbl.find sz_tbl m in
                _tsz := !_tsz + s
              end
            with _ -> ()
          );
        let st_sz1 = !_st_sz1 in
        let st_sz2 = tree2#whole_initial_subtree_size rt2 in
        let tsz_ = !_tsz in
        let d1 = (float tsz_) /. (float st_sz1) in
        let d2 = (float tsz_) /. (float st_sz2) in
        let d = (float (tsz_*2)) /. (float (st_sz1+st_sz2)) in
        [%debug_log "%a: density = tsz_*2/(st_sz1+st_sz2) = %d*2/(%d+%d) = %f: density1=%f, density2=%f"
          MID.ps mid tsz_ st_sz1 st_sz2 d d1 d2];
        Hashtbl.add move_density_tbl mid (d, d1, d2)
      ) sz_list;
    let _get_move_density m = try Hashtbl.find move_density_tbl m with _ -> 0.0, 0.0, 0.0 in
    let get_move_density m =
      let d, _, _ = _get_move_density m in
      [%debug_log "%a -> %f" MID.ps m d];
      d
    in
    let get_move_density1 m =
      let _, d1, _ = _get_move_density m in
      [%debug_log "%a -> %f" MID.ps m d1];
      d1
    in
    let get_move_density2 m =
      let _, _, d2 = _get_move_density m in
      [%debug_log "%a -> %f" MID.ps m d2];
      d2
    in

    let dels = Xset.create 0 in
    let inss = Xset.create 0 in
    let movs = Xset.create 0 in
    let npairs = Xset.create 0 in

    let boundary_cond n1 n2 =
      let b =
        not n1#data#is_boundary && not n2#data#is_boundary &&
        List.for_all
          (fun n ->
            let children = n#initial_parent#initial_children in
            Array.for_all (fun c -> not c#data#is_boundary) children
          ) [n1; n2]
      in
      [%debug_log "%a-%a: %B" nps n1 nps n2 b];
      b
    in
    let rec iter_desc_moves f n chk =
      let ca = n#initial_children in
      for i = 0 to n#initial_nchildren - 1 do
        let cn = ca.(i) in
        [%debug_log "  %d: cn=%a" i nps cn];
        try
          let cn' = nmapping#find cn in
          [%debug_log "  %a -> %a" nps cn nps cn'];
          if chk cn' then begin
            try
              match edits#find_mov12 cn cn' with
              | Edit.Move(m, _, _, _) -> f !m
              | _ -> raise Not_found
            with
              Not_found -> iter_desc_moves f cn chk
          end
        with _ -> ()
      done
    in
    let sibling_count_thresh = 2 in
    [%debug_log "sibling_count_thresh=%d" sibling_count_thresh];

    let move_density_thresh = 0.5 in
    [%debug_log "move_density_thresh=%f" move_density_thresh];

    let sibling_move_tbl = Hashtbl.create 0 in
    let sibling_cond n1 n2 =
      let count = ref 0 in
      let b =
        try
          let pn1 = n1#initial_parent in
          let pn2 = n2#initial_parent in
          [%debug_log "pn1=%a pn2=%a" nps pn1 nps pn2];
          let moves = Xset.create 0 in
          let ca = pn1#initial_children in
          for i = 0 to pn1#initial_nchildren - 1 do
            let cn = ca.(i) in
            [%debug_log "%d: cn=%a" i nps cn];
            if cn != n1 then
            try
              let cn' = nmapping#find cn in
              [%debug_log "%a -> %a" nps cn nps cn'];
              if cn'#initial_parent == pn2 then begin
                [%debug_log "parent of %a is %a" nps cn' nps pn2];
                try
                  let m =
                    match edits#find_mov12 cn cn' with
                    | Edit.Move(m, _, _, _) -> !m
                    | _ -> raise Not_found
                  in
                  if get_move_density m > move_density_thresh then begin
                    Xset.add moves m;
                    incr count;
                    [%debug_log "count->%d" !count];
                  end
                with _ -> ()
              end
              else
                let ml =
                  let l = ref [] in
                  let f x = l := x :: !l in
                  iter_desc_moves f cn
                    (fun x ->
                      let b = tree2#is_initial_ancestor pn2 x in
                      [%debug_log "  ancestor of %a is %a" nps x nps pn2];
                      b
                    );
                  !l
                in
                if
                  ml <> [] &&
                  List.for_all (fun m -> get_move_density m > move_density_thresh) ml
                then begin
                  List.iter (Xset.add moves) ml;
                  incr count;
                  [%debug_log "count->%d" !count];
                end
            with _ -> ()
          done;
          let b = !count > sibling_count_thresh in
          Hashtbl.add sibling_move_tbl pn1 (if b then moves else Xset.create 0);
          b
        with _ -> false
      in
      [%debug_log "%a-%a: %B (count=%d)" nps n1 nps n2 b !count];
      b
    in
    let get_similarity_score =
      cenv#get_similarity_score ?ignore_cache:(Some true) ?bonus_named:(Some true) ?flat:(Some true)
    in
    let is_region_changing_move mid rt1 rt2 =
      let _ = mid in
      let b =
      not rt1#data#is_boundary && not rt2#data#is_boundary &&
      let get_bn = get_p_ancestor (fun x -> x#data#is_boundary) in
      (try
        let bn1 = get_bn rt1 in
        let bn2 = get_bn rt2 in
        [%debug_log "bn1: %a %s %s" nps bn1 bn1#data#label (Loc.to_string bn1#data#src_loc)];
        [%debug_log "bn2: %a %s %s" nps bn2 bn2#data#label (Loc.to_string bn2#data#src_loc)];
        is_map bn1 bn2
      with
        Not_found -> false)
        &&
      let _ = () in
      (try
        let rt1_is_seq = rt1#data#is_sequence in
        tree1#fast_scan_whole_initial_subtree rt1
          (fun n1 ->
            if is_stable1 n1 && (rt1_is_seq || n1#initial_parent#data#is_sequence) then
              let n2 = nmapping#find n1 in
              if
                (*(try (edits#find_mid12 n1#initial_parent n2#initial_parent) = mid with _ -> false) &&*)
                not (tree2#is_initial_ancestor rt2 n2)
              then begin
                [%debug_log "found: %a->%a" nps n1 nps n2];
                raise Exit
              end
          );
        false
      with
      | Exit -> true
      | _ -> false) ||
        try
          let rt2_is_seq = rt2#data#is_sequence in
          tree2#fast_scan_whole_initial_subtree rt2
            (fun n2 ->
              if is_stable2 n2 && (rt2_is_seq || n2#initial_parent#data#is_sequence) then
                let n1 = nmapping#inv_find n2 in
                if
                  (*(try (edits#find_mid12 n1#initial_parent n2#initial_parent) = mid with _ -> false) &&*)
                  not (tree1#is_initial_ancestor rt1 n1)
                then begin
                  [%debug_log "found: %a<-%a" nps n1 nps n2];
                  raise Exit
                end
            );
          false
        with
        | Exit -> true
        | _ -> false
      in
      [%debug_log "%a %a-%a -> %B" MID.ps mid nps rt1 nps rt2 b];
      b
    in
    let is_staying_move mid rt1 rt2 =
      let b =
        (try is_map rt1#initial_parent rt2#initial_parent with _ -> false) &&
        is_region_changing_move mid rt1 rt2
      in
      [%debug_log "%a %a-%a -> %B" MID.ps mid nps rt1 nps rt2 b];
      b
    in
    (*let iter_siblings n f =
      let ca =
        try
          n#initial_parent#initial_children
        with
          _ -> [||]
      in
      Array.iter
        (fun x ->
          if x != n then
            f x
        ) ca
    in*)
    (*let for_all_siblings n pred =
      try
        iter_siblings n
          (fun x ->
            if not (pred x) then
              raise Exit
          );
        true
      with
        Exit -> false
    in*)
    (*let exists_sibling n pred =
      try
        iter_siblings n
          (fun x ->
            if pred x then
              raise Exit
          );
        false
      with
        Exit -> true
    in*)
    let nmap1 = nmapping#find in
    let nmap2 = nmapping#inv_find in

    let to_be_excluded = Xset.create 0 in

    List.iter
      (fun (mid, (sz, esz, tsz, kind, rt1, rt2, movl)) ->
        [%debug_log "%a: %s %a-%a [%a]-[%a] sz=%d esz=%d tsz=%d %a" MID.ps mid
          (Edit.move_kind_to_string kind) nups rt1 nups rt2 locps rt1 locps rt2
          sz esz tsz labps rt1];

        let boundary_move_flag = rt1#data#is_boundary || rt2#data#is_boundary in
        [%debug_log "boundary_move_flag=%B" boundary_move_flag];

        (*if nmapping#is_locked_mapping rt1 rt2 then begin
          [%debug_log "!!!!!!!! locked mapping: %a-%a" nups rt1 nups rt2];
        end
        else*)

        let is_staying =
          let is_staying_opt = ref None in
          fun () ->
            match !is_staying_opt with
            | Some b -> b
            | None ->
                let b = is_staying_move mid rt1 rt2 in
                is_staying_opt := Some b;
                b
        in
        if
          (*rt1#data#is_boundary && rt2#data#is_boundary &&
          has_p_descendant
            (fun n1 ->
              try
                let n1' = nmap1 n1 in
                is_stable1 n1 && tree2#is_initial_ancestor rt2 n1'
              with _ -> false
            ) rt1
        then begin
          [%debug_log "boundary on stable mappping"];
        end
        else if*)
          not force &&
          (
           rt1#initial_nchildren = 0 && rt2#initial_nchildren = 0 && node_eq rt1 rt2 ||
           rt1#data#subtree_equals rt2#data && tsz > 1
          ) &&
          (cenv#has_uniq_match rt1 rt2)
        then begin
          [%debug_log "unique move"];
          Xset.add movs (mid, rt1, rt2)
        end

        else if
          not force &&
          sz > 0 &&
          not rt1#data#is_boundary && not rt2#data#is_boundary &&
          not rt1#data#is_sequence && not rt2#data#is_sequence &&
          (*rt1#data#is_named_orig && rt2#data#is_named_orig &&*)
          rt1#initial_nchildren > 0 && rt2#initial_nchildren > 0 &&
          try
          let bn1 = get_bn rt1 in
          let bn2 = get_bn rt2 in
          [%debug_log "bn1: %a %s %s" nps bn1 bn1#data#label (Loc.to_string bn1#data#src_loc)];
          [%debug_log "bn2: %a %s %s" nps bn2 bn2#data#label (Loc.to_string bn2#data#src_loc)];
          is_map bn1 bn2 &&
          let moveon x = not x#data#is_sequence in
          let get_mapped_descendants mem = get_p_descendants ~moveon mem in
          let get_dn = get_p_ancestor (fun x -> B.is_def x#data#binding) in
          let name_tbl_to_str tbl =
            Hashtbl.fold
              (fun n bil s ->
                (if s = "" then "" else s^";") ^
                (sprintf "%s(%s)" n (Xlist.to_string (fun bi -> BID.to_string bi) ";" bil))
              ) tbl ""
          in
          let _ = name_tbl_to_str in
          let add_bid tbl x =
            let n = x#data#get_name in
            let bi = Edit.get_bid x in
            try
              let bil = Hashtbl.find tbl n in
              if not (List.mem bi bil) then
                Hashtbl.replace tbl n (bi::bil)
            with
              Not_found ->
                Hashtbl.add tbl n [bi]
          in
          let chk_bid tbl x =
            let b =
              try
                let bidl = Hashtbl.find tbl x#data#get_name in
                List.mem (Edit.get_bid x) bidl
              with
                Not_found -> false
            in
            if b then
              [%debug_log "%a -> %B" nps x b];
            b
          in
          let is_crossing n1 n2 =
            let b =
              edits#is_crossing_with_untouched
                ?full_scan:None ?mask:None ?incompatible_only:None ?weak:None
                nmapping n1 n2
            in
            [%debug_log "%a %a -> %B" nps n1 nps n2 b];
            b
          in
          (
           (let ds1 = get_mapped_descendants nmapping#mem_dom rt1 in
           let name_tbl1 = Hashtbl.create 0 in
           List.iter
             (fun d1 ->
               [%debug_log "d1=%a %s %s" nps d1 d1#data#label (Loc.to_string d1#data#src_loc)];
               try
                 let d2 = nmap1 d1 in
                 [%debug_log "d2=%a %s %s" nps d2 d2#data#label (Loc.to_string d2#data#src_loc)];
                 let dn2 = get_dn d2 in
                 [%debug_log "dn2=%a %s %s" nps dn2 dn2#data#label (Loc.to_string dn2#data#src_loc)];
                 if
                   dn2#data#is_named_orig && is_ins dn2 && not (tree2#is_initial_ancestor rt2 dn2)
                 then
                   add_bid name_tbl1 dn2
               with _ -> ()
             ) ds1;
           [%debug_log "defined names1: [%s]" (name_tbl_to_str name_tbl1)];
           (Hashtbl.length name_tbl1 > 0) &&
           let us2 =
             let chk_parent =
               try
                 let prt1 = rt1#initial_parent in
                 if true(*is_del prt1*) then
                   fun x ->
                     try
                       let px = x#initial_parent in
                       [%debug_log "%a(%s) vs %a(%s)"
                         nups prt1 prt1#data#label nups px px#data#label];

                       if is_ins px && node_eq prt1 px && not (is_crossing prt1 px) then begin

                         [%debug_log "!!!!! adding to npairs: %a [%s] - %a [%s]"
                           nups prt1 (Loc.to_string prt1#data#src_loc)
                           nups px (Loc.to_string px#data#src_loc)];

                         Xset.add npairs ((prt1, px), LocalVariableInliningOrExtraction)
                       end
                     with
                       _ -> ()
                 else
                   fun _ -> ()
               with
                 _ -> fun _ -> ()
             in
             get_p_descendants
               (fun x ->
                 let b =
                   x#data#is_named_orig && is_ins x(* && is_use x*) && chk_bid name_tbl1 x
                 in
                 if b then begin
                   [%debug_log "found: %a %s [%s]" nps x x#data#label (Loc.to_string x#data#src_loc)];
                   chk_parent x
                 end;
                 b
               ) bn2
           in
           us2 <> []
           (*has_p_descendant
             (fun x ->
               let b =
                 x#data#is_named_orig && chk_bid name_tbl1 x && is_ins x
               in
               if b then
                 [%debug_log "found: %a %s %s" nps x x#data#label (Loc.to_string x#data#src_loc)];
               b
             ) bn2*)
           )
         ||
           (let ds2 = get_mapped_descendants nmapping#mem_cod rt2 in
           let name_tbl2 = Hashtbl.create 0 in
           List.iter
             (fun d2 ->
               [%debug_log "d2=%a %s %s" nps d2 d2#data#label (Loc.to_string d2#data#src_loc)];
               try
                 let d1 = nmap2 d2 in
                 [%debug_log "d1=%a %s %s" nps d1 d1#data#label (Loc.to_string d1#data#src_loc)];
                 let dn1 = get_dn d1 in
                 [%debug_log "dn1=%a %s %s" nps dn1 dn1#data#label (Loc.to_string dn1#data#src_loc)];
                 if
                   dn1#data#is_named_orig && is_del dn1 && not (tree1#is_initial_ancestor rt1 dn1)
                 then
                   add_bid name_tbl2 dn1
               with _ -> ()
             ) ds2;
           [%debug_log "defined names2: [%s]" (name_tbl_to_str name_tbl2)];
           (Hashtbl.length name_tbl2 > 0) &&
           let us1 =
             let chk_parent =
               try
                 let prt2 = rt2#initial_parent in
                 if true(* is_ins prt2*) then
                   fun x ->
                     try
                       let px = x#initial_parent in
                       [%debug_log "%a(%s) vs %a(%s)" nups px px#data#label nups prt2 prt2#data#label];
                       if is_del px && node_eq prt2 px && not (is_crossing px prt2) then begin

                         [%debug_log "!!!!! adding to npairs: %a [%s] - %a [%s]"
                           nups px (Loc.to_string px#data#src_loc)
                           nups prt2 (Loc.to_string prt2#data#src_loc)];

                         Xset.add npairs ((px, prt2), LocalVariableInliningOrExtraction)
                       end
                     with
                       _ -> ()
                 else
                   fun _ -> ()
               with
                 _ -> fun _ -> ()
             in
             get_p_descendants
               (fun x ->
                 let b =
                   x#data#is_named_orig && is_del x(* && is_use x*) && chk_bid name_tbl2 x
                 in
                 if b then begin
                   [%debug_log "found: %a %s [%s]" nps x x#data#label (Loc.to_string x#data#src_loc)];
                   chk_parent x
                 end;
                 b
               ) bn1
           in
           us1 <> []
           (*has_p_descendant
             (fun x ->
               let b =
                 x#data#is_named_orig && chk_bid name_tbl2 x && is_del x
               in
               if b then
                 [%debug_log "found: %a %s %s" nps x x#data#label (Loc.to_string x#data#src_loc)];
               b
             ) bn1*)
           )
          )
          with Not_found -> false
        then begin
          [%debug_log "local variable inlining or extraction"];
          edits#add_indivisible_move mid
          (*Xset.add movs (mid, rt1, rt2)*)
        end
        else if
          not force &&
          tsz > 1 &&
          not rt1#data#move_disallowed && not rt2#data#move_disallowed &&
          (
           (let b = rt1#data#subtree_equals rt2#data in [%debug_log "equals=%B" b]; b) ||
           (let b =
             sz > 0 &&
             let d, _, _ = _get_move_density mid in
             (d > 0.75(* || d1 > 0.9 || d2 > 0.9!!!NG!!!*)) &&
             (float esz) /. (float tsz) > 0.75
           in
           [%debug_log "almost_equals=%B" b];
           b)
          ) &&
          not (
          rt1#data#is_op && rt2#data#is_op &&
          let has_matched_subtree1 r1 r2 =
            has_p_descendant (cenv#is_matched_subtree nmapping r1 r2)
          in
          let has_matched_subtree2 r2 r1 =
            has_p_descendant (cenv#is_matched_subtree nmapping r1 r2)
          in
          let has_stable_twin (*tree*)_ tree' nmap is_stable' is_ins_or_del has_matched_subtree rt rt' =
            try
              let prt = rt#initial_parent in
              let prt' = rt'#initial_parent in
              let prt_ = nmap prt in
              prt_ != prt' && is_stable' prt_ &&
              has_p_descendant
                (fun x ->
                  let x' = nmap x in
                  is_stable' x' && tree'#is_initial_ancestor prt_ x'
                ) rt &&
              Array.exists
                (fun n' ->
                  is_ins_or_del n' && node_eq rt n' &&
                  n'#initial_nchildren = rt#initial_nchildren &&
                  let a = rt#initial_children in
                  let b =
                    try
                      Array.iteri
                        (fun i c' ->
                          if not (is_ins_or_del c' && node_eq c' a.(i)) then
                            raise Exit
                        ) n'#initial_children;
                      has_matched_subtree rt n' n'
                    with
                      Exit -> false
                  in
                  [%debug_log "!!!!!!! found: %a" nps n'];
                  b
                ) prt_#initial_children
            with
              _ -> false
          in
          has_stable_twin tree1 tree2 nmap1 is_stable2 is_ins has_matched_subtree1 rt1 rt2 ||
          has_stable_twin tree2 tree1 nmap2 is_stable1 is_del has_matched_subtree2 rt2 rt1
          ) &&
          (
           (try
             let prt1 = rt1#initial_parent in
             let prt2 = rt2#initial_parent in
             (
              let b =
                (not rt1#data#is_common || not rt2#data#is_common) &&
                (is_stable1 prt1 || is_stable2 prt2)
              in
              [%debug_log "is_stable=%B" b];
              b
             ) ||
             let b = is_mov1 prt1 && is_mov2 prt2 in [%debug_log "is_mov=%B" b]; b
           with _ -> false) ||
             (*is_stable1 prt1
               && (try
                 not (rt1#data#relabel_allowed (nmap1 prt1)#initial_children.(rt1#initial_pos)#data)
               with _ -> true)
           ||
             is_stable2 prt2
               && (try
                 not ((nmap2 prt2)#initial_children.(rt2#initial_pos)#data#relabel_allowed rt2#data)
               with _ -> true)
           ||
             is_mov1 prt1 && is_mov2 prt2
           with
             _ -> false) ||!!!NG!!!*)
           (*tsz > 1 &&*)
           (
            (let b = cenv#has_uniq_match rt1 rt2 in [%debug_log "has_uniq_match=%B" b]; b) ||
            (let b = exists_uniq_match movl in [%debug_log "exists_uniq_match=%B" b]; b) ||
            let b = not (surrounded_by is_del rt1 || surrounded_by is_ins rt2) in [%debug_log "%B" b]; b
           )
           (*not (surrounded_by is_del rt1) || not (surrounded_by is_ins rt2))!!!NG!!!*)
          )
        then begin
          [%debug_log "federated move"]
        end
        else if
          not force &&
          sz > 0 &&
          not rt1#data#is_boundary && not rt2#data#is_boundary &&
          rt1#data#is_named_orig && rt2#data#is_named_orig(* && cenv#has_uniq_match rt1 rt2*) &&
          rt1#initial_nchildren > 0 && rt2#initial_nchildren > 0 &&
          (
           let has_same_name n x =
             try
               let b = x#data#get_name = n in
               if b then
                 [%debug_log "found: %a" nps x];
               b
             with _ -> false
           in
           let bn1 = get_bn rt1 in
           let bn2 = get_bn rt2 in
           [%debug_log "bn1: %a" nps bn1];
           [%debug_log "bn2: %a" nps bn2];
           (has_p_ancestor ~moveon:(fun x -> x != bn1) (fun x -> x#data#is_sequence) rt1) &&
           (has_p_ancestor ~moveon:(fun x -> x != bn2) (fun x -> x#data#is_sequence) rt2) &&
           (
            (is_del bn1 && bn1#data#is_named_orig && not (is_ins bn2) &&
             let an2 = Sourcecode.find_nearest_mapped_ancestor_node nmapping#mem_cod rt2 in
             tree2#is_initial_ancestor bn2 an2 &&
             let an2' = nmap2 an2 in
             not (tree1#is_initial_ancestor bn1 an2') && not an2'#data#is_sequence &&
             let _ = [%debug_log "an2': %a" nps an2'] in
             (try an2'#data#get_name = bn1#data#get_name with _ -> false) ||
             has_p_descendant (has_same_name bn1#data#get_name) an2')
          ||
            (is_ins bn2 && bn2#data#is_named_orig && not (is_del bn1) &&
             let an1 = Sourcecode.find_nearest_mapped_ancestor_node nmapping#mem_dom rt1 in
             tree1#is_initial_ancestor bn1 an1 &&
             let an1' = nmap1 an1 in
             not (tree2#is_initial_ancestor bn2 an1') && not an1'#data#is_sequence &&
             let _ = [%debug_log "an1': %a" nps an1'] in
             (try an1'#data#get_name = bn2#data#get_name with _ -> false) ||
             has_p_descendant (has_same_name bn2#data#get_name) an1')
           )
          )
        then begin
          [%debug_log "inlining or extraction"];
          Xset.add movs (mid, rt1, rt2)
        end

        (*!20240324!else if
          let _ = [%debug_log "@"] in
          not force &&
          sz > 0 &&
          rt1#data#is_boundary && rt2#data#is_boundary &&
          rt1#data#is_named_orig && rt2#data#is_named_orig &&
          rt1#data#eq rt2#data &&
          rt1#initial_nchildren > 0 && rt2#initial_nchildren > 0 &&
          has_p_descendant
            (fun x1 ->
              x1#data#is_statement &&
              try
                let x1' = nmap1 x1 in
                let bn1' = get_bn x1' in
                [%debug_log "bn1': %a" nps bn1'];
                bn1'#data#_stripped_label = rt2#data#_stripped_label &&
                is_ins bn1'
              with _ -> false
            ) rt1
        ||
          has_p_descendant
            (fun x2 ->
              x2#data#is_statement &&
              try
                let x2' = nmap2 x2 in
                let bn2' = get_bn x2' in
                [%debug_log "bn2': %a" nps bn2'];
                bn2'#data#_stripped_label = rt1#data#_stripped_label &&
                is_del bn2'
              with _ -> false
            ) rt1
        then begin
          [%debug_log "inlining or extraction"];
          Xset.add movs (mid, rt1, rt2)
        end*)

        else if
          not force &&
          esz > 2 && get_move_density mid > move_density_thresh &&
          let _sim0 = ref (-1.0) in
          try
            Array.exists
              (fun c2 ->
                is_stable2 c2 &&
                let c1 = nmapping#inv_find c2 in
                let pc1 = c1#initial_parent in
                let sim = get_similarity_score pc1 rt2 in
                [%debug_log "found another map: %a-%a (similarity=%f)" nps pc1 nps rt2 sim];
                if !_sim0 < 0.0 then begin
                  _sim0 := get_similarity_score pc1 rt2;
                  [%debug_log "moved subtree similarity (%a-%a): %f" nps rt1 nps rt2 !_sim0];
                end;
                !_sim0 >= sim
              ) rt2#initial_children
          with
            _ -> false
        then begin
          [%debug_log "similarity comparison: moved vs stable"]
        end
        else if
          not force &&
          sz > 0 && not (is_staying()) &&
          try
            let prt1 = rt1#initial_parent in
            let ms = Hashtbl.find sibling_move_tbl prt1 in
            [%debug_log "%a -> [%s]" nps prt1 (Xlist.to_string MID.to_string ";" (Xset.to_list ms))];
            Xset.mem ms mid
          with
            _ ->
              try
                let pprt1 = rt1#initial_parent#initial_parent in
                let ms = Hashtbl.find sibling_move_tbl pprt1 in
                [%debug_log "%a -> [%s]" nps pprt1 (Xlist.to_string MID.to_string ";" (Xset.to_list ms))];
                Xset.mem ms mid
              with
                _ -> sibling_cond rt1 rt2
        then begin
          [%debug_log "sibling_cond=true"]
        end
        else if
          not force &&
          weak && esz > 0 &&
          boundary_cond rt1 rt2 && kind = Edit.Mpermutation &&
          (*try is_map rt1#initial_parent rt2#initial_parent with _ -> false*)
          try
            let prt1 = rt1#initial_parent in
            let prt2 = rt2#initial_parent in
            not prt1#data#is_sequence && not prt2#data#is_sequence &&
            is_map prt1 prt2
          with _ -> false
          (*(try
            let prt1 = rt1#initial_parent in
            let prt2 = rt2#initial_parent in
            is_map prt1 prt2 &&
            rt1#initial_nchildren = 0 && rt2#initial_nchildren = 0 ||
            not (has_p_descendant is_stable1 rt1) &&
            not (has_p_descendant is_stable2 rt2)
          with _ -> false) &&
          (sz <> 1 ||
          not
            (List.exists
               (function
                 | Edit.Move(_, _, (_, i1, _), (_, i2, _)) -> begin
                     let n1 = Info.get_node i1 in
                     let n2 = Info.get_node i2 in
                     n1#data#is_named_orig && n2#data#is_named_orig && n1#data#eq n2#data &&
                     n1#data#is_common
                 end
                 | _ -> false
               ) movl))???NG???*)
        then begin
          [%debug_log "parents of %a-%a are mapped" nps rt1 nps rt2];
          if sz = 1 then begin
            if rt1#initial_nchildren = 1 && rt2#initial_nchildren = 1 then begin
              let c1 = rt1#initial_children.(0) in
              let c2 = rt2#initial_children.(0) in
              try
                let del = edits#find_del c1 in
                let ins = edits#find_ins c2 in
                let _ = nmapping#add_unsettled c1 c2 in
                edits#remove_edit del;
                edits#remove_edit ins;
                let m = Edit.make_move mid (mkinfo c1) (mkinfo c2) in
                [%debug_log "adding %s" (Edit.to_string m)];
                edits#add_edit m;
                if not (node_eq c1 c2) then begin
                  let r = Edit.make_relabel c1 c2 in
                  [%debug_log "adding %s" (Edit.to_string r)];
                  edits#add_edit r
                end
              with _ -> ()
            end
          end
        end
        else if
          not force &&
          let geta = get_p_ancestor (fun x -> x#data#is_sequence) in
          (
           rt1#data#is_sequence && rt2#data#is_sequence &&
           rt1#initial_parent#data#is_boundary && rt2#initial_parent#data#is_boundary ||
           try
             let a1 = geta rt1 in
             let a2 = geta rt2 in
             [%debug_log "a1=%a a2=%a" nps a1 nps a2];
             is_stable1 a1 && is_stable2 a2 &&
             not (is_map a1 a2)
           with _ -> true
          ) &&
          is_region_changing_move mid rt1 rt2
        then begin
          [%debug_log "region changing move"]
        end
        else if
          boundary_move_flag &&
          not rt1#data#is_named && not rt2#data#is_named &&
          rt1#data#is_order_insensitive && rt2#data#is_order_insensitive &&
          sz > 2 &&
          (get_move_density1 mid = 1.0 || get_move_density2 mid = 1.0)
        then begin
          [%debug_log "unnamed boundary move"];
        end
        else if size_limit = 0 || sz <= size_limit then begin
          let cond =
            is_staying() ||
            (*let total = ref 0 in
            let non_xxx_count = ref 0 in*)
            (*let nmapped = ref 0 in*)
            let unstable_context_flag =
              try
                let prt1 = rt1#initial_parent in
                let prt2 = rt2#initial_parent in
                not (is_stable_map prt1 prt2) &&
                let b =
                  not (rt1#data#has_non_trivial_value && node_eq rt1 rt2) ||
                  not ((is_stable1 prt1 ||
                        is_stable2 prt2)(* && prt1#data#is_op*) && node_eq prt1 prt2)
                in
                if not b then
                  [%debug_log "!!! %a-%a [%a]-[%a] %a" nups rt1 nups rt2 locps rt1 locps rt2 labps rt1];
                b
              with _ -> false
            in
            [%debug_log "unstable_context_flag=%B" unstable_context_flag];
            let is_rename_pat n1 n2 =
              try
                n1#data#anonymized_label = n2#data#anonymized_label &&
                cenv#is_rename_pat (n1#data#get_stripped_name, n2#data#get_stripped_name)
              with _ -> false
            in
            List.for_all
              (function
                | (Edit.Move(_, _, (info1, _), (info2, _)) as mov) -> begin
                    (*incr total;*)
                    let nd1 = Info.get_node info1 in
                    let nd2 = Info.get_node info2 in
                    let is_root = nd1 == rt1 &&  nd2 == rt2 in
                    [%debug_log "%a-%a (is_root=%B) %a - %a" nups nd1 nups nd2 is_root labps nd1 labps nd2];
                    let b =
                      (
                       (*check_parent nd1 nd2 && *)
                       is_xxx_pair nd1 nd2 ||
                       (try (*do not remove!!!NG!!!*)
                         unstable_context_flag && not (is_map nd1#initial_parent nd2#initial_parent)
                       with _ -> false)
                      ) &&
                    not (
                    (*cenv#weak_node_eq nd1 nd2 &&*)
                    (
                     cenv#weak_node_eq nd1 nd2 ||
                     is_rename_pat nd1 nd2(* ||
                     try
                       nd1#data#relabel_allowed nd2#data &&
                       let bn1 = get_bn nd1 in
                       let bn2 = get_bn nd2 in
                       [%debug_log "bn1: %s" bn1#data#to_string];
                       [%debug_log "bn2: %s" bn2#data#to_string];
                       is_map bn1 bn2
                     with _ -> false*)
                    ) &&
                    (nd1#data#has_value || nd1#data#is_named) &&
                    (not nd1#data#has_value || nd1#data#has_non_trivial_value) &&
                    (not nd1#data#is_named || nd1#data#is_named_orig(* || B.is_def nd1#data#binding*)) &&
                    let _ = [%debug_log "@"] in
                    try
                      let stmt1 = find_nearest_anc_stmt nd1 in
                      let stmt2 = find_nearest_anc_stmt nd2 in
                      [%debug_log " stmt: %a-%a %a [%a]-[%a]"
                        nups stmt1 nups stmt2 labps stmt1 locps stmt1 locps stmt2];
                      let b0 =
                        (
                         stmt1 == rt1 && stmt2 == rt2 ||
                         is_stable_map stmt1 stmt2 ||
                         is_map stmt1 stmt2 &&
                         try is_map stmt1#initial_parent stmt2#initial_parent with _ -> false
                        ) &&
                        (
                         not (has_p_descendant (fun n -> n != nd1 && node_eq n nd1) stmt1) ||
                         not (has_p_descendant (fun n -> n != nd2 && node_eq n nd2) stmt2)
                        ) &&
                        (
                         not (is_use nd1 && is_use nd2) ||
                         try
                           nmapping#find (get_def_node tree1 nd1) == get_def_node tree2 nd2
                         with _ -> false
                        ) &&
                        edits#is_crossing_with_untouched
                          ?full_scan:None ?mask:None ?incompatible_only:None ?weak:None
                          nmapping nd1 nd2
                      in
                      [%debug_log "b0=%B" b0];
                      if b0 then begin

                        [%debug_log "!!! %a-%a %a [%a]-[%a]"
                          nups nd1 nups nd2 labps nd1 locps nd1 locps nd2];
                        [%debug_log " stmt: %a-%a %a [%a]-[%a]: %B"
                          nups stmt1 nups stmt2 labps stmt1 locps stmt1 locps stmt2 b0];

                        begin
                          try
                            let pnd1 = nd1#initial_parent in
                            let pnd2 = nd2#initial_parent in
                            if not (nmapping#mem_dom pnd1) && nmapping#mem_cod pnd2 then begin
                              Array.iter
                                (fun n ->
                                  if n != nd1 then
                                    try
                                      let n' = nmap1 n in
                                      if is_stable_map n n' then
                                        let pn' = n'#initial_parent in
                                        if not (nmapping#mem_cod pn') then begin
                                          [%debug_log "!!! upair cand: %a-%a" nups nd1 nups n'];
                                          Xset.add npairs ((nd1, n'), StableContext)
                                        end
                                    with
                                      _ -> ()
                                ) pnd1#initial_children
                            end
                            else if
                              nmapping#mem_dom pnd1 && not (nmapping#mem_cod pnd2)
                            then begin
                              Array.iter
                                (fun n ->
                                  if n != nd2 then
                                    try
                                      let n' = nmap2 n in
                                      if is_stable_map n' n then
                                        let pn' = n'#initial_parent in
                                        if not (nmapping#mem_dom pn') then begin
                                          [%debug_log "!!! upair cand: %a-%a" nups n' nups nd2];
                                          Xset.add npairs ((n', nd2), StableContext)
                                        end
                                    with
                                      _ -> ()
                                ) pnd2#initial_children
                            end
                            else if nmapping#mem_dom pnd1 && nmapping#mem_cod pnd2 then begin
                              let pnd1' = nmapping#find pnd1 in
                              if pnd1' != pnd2 then begin
                                if is_stable_map pnd1 pnd1' then begin
                                  [%debug_log "!!! upair cand: %a-%a %a [%a]-[%a]" nups pnd1 nups pnd1'
                                    labps pnd1 locps pnd1 locps pnd1'];

                                  Xset.add npairs ((pnd1, pnd1'), StableContext)
                                end;
                                (*if is_stable_map pnd2' pnd2 then begin
                                  [%debug_log "!!! upair cand: %a-%a %a [%a]-[%a]" nups pnd2' nups pnd2
                                    labps pnd2' locps pnd2' locps pnd2];
                                  Xset.add npairs ((pnd2', pnd2), StableContext)
                                end*)
                              end
                            end

                          with
                            _ -> ()
                        end

                      end;

                      if b0 then begin
                        Xset.add to_be_excluded mov;
                        [%debug_log "to be excluded: %s" (Edit.to_string mov)];
                        is_root
                      end
                      else
                        false
                      (*else begin
                        stmt1 == rt1 && stmt2 == rt2 &&
                        begin
                          try
                            tree1#fast_scan_whole_initial_subtree stmt1
                              (fun n1 ->
                                try
                                  let nm1 = get_orig_name n1 in
                                  tree2#fast_scan_whole_initial_subtree stmt2
                                    (fun n2 ->
                                      try
                                        let nm2 = get_orig_name n2 in
                                        if cenv#is_rename_pat (nm1, nm2) then begin
                                          [%debug_log "%a-%a" nps n1 nps n2];
                                          raise Exit
                                        end
                                      with Not_found -> ()
                                    )
                                with Not_found -> ()
                              );
                            false
                          with Exit -> true
                        end
                      end*)

                    with _ ->
                      [%debug_log "@"];
                      (
                       nd1#data#is_statement || nd2#data#is_statement ||
                       nd1#data#is_boundary && nd2#data#is_boundary
                      ) &&
                      edits#is_crossing_with_untouched
                        ?full_scan:None ?mask:None ?incompatible_only:None ?weak:None
                        nmapping nd1 nd2
                   )
                   in
                   [%debug_log "%a-%a -> %B" nps nd1 nps nd2 b];
                   b
                end
                | _ -> assert false
              ) movl
            (*[%debug_log "total=%d" !total];*)
            (*let nmap1 = nmapping#find in
            let nmap2 = nmapping#inv_find in
            tree1#scan_whole_initial_subtree rt1
              (fun n1 ->
                try
                  let n2 = nmap1 n1 in
                  if not (tree2#initial_subtree_mem rt2 n2) && n1#data#eq n2#data then
                    incr nmapped
                with
                  Not_found -> ()
              );
            tree2#scan_whole_initial_subtree rt2
              (fun n2 ->
                try
                  let n1 = nmap1 n2 in
                  if not (tree1#initial_subtree_mem rt1 n1) && n1#data#eq n2#data then
                    incr nmapped
                with
                  Not_found -> ()
              );
            [%debug_log "nmapped=%d" !nmapped];
            total := !total + !nmapped / 2;
            [%debug_log "total = total + nmapped / 2 = %d" !total];*)
            (*let sz1 = tree1#whole_initial_subtree_size rt1 in
            let sz2 = tree2#whole_initial_subtree_size rt2 in
            [%debug_log "sz1=%d sz2=%d" sz1 sz2];
            total := !total + (sz1 + sz2) / 2;
            [%debug_log "total = total + (sz1 + sz2) / 2 = %d" !total];
            let r = (float !non_xxx_count) /. (float !total) in
            [%debug_log "non_xxx_count=%d/%d=%f (thresh=%f)" !non_xxx_count !total r thresh];
            r < thresh*)
          in (* cond *)
          [%debug_log "cond=%B" cond];
          if cond then begin

            begin
              let xtbl = Hashtbl.create 0 in
              let xset = Xset.create 0 in
              let sz = List.length movl in
              List.iter
                (fun mov ->
                  match mov with
                  | Edit.Move(_mid, _, (info1, _), (info2, _)) -> begin
                      let mid = !_mid in
                      let nd1 = Info.get_node info1 in
                      let nd2 = Info.get_node info2 in
                      if has_same_digest nd1 nd2 then begin
                        try
                          let r1, movs = Hashtbl.find xtbl mid in
                          let r1_ =
                            if tree1#is_initial_ancestor nd1 r1 then
                              nd1
                            else
                              r1
                          in
                          let movs_ = mov::movs in
                          [%debug_log "%a: r1: %a -> %a (count=%d)"
                            MID.ps mid nps r1 nps r1_ (List.length movs_)];
                          Hashtbl.replace xtbl mid (r1_, movs_)
                        with
                          Not_found -> begin
                            [%debug_log "%a: r1: %a (count=1)" MID.ps mid nps nd1];
                            Hashtbl.add xtbl mid (nd1, [mov])
                          end
                      end;
                      if nmapping#is_final_mapping nd1 nd2 then begin
                        [%debug_log "to be excluded: %a (final mapping)" MID.ps mid];
                        Xset.add xset mid
                      end
                      else if
                        try
                          let pnd1 = nd1#initial_parent in
                          let pnd2 = nd2#initial_parent in
                          not pnd1#data#is_boundary && not pnd2#data#is_boundary &&
                          let ppnd1 = pnd1#initial_parent in
                          let ppnd2 = pnd2#initial_parent in
                          pnd1#data#is_order_insensitive && pnd2#data#is_order_insensitive &&
                          is_stable_map ppnd1 ppnd2
                        with _ -> false
                      then begin
                        [%debug_log "to be excluded: %a (ancestor mapping)" MID.ps mid];
                        Xset.add xset mid
                      end
                      (*else if
                        try
                          let pnd1 = nd1#initial_parent in
                          let pnd2 = nd2#initial_parent in
                          pnd1#data#is_boundary && pnd2#data#is_boundary &&
                          pnd1#data#is_named && pnd2#data#is_named &&
                          pnd1#data#get_name = nd1#data#get_name &&
                          pnd2#data#get_name = nd2#data#get_name &&
                          nmapping#find pnd1 == pnd2
                        with _ -> false
                      then begin
                        [%debug_log "to be excluded: %a (namesake boundary)" MID.ps mid];
                        Xset.add xset mid
                      end*)
                      else if
                        try
                          let nm1 = get_orig_name nd1 in
                          let nm2 = get_orig_name nd2 in
                          nd1#data#anonymized2_label = nd2#data#anonymized2_label &&
                          (
                           let pnd1 = nd1#initial_parent in
                           let pnd2 = nd2#initial_parent in
                           nmapping#find pnd1 == pnd2(* ||
                           try
                             let ppnd1 = pnd1#initial_parent in
                             let ppnd2 = pnd2#initial_parent in
                             not ppnd1#data#is_sequence && not ppnd2#data#is_sequence &&
                             nmapping#find ppnd1 == ppnd2 ||
                             try
                               let pppnd1 = ppnd1#initial_parent in
                               let pppnd2 = ppnd2#initial_parent in
                               not pppnd1#data#is_sequence && not pppnd2#data#is_sequence &&
                               nmapping#find pppnd1 == pppnd2
                             with _ -> false
                           with _ -> false*)
                          ) &&
                          cenv#is_rename_pat (nm1, nm2) &&
                          not (is_cross_boundary nmapping nd1 nd2)
                        with
                          _ -> false
                      then begin
                        [%debug_log "to be excluded: %a (possible rename)" MID.ps mid];
                        Xset.add xset mid
                      end
                      else if
                        not boundary_move_flag &&
                        try
                          let bid1 = Edit.get_bid nd1 in
                          let bid2 = Edit.get_bid nd2 in
                          [%debug_log "bid1=%a bid2=%a" BID.ps bid1 BID.ps bid2];
                          List.exists
                            (function
                              | (Edit.Move(_, _, (i1, _), (i2, _)) as m) -> begin
                                  m != mov &&
                                  let n1 = Info.get_node i1 in
                                  let n2 = Info.get_node i2 in
                                  try
                                    let bi1 = Edit.get_bid n1 in
                                    let bi2 = Edit.get_bid n2 in
                                    [%debug_log "bi1=%a bi2=%a" BID.ps bi1 BID.ps bi2];
                                    bi1 = bid1 && bi2 = bid2 &&
                                    has_same_digest n1 n2
                                  with
                                    _ -> false
                              end
                              | _ -> assert false
                            ) movl
                        ||
                          cenv#has_use_mapping nmapping nd1 nd2
                        ||
                          try
                            let def1 = get_def_node tree1 nd1 in
                            let def2 = get_def_node tree2 nd2 in
                            [%debug_log "def1=%a def2=%a" nups def1 nups def2];
                            nmapping#find def1 == def2
                          with
                            _ -> false
                        (*||
                          not (nd1#data#eq nd2#data) &&
                          B.is_def nd1#data#binding && B.is_def nd2#data#binding &&
                          edits#relabel_exists
                            (function
                              | Edit.Relabel(_, (i1, _), (i2, _)) -> begin
                                  let n1 = Info.get_node i1 in
                                  let n2 = Info.get_node i2 in
                                  is_use n1 && is_use n2 &&
                                  try
                                    let bi1 = Edit.get_bid n1 in
                                    let bi2 = Edit.get_bid n2 in
                                    [%debug_log "bi1=%a bi2=%a" BID.ps bi1 BID.ps bi2];
                                    bi1 = bid1 && bi2 = bid2
                                  with
                                    _ -> false
                              end
                              | _ -> assert false
                            )*)
                        with
                          _ -> false
                      then begin
                        if sz = 1 && is_cross_boundary nmapping nd1 nd2 then
                          [%debug_log "single cross boundary move: %a" MID.ps mid]
                        else if
                          sz = 1 &&
                          let stmt1_opt = ref None in
                          let stmt2_opt = ref None in
                          let stmt_deleted () =
                            try
                              let stmt1 =
                                match !stmt1_opt with
                                | Some x -> x
                                | _ ->
                                    let x = Comparison.get_stmt nd1 in
                                    stmt1_opt := Some x;
                                    x
                              in
                              is_del stmt1
                            with
                              _ -> false
                          in
                          let stmt_inserted () =
                            try
                              let stmt2 =
                                match !stmt2_opt with
                                | Some x -> x
                                | _ ->
                                    let x = Comparison.get_stmt nd2 in
                                    stmt2_opt := Some x;
                                    x
                              in
                              is_ins stmt2
                            with
                              _ -> false
                          in
                          (*let stmt_eq () =
                            match !stmt1_opt, !stmt2_opt with
                            | Some x1, Some x2 -> x1#data#eq x2#data
                            | _ -> false
                          in*)
                          (stmt_deleted() || stmt_inserted()) &&
                          (
                           stmt_deleted() && stmt_inserted()(* && not (stmt_eq())*) ||
                           not (
                             not (is_use nd1 && is_use nd2) ||
                             try
                               let def1 = get_def_node tree1 nd1 in
                               let def2 = get_def_node tree2 nd2 in
                               is_local_def def1 && is_local_def def2 &&
                               nmapping#find def1 == def2
                             with _ -> false
                           )
                          )
                        then
                          [%debug_log "single cross statement move: %a" MID.ps mid]
                        else begin
                          [%debug_log "to be excluded: %a (binding)" MID.ps mid];
                          Xset.add xset mid
                        end
                      end
                  end
                  | _ -> assert false
                ) movl;
              let named_or_op_ratio_thresh = 0.9 in
              Hashtbl.iter
                (fun m (r1, movs) ->
                  let _ = m in
                  (*let sz = tree1#whole_initial_subtree_size r1 in*)
                  let named_or_op_count = ref 0 in
                  let _sz = ref 0 in
                  let _ =
                    tree1#scan_whole_initial_subtree r1
                      (fun n1 ->
                        incr _sz;
                        if n1#data#is_named(*_orig*) || n1#data#has_non_trivial_value then
                          incr named_or_op_count
                        else if n1#data#is_op then
                          incr named_or_op_count
                        else begin
                          [%debug_log "%a" nps n1]
                        end
                      )
                  in
                  let sz = !_sz in
                  [%debug_log "%a: sz=%d r1=%a nmovs=%d named_or_op_count=%d" MID.ps m
                    sz nps r1 (List.length movs) !named_or_op_count];
                  if
                    sz > 1 &&
                    (
                     List.length movs = sz
                    ||
                     let named_or_op_ratio = (float !named_or_op_count) /. (float sz) in
                     [%debug_log "named_or_op_rate=%.2f (thresh=%.2f)" named_or_op_ratio named_or_op_ratio_thresh];
                     named_or_op_ratio > named_or_op_ratio_thresh
                    )
                  then
                    List.iter
                      (fun m ->
                        [%debug_log "to be excluded: %s" (Edit.to_string m)];
                        Xset.add to_be_excluded m
                      ) movs
                ) xtbl;
              List.iter
                (fun mov ->
                  match mov with
                  | Edit.Move(_mid, _, _, _) -> begin
                      if Xset.mem xset !_mid then begin
                        [%debug_log "to be excluded: %s" (Edit.to_string mov)];
                        Xset.add to_be_excluded mov
                      end
                  end
                  | _ -> assert false
                ) movl
            end;

            let only_common_excluded, excluded =
              let b = ref true in
              let xl = ref [] in
              begin
                try
                  Xset.iter
                    (function
                      | Edit.Move(m, _, (i1, _), (i2, _)) as mov ->
                          if !m = mid then begin
                            [%debug_log "checking %s" (Edit.to_string mov)];
                            let n1 = Info.get_node i1 in
                            let n2 = Info.get_node i2 in
                            if not n1#data#is_common || not n2#data#is_common then begin
                              b := false;
                              raise Exit
                            end
                            else
                              xl := mov :: !xl
                          end
                      | _ -> ()
                    ) to_be_excluded
                with
                  Exit -> ()
              end;
              !b, !xl
            in
            [%debug_log "only_common_excluded=%B" only_common_excluded];

            if only_common_excluded then begin
              List.iter (Xset.remove to_be_excluded) excluded
            end;

            begin %debug_block
              let xlen =
                let count = ref 0 in
                Xset.iter
                  (function
                    | Edit.Move(m, _, _, _) as mov ->
                        if !m = mid then begin
                          [%debug_log "to be excluded[%d]: %s" !count (Edit.to_string mov)];
                          incr count;
                        end
                    | _ -> ()
                  ) to_be_excluded;
                !count
              in
              let head =
                if xlen > 0 then
                  sprintf "PARTIALLY (excluded %d moves) " xlen
                else
                  ""
              in
              [%debug_log "%sdecomposing %a..." head MID.ps mid];
            end;
            List.iter
              (fun mov ->
                [%debug_log "decomposing %s" (Edit.to_string mov)];
                match mov with
                | Edit.Move(_, _, (info1, ex1), (info2, ex2)) -> begin
                    let nd1 = Info.get_node info1 in
                    let nd2 = Info.get_node info2 in

                    if Xset.mem to_be_excluded mov then begin
                      [%debug_log "!!!!!! excluded: %a-%a" nps nd1 nps nd2];
                    end
                    else begin
                      let _ = nmapping#remove nd1 nd2 in
                      edits#remove_edit mov;
                      begin
                        try
                          match edits#find_rel12 nd1 nd2 with
                          | Edit.Relabel _ as rel ->
                              edits#remove_edit rel
                          | _ -> assert false
                        with
                          Not_found -> ()
                      end;
                      edits#add_edit (Edit.Delete(false, info1, ex1));
                      edits#add_edit (Edit.Insert(false, info2, ex2));
                      Xset.add dels nd1;
                      Xset.add inss nd2
                    end
                end
                | _ -> assert false

              ) movl
          end
        end
      ) sz_list;
    dels, inss, movs, npairs
  (* end of decompose_moves *)

  (* *)
  let elaborate_edits_for_delta options ?(sim_thresh=0.05) cenv tree1 tree2 nmapping edits =
    let dels = Xset.create 0 in
    let inss = Xset.create 0 in

    let move_size_tbl = Hashtbl.create 0 in
    edits#iter_moves
      (function
        | Edit.Move(mid, _, (info1, _), (info2, _)) -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            if nd1#data#eq nd2#data then
              try
                let sz = Hashtbl.find move_size_tbl !mid in
                Hashtbl.replace move_size_tbl !mid (sz + 1)
              with
                Not_found -> Hashtbl.add move_size_tbl !mid 1
        end
        | _ -> assert false
      );

    let nmap = nmapping#find in
    let get_subtree_similarity = get_subtree_similarity tree1 tree2 nmap in
    let visited = Xset.create 0 in
    let is_ancestor_of_visited n =
      try
        Xset.iter
          (fun x ->
            if tree1#is_initial_ancestor n x then
              raise Exit
          ) visited;
        false
      with
        Exit -> true
    in
    let eliminate_edits rt1 rt2 =
      [%debug_log "rt1=%a rt2=%a" nups rt1 nups rt2];
      let bname_opt =
        if
          rt1#data#is_named_orig && rt2#data#is_named_orig &&
          rt1#data#get_name = rt2#data#get_name
        then begin
          [%debug_log "boundary name: %s" rt1#data#get_name];
          Some rt1#data#get_name
        end
        else
          None
      in
      let has_boundary_of_same_name =
        match bname_opt with
        | Some bn -> begin
            [%debug_log "boundary name: %s" bn];
            let pred n = try n#data#is_boundary && n#data#get_name = bn with _ -> false in
            fun nd ->
              let b =
                (try nd#data#get_name = bn with _ -> false) || has_p_ancestor pred nd
              in
              [%debug_log "%a -> %B" nps nd b];
              b
        end
        | None -> fun _ -> false
      in
      let has_boundary_of_relevant_name =
        match bname_opt with
        | Some _ -> begin
            fun rt nd ->
              let pred n =
                try
                  n#data#is_boundary && n#data#is_named_orig && (edits#mem_ins n || edits#mem_del n)
                with _ -> false
              in
              let b =
                try
                  let a = get_p_ancestor pred nd in
                  let aname = a#data#get_name in
                  [%debug_log "a=%a aname=%s" nps a aname];
                  try
                    Sourcecode.scan_descendants rt
                      (fun n ->
                        if
                          n#data#is_named_orig &&
                          (edits#mem_ins n || edits#mem_del n) &&
                          (n#data#get_name = aname ||
                          match n#data#orig_lab_opt with
                          | Some o when
                              Label.get_name (Obj.obj o) = Label.get_name (Obj.obj n#data#_label)
                            -> true
                          | _ -> false)
                        then begin
                          [%debug_log "found: %a" nps n];
                          raise Exit
                        end
                      );
                    false
                  with
                  | Exit -> true
                  | _ -> false
                with _ -> false
              in
              [%debug_log "rt=%a nd=%a b=%B" nps rt nps nd b];
              b
        end
        | _ -> fun _ _ -> false
      in
      let safe_subroot_list = ref [] in
      let is_good_pair ?(mid=MID.unknown) n1 n2 =
        let b0 =
          not n1#data#is_common &&
          n1#data#_digest <> None &&
          n1#initial_nchildren > 0 &&
          n1#data#subtree_equals n2#data
        in
        if b0 then
          safe_subroot_list := (n1, n2) :: !safe_subroot_list;
        let b =
          b0 ||
          (try
            let sz = Hashtbl.find move_size_tbl mid in
            [%debug_log "mid=%a sz=%d" MID.ps mid sz];
            sz > 3(*16*)
          with _ -> false) ||
          List.exists
            (fun (r1, r2) ->
              tree1#is_initial_ancestor r1 n1 && tree2#is_initial_ancestor r2 n2
            ) !safe_subroot_list
        in
        [%debug_log "%a %a-%a -> %B" MID.ps mid nps n1 nps n2 b];
        b
      in
      let survived_pairs = Xset.create 0 in
      let is_crossing_or_incompatible = cenv#is_crossing_or_incompatible in
      edits#iter_moves_topdown
        (function
          | Edit.Move(mid, _, (info1, ex1), (info2, ex2)) as mov -> begin
              let nd1 = Info.get_node info1 in
              let nd2 = Info.get_node info2 in
              let b1 = tree1#initial_subtree_mem rt1 nd1 in
              let b2 = tree2#initial_subtree_mem rt2 nd2 in
              if b1 || b2 then begin
                if
                  (not b1 || not b2) && has_boundary_of_same_name nd1 && has_boundary_of_same_name nd2 ||
                  (not b1 && has_boundary_of_relevant_name rt1 nd1) ||
                  (not b2 && has_boundary_of_relevant_name rt2 nd2) ||
                  match bname_opt with
                  | Some bn -> begin
                      nd1 == rt1 && nd2 == rt2 ||
                      (nd1#data#get_name = bn && nd2#data#get_name = bn ||
                      Xset.mem survived_pairs (nd1#initial_parent, nd2#initial_parent) &&
                      try
                        Xset.iter
                          (fun (n1, n2) ->
                            if is_crossing_or_incompatible n1 n2 nd1 nd2 then
                              raise Exit
                          ) survived_pairs;
                        true
                      with Exit -> false
                     ) &&
                      tree1#is_initial_ancestor rt1 nd1 && tree2#is_initial_ancestor rt2 nd2
                  end
                  | None when begin
                      try
                        nd1#data#get_name = rt1#data#get_name || nd2#data#get_name = rt2#data#get_name
                      with _ -> false
                  end -> false
                  | _  -> begin
                      is_good_pair ~mid:!mid nd1 nd2 ||
                      Array.exists
                        (fun c1 ->
                          try
                            let c2 = nmap c1 in
                            c2#initial_parent == nd2 &&
                            is_good_pair c1 c2
                          with
                            Not_found -> false
                        ) nd1#initial_children
                  end
                then begin
                  [%debug_log "not eliminated: %s" (Edit.to_string mov)];
                  Xset.add survived_pairs (nd1, nd2)
                end
                else begin
                  [%debug_log "eliminating %s" (Edit.to_string mov)];
                  let _ = nmapping#remove nd1 nd2 in
                  edits#remove_edit mov;
                  begin
                    try
                      match edits#find_rel12 nd1 nd2 with
                      | Edit.Relabel _ as rel ->
                          edits#remove_edit rel
                      | _ -> assert false
                    with
                      Not_found -> ()
                  end;
                  edits#add_edit (Edit.Delete(false, info1, ex1));
                  edits#add_edit (Edit.Insert(false, info2, ex2));
                  Xset.add dels nd1;
                  Xset.add inss nd2
                end
              end
          end
          | _ -> assert false
        )
    in
    let eliminate_mappings rt1 rt2 =
      [%debug_log "rt1=%a rt2=%a" nups rt1 nups rt2];
      tree1#scan_whole_initial_subtree rt1
        (fun nd1 ->
          try
            let nd1' = nmapping#find nd1 in
            if tree2#is_initial_ancestor rt2 nd1' then begin
              if
                (*nd1#data#is_common && nd1'#data#is_common &&*)
                not (edits#mem_mov12 nd1 nd1') && not (edits#mem_rel12 nd1 nd1')
              then begin
                let _ = nmapping#remove nd1 nd1' in
                edits#add_edit (Edit.make_delete nd1);
                edits#add_edit (Edit.make_insert nd1')
              end
            end
          with _ -> ()
        )
    in
    tree1#scan_whole_initial
      (fun n1 ->
        if n1#data#is_boundary then begin
          if not (is_ancestor_of_visited n1) then begin
            Xset.add visited n1;
            try
              let n2 = nmap n1 in
              let sim = get_subtree_similarity n1 n2 in
              (*[%debug_log "n1=%s" n1#initial_to_string];
              [%debug_log "n2=%s" n2#initial_to_string];
              [%debug_log "similarity=%f" sim];*)
              if sim < sim_thresh then begin
                [%debug_log "elaborating edits on %s-%s (similarity=%f<%f)"
                  n1#initial_to_string n2#initial_to_string sim sim_thresh];
                Xprint.verbose options#verbose_flag "elaborating edits on %s -- %s (similarity=%f)"
                  n1#data#to_string n2#data#to_string sim;

                eliminate_edits n1 n2;
                eliminate_mappings n1 n2
              end
            with
              Not_found -> ()
          end
        end
      );
    dels, inss

  let is_mid (MID.MOVE x) = x >= 0
  let get_level nd =
    let rec count nd =
      try
        (count nd#parent) + 1
      with
        Otree.Parent_not_found _ -> 1
    in
    count nd
  let make_level_mid nd = MID.MOVE (-(get_level nd))

  (* eliminate false moves *)
  let eliminate_false_moves options cenv edits nmapping =
    let tree1 = cenv#tree1 in
    let tree2 = cenv#tree2 in

    [%debug_log "* ELIMINATING FALSE MOVES...\n"];

    [%debug_log "nmapping:\n%s\n" nmapping#to_string];
    (*[%debug_log "nmapping (gindex):\n%s" nmapping#to_string_gid];*)

    let crossing_with_untouched = Xset.create 0 in (* mid set *)
    let crossing_checked = Xset.create 0 in (* mid set *)
    let move_size_tbl = Hashtbl.create 0 in (* mid -> size *)
    let move_top_tbl = Hashtbl.create 0 in (* mid -> node * node *)
    let move_mem_tbl = Hashtbl.create 0 in (* mid -> (node * node) list *)

    edits#iter_moves
      (function
        | Edit.Move(mid, _, (info1, _), (info2, _)) -> begin

            let sz1 = Info.get_size info1 in
            let sz2 = Info.get_size info2 in

            assert (sz1 = sz2);

            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in

            [%debug_log "checking %a %a-%a (%a-%a) sz=%d" MID.ps !mid nups nd1 nups nd2 ngps nd1 ngps nd2 sz1];

            begin
              try
                let ndpairs = Hashtbl.find move_mem_tbl !mid in
                Hashtbl.replace move_mem_tbl !mid ((nd1, nd2)::ndpairs)
              with
                Not_found -> Hashtbl.add move_mem_tbl !mid [nd1, nd2]
            end;
            begin
              try
                let rt1, _ = Hashtbl.find move_top_tbl !mid in
                if nd1#gindex > rt1#gindex then
                  Hashtbl.replace move_top_tbl !mid (nd1, nd2)
              with
                Not_found -> Hashtbl.add move_top_tbl !mid (nd1, nd2)
            end

        end
        | _ -> assert false

      ); (* edits#iter_moves *)

    let mid_list = ref [] in
    let x_move_size_tbl = Hashtbl.create 0 in (* mid -> size *)
    let y_move_size_tbl = Hashtbl.create 0 in (* mid -> size *)
    let move_depth_tbl = Hashtbl.create 0 in (* mid -> depth *)

    Hashtbl.iter
      (fun mid ndpairs ->
        mid_list := mid :: !mid_list;
        let sz =
          List.fold_left
            (fun s (n1, n2) ->
              if n1#data#eq n2#data then
                s +. 1.0
              else if n1#data#_anonymized_label = n2#data#_anonymized_label then
                s +. 0.5
              else
                s
            ) 0.0 ndpairs
        in
(*
        let sz = if sz = 0 then 1 else sz in (* EXPERIMENTAL!!! *)
*)
        let xsz, ysz =
          List.fold_left
            (fun (x, y) (n1, n2) ->
              let x' =
              if n1#data#eq n2#data then
                if
                  n1#data#is_sequence ||
                  n1#data#is_boundary
                then
                  x +. 1.0
                else if n1#data#is_statement then
                  if n1#data#is_named_orig then
                    x +. 1.0
                  else
                    x +. 0.5
                else
                  x
              else
                x
(*
                if n1#data#eq n2#data then
                  x +. 1.0
                  (*if n1#data#is_named then
                    if n1#data#is_common then
                      x
                    else if n1#data#is_named_orig then
                      x +. 1.0
                    else
                      x
                  else if n1#data#is_sequence || n1#data#is_boundary then
                    x +. 2.0
                  else if n1#data#is_statement then
                    x +. 1.0
                  else
                    x*)
                else
                  if
                    n1#data#is_named_orig &&
                    n1#data#_anonymized_label = n2#data#_anonymized_label
                  then
                    x +. 0.5
                  (*else if n1#data#is_sequence || n1#data#is_boundary then
                    x +. 1.0*)
                  else
                    x
*)
              in
              x', y + 1
            ) (0.0, 0) ndpairs
        in
        Hashtbl.add move_size_tbl mid sz;
        Hashtbl.add x_move_size_tbl mid xsz;
        Hashtbl.add y_move_size_tbl mid ysz
      ) move_mem_tbl;

    [%debug_log "top nodes:"];
    Hashtbl.iter
      (fun mid (rt1, rt2) ->
        [%debug_log "%a: %a-%a" MID.ps mid nups rt1 nups rt2];
        let d1 = List.length (tree1#initial_ancestor_nodes rt1) in
        let d2 = List.length (tree2#initial_ancestor_nodes rt2) in
        Hashtbl.add move_depth_tbl mid (d1 + d2)
      ) move_top_tbl;

    let get_ln n = n#data#src_loc.Loc.start_line in

    let sorted_mid_list =
      let cmp m0 m1 =
        (*let d0 = Hashtbl.find move_depth_tbl m0 in
        let d1 = Hashtbl.find move_depth_tbl m1 in
        let c = Stdlib.compare d0 d1 in*)
        let r0, r0_ = Hashtbl.find move_top_tbl m0 in
        let r1, r1_ = Hashtbl.find move_top_tbl m1 in
        let c =
          if
            tree1#is_initial_ancestor r0 r1 ||
            tree2#is_initial_ancestor r0_ r1_
          then
            -1
          else if
            tree1#is_initial_ancestor r1 r0 ||
            tree2#is_initial_ancestor r1_ r0_
          then
            1
          else
            0
        in
        if c = 0 then
          let xsz0 = Hashtbl.find x_move_size_tbl m0 in
          let xsz1 = Hashtbl.find x_move_size_tbl m1 in
          let c = Stdlib.compare xsz1 xsz0 in
          if c = 0 then

              let ysz0 = Hashtbl.find y_move_size_tbl m0 in
              let ysz1 = Hashtbl.find y_move_size_tbl m1 in
              let c = Stdlib.compare ysz1 ysz0 in
              if c = 0 then
                let ln0 = get_ln r0 in
                let ln1 = get_ln r1 in
                let c = Stdlib.compare ln0 ln1 in
                c
              else
                c
(*
              let ln0 = get_ln r0 in
              let ln1 = get_ln r1 in
              let c = Stdlib.compare ln0 ln1 in
              if c = 0 then
                let ysz0 = Hashtbl.find y_move_size_tbl m0 in
                let ysz1 = Hashtbl.find y_move_size_tbl m1 in
                let c = Stdlib.compare ysz1 ysz0 in
                c
              else
                c
*)
          else
            c
        else
          c
      in
      List.fast_sort cmp !mid_list
    in

    let virtually_untouched = Xset.create 0 in

    let n_mids = List.length sorted_mid_list in
    let _ = n_mids in

    let mid_count = ref 0 in

    let get_depth mi = Hashtbl.find move_depth_tbl mi in
    let _ = get_depth in

    List.iter
      (fun mid ->
        incr mid_count;
        [%debug_log "[%d/%d] mid=%a (depth=%d)" !mid_count n_mids MID.ps mid (get_depth mid)];

        if not (Xset.mem crossing_checked mid) then begin
          Xset.add crossing_checked mid;
          let crossing_movs = Xset.create 0 in
          let nd1, nd2 = Hashtbl.find move_top_tbl mid in
          [%debug_log "%a: %a-%a" MID.ps mid nps nd1 nps nd2];

          let incompat_nds1 = Xset.create 0 in
          let incompat_nds2 = Xset.create 0 in

          let crossing_nds1 = Xset.create 0 in
          let crossing_nds2 = Xset.create 0 in

          try
            nmapping#iter_crossing_or_incompatible_mapping nd1 nd2
              (fun n1 n2 ->
                match edits#find12 n1 n2 with
                | [] | [Edit.Relabel _] -> begin
                    if not (is_ghost_node n1) && not (is_ghost_node n2) then begin
                      [%debug_log "-->  crossing with untouched: %a-%a" nups n1 nups n2];
                      Xset.add crossing_with_untouched mid;
                      raise Break
                    end
                end
                | eds when not (is_ghost_node n1) && not (is_ghost_node n2) -> begin
                    [%debug_log "-->  crossing or incompatible with:"];
                    List.iter
                      (fun e ->
                        [%debug_log "!!!    %s" (Edit.to_string e)];
                        match e with
                        | Edit.Move(id, _, (i1, _), (i2, _)) -> begin

                            let n1 = Info.get_node i1 in
                            let n2 = Info.get_node i2 in
                            if Node_mapping.is_incompatible tree1 tree2 nd1 nd2 n1 n2 then begin
                              Xset.add incompat_nds1 n1;
                              Xset.add incompat_nds2 n2
                            end
                            else(* if is_cross_boundary nmapping n1 n2 then*) begin
                              Xset.add crossing_nds1 n1;
                              Xset.add crossing_nds2 n2
                            end;

                            if Xset.mem virtually_untouched !id then begin
                              [%debug_log "%a is virtually untouched" MID.ps !id];
                              Xset.add crossing_with_untouched mid;
                              Xset.add crossing_checked mid;
                              raise Break
                            end
                            else
                              Xset.add crossing_movs !id
                        end
                        | _ -> ()
                      ) eds
                end
                | _ -> ()
              );

            (*let get_xsz mi = Hashtbl.find x_move_size_tbl mi in*)
            let get_ysz mi = Hashtbl.find y_move_size_tbl mi in
            let _ = get_ysz in

            let n_crossing_movs = Xset.length crossing_movs in
            if n_crossing_movs > 0 then begin
              let ml = Xset.to_list crossing_movs in
              [%debug_log "-->  %a crossing with %d moves: [%s]" MID.ps mid n_crossing_movs
                (Xlist.to_string
                   (fun m -> sprintf "%a(ysz:%d)" MID.ps m (get_ysz m))
                   ";" ml)];

              let xsz = Hashtbl.find x_move_size_tbl mid in

              [%debug_log "%a(depth=%d,xsz=%f,ysz=%d): %a-%a is shallowest"
                MID.ps mid (get_depth mid) xsz (get_ysz mid) nps nd1 nps nd2];

              let anc_ok () =
                let mem_dom n1 =
                  if
                    Xset.mem incompat_nds1 n1 ||
                    Xset.mem crossing_nds1 n1 && try nd1#initial_parent == n1 with _ -> false
                  then
                    false
                  else
                    nmapping#mem_dom n1
                in
                let mem_cod n2 =
                  if
                    Xset.mem incompat_nds2 n2 ||
                    Xset.mem crossing_nds2 n2 && try nd2#initial_parent == n2 with _ -> false
                  then
                    false
                  else
                    nmapping#mem_cod n2
                in
                let b =
                  try
                    let an1 = Sourcecode.find_nearest_mapped_ancestor_node mem_dom nd1 in
                    let an2 = Sourcecode.find_nearest_mapped_ancestor_node mem_cod nd2 in
                    [%debug_log "an1=%a an2=%a" nups an1 nups an2];
                    (*(an1 == nd1#initial_parent || an2 == nd2#initial_parent) &&*)
                    (*not (is_cross_boundary nmapping an1 an2) &&*)
                    nmapping#find an1 == an2
                  (*||
                    let an1_ = Sourcecode.find_nearest_mapped_ancestor_node nmapping#mem_dom nd1 in
                    let an2_ = Sourcecode.find_nearest_mapped_ancestor_node nmapping#mem_cod nd2 in
                    [%debug_log "an1=%a an2=%a" nups an1 nups an2];
                    (*(an1_ != an1 || an2_ != an2) &&*)
                    nmapping#find an1_ == an2_*)
                  with
                    _ -> false
                in
                [%debug_log "%B" b];
                b
              in

              if xsz < 1.0 && not (anc_ok()) then begin (* NB checking move roots is insufficient *)
                [%debug_log "%a --> crossing with untouched" MID.ps mid];
                Xset.add crossing_with_untouched mid
              end
              else begin
                [%debug_log "%a --> virtually untouched" MID.ps mid];
                Xset.add virtually_untouched mid
              end;
              List.iter (Xset.add crossing_with_untouched) ml;
              List.iter (Xset.add crossing_checked) ml
            end
          with
            Break -> ()
        end

      ) sorted_mid_list;

    begin %debug_block
      let crossing_with_untouched_l = Xset.to_list crossing_with_untouched in
      [%debug_log "moves crossing with untouched: [%s]"
        (Xlist.to_string MID.to_string ";"
           (List.fast_sort Stdlib.compare crossing_with_untouched_l))];
    end;

    let top_mid_tbl1 = Hashtbl.create 0 in (* top node -> mid *)

    let move_roots =
      Hashtbl.fold
        (fun m (nd1, nd2) l ->
          if not (Xset.mem crossing_with_untouched m) then begin
            Hashtbl.add top_mid_tbl1 nd1 m;
            (m, nd1, nd2)::l
          end
          else
            l
        ) move_top_tbl []
    in

    let sorted_move_roots =
      (List.fast_sort
         (fun (_, nd0, _) (_, nd1, _) -> Stdlib.compare nd0#gindex nd1#gindex)
         move_roots)
    in

    begin %debug_block
      let sort_nds = List.fast_sort (fun n0 n1 -> Stdlib.compare n0#gindex n1#gindex) in
      [%debug_log "move roots:"];
      List.iter
        (fun (mid, nd1, nd2) ->
          [%debug_log "%a  %a -> %a (size:%f)"
            MID.ps mid nups nd1 nups nd2 (try Hashtbl.find move_size_tbl mid with Not_found -> 0.0)];
          let ndpairs = Hashtbl.find move_mem_tbl mid in
          let nds1, nds2 = List.split ndpairs in
          [%debug_log "      [%a]" nsps (sort_nds nds1)];
          [%debug_log "   -> [%a]" nsps (sort_nds nds2)];
        )
      (List.fast_sort
         (fun (_, nd0, _) (_, nd1, _) -> Stdlib.compare nd0#gindex nd1#gindex)
         move_roots);
      [%debug_log "move roots (gindex):"];
      List.iter
        (fun (mid, nd1, nd2) ->
          [%debug_log "%a  %a -> %a (size:%f)"
            MID.ps mid ngps nd1 ngps nd2 (try Hashtbl.find move_size_tbl mid with Not_found -> 0.0)];
          let ndpairs = Hashtbl.find move_mem_tbl mid in
          let nds1, nds2 = List.split ndpairs in
          [%debug_log "      [%a]" ngsps (sort_nds nds1)];
          [%debug_log "   -> [%a]" ngsps (sort_nds nds2)];
        ) sorted_move_roots
    end;

    let extra_move_elements = Xset.create 0 in
    List.iter
      (fun (mid, nd1, nd2) ->
        let _ = mid in
        [%debug_log "mid=%a nd1=%a nd2=%a" MID.ps mid nups nd1 nups nd2];
        [%debug_log "%a-%a" ngps nd1 ngps nd2];
        nd1#iter_initial_ancestor_nodes
          (fun n1 ->
            try
              let m = Hashtbl.find top_mid_tbl1 n1 in
              let n1' = nmapping#find n1 in

              if tree2#is_initial_ancestor n1' nd2 then

                let ndpairs = Hashtbl.find move_mem_tbl m in
                try
                  List.iter
                    (fun (mn1, mn2) ->
                      [%debug_log "    mn1=%a mn2=%a" nups mn1 nups mn2];
                      [%debug_log "    %a-%a" ngps mn1 ngps mn2];
                      if
                        cenv#is_crossing_or_incompatible nd1 nd2 mn1 mn2
                      then begin
                        [%debug_log "crossing_or_incompatible: (%a-%a) (%a, %a-%a)"
                          nups nd1 nups nd2 MID.ps m nups mn1 nups mn2];
                        Xset.add extra_move_elements (m, mn1, mn2);
                        raise Break
                      end
                    )
                    (List.fast_sort
                       (fun (n0, _) (n1, _) -> Stdlib.compare n1#gindex n0#gindex)
                       ndpairs)
                with
                  Break -> ()
            with
              Not_found -> ()
          )
      ) sorted_move_roots;

    let extra_move_element_list = Xset.to_list extra_move_elements in

    begin %debug_block
      [%debug_log "extra_move_elements: %s"
        (Xlist.to_string
           (fun (m, n1, n2) -> sprintf "(%a,%a-%a)" MID.ps m nups n1 nups n2)
           ";"
           (List.fast_sort
              (fun (_, nd0, _) (_, nd1, _) -> Stdlib.compare nd0#gindex nd1#gindex)
              extra_move_element_list)
        )];
      [%debug_log "extra_move_elements (gindex): %s"
        (Xlist.to_string
           (fun (m, n1, n2) -> sprintf "(%a,%a-%a)" MID.ps m ngps n1 ngps n2)
           ";"
           (List.fast_sort
              (fun (_, nd0, _) (_, nd1, _) -> Stdlib.compare nd0#gindex nd1#gindex)
              extra_move_element_list)
        )]
    end;

    let get_mid (mid, _, _) = mid in
    let get_nd1 (_, nd, _) = nd in
    let get_nd2 (_, _, nd) = nd in

    let next_l mdat tree nd l =
      match l with
      | [] -> [Otree.create_leaf mdat]
      | _ ->
          let gi = nd#gindex in
          let lgi = (tree#initial_leftmost nd)#gindex in
          let unchanged, children =
            List.partition
              (fun mnd ->
                let mgi = mnd#data#node#gindex in
                let b = lgi <= mgi && mgi <= gi in
                not b
              ) l
          in
          unchanged @ [Otree.create_node mdat (Array.of_list children)]
    in

    let get_children get_nd tree sorted_tops =
      Array.of_list
        (List.fold_left
           (fun l x ->
             let mid = get_mid x in
             let nd = get_nd x in
             let w = try Hashtbl.find move_size_tbl mid with Not_found -> 0.0 in
             let mdat = new mid_data mid w nd in

             next_l mdat tree nd l

           ) [] sorted_tops
        )
    in

    let move_elems = sorted_move_roots @ extra_move_element_list in

    let children1 =
      get_children get_nd1 tree1
        (List.fast_sort
           (fun (_, nd0, _) (_, nd1, _) -> Stdlib.compare nd0#gindex nd1#gindex)
           move_elems)
    in

    let children2 =
      get_children get_nd2 tree2
        (List.fast_sort
           (fun (_, _, nd0) (_, _, nd1) -> Stdlib.compare nd0#gindex nd1#gindex)
           move_elems)
    in

    let mroot_mdat1 = new mid_data MID.unknown 1.0 tree1#root in
    let mroot_mdat2 = new mid_data MID.unknown 1.0 tree2#root in

    let mroot1 = Otree.create_node mroot_mdat1 children1 in
    let mroot2 = Otree.create_node mroot_mdat2 children2 in

    let mtree1 = new Otree.otree mroot1 in
    let mtree2 = new Otree.otree mroot2 in

(* EXPERIMENTAL!!! *)

    let disable_true_move_detection_flag =
      check_hard_tree_size_limit options mtree1#size mtree2#size
    in
    [%debug_log "disable_true_move_detection_flag=%B" disable_true_move_detection_flag];

    let true_moves =
      if disable_true_move_detection_flag then begin
        (*let mk x =
          let l = ref [] in
          let rec do_scan nd =
            Array.iter do_scan nd#children;
            l := nd#data#mid :: (make_level_mid nd) :: !l
          in
          do_scan x;
          !l
        in
        let a1 = Array.map mk children1 in
        let a2 = Array.map mk children2 in
        begin %debug_block
          let pr i x = [%debug_log "%d: [%s]" i (String.concat ";" (List.map MID.to_string x))] in
          [%debug_log "a1:"];
          Array.iteri pr a1;
          [%debug_log "a2:"];
          Array.iteri pr a2;
        end;
        let m, rs, ds, is = Adiff.adiff a1 a2 in
        let s = Xset.create 0 in
        let proc a i =
          [%debug_log "%d: [%s]" i (String.concat ";" (List.map MID.to_string a.(i)))];
          List.iter
            (fun x ->
              if is_mid x then
                Xset.add s x
            ) a.(i)
        in
        begin %debug_block
          [%debug_log "|m|=%d" (List.length m)];
          List.iter
            (fun (i, j) ->
              [%debug_log "%d->%d: [%s]" i j (String.concat ";" (List.map MID.to_string a1.(i)))];
              (*proc a1 i ; proc a2 j*)
            ) m
        end;
        [%debug_log "rel:"];
        List.iter (fun (i, j) -> proc a1 i; proc a2 j) rs;
        [%debug_log "del:"];
        List.iter (proc a1) ds;
        [%debug_log "ins:"];
        List.iter (proc a2) is;
        [%debug_log "%d true moves found" (Xset.length s)];
        Xset.to_list s*)[]
      end
      else begin
        Xprint.verbose options#verbose_flag "performing experimental false move detection...";
        let mid_count_tbl = Hashtbl.create 0 in
        List.iter
          (fun (mid, _, _) ->
            try
              let c = Hashtbl.find mid_count_tbl mid in
              Hashtbl.replace mid_count_tbl mid (c+1)
            with
              Not_found -> Hashtbl.add mid_count_tbl mid 2
          ) extra_move_element_list;

        let modify_weight n =
          try
            let c = Hashtbl.find mid_count_tbl n#data#mid in
            n#data#set_weight (n#data#weight /. (float c))
          with
            Not_found -> ()
        in
        mtree1#fast_scan_all modify_weight;
        mtree2#fast_scan_all modify_weight;

        begin %debug_block
          [%debug_log "* mid tree 1:\n%s" mtree1#to_string];
          [%debug_log "* mid tree 2:\n%s" mtree2#to_string];
        end;

        let cost t1 t2 i j =
          let nd1 = t1#get i in
          let nd2 = t2#get j in
          let w1 = nd1#data#weight in
          let w2 = nd2#data#weight in

          if j = 0 then (* delete *)
            w1
          else if i = 0 then (* insert *)
            w2
          else
            if nd1#data#equals nd2#data then
              0.0
            else (* relabel *)
              w1 +. w2
        in

        let eds, map, _ = ZS.Float.find cost mtree1 mtree2 in
        let _ = map in

        begin %debug_block
          [%debug_log "eds:\n%s" (Diffast_misc.Edit.seq_to_string eds)];
          [%debug_log "mapping:\n%s" (Mapping.to_string map)]
        end;

        let true_moves =
          List.fold_left
            (fun l ed ->
              if Diffast_misc.Edit.isdel ed then
                let i = Diffast_misc.Edit.get_del_idx ed in
                let m = (mtree1#get i)#data#mid in
                if not (List.mem m l) then
                  m :: l
                else
                  l

              else if Diffast_misc.Edit.isrel ed then
                let i = Diffast_misc.Edit.get_rel_idx1 ed in
                let m = (mtree1#get i)#data#mid in
                if not (List.mem m l) then
                  m :: l
                else
                  l

              else
                l
            ) [] eds
        in
        true_moves
      end
    in
    [%debug_log "true moves: [%s]"
      (Xlist.to_string MID.to_string ";"
         (List.fast_sort Stdlib.compare true_moves))];

    edits#iter_moves
      (function
        | Edit.Move(mid, kind, (info1, _), (info2, _)) as mov ->
            let _ = info1 in
            let _ = info2 in
            let crossing = Xset.mem crossing_with_untouched !mid in
            if Xset.mem virtually_untouched !mid then begin
              [%debug_log "removing virtually untouched %s" (Edit.to_string mov)];
              edits#remove_edit mov
            end
            else if
              crossing ||
              (disable_true_move_detection_flag || List.mem !mid true_moves)
            then begin

              begin %debug_block
                if List.mem !mid true_moves then
                  if
                    not
                      (edits#is_crossing_with_untouched
                         ?full_scan:None ?mask:None ?incompatible_only:None ?weak:None
                         nmapping (Info.get_node info1) (Info.get_node info2))
                  then
                    [%debug_log "is this a move? %s" (Edit.to_string mov)]
              end;

              if
                crossing && !kind <> Edit.Mpermutation &&
                !kind <> Edit.Modd
              then begin
                [%debug_log "kind changed: %a: %s -> %s (crossing with untouched)"
                  MID.ps !mid
                  (Edit.move_kind_to_string !kind) (Edit.move_kind_to_string Edit.Mpermutation)];

                kind := Edit.Mpermutation
              end

            end
            else begin
              [%debug_log "removing untouched %s" (Edit.to_string mov)];
              edits#remove_edit mov
            end

        | _ -> assert false
      );

    [%debug_log "* END OF FALSE MOVE ELIMINATION\n"]
   (* end of eliminate_false_moves *)


  (* examine moves are normal or permutation *)
  let examine_moves edits =
    let permutations = ref [] in (* mid list *)
    edits#iter_moves
      (function
        | Edit.Move(mid, kind, (_, _), (_, _)) ->
            if !kind = Edit.Mpermutation then begin
              if not (List.mem !mid !permutations) then
                permutations := !mid :: !permutations
            end

        | _ -> assert false
      );
    edits#iter_moves
      (function
        | Edit.Move(mid, kind, _, _) ->
            if !kind <> Edit.Mpermutation && List.mem !mid !permutations then begin

              [%debug_log "kind changed: %a: %s -> %s (same group)"
                MID.ps !mid (Edit.move_kind_to_string !kind) (Edit.move_kind_to_string Edit.Mpermutation)];

              kind := Edit.Mpermutation
            end
        | _ -> assert false
      )
  (* end of examine_moves *)



  (********** fix up edit operations **********)
  let fixup_edits
      options lang cenv
      tree1 tree2
      (*pruned*)_
      edits
      nmapping
      pre_nmapping
      =
    let extend_move n1 n2 =
      [%debug_log "n1=%a n2=%a" nups n1 nups n2];
      try
        let pn1 = n1#initial_parent in
        let pn2 = n2#initial_parent in
        [%debug_log "pn1=%a pn2=%a" nups pn1 nups pn2];

        try
          match edits#find_mov12 pn1 pn2 with
          | Edit.Move(mid, k, _, _) -> begin
              [%debug_log "mid=%a" MID.ps !mid];
              let chk1 c1 =
                try
                  match edits#find_mov1 c1 with
                  | Edit.Move(m, _, _, (ci2, _)) -> begin
                      [%debug_log "m=%a" MID.ps !m];
                      !m <> !mid ||
                      let c2 = Info.get_node ci2 in
                      [%debug_log "c1=%a c2=%a" nups c1 nups c2];
                      not (cenv#is_crossing_or_incompatible c1 c2 n1 n2)
                  end
                  | _ -> assert false
                with
                  Not_found -> true
              in
              let ok =
                Array.for_all
                  (fun c1 ->
                    c1 == n1 ||
                    chk1 c1 && not (has_p_descendant (fun x -> not (chk1 x)) c1)
                  ) pn1#initial_children
              in
              [%debug_log "ok=%B" ok];
              if ok then
                fun () ->
                  let mov = Edit._make_move !mid !k (mkinfo n1) (mkinfo n2) in
                  [%debug_log "generated move: %s" (Edit.to_string mov)];
                  edits#add_edit mov
              else
                failwith "extend_move"
          end
          | _ -> assert false
        with
          Not_found -> begin
            if try nmapping#find pn1 == pn2 with _ -> false then
              fun () -> [%debug_log "stably mapped"]
            else
              failwith "extend_move"
          end
      with
        _ -> failwith "extend_move"
    in
    let add_move n1 n2 =
      fun () ->
        let mid = options#moveid_generator#gen in
        let mov = Edit.make_move_permutation mid (mkinfo n1) (mkinfo n2) in
        [%debug_log "generated move: %s" (Edit.to_string mov)];
        edits#add_edit mov
    in

    let use_binding_info = lang#elaborate_edits <> None in
    let rely_on_binding_info = use_binding_info in

    begin %debug_block
      [%debug_log "*** fixing up edits ***"];
      [%debug_log "nmapping:\n%s\n" nmapping#to_string];
    end;

    let mid_chg_tbl = group_moves options tree1 tree2 edits nmapping in

    begin %debug_block
      [%debug_log "* AFTER GROUPING MOVES *"];

      Hashtbl.iter
      (fun mid0 mid1 -> [%debug_log "%a -> %a" MID.ps mid0 MID.ps mid1])
      mid_chg_tbl;

      let tbl = Hashtbl.create 0 in
      edits#iter_moves
        (function
          | Edit.Move(mid, _, (info1, _), (_, _)) -> begin
              let nd1 = Info.get_node info1 in
              let gi1 = nd1#gindex in
              try
                let c, gi, n = Hashtbl.find tbl !mid in
                Hashtbl.replace tbl !mid (if gi < gi1 then c+1, gi1, nd1 else c+1, gi, n)
              with
                Not_found -> Hashtbl.add tbl !mid (1, gi1, nd1)
          end
          | _ -> assert false
        );
      let keys = Hashtbl.fold (fun k _ l -> k::l) tbl [] in
      let sorted_keys = List.fast_sort Stdlib.compare keys in
      List.iter
        (fun k ->
          let c, gi, n = Hashtbl.find tbl k in
          [%debug_log " %a root:%a(%a) size=%d" MID.ps k gps gi nups n c]
        ) sorted_keys;

      [%debug_log "edits:\n%s\n" edits#to_string];
    end;

    eliminate_false_moves options cenv edits nmapping;

    begin %debug_block
      [%debug_log "* AFTER FALSE MOVE ELIMINATION *"];
      [%debug_log "edits:\n%s\n" edits#to_string];
    end;

    examine_moves edits;

    (* eliminating odd relabels again *)
    let _ = eliminate_odd_relabels options tree1 tree2 edits nmapping in

    let move_region_tbl = make_move_region_tbl tree1 tree2 edits in
    let parent_move_tbl = make_parent_move_tbl cenv move_region_tbl edits in
    let child_move_tbl  = make_child_move_tbl parent_move_tbl in

    let suggested_pairs =
      handle_movrels options cenv tree1 tree2 edits nmapping parent_move_tbl child_move_tbl
    in

    (* shrink moves in order to increase SPSM *)
    if options#shrink_moves_flag then begin
      let move_region_tbl = make_move_region_tbl tree1 tree2 edits in
      let removed_move_tbl = edits#shrink_moves_rp cenv tree1 tree2 nmapping move_region_tbl in
      let move_region_tbl = make_move_region_tbl tree1 tree2 edits in
      edits#shrink_moves cenv tree1 tree2 nmapping move_region_tbl removed_move_tbl
    end;

    let move_region_tbl = make_move_region_tbl tree1 tree2 edits in
    let parent_move_tbl = make_parent_move_tbl cenv move_region_tbl edits in
    let child_move_tbl  = make_child_move_tbl parent_move_tbl in

    let suggested_pairs0 =
      handle_movrels options cenv tree1 tree2 edits nmapping parent_move_tbl child_move_tbl
    in

    Xset.add_set suggested_pairs suggested_pairs0;

    begin %debug_block
      if Xset.length suggested_pairs > 0 then begin
        [%debug_log "suggested_pairs:"];
        Xset.iter
          (fun (n1, n2) ->
            [%debug_log "%a-%a" nups n1 nups n2]
          ) suggested_pairs
      end
    end;

    let is_crossing_with_untouched = is_crossing_with_untouched edits nmapping in

    (* check moves *)
    [%debug_log "checking moves..."];
    let full_scan =
      options#rename_rectification_level > 0
    in
    let moves = Xset.create 0 in
    let non_moves = Xset.create 0 in
    edits#iter_moves_topdown
      (function
        | Edit.Move(mid, _, (info1, _), (info2, _)) as mov ->
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in

            [%debug_log "checking: %a %a-%a" MID.ps !mid nups nd1 nups nd2];

            if Xset.mem non_moves !mid then begin
              [%debug_log "not a move: %s" (Edit.to_string mov)];
              edits#remove_edit mov
            end
            else if Xset.mem moves !mid then
              ()
            else

            if is_crossing_with_untouched ~full_scan ~weak:true nd1 nd2 then begin
              Xset.add moves !mid
            end
            else begin
              [%debug_log "not a move: %s" (Edit.to_string mov)];
              edits#remove_edit mov;
              Xset.add non_moves !mid
            end

        | _ -> assert false
      );


    [%debug_log "nmapping:\n%s\n" nmapping#to_string];

    (* extra postprocessing *)
    if true then begin
      [%debug_log "* STARTING EXTRA POSTPROCESSING"];

      let _, keyroots_moderate =
        let filt n1 n2 =
          not (edits#mem_mov12 n1 n2)(* ||
          not (is_cross_boundary nmapping n1 n2)*)
        in
        find_keyroots options ~relax:true ~ignore_sequence:true ~filt tree1 tree2 nmapping
      in
      let keyroots = keyroots_moderate in

      begin %debug_block
        List.iter
        (fun (n1, n2) ->
          [%debug_log "keyroot pair: %a(size=%d) - %a(size=%d)  %a[%a] - %a[%a]"
            nups n1 (tree1#whole_initial_subtree_size n1)
            nups n2 (tree2#whole_initial_subtree_size n2)
            labps n1 locps n1 labps n2 locps n2]
        ) keyroots;
      end;

      if keyroots <> [] || Xset.length suggested_pairs > 0 then begin

        let starting_pairs =
          Xlist.union
            keyroots
            (Xlist.filter_map
               (fun (n1, n2) ->
                 try
                   let p1 = n1#initial_parent in
                   let p2 = n2#initial_parent in
                   [%debug_log "%a-%a -> %a-%a" nups n1 nups n2 nups p1 nups p2];
                   Some (p1, p2)
                 with
                 | Otree.Parent_not_found _
                 | Not_found -> None
               ) (Xset.to_list suggested_pairs))
        in

        nmapping#set_starting_pairs_for_glueing starting_pairs;
        let removed_pairs, added_pairs =
          if not options#no_glue_flag then begin
          [%debug_log "@"];
          let removed_pairs, added_pairs, _ =
            let is_move n1 n2 =
              let b =
                (edits#mem_mov12 n1 n2 || is_crossing_with_untouched ~weak:true n1 n2) &&
                not
                  (try
                    not n1#data#is_order_insensitive && not n1#data#is_order_insensitive &&
                    nmapping#find n1#initial_parent == n2#initial_parent &&
                    n1#data#equals n2#data
                  with
                    _ -> false)
              in
              [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
              b
            in
            glue_deletes_and_inserts options cenv tree1 tree2
              ~override:true ~is_move ~downward:true ~no_moves:true ~extend_move ~add_move
              ~use_binding_info ~rely_on_binding_info
              ~edits_opt:(Some edits)
              nmapping (new Node_mapping.c cenv)
          in
          removed_pairs, added_pairs
          end
          else
            [], []
        in
        begin %debug_block
          [%debug_log "removed_pairs:"];
        List.iter
          (fun (n1, n2) -> [%debug_log "  %a-%a" nups n1 nups n2]) removed_pairs;
        [%debug_log "added_pairs:"];
        List.iter
          (fun (n1, n2) -> [%debug_log "  %a-%a" nups n1 nups n2]) added_pairs;
        end;

        let is_mov nd1 nd2 =
          [%debug_log "%a-%a" nups nd1 nups nd2];
          let mid_opt = ref None in
          try
            List.iter
              (fun (rn1, rn2) ->
                if tree1#is_initial_ancestor rn1 nd1 && tree2#is_initial_ancestor rn2 nd2 then begin
                  [%debug_log "keyroot pair: %a-%a" nups rn1 nups rn2];
                  let movs = ref [] in

                  edits#iter_moves
                    (function
                      | Edit.Move(mid, _, (info1, _), (info2, _)) -> begin
                          let n1 = Info.get_node info1 in
                          let n2 = Info.get_node info2 in
                          if
                            tree1#is_initial_ancestor rn1 n1 && tree2#is_initial_ancestor rn2 n2
                          then begin
                            movs := (mid, n1, n2) :: !movs
                          end
                      end
                      | _ -> assert false
                    );

                  begin %debug_block
                    List.iter
                    (fun (mid, _, _) ->
                      [%debug_log "  %a" MID.ps !mid]
                    ) !movs
                  end;

                  tree1#scan_whole_initial_subtree rn1
                    (fun n1 ->
                      try
                        let n2 = nmapping#find n1 in
                        if not (edits#mem_mov12 n1 n2) then
                          if
                            cenv#is_crossing_or_incompatible nd1 nd2 n1 n2
                          then begin
                            List.iter
                              (fun (m, mn1, mn2) ->
                                let crossing_or_incompat =
                                  cenv#is_crossing_or_incompatible nd1 nd2 mn1 mn2
                                in
                                if not crossing_or_incompat then begin
                                  mid_opt := Some !m;
                                  raise Exit
                                end
                              ) !movs;
                            raise Exit
                          end
                      with
                      | Not_found | Exit -> ()
                    )
                end
              ) keyroots;

            if is_crossing_with_untouched ~mask:added_pairs ~weak:true nd1 nd2 then
              true, None
            else
              false, None
          with
            Exit -> true, !mid_opt
        in (* is_mov *)

        sync_edits options ~is_mov ~check_conflicts:true cenv edits removed_pairs added_pairs;

      end

    end; (* extra postprocessing *)


    if Hashtbl.length mid_chg_tbl > 0 then
      edits#iter_moves
        (function
          | Edit.Move(mid, _, _, _) -> begin
              try
                let id = Hashtbl.find mid_chg_tbl !mid in
                [%debug_log "!!! changing move id: %a --> %a" MID.ps !mid MID.ps id];
                mid := id
              with
                Not_found -> ()
          end
          | _ -> assert false
        );



    (* identify relative permutations *)

    [%debug_log "IDENTIFYING RELATIVE PERMUTATIONS..."];

    let move_region_tbl = make_move_region_tbl tree1 tree2 edits in
    let parent_move_tbl = make_parent_move_tbl cenv move_region_tbl edits in
    let child_move_tbl  = make_child_move_tbl parent_move_tbl in

    let _mid_fusion_tbl = Hashtbl.create 0 in

    let find_move_root_pair m =
      let _, g1, _, g2 = Hashtbl.find move_region_tbl m in
      let n1 = tree1#search_node_by_gindex g1 in
      let n2 = tree2#search_node_by_gindex g2 in
      [%debug_log "%a -> %a-%a" MID.ps m nps n1 nps n2];
      n1, n2
    in

    Hashtbl.iter
      (fun mid _cmids ->
        if _cmids <> [] then begin
          [%debug_log "child moves of %a --> [%s]" MID.ps mid
            (Xlist.to_string (fun m -> MID.to_string m) ";" _cmids)];

          let cmids =
            List.filter
              (fun cmid ->
                let n1, n2 = find_move_root_pair cmid in
                (*let (_, g1, _, g2) = Hashtbl.find move_region_tbl cmid in
                let n1 = tree1#search_node_by_gindex g1 in
                let n2 = tree2#search_node_by_gindex g2 in*)
                [%debug_log "root pair of %a --> %a-%a" MID.ps cmid nups n1 nups n2];
                let is_crossing_or_incompatible =
                  cenv#is_crossing_or_incompatible n1 n2
                in
                try
                  edits#iter_moves
                    (function
                      | Edit.Move(m, _, (info1, _), (info2, _)) ->
                          if !m = mid then
                            let n1' = Info.get_node info1 in
                            let n2' = Info.get_node info2 in
                            let b = is_crossing_or_incompatible n1' n2' in
                            [%debug_log "crossing_or_incompatible %a-%a --> %B" nups n1' nups n2' b];
                            if b then
                              raise Exit
                      | _ -> assert false
                    );
                  true
                with
                  Exit -> false
              ) _cmids
          in

          [%debug_log "child moves of %a (filtered) --> [%s]" MID.ps mid
            (Xlist.to_string (fun m -> MID.to_string m) ";" cmids)];


          let pair_weight_list =
            List.map
              (fun cmid ->
                try
                  let (_, g1, _, g2) = Hashtbl.find move_region_tbl cmid in
                  let n1 = tree1#search_node_by_gindex g1 in
                  let n2 = tree2#search_node_by_gindex g2 in
                  let sz = estimate_cost_of_move tree1 tree2 nmapping n1 n2 in
                  (n1, n2, Comparison.weight_of_int sz)
                with
                  Not_found -> assert false
              ) cmids
          in
          let compat, _ =
            cenv#select_compatible_and_not_crossing_pairs pair_weight_list
          in

          List.iter
            (fun (n1, n2, _) ->
              try
                let m = edits#find_mid12 n1 n2 in
                [%debug_log "compatible move: %a -> %a" MID.ps m MID.ps mid];
                Hashtbl.add _mid_fusion_tbl m mid
              with
                Not_found -> assert false
            ) compat

        end
      ) child_move_tbl;

    (* calculate fixpoint *)
    let mid_fusion_tbl = Hashtbl.create 0 in

    let rec _find_anc_move visited m =
      Xset.add visited m;
      try
        let m' = Hashtbl.find _mid_fusion_tbl m in
        [%debug_log "%a -> %a" MID.ps m MID.ps m'];
        if Xset.mem visited m' then begin
          [%debug_log "loop detected!"];
          m
        end
        else
          _find_anc_move visited m'
      with
        Not_found -> m
    in
    let find_anc_move m = _find_anc_move (Xset.create 0) m in

    let boundary_exists (*tree*)_ rt n =
      let b =
        (*try
          tree1#iter_initial_ancestor_nodes n
            (fun a ->
              if a#data#is_boundary then
                raise Exit;
              if a == rt then
                raise Not_found
            );
          false
        with
        | Not_found -> false
        | Exit -> true*)
        n#data#is_boundary ||
        let moveon x = x != rt in
        has_p_ancestor ~moveon (fun x -> x#data#is_boundary) n
      in
      [%debug_log "%a %a -> %B" nps rt nps n b];
      b
    in
    let stable_map_exists rt1 rt2 n1 n2 =

      let is_stable_map n1 n2 =
        let b =
          (try nmapping#find n1 == n2 with _ -> false) &&
          not (edits#mem_mov12 n1 n2)
        in
        [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
        b
      in
      let moveon x = x != rt1 in
      let b =
        has_p_ancestor ~moveon
          (fun x1 ->
            try
              let x2 = nmapping#find x1 in
              is_stable_map x1 x2 &&
              tree2#is_initial_ancestor rt2 x2 && tree2#is_initial_ancestor x2 n2
            with _ -> false
          ) n1 ||
        has_p_descendant
          (fun x1 ->
            try
              let x2 = nmapping#find x1 in
              is_stable_map x1 x2 &&
              tree2#is_initial_ancestor rt2 x2 &&
              let ngi1 = n1#gindex in
              let ngi2 = n2#gindex in
              let xgi1 = x1#gindex in
              let xgi2 = x2#gindex in
              [%debug_log "ngi1=%d xgi1=%d ngi2=%d xgi2=%d" ngi1 xgi1 ngi2 xgi2];
              ngi1 <> xgi1 && ngi2 <> xgi2 &&
              (ngi1 - xgi1) * (ngi2 - xgi2) < 0
            with _ -> false
          ) rt1
      in
      [%debug_log "%a %a -> %B" nps n1 nps n2 b];
      b
    in
    Hashtbl.iter
      (fun m0 m1 ->
        let m' = find_anc_move m1 in
        let n1, n2 = find_move_root_pair m0 in
        let n1', n2' = find_move_root_pair m' in
        if boundary_exists tree1 n1' n1 && boundary_exists tree2 n2' n2 then
        (*if
          n1'#data#is_boundary || n2'#data#is_boundary ||
          boundary_exists tree1 n1' n1 || boundary_exists tree2 n2' n2
        then*)
         ()
        else if stable_map_exists n1' n2' n1 n2 then begin
          [%debug_log "%a %s %s -- %a %s %s"
            nups n1' n1'#data#label (Loc.to_string n1'#data#src_loc)
            nups n2' n2'#data#label (Loc.to_string n2'#data#src_loc)];
          [%debug_log "%a %s %s -- %a %s %s"
            nups n1 n1#data#label (Loc.to_string n1#data#src_loc)
            nups n2 n2#data#label (Loc.to_string n2#data#src_loc)]
        end
        else begin
          [%debug_log "changing move id: %a --> %a" MID.ps m0 MID.ps m'];
          Hashtbl.add mid_fusion_tbl m0 m'
        end
      ) _mid_fusion_tbl;

    if Hashtbl.length mid_fusion_tbl > 0 then begin
      edits#iter_moves
        (function
          | Edit.Move(mid, _, _, _) -> begin
              try
                let id = Hashtbl.find mid_fusion_tbl !mid in
                mid := id
              with
                Not_found -> ()
          end
          | _ -> assert false
        )
    end;

    (* eliminate small move of unnamed entities *)
    if options#no_unnamed_node_move_flag then begin
      let is_unnamed_pair n1 n2 =
        (not n1#data#is_named_orig || not n2#data#is_named_orig) &&
        (not n1#data#has_non_trivial_value || not n2#data#has_non_trivial_value) ||
        n1#data#move_disallowed || n2#data#move_disallowed
      in
      ignore (decompose_moves cenv tree1 tree2 is_unnamed_pair options edits nmapping 1)
    end;

    (* *)
    if options#dump_delta_flag || options#conservative_flag then begin
      [%debug_log "elaborating edits..."];

      let is_stable_map n1 n2 =
        let b =
          (*(try nmapping#find n1 == n2 with _ -> false) &&*)
          try
            let _ = edits#find_mov12 n1 n2 in
            false
          with
            Not_found -> true
        in
        [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
        b
      in
      let is_stable1 n =
        let b =
          try
            let _ = edits#find_mov1 n in
            false
          with
            Not_found -> true
        in
        [%debug_log "%a -> %B" nps n b];
        b
      in
      let is_stable2 n =
        let b =
          try
            let _ = edits#find_mov2 n in
            false
          with
            Not_found -> true
        in
        [%debug_log "%a -> %B" nps n b];
        b
      in
      let dels0, inss0, movs0, npairs0 =
        let is_bad_pair n1 n2 =
          let b =
            try
              match cenv#multiple_node_matches#find n1#data#_label with
              | _, [] | [], _ | [_], [_] -> false
              | _ ->
                  n1#data#eq n2#data && not (n1#data#is_named_orig && n1#data#is_order_insensitive)
            with
              _ -> false
          in
          let b =
            b &&
            not (n1#initial_nchildren > 1 && n1#data#equals n2#data ||
                 not (is_cross_boundary nmapping n1 n2))
          in
          [%debug_log "%a %a -> %B" labps n1 labps n2 b];
          b
        in
        decompose_moves cenv tree1 tree2 is_bad_pair options edits nmapping 2
      in

      let nmap1 n1 =
        let n1' = nmapping#find n1 in
        [%debug_log "%a->%a" nps n1 nps n1'];
        n1'
      in
      let nmap2 n2 =
        let n2' = nmapping#inv_find n2 in
        [%debug_log "%a<-%a" nps n2' nps n2];
        n2'
      in

      if not options#no_moves_flag && Xset.length movs0 > 0 then begin
        let is_stable1 n =
          match edits#find1 n with
          | [] | [Edit.Relabel _] -> true
          | _ -> false
        in
        let is_stable2 n =
          match edits#find2 n with
          | [] | [Edit.Relabel _] -> true
          | _ -> false
        in
        let rmmap n1 n2 =
          begin
            try
              ignore (nmapping#remove n1 n2)
            with _ -> ()
          end;
          begin
            try
              let rel = edits#find_rel12 n1 n2 in
              edits#remove_edit rel
            with _ -> ()
          end;
          if not (edits#mem_del n1) then
            edits#add_edit (Edit.make_delete n1);
          if not (edits#mem_ins n2) then
            edits#add_edit (Edit.make_insert n2)
        in
        Xset.iter
          (fun (mid, nd1, nd2) ->
            [%debug_log "mid=%a nd1=%a nd2=%a" MID.ps mid nps nd1 nps nd2];
            let has_key_node1 =
              try
                tree1#fast_scan_whole_initial_subtree nd1
                  (fun n1 ->
                    if
                      is_stable1 n1 &&
                      (n1#data#is_named_orig || n1#data#has_non_trivial_value)
                    then
                      raise Found
                  );
                false
              with Found -> true
            in
            [%debug_log "has_key_node1=%B" has_key_node1];
            if not has_key_node1 then
              tree1#fast_scan_whole_initial_subtree nd1
                (fun n1 ->
                  if is_stable1 n1 then begin
                    let n2 = nmap1 n1 in
                    rmmap n1 n2
                  end
                );
            let has_key_node2 =
              try
                tree2#fast_scan_whole_initial_subtree nd2
                  (fun n2 ->
                    if
                      is_stable2 n2 &&
                      (n2#data#is_named_orig || n2#data#has_non_trivial_value)
                    then
                      raise Found
                  );
                false
              with Found -> true
            in
            [%debug_log "has_key_node2=%B" has_key_node2];
            if not has_key_node2 then
              tree2#fast_scan_whole_initial_subtree nd2
                (fun n2 ->
                  if is_stable2 n2 then begin
                    let n1 = nmap2 n2 in
                    rmmap n1 n2
                  end
                );

            nmapping#set_starting_pairs_for_glueing [nd1, nd2];

            let glue_filt n1 n2 =
              tree1#is_initial_ancestor nd1 n1 && tree2#is_initial_ancestor nd2 n2
            in
            let removed_pairs, added_pairs, _ =
              glue_deletes_and_inserts options cenv tree1 tree2
                ~override:true ~downward:true ~no_moves:false ~glue_filt
                ~edits_opt:(Some edits)
                nmapping (new Node_mapping.c cenv)
            in
            let is_mov n1 n2 =
              [%debug_log "mid=%a n1=%a n2=%a" MID.ps mid nups n1 nups n2];
              if
                try
                  let pn1 = n1#initial_parent in
                  let pn2 = n2#initial_parent in
                  try
                    Array.iter
                      (fun x1 ->
                        if x1 != n1 then begin
                          let x1' = nmapping#find x1 in
                          if x1'#initial_parent == pn2 then begin
                            match edits#find_mov12 x1 x1' with
                            | Edit.Move(id, _, _, _) when !id = mid -> begin
                                if cenv#is_crossing_or_incompatible x1 x1' n1 n2 then begin
                                  [%debug_log "%a-%a is crossing with %a-%a"
                                    nups n1 nups n2 nups x1 nups x1'];
                                  raise Exit
                                end
                            end
                            | _ -> ()
                          end
                        end
                      ) pn1#initial_children;
                    false
                  with
                    Exit -> true
                with
                  _ -> false
              then
                true, None
              else
                true, Some mid
            in
            sync_edits options ~is_mov cenv edits removed_pairs added_pairs

          ) movs0
      end;

      let npairs0 =
        Xset.filter_map
          (fun (upair, kind) ->
            match kind with
            | LocalVariableInliningOrExtraction -> Some upair
            | _ -> None
          ) npairs0
      in
      let nnpairs0 = Xset.length npairs0 in
      if nnpairs0 > 0 then begin
        begin %debug_block
          [%debug_log "!!!!! %d starting pair(s) for glueing from decompose_moves:" nnpairs0];
          Xset.iter
            (fun (n1, n2) ->
              [%debug_log "%a-%a" nups n1 nups n2]
            ) npairs0
        end;

        nmapping#set_starting_pairs_for_glueing (Xset.to_list npairs0);

        let removed_pairs, added_pairs, _ =
          glue_deletes_and_inserts options cenv tree1 tree2
            ~override:true ~downward:true ~no_moves:false
            ~edits_opt:(Some edits)
            nmapping (new Node_mapping.c cenv)
        in
        let is_mov n1 n2 =
          [%debug_log "%a-%a" nups n1 nups n2];
          edits#is_crossing_with_untouched
            ?full_scan:None
            ?mask:None ?incompatible_only:None ?weak:None
            nmapping n1 n2,
          None
        in
        sync_edits options ~is_mov cenv edits removed_pairs added_pairs
      end;

      let dels0 = Xset.filter (fun x -> edits#mem_del x) dels0 in
      let inss0 = Xset.filter (fun x -> edits#mem_ins x) inss0 in

      let dels1, inss1 = elaborate_edits_for_delta options cenv tree1 tree2 nmapping edits in

      let dels, inss, _, npairs =
        if options#no_moves_flag then begin
          decompose_moves cenv tree1 tree2 ~force:true (fun _ _ -> true) options edits nmapping 0
        end
        else begin
          (*let is_common_pair n1 n2 =
            n1#data#is_common || n2#data#is_common
          in
          ignore (decompose_moves cenv tree1 tree2 is_common_pair options edits nmapping 1);*)

          let is_unnamed_or_changed_pair n1 n2 =
            let b =
            (not
               ((n1#data#eq n2#data(* ||
               match n1#data#orig_lab_opt, n2#data#orig_lab_opt with
               | Some o1, Some o2 -> o1 = o2
               | _ -> false*)
               ) &&
                (n1#data#is_named_orig && n2#data#is_named_orig ||
                cenv#has_non_trivial_value n1 && cenv#has_non_trivial_value n2)
               )) ||
            n1#data#move_disallowed || n2#data#move_disallowed ||
            n1#data#is_common || n2#data#is_common
            in
            [%debug_log "%a %a -> %B" labps n1 labps n2 b];
            b
          in
          let is_uncertain_pair n1 n2 =
            let b =
              try
                let pn1 = n1#initial_parent in
                let pn2 = n2#initial_parent in
                (
                 pn1#data#is_sequence && pn2#data#is_sequence ||
                 edits#mem_mov12 pn1 pn2 ||
                 (
                  (edits#mem_del pn1 || edits#mem_mov1 pn1) &&
                  (edits#mem_ins pn2 || edits#mem_mov2 pn2)
                 )
                ) &&
                match cenv#multiple_node_matches#find n1#data#_label with
                | _, [] | [], _ | [_], [_] -> raise Not_found
                | l1, l2 ->
                    begin %debug_block
                      [%debug_log "[%a] <--> [%a]" nsps l1 nsps l2];
                      let freq1 = List.length l1 in
                      let freq2 = List.length l2 in
                      [%debug_log "freq1=%d freq2=%d" freq1 freq2];
                    end;

                    let is_certain =
                      [%debug_log "%a-%a [%a]-[%a] %a" nps n1 nps n2 locps n1 locps n2 labps n1];

                      let get_mid1 n1 =
                        match edits#find_mov1 n1 with
                        | Edit.Move(id, _, _, _) -> !id
                        | _ -> raise Not_found
                      in
                      let is_map = _is_map tree1 tree2 nmapping in
                      try
                        let sn1 = find_nearest_anc_stmt n1 in
                        let sn2 = find_nearest_anc_stmt n2 in

                        [%debug_log "stmt pair: %a-%a: [%a]-[%a] %a-%a" nups sn1 nups sn2
                          locps sn1 locps sn2 labps sn1 labps sn2];

                        let same_move =
                          try
                            let mid = get_mid1 sn1 in
                            get_mid1 n1 = mid
                          with
                            Not_found -> false
                        in
                        [%debug_log "same_move=%B" same_move];

                        if same_move then
                          raise Exit;

                        let is_stable1 n =
                          match edits#find1 n with
                          | [] | [Edit.Relabel _] -> true
                          | _ -> false
                        in
                        let is_stable2 n =
                          match edits#find2 n with
                          | [] | [Edit.Relabel _] -> true
                          | _ -> false
                        in

                        let bn1 = get_bn sn1 in
                        let bn2 = get_bn sn2 in

                        is_map bn1 bn2 && is_map sn1 sn2 &&

                        let is_stable tree s is_stable x =
                          tree#is_initial_ancestor s x && is_stable x
                        in
                        let l1_s = List.filter (is_stable tree1 sn1 is_stable1) l1 in
                        let l2_s = List.filter (is_stable tree2 sn2 is_stable2) l2 in

                        begin %debug_block
                          let freq1_s = List.length l1_s in
                          let freq2_s = List.length l2_s in
                          [%debug_log "l1_s=[%a] (%d)" nsps l1_s freq1_s];
                          [%debug_log "l2_s=[%a] (%d)" nsps l2_s freq2_s];
                        end;

                        let cond_s =
                          match l1_s, l2_s with
                          | [], _ | _, [] -> true
                          | [n1_], [n2_] -> n1 != n1_ && n2 != n2_
                          | _ -> false
                        in
                        cond_s &&
                        let is_unstable tree s is_stable x =
                          tree#is_initial_ancestor s x && not (is_stable x)
                        in
                        let l1_u = List.filter (is_unstable tree1 sn1 is_stable1) l1 in
                        let l2_u = List.filter (is_unstable tree2 sn2 is_stable2) l2 in

                        begin %debug_block
                          let freq1_u = List.length l1_u in
                          let freq2_u = List.length l2_u in
                          [%debug_log "l1_u=[%a] (%d)" nsps l1_u freq1_u];
                          [%debug_log "l2_u=[%a] (%d)" nsps l2_u freq2_u];
                        end;

                        match l1_u, l2_u with
                        | [n1_], [n2_] when n1_ == n1 && n2_ == n2 -> begin
                            [%debug_log "%a [%a]-[%a]" labps n1 locps n1 locps n2];
                            true
                        end
                        | _ -> false

                      with
                        _ -> false
                    in
                    if is_certain then begin
                      [%debug_log "!!!!! is_certain=%B" is_certain];
                      raise Certain
                    end
                    else if
                      is_cross_boundary nmapping n1 n2 ||
                      is_crossing_with_untouched ~incompatible_only:true n1 n2
                    then
                      true
                    else
                      try
                        match edits#find_mov12 pn1 pn2 with
                        | Edit.Move(pm, pk, _, _) when !pk = Edit.Mpermutation -> begin
                            match edits#find_mov12 n1 n2 with
                            | Edit.Move(m, k, _, _) when !k = Edit.Mpermutation && !m = !pm -> begin
                                let freq1' =
                                  List.length (List.filter (fun x -> not (is_stable1 x)) l1)
                                in
                                let freq2' =
                                  List.length (List.filter (fun x -> not (is_stable2 x)) l2)
                                in
                                [%debug_log "freq1'=%d freq2'=%d" freq1' freq2'];
                                freq1' > 1 || freq2' > 1
                            end
                            | _ -> true
                        end
                        | _ -> true
                      with
                        _ -> true
              with
              | Certain -> false
              | _ -> begin
                  let freq1 = List.length (try cenv#get_use1 (Edit.get_bid n1) with _ -> []) in
                  let freq2 = List.length (try cenv#get_use2 (Edit.get_bid n2) with _ -> []) in
                  [%debug_log "freq1: %a -> %d" labps n1 freq1];
                  [%debug_log "freq2: %a -> %d" labps n2 freq2];
                  freq1 > 3 && freq2 > 3
                end
            in
            [%debug_log "%a %a -> %B" labps n1 labps n2 b];
            b
          in
          let get_mid n =
            match edits#find_mov1 n with
            | Edit.Move(id, _, _, _) -> !id
            | _ -> raise Not_found
          in
          let is_unstable_pair n1 n2 =
            let b =
              not n1#data#is_boundary && not n2#data#is_boundary &&
              try
                Sourcecode.scan_ancestors ~moveon:(fun x -> not (is_stable1 x)) n1
                  (fun a ->
                    let a' = nmapping#find a in
                    [%debug_log "a=%a a'=%a" nps a nps a'];
                    if is_stable_map a a' then begin

                      if tree2#is_initial_ancestor a' n2 then
                        [%debug_log "a'=%a is an ancestor of n2=%a" nps a' nps n2]
                      else if
                        n1#initial_nchildren = 0 &&
                        let mid_opt =
                          try
                            let m = get_mid n1 in
                            [%debug_log "m=%a" MID.ps m];
                            Some m
                          with _ -> None
                        in
                        let pmid_opt =
                          try
                            let pm = get_mid n1#initial_parent in
                            [%debug_log "pm=%a" MID.ps pm];
                            Some pm
                          with _ -> None
                        in
                        match mid_opt, pmid_opt with
                        | Some m, Some pm -> m <> pm
                        | Some _, None when begin
                            n1#data#has_non_trivial_value && n1#data#eq n2#data &&
                            try
                              let p1 = n1#initial_parent in
                              let p2 = n2#initial_parent in
                              nmapping#mem_dom p1 && nmapping#mem_cod p2
                              (*not
                                (
                                 _is_map tree1 tree2 nmapping p1 p2 ||
                                 nmapping#mem_dom p1 ||
                                 nmapping#mem_cod p2
                                )*)
                            with _ -> false
                        end -> begin
                          [%debug_log "!!! %a-%a [%a]-[%a] %a" nups n1 nups n2 locps n1 locps n2 labps n1];
                          false
                        end
                        | _ when nmapping#is_locked_mapping n1 n2 -> false
                        | _ -> true
                      then begin
                        [%debug_log "@"];
                        raise Exit
                      end
                      else if
                        let lab1 = n1#data#label in
                        Array.exists
                          (fun x' ->
                            not (nmapping#mem_cod x') && x'#data#label = lab1
                          ) a'#initial_children
                      then begin
                        [%debug_log "@"];
                        raise Exit
                      end
                      else
                        Sourcecode.scan_descendants ~moveon:(fun x -> not (is_stable1 x)) n1
                          (fun d ->
                            try
                              let d' = nmapping#find d in
                              [%debug_log "d=%a d'=%a" nps d nps d'];
                              if
                                tree2#is_initial_ancestor a' d' &&
                                is_stable_map d d' &&
                                not (tree2#is_initial_ancestor n2 d')
                              then
                                raise Exit
                            with
                              Not_found -> ()
                          )

                    end
                  );
                false
              with
              | Exit -> true
              | _ -> false
            in
            [%debug_log "%a-%a -> %B" nps n1 nps n2 b];
            b
          in
          let is_bad_pair n1 n2 =
              is_unnamed_or_changed_pair n1 n2 || is_uncertain_pair n1 n2 || is_unstable_pair n1 n2
          in
          decompose_moves cenv tree1 tree2 ~weak:true is_bad_pair options edits nmapping 16
        end
      in (* dels, inss, _, npairs *)
      (*if not options#no_moves_flag then begin
        let starting_pairs = Xset.create 0 in
        let mov_tbl1 = Hashtbl.create 0 in
        let mov_tbl2 = Hashtbl.create 0 in
        let mov_tbl = Hashtbl.create 0 in
        Xset.iter
          (fun x1 ->
            try
              let n1 = x1#initial_parent in
              match edits#find_mov1 n1 with
              | Edit.Move(mid, kind, _, (_, info2, _)) as mov -> begin
                  let n2 = Info.get_node info2 in
                  [%debug_log "adding %a %a-%a" MID.ps !mid nps n1 nps n2];
                  Xset.add starting_pairs (n1, n2);
                  Hashtbl.add mov_tbl1 x1 !mid;
                  Hashtbl.add mov_tbl !mid (n1, n2)
              end
              | _ -> ()
            with _ -> ()
          ) dels;
        Xset.iter
          (fun x2 ->
            try
              let n2 = x2#initial_parent in
              match edits#find_mov2 n2 with
              | Edit.Move(mid, kind, (_, info1, _), _) as mov -> begin
                  let n1 = Info.get_node info1 in
                  [%debug_log "adding %a %a-%a" MID.ps !mid nps n1 nps n2];
                  Xset.add starting_pairs (n1, n2);
                  Hashtbl.add mov_tbl2 n2 !mid;
                  Hashtbl.add mov_tbl !mid (n1, n2)
              end
              | _ -> ()
            with _ -> ()
          ) inss;
        if Xset.length starting_pairs > 0 then begin
          nmapping#set_starting_pairs_for_glueing (Xset.to_list starting_pairs);
          let removed_pairs, added_pairs, _ =
            glue_deletes_and_inserts options cenv tree1 tree2
              ~override:true ~downward:true ~no_moves:false
              nmapping (new Node_mapping.c cenv)
          in
          let is_mov n1 n2 =
            try
              let m = Hashtbl.find mov_tbl1 n1 in
              true, Some m
            with
              Not_found ->
                try
                  let m = Hashtbl.find mov_tbl2 n2 in
                  true, Some m
                with
                  Not_found ->
                    let res = ref (false, None) in
                    try
                      Hashtbl.iter
                        (fun m (r1, r2) ->
                          if
                            n1 == r1 && n2 == r2 ||
                            tree1#is_initial_ancestor r1 n1 &&
                            tree2#is_initial_ancestor r2 n2
                          then begin
                            res := (true, Some m);
                            raise Exit
                          end
                        ) mov_tbl;
                      !res
                    with
                      Exit -> !res
          in
          sync_edits options ~is_mov tree1 tree2 edits removed_pairs added_pairs
        end
      end;*)

      let glue_filt n1 n2 =
        n1#data#relabel_allowed n2#data ||
        not n1#data#is_named_orig && not n2#data#is_named_orig &&
        n1#data#anonymized_label = n2#data#anonymized_label
      in
      let glue_filt =
        if options#no_moves_flag then begin
          fun n1 n2 -> n1#data#anonymized_label = n2#data#anonymized_label
        end
        else
          glue_filt
      in
      let rec find_mapped_anc nmap is_mov add tree' n =
        (*[%debug_log "n=%a" nps n];*)
        try
          let n' = nmap n in
          if is_mov n n'(* && not (n#data#eq n'#data)*) then
            find_mapped_anc nmap is_mov add tree' n#initial_parent
          else
            [%debug_log "n=%a n'=%a" nps n nps n'];
            add n n'
        with
          Not_found ->
            try
              find_mapped_anc nmap is_mov add tree' n#initial_parent
            with _ -> ()
      in
      let find_mapped_desc nmap is_mov add (*tree'*)_ n =
        let found = ref false in
        let pred n =
          try
            let n' = nmap n in
            let b = not (is_mov n n') in
            if b then
              found := true;
            b
          with
            Not_found -> false
        in
        let moveon _ = not !found in
        try
          let dl = get_p_descendants ~moveon pred n in
          List.iter
            (fun d ->
              let d' = nmap d in
              [%debug_log "d=%a d'=%a" nps d nps d'];
              add d d'
            ) dl
        with
          _ -> ()
      in
      let starting_pairs = Xset.create 0 in
      let add12 n n' = Xset.add starting_pairs (n#gindex, n, n') in
      let add21 n' n = Xset.add starting_pairs (n#gindex, n, n') in
      [%debug_log "anc from dels0:"];
      Xset.iter (find_mapped_anc nmapping#find edits#mem_mov12 add12 tree2) dels0;
      [%debug_log "anc from inss0:"];
      Xset.iter (find_mapped_anc nmapping#inv_find edits#mem_mov21 add21 tree1) inss0;
      [%debug_log "anc from dels1:"];
      Xset.iter (find_mapped_anc nmapping#find edits#mem_mov12 add12 tree2) dels1;
      [%debug_log "anc from inss1:"];
      Xset.iter (find_mapped_anc nmapping#inv_find edits#mem_mov21 add21 tree1) inss1;
      [%debug_log "anc from dels:"];
      Xset.iter (find_mapped_anc nmapping#find edits#mem_mov12 add12 tree2) dels;
      [%debug_log "anc from inss:"];
      Xset.iter (find_mapped_anc nmapping#inv_find edits#mem_mov21 add21 tree1) inss;

      [%debug_log "desc from dels0:"];
      Xset.iter (find_mapped_desc nmapping#find edits#mem_mov12 add12 tree2) dels0;
      [%debug_log "desc from inss0:"];
      Xset.iter (find_mapped_desc nmapping#inv_find edits#mem_mov21 add21 tree1) inss0;
      [%debug_log "desc from dels1:"];
      Xset.iter (find_mapped_desc nmapping#find edits#mem_mov12 add12 tree2) dels1;
      [%debug_log "desc from inss1:"];
      Xset.iter (find_mapped_desc nmapping#inv_find edits#mem_mov21 add21 tree1) inss1;
      [%debug_log "desc from dels:"];
      Xset.iter (find_mapped_desc nmapping#find edits#mem_mov12 add12 tree2) dels;
      [%debug_log "desc from inss:"];
      Xset.iter (find_mapped_desc nmapping#inv_find edits#mem_mov21 add21 tree1) inss;

      let starting_pair_list =
        List.map (fun (_, n1, n2) -> n1, n2)
          (List.fast_sort
             (fun (i, _, _) (j, _, _) -> Stdlib.compare j i)
             (Xset.to_list starting_pairs))
      in

      let npairs =
        Xset.filter_map
          (fun (upair, kind) ->
            match kind with
            | StableContext -> Some upair
            | _ -> None
          ) npairs
      in
      let nnpairs = Xset.length npairs in
      let starting_pair_list =
        if nnpairs > 0 then begin
          [%debug_log "!!!!!! %d starting pair(s) for glueing from decompose_moves:" nnpairs];
          let l = ref starting_pair_list in
          Xset.iter
            (fun ((n1, n2) as np) ->
              let _ = n1 in
              let _ = n2 in
              [%debug_log "%a-%a" nups n1 nups n2];
              l := np :: !l
            ) npairs;
          !l
        end
        else
          starting_pair_list
      in

      nmapping#set_starting_pairs_for_glueing starting_pair_list;
      let is_move n1 n2 =
        edits#mem_mov12 n1 n2 || is_crossing_with_untouched ~weak:true n1 n2(* ||
        let ca1 = n1#initial_parent#initial_children in
        let ca2 = n2#initial_parent#initial_children in
        let nc1 = Array.length ca1 in
        nc1 > 1 && (Array.length ca2) > 1 &&
        let b =
          try
            for i = n1#initial_pos + 1 to nc1 - 1 do
              let rn = ca1.(i) in
              if not rn#data#is_named_orig then
                for j = 0 to n2#initial_pos - 1 do
                  let ln = ca2.(j) in
                  if
                    not ln#data#is_named_orig &&
                    rn#data#anonymized_label = ln#data#anonymized_label
                  then
                    raise Exit
                done
            done;
            false
          with
            Exit -> true
        in
        b*)
      in
      if not options#no_glue_flag then begin
        [%debug_log "@"];
        (*begin
          match lang#elaborate_edits with
          | Some f -> f options cenv nmapping edits
          | None -> ()
        end;*)
        let rps, aps, _ =
          glue_deletes_and_inserts options cenv tree1 tree2
            ~no_mapping_override:true
            ~no_moves:true
            ~extend_move
            ~add_move
            ~last:true
            ~is_move
            ~glue_filt
            ~use_binding_info
            ~rely_on_binding_info
            ~rely_on_context:true
            ~edits_opt:(Some edits)
            nmapping pre_nmapping
        in
        (*let is_mov n1 n2 =
          if is_move n1 n2 then
            true, Some options#moveid_generator#gen
          else
            false, None
        in*)
        sync_edits(* ~is_mov*) options cenv edits rps aps;
        (*eliminate_false_moves options cenv edits nmapping*)
      end;

      if options#no_moves_flag then begin
        let filt = fun _ _ -> true in
        ignore (decompose_moves cenv tree1 tree2 ~force:true filt options edits nmapping 0);
      end;

      [%debug_log "done."];
    end; (* if options#dump_delta_flag || options#conservative_flag *)

    (*[%debug_log "pre_nmapping:\n%s\n" pre_nmapping#to_string];*)
    let nmap = nmapping#find in
    let nmap' = nmapping#inv_find in
    let changed_flag = ref true in
    let mid_change_tbl = Hashtbl.create 0 in
    while !changed_flag do
      changed_flag := false;

    let relabel_allowed n1 n2 =
      n1#data#relabel_allowed n2#data &&
      (not use_binding_info || cenv#is_possible_rename n1 n2)
    in

    edits#iter_deletes
      (function
        | Edit.Delete(_, info, _) as del -> begin
            try
              let nd = Info.get_node info in
              begin
                try
                  let nd_opt' = ref None in
                  let cs' =
                    Array.map
                      (fun c ->
                        let c' = nmapping#find c in
                        match edits#find12 c c' with
                        | [] | [Edit.Relabel _] -> begin
                            let n' = c'#initial_parent in
                            match !nd_opt' with
                            | None -> begin
                                nd_opt' := Some n';
                                c'
                            end
                            | Some x when x == n' -> c'
                            | _ -> raise Not_found
                        end
                        | _ -> raise Not_found
                      ) nd#initial_children
                  in
                  match !nd_opt' with
                  | Some nd' when nd'#initial_children = cs' -> begin
                      if
                        (*not options#no_moves_flag || *)not (is_crossing_with_untouched nd nd')
                      then begin
                        let ins = edits#find_ins nd' in
                        if not (nd#data#eq nd'#data) then begin
                          if relabel_allowed nd nd' then
                            edits#add_edit (Edit.make_relabel nd nd')
                          else
                            raise Not_found
                        end;
                        [%debug_log "del-ins pair found: %s-%s" (Edit.to_string del) (Edit.to_string ins)];
                        edits#remove_edit del;
                        edits#remove_edit ins;
                        ignore (nmapping#add_settled nd nd');
                        changed_flag := true;
                        raise Exit
                      end
                  end
                  | _ -> ()
                with
                  Not_found -> ()
              end;

              let pnd = nd#initial_parent in

              let nd', pnd' =
                try
                  let nd' = pre_nmapping#find nd in
                  [%debug_log "pre_nmapping: %a -> %a" nups nd nups nd'];
                  nd', nd'#initial_parent
                with
                  _ ->
                    let pnd' = nmapping#find pnd in

                    let cl' =
                      Array.fold_left
                        (fun l c ->
                          if c != nd then begin
                            let c' = nmap c in
                            if c'#initial_parent == pnd' then
                              c' :: l
                            else
                              raise Not_found
                          end
                          else
                            nd :: l
                        ) [] pnd#initial_children
                    in
                    let l, cl =
                      Array.fold_left
                        (fun (l, cl) c' ->
                          if nmapping#mem_cod c' then begin
                            let c = nmap' c' in
                            if c#initial_parent == pnd then
                              l, c' :: cl
                            else
                              raise Not_found
                          end
                          else
                            c' :: l, nd :: cl
                        ) ([], []) pnd'#initial_children
                    in
                    if cl <> cl' then
                      raise Not_found;

                    match l with
                    | [nd'] -> nd', pnd'
                    | _ -> raise Not_found
              in

              let base_cond =
                let ds =
                  Sourcecode.find_nearest_mapped_descendant_nodes nmapping#mem_dom nd
                in
                let ds' =
                  Sourcecode.find_nearest_mapped_descendant_nodes nmapping#mem_cod nd'
                in
                List.map nmap ds = ds'
              in

              if base_cond then

              let ins = edits#find_ins nd' in

              let cond0 =
                try
                  nmapping#find pnd == pnd' &&
                  match edits#find12 pnd pnd' with
                  | [] | [Edit.Relabel _] -> true
                  | _ -> false
                with
                  Not_found -> false
              in
              let cond1 =
                let ok = ref false in
                Array.for_all
                  (fun c ->
                    try
                      let c' = nmapping#find c in
                      c'#initial_parent == nd' &&
                      match edits#find12 c c' with
                      | [] | [Edit.Relabel _] -> ok := true; true
                      | _ -> false
                    with
                      Not_found -> true
                  ) nd#initial_children &&
                Array.for_all
                  (fun c' ->
                    try
                      let c = nmapping#inv_find c' in
                      c#initial_parent == nd &&
                      match edits#find12 c c' with
                      | [] | [Edit.Relabel _] -> true
                      | _ -> false
                    with
                      Not_found -> true
                  ) nd'#initial_children && !ok
              in
              if
                (cond0 || cond1) && (not options#no_moves_flag || not (is_crossing_with_untouched nd nd'))
              then begin
                if not (nd#data#eq nd'#data) then begin
                  if relabel_allowed nd nd' then
                    edits#add_edit (Edit.make_relabel nd nd')
                  else
                    raise Not_found
                end;
                begin
                  match ins with
                  | Edit.Insert(_, info', _) -> begin
                      (*let nd' = Info.get info' in*)
                      if is_crossing_with_untouched nd nd' then
                        let mid = options#moveid_generator#gen in
                        begin
                          try
                            let ml = ref [] in
                            Array.iteri
                              (fun i c ->
                                match edits#find_mov1 c with
                                | Edit.Move(m, _, (_, _), (info2, _)) -> begin
                                    let c' = Info.get_node info2 in
                                    [%debug_log "%a -> %a" nups c nups c'];
                                    if nd'#initial_children.(i) == c' then
                                      ml := m :: !ml
                                    else
                                      raise Exit
                                end
                                | _ -> assert false
                              ) nd#initial_children;
                            List.iter
                              (fun m ->
                                [%debug_log "%a -> %a" MID.ps !m MID.ps mid];
                                Hashtbl.replace mid_change_tbl !m mid
                              ) !ml
                          with
                            _ -> ()
                        end;
                        let mov = Edit.make_move_permutation mid info info' in
                        edits#add_edit mov;
                  end
                  | _ -> assert false
                end;
                [%debug_log "del-ins pair found: %s-%s" (Edit.to_string del) (Edit.to_string ins)];
                edits#remove_edit del;
                edits#remove_edit ins;
                ignore (nmapping#add_settled nd nd');
                (*if not base_cond then begin
                  match ins with
                  | Edit.Insert(_, info', _) ->
                      let mid = options#moveid_generator#gen in
                      let mov = Edit._make_move mid Edit.Modd info info' in
                      edits#add_edit mov
                  | _ -> assert false
                end;*)
                changed_flag := true
              end
            with
            | Not_found -> ()
            | Exit -> ()
        end
        | _ -> ()
      )
    done;

    if Hashtbl.length mid_change_tbl > 0 then begin
      edits#iter_moves
        (function
          | Edit.Move(mid, _, _, _) -> begin
              try
                let id = Hashtbl.find mid_change_tbl !mid in
                mid := id
              with
                Not_found -> ()
          end
          | _ -> assert false
        )
    end;

    begin %debug_block
      [%debug_log "CHECKING BEFORE FINAL FIXUP..."];
      tree1#fast_scan_whole_initial
        (fun n1 ->
          if nmapping#mem_dom n1 then
            let n1' = nmapping#find n1 in
            if not (n1#data#eq n1'#data) then
              if not (edits#mem_rel12 n1 n1') then
                [%debug_log "relabel not found for %s-%s"
                  n1#initial_to_string n1'#initial_to_string]
          else
            if not (edits#mem1 n1) then
              [%debug_log "delete not found for %s" n1#initial_to_string]
        );
      tree2#fast_scan_whole_initial
        (fun n2 ->
          if nmapping#mem_cod n2 then
            let n2' = nmapping#inv_find n2 in
            if not (n2'#data#eq n2#data) then
              if not (edits#mem_rel12 n2' n2) then
                [%debug_log "relabel not found for %s-%s"
                  n2'#initial_to_string n2#initial_to_string]
          else
            if not (edits#mem2 n2) then
              [%debug_log "insert not found for %s" n2#initial_to_string]
        );
      [%debug_log "DONE."]
    end;

    (* final fixup *)

    edits#iter_relabels
      (function
        | Edit.Relabel(movrel, (i1, _), (i2, _)) ->
            let n1 = Info.get_node i1 in
            let n2 = Info.get_node i2 in
            if edits#mem_mov12 n1 n2 then
              movrel := true
        | _ -> assert false
      );

    (* count inserts and deletes *)
    edits#iter_deletes_and_inserts
      (function
        | Edit.Delete(whole, info, _) ->
            if whole then
              assert false
            else begin
              Info.set_size info 1;
            end

        | Edit.Insert(whole, info, _) ->
            if whole then
              assert false
            else begin
              Info.set_size info 1;
            end
        | _ -> assert false
      );

    if true then begin
      [%debug_log "tidying up..."];
      let add_move n1 n2 =
        [%debug_log "%a-%a" nups n1 nups n2];
        if edits#mem_mov12 n1 n2 then
          [%debug_log "already contained in edits"]
        else
        let mid, kind =
          try
            let pn1 = n1#initial_parent in
            let pn2 = n2#initial_parent in
            if
              pn1#initial_nchildren = 1 || pn2#initial_nchildren = 1 ||
              is_extendable_move tree1 tree2 nmapping n1 n2
            then begin
              [%debug_log "@"];
              match edits#find_mov12 pn1 pn2 with
              | Edit.Move(mid, k, _, _) -> !mid, !k
              | _ -> raise Not_found
            end
            else
              raise Not_found
          with
            _ -> options#moveid_generator#gen, Edit.Mnormal
        in
        let mov = Edit._make_move mid kind (mkinfo n1) (mkinfo n2) in
        [%debug_log "generated move: %s" (Edit.to_string mov)];
        edits#add_edit mov
      in

      edits#iter_deletes
        (function
          | Edit.Delete(_, info, _) as del -> begin
              let nd1 = Info.get_node info in
              if nd1#data#is_named then begin
                try
                  let pnd1 = nd1#initial_parent in
                  if
                    pnd1#data#is_boundary && pnd1#data#is_named &&
                    pnd1#data#get_name = nd1#data#get_name
                  then begin
                    let pnd2 = nmapping#find pnd1 in
                    if
                      pnd2#data#is_boundary && pnd2#data#is_named
                    then begin
                      [%debug_log "nd1=%a" nps nd1];
                      [%debug_log "pnd1=%a" nps pnd1];
                      [%debug_log "pnd2=%a" nps pnd2];
                      let pname2 = pnd2#data#get_name in
                      let alab1 = nd1#data#_anonymized_label in
                      let nl2 = ref [] in
                      Array.iter
                        (fun n2 ->
                          if
                            edits#mem_ins n2 &&
                            not (nd1#data#eq n2#data) &&
                            n2#data#_anonymized_label = alab1 &&
                            n2#data#is_named && n2#data#get_name = pname2
                          then begin
                            nl2 := n2 :: !nl2
                          end
                        ) pnd2#initial_children;
                      match !nl2 with
                      | [nd2] -> begin
                          [%debug_log "nd2=%a" nps nd2];
                          ignore (nmapping#add_unsettled nd1 nd2);
                          add_move nd1 nd2;
                          edits#add_edit (Edit.make_relabel nd1 nd2);
                          let ins = edits#find_ins nd2 in
                          edits#remove_edit del;
                          edits#remove_edit ins
                      end
                      | _ -> ()
                    end
                  end
                with _ -> ()
              end
          end
          | _ -> assert false
        );

      cenv#multiple_node_matches#iter
        (fun (_lab, _nds1, _nds2) ->
          let nds1 = List.filter (fun x -> not (nmapping#mem_dom x)) _nds1 in
          let nds2 = List.filter (fun x -> not (nmapping#mem_cod x)) _nds2 in
          match nds1, nds2 with
          | [nd1], [nd2] -> begin
              [%debug_log "%s nds1=[%a] nds2=[%a]"
                (Label.to_string (Obj.obj _lab)) nsps nds1 nsps nds2];
              if
                nd1#initial_nchildren = 0 && nd2#initial_nchildren = 0 &&
                try
                  nmapping#find nd1#initial_parent == nd2#initial_parent
                with _ -> false
              then begin
                ignore (nmapping#add_unsettled nd1 nd2);
                add_move nd1 nd2;
                let del = edits#find_del nd1 in
                let ins = edits#find_ins nd2 in
                edits#remove_edit del;
                edits#remove_edit ins
              end
          end
          | _::_, _::_(* when false*) -> begin
              [%debug_log "%s nds1=[%a] nds2=[%a]"
                (Label.to_string (Obj.obj _lab)) nsps nds1 nsps nds2];
              let tbl1 = Nodetbl.create 0 in
              let tbl2 = Nodetbl.create 0 in
              let tbl_add tbl mem n =
                if n#initial_nchildren = 0 then
                  let moveon_ x = not x#data#is_boundary in
                  try
                    let an = Sourcecode.find_nearest_p_ancestor_node ~moveon_ mem n in
                    try
                      let nl = Nodetbl.find tbl an in
                      Nodetbl.replace tbl an (n::nl)
                    with
                      Not_found -> Nodetbl.add tbl an [n]
                  with
                    _ -> ()
              in
              List.iter (tbl_add tbl1 nmapping#mem_dom) nds1;
              List.iter (tbl_add tbl2 nmapping#mem_cod) nds2;
              Nodetbl.iter
                (fun an1 nl1 ->
                  try
                    let nl2 = Nodetbl.find tbl2 (nmapping#find an1) in
                    [%debug_log "%s nl1=[%a] nl2=[%a]"
                      (Label.to_string (Obj.obj _lab)) nsps nl1 nsps nl2];

                    match nl1, nl2 with
                    | [n1], [n2] -> begin

                        ignore (nmapping#add_unsettled n1 n2);
                        let del = edits#find_del n1 in
                        let ins = edits#find_ins n2 in
                        edits#remove_edit del;
                        edits#remove_edit ins;

                        let cur1 = ref n1 in
                        let cur2 = ref n2 in

                        let midl = ref [(n1, n2)] in
                        begin
                          try
                            while true do
                              let pn1 = (!cur1)#initial_parent in
                              let pn2 = (!cur2)#initial_parent in
                              if
                                pn1#initial_nchildren = 1 && pn2#initial_nchildren = 1 &&
                                not (pn1#data#eq pn2#data) &&
                                not (nmapping#mem_dom pn1) && not (nmapping#mem_cod pn2) &&
                                pn1#data#_anonymized_label = pn2#data#_anonymized_label
                              then begin
                                ignore (nmapping#add_unsettled pn1 pn2);
                                midl := (pn1, pn2) :: !midl;
                                edits#add_edit (Edit.make_relabel pn1 pn2);
                                let del = edits#find_del pn1 in
                                let ins = edits#find_ins pn2 in
                                edits#remove_edit del;
                                edits#remove_edit ins;
                                cur1 := pn1;
                                cur2 := pn2
                              end
                              else
                                raise Exit
                            done
                          with
                            _ -> ()
                        end;
                        add_move !cur1 !cur2;
                        match !midl with
                        | [] -> assert false
                        | [(n1, n2)] -> add_move n1 n2
                        | _::pl -> begin
                            List.iter
                              (fun (x1, x2) ->
                                add_move x1 x2
                              ) pl
                        end
                    end
                    | _ -> ()
                  with
                    _ -> ()
                ) tbl1;

          end
          | _ -> ()
        )
    end;

    let delete_exclude_map = Nodetbl.create 0 in
    let insert_exclude_map = Nodetbl.create 0 in
    let relabel_exclude_map1 = Nodetbl.create 0 in
    let relabel_exclude_map2 = Nodetbl.create 0 in
    let move_exclude_map1 = Nodetbl.create 0 in
    let move_exclude_map2 = Nodetbl.create 0 in
    let insert_link_map = Nodetbl.create 0 in
    let delete_link_map = Nodetbl.create 0 in
    let relabel_link_map1 = Nodetbl.create 0 in
    let relabel_link_map2 = Nodetbl.create 0 in
    let move_link_map1 = Nodetbl.create 0 in
    let move_link_map2 = Nodetbl.create 0 in

    let rec trace_link map nd =
      try
        let nds = Nodetbl.find map nd in
        nd::(List.concat_map (trace_link map) nds)
      with Not_found -> [nd]
    in

    let get_excludes exclude_map link_map nd =
      let nds = trace_link link_map nd in

      [%debug_log "(%a): members: [%a]" nups nd nsps nds];

      let excludes =
        List.fold_left
          (fun l nd ->
            let e =
              try
                Nodetbl.find exclude_map nd
              with
                Not_found -> []
            in

            [%debug_log "(%a): excludes: [%s]" nups nd
              (Xlist.to_string (fun i -> UID.to_string (Info.get_uid i)) ";" e)];

            Xlist.union l e
          ) [] nds
      in

      [%debug_log "(%a): [%s]" nups nd
        (Xlist.to_string (fun i -> UID.to_string (Info.get_uid i)) ";" excludes)];

      excludes
    in (* end of func get_excludes *)

    let mkexcl = List.map mkinfo in
    let map_add m k v =

      [%debug_log "(link) map_add: %a -> %a" nups k nups v];

      try
        let vs = Nodetbl.find m k in
        if not (List.mem v vs) then
          Nodetbl.replace m k (v::vs)
      with
        Not_found -> Nodetbl.add m k [v]
    in (* end of func map_add *)



    [%debug_log "GROUPING EDITS..."];

    let split_hunk_flag = options#split_hunk_flag in(*!!!!!*)

    let check_hunk_boundary =(*!!!!!*)
      let check pnd cnd =
        Label.is_hunk_boundary (getlab pnd) (getlab cnd)
      in
      if split_hunk_flag then
        check
      else
        fun _ _ -> false
    in

    let handle_excludes =(*!!!!!*)
      let normal (*tree*) w eref (*nd*)_ children filt =
        if w then
          !eref
        else
          mkexcl (List.filter filt children)
      in
      let split (*tree*) (*w*)_ (*eref*)_ nd children filt =
        (*let whole =
          try
            tree#scan_whole_initial_subtree nd
              (fun n -> if filt n then raise Exit);
            true
          with
            Exit -> false
        in
        [%debug_log "whole=%B" whole];
        if whole then*)
          mkexcl
            (List.filter
               (fun n ->
                 filt n || check_hunk_boundary nd n
               ) children)
        (*else
          normal tree w eref nd children filt*)
      in
      if split_hunk_flag then
        split
      else
        normal
    in

    edits#iter (* group edits *)
      (fun ed ->
        [%debug_log "[grouping] %s" (Edit.to_string ed)];

        match ed with
        | Edit.Delete(whole, info, excludes) -> begin
            let nd = Info.get_node info in
            let ichildren = Array.to_list nd#initial_children in
            let excl =
              handle_excludes (*tree1*) whole excludes nd ichildren
                nmapping#mem(* not deleted *)(*!!!!!*)
              (*if whole then
                !excludes
              else
                mkexcl (List.filter nmapping#mem ichildren)*)
            in

            begin %debug_block
              [%debug_log "[grouping] Delete: children of\t <%a>: [%a]" nups nd nsps ichildren];
              [%debug_log "[grouping] Delete: excl: [%s]" (Xlist.to_string Info.to_string ", " excl)];
            end;

            if nd#has_initial_parent then begin
              let pnd = nd#initial_parent in
              (*let w =
                try
                  tree1#scan_whole_initial_subtree pnd
                    (fun n -> if nmapping#mem n then raise Exit);
                  true
                with
                  Exit -> false
              in!!!!!*)
              if
                not (nmapping#mem pnd) (* pnd is deleted *) &&
                not ((*w &&*) check_hunk_boundary pnd nd)(*!!!!!*)
              then
                map_add delete_link_map pnd nd
            end;

            Nodetbl.add delete_exclude_map nd excl;

            [%debug_log "[grouping] delete_exclude_map: added: %a -> [%s]"
              nups nd (Xlist.to_string Info.to_string ", " excl)]
        end
        | Edit.Insert(whole, info, excludes) -> begin
            let nd = Info.get_node info in
            let ichildren = Array.to_list nd#initial_children in

            [%debug_log "[grouping] Insert: whole=%B children of %a: [%a]" whole nups nd nsps ichildren];

            let excl =
              handle_excludes (*tree2*) whole excludes nd ichildren
                nmapping#mem_cod(* not inserted *)(*!!!!!*)
              (*if whole then
                !excludes
              else
                mkexcl (List.filter nmapping#mem_cod ichildren)*)
            in

            [%debug_log "[grouping] Insert: excl: [%s]" (Xlist.to_string Info.to_string ", " excl)];

            if nd#has_initial_parent then begin
              let pnd = nd#initial_parent in
              (*let w =
                try
                  tree1#scan_whole_initial_subtree pnd
                    (fun n -> if nmapping#mem_cod n then raise Exit);
                  true
                with
                  Exit -> false
              in!!!!!*)
              if
                not (nmapping#mem_cod pnd) (* pnd is inserted *) &&
                not ((*w &&*) check_hunk_boundary pnd nd)(*!!!!!*)
              then
                map_add insert_link_map pnd nd
            end;

            Nodetbl.add insert_exclude_map nd excl;

            [%debug_log "[grouping] insert_exclude_map: added: %a -> [%s]"
              nups nd (Xlist.to_string Info.to_string ", " excl)]
        end
        | Edit.Relabel(_, (info1, _), (info2, _)) ->
            if options#group_relabels_flag then

              let nd1 = Info.get_node info1 in
              let nd2 = Info.get_node info2 in

              [%debug_log "[grouping] Relabel: %a collapsed=%B" nups nd1 nd1#is_collapsed];
              [%debug_log "[grouping] Relabel: %a collapsed=%B" nups nd2 nd2#is_collapsed];

              let filt1 nd =
                match edits#find1 nd with
                | [] -> true
                | [Edit.Relabel(_, _, (i2, _))] -> begin
                    let n2 = Info.get_node i2 in
                    if n2#has_initial_parent then
                      not (n2#initial_parent = nd2)
                    else
                      true
                end
                | [Edit.Relabel(_, _, (i2, _));Edit.Move(_, s, _, _)]
                | [Edit.Move(_, s, _, _);Edit.Relabel(_, _, (i2, _))] -> begin
                    let n2 = Info.get_node i2 in
                    if n2#has_initial_parent then
                      not (!s = Edit.Mnormal && n2#initial_parent == nd2)
                    else
                      true
                end
                | [_] -> true
                | eds ->
                    Xprint.message "[grouping] edits for %a:\n%s" nups nd
                      (Xlist.to_string Edit.to_string "\n" eds);
                    assert false
              in
              let filt2 nd =
                match edits#find2 nd with
                | [] -> true
                | [Edit.Relabel(_, (i1, _), _)] -> begin
                    let n1 = Info.get_node i1 in
                    if n1#has_initial_parent then
                      not (n1#initial_parent = nd1)
                    else
                      true
                end
                | [Edit.Relabel(_, (i1, _), _);Edit.Move(_, s, _, _)]
                | [Edit.Move(_, s, _, _);Edit.Relabel(_, (i1, _), _)] -> begin
                    let n1 = Info.get_node i1 in
                    if n1#has_initial_parent then
                      not (!s = Edit.Mnormal && n1#initial_parent = nd1)
                    else
                      true
                end
                | [_] -> true
                | eds ->
                    Xprint.message "[grouping] edits for %a:\n%s" nups nd
                      (Xlist.to_string Edit.to_string "\n" eds);
                    assert false
              in

              let children1 = Array.to_list nd1#initial_children in
              let children2 = Array.to_list nd2#initial_children in

              let excl1 = mkexcl (List.filter filt1 children1) in
              let excl2 = mkexcl (List.filter filt2 children2) in

              [%debug_log ("\n[grouping] Relabel: children1 of\t <%a>: [%a]\n" ^^
                         "[grouping] Relabel: excl1: [%s]\n" ^^
                         "[grouping] Relabel children2 of\t <%a>: [%a]\n" ^^
                         "[grouping] Relabel: excl2: [%s]\n" ^^
                         "[grouping] relabel_exclude_map1: added: %a -> [%s]\n" ^^
                         "[grouping] relabel_exclude_map2: added: %a -> [%s]")
                nups nd1 nsps children1
                (Xlist.to_string Info.to_string ", " excl1)
                nups nd2 nsps children2
                (Xlist.to_string Info.to_string ", " excl2)
                nups nd1 (Xlist.to_string Info.to_string ", " excl1)
                nups nd2 (Xlist.to_string Info.to_string ", " excl2)];


              Nodetbl.add relabel_exclude_map1 nd1 excl1;
              Nodetbl.add relabel_exclude_map2 nd2 excl2;

              begin
                try
                  let pnd1 = nd1#initial_parent in
                  let pnd2 = nd2#initial_parent in

                  [%debug_log "[grouping] parents: %a, %a" nups pnd1 nups pnd2];

                  let is_permu_top =
                    match edits#find1 nd1 with
                    | [Edit.Relabel _] -> false
                    | [Edit.Move(_, s, _, _);Edit.Relabel _]
                    | [Edit.Relabel _;Edit.Move(_, s, _, _)] ->
                        !s = Edit.Mpermutation
                    | _ -> assert false
                  in

                  if not is_permu_top then
                    match edits#find1 pnd1 with
                    | [] -> ()
                    | [Edit.Relabel(_, _, (i2, _))]
                    | [Edit.Relabel(_, _, (i2, _));Edit.Move _]
                    | [Edit.Move _;Edit.Relabel(_, _, (i2, _))] ->
                        if Info.get_node i2 = pnd2 then begin
                          map_add relabel_link_map1 pnd1 nd1;
                          map_add relabel_link_map2 pnd2 nd2
                        end
                    | [_] -> ()
                    | _ -> assert false

                with Otree.Parent_not_found _ -> ()
              end

        | Edit.Move(mid, _, (info1, _), (info2, _)) ->
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in

            let filt1 is_mov nd =

              match edits#find1 nd with
              | [] -> true
              | [Edit.Move(id, _, _, (_, _));Edit.Relabel _]
              | [Edit.Relabel _;Edit.Move(id, _, _, (_, _))]
              | [Edit.Move(id, _, _, (_, _))] ->

                  [%debug_log "[grouping] filt1(%a:%a): mov: mid=%a" nups nd ngps nd MID.ps !id];

                  if !mid = !id then
                    if is_mov nd then
                      false
                    else
                      true

                  else
(*
                    let n2 = Info.get_node i2 in
                    if n2#has_initial_parent then begin
                      not (!k = Edit.Mnormal && n2#initial_parent = nd2)
                    end
                    else
*)
                      true

              | [Edit.Relabel(_, _, ((*i2*)_, _))] ->

                  [%debug_log "[grouping] filt1(%a:%a): rel" nups nd ngps nd];
(*
                  let n2 = Info.get_node i2 in
                  if n2#has_initial_parent then
                    n2#initial_parent != nd2
                  else
*)
                    true

              | [_] -> true
              | eds -> begin
                  let _ = eds in
                  [%debug_log "[grouping] incompatible edits found:\n%s"
                    (Xlist.to_string Edit.to_string "\n" eds)];
                  assert false
              end
            in
            let filt2 is_mov nd =
              match edits#find2 nd with
              | [] -> true
              | [Edit.Move(id, (*k*)_, ((*i1*)_, _), _);Edit.Relabel _]
              | [Edit.Relabel _;Edit.Move(id, (*k*)_, ((*i1*)_, _), _)]
              | [Edit.Move(id, (*k*)_, ((*i1*)_, _), _)] ->

                  [%debug_log "[grouping] filt2(%a:%a): mov: mid=%a" nups nd ngps nd MID.ps !id];

                  if !mid = !id then
                    if is_mov nd then
                      false
                    else
                      true

                  else
(*
                    let n1 = Info.get_node i1 in
                    if n1#has_initial_parent then begin
                      not (!k = Edit.Mnormal && n1#initial_parent == nd1)
                    end
                    else
*)
                      true

              | [Edit.Relabel(_, ((*i1*)_, _), _)] ->

                  [%debug_log "[grouping] filt2(%a:%a): rel" nups nd ngps nd];
(*
                  let n1 = Info.get_node i1 in
                  if n1#has_initial_parent then
                    n1#initial_parent != nd1
                  else
*)
                    true

              | [_] -> true
              | eds -> begin
                  let _ = eds in
                  [%debug_log "[grouping] edits found:\n%s"
                    (Xlist.to_string Edit.to_string "\n" eds)];
                  assert false
              end
            in

            let children1 = Array.to_list nd1#initial_children in
            let children2 = Array.to_list nd2#initial_children in

            let is_mov1 n =
              let b =
                try
                  let n' = nmapping#find n in
                  List.memq n' children2
                with
                  Not_found -> false
              in
              [%debug_log "%a --> %B" nups n b];
              b
            in
            let is_mov2 n =
              let b =
                try
                  let n' = nmapping#inv_find n in
                  List.memq n' children1
                with
                  Not_found -> false
              in
              [%debug_log "%a --> %B" nups n b];
              b
            in

            let filt1' n = filt1 is_mov1 n || check_hunk_boundary nd1 n(*!!!!!*) in
            let filt2' n = filt2 is_mov2 n || check_hunk_boundary nd2 n(*!!!!!*) in

            let excl1 = mkexcl (List.filter filt1' children1) in
            let excl2 = mkexcl (List.filter filt2' children2) in

            [%debug_log ("\n[grouping] Move: children1 of\t <%a>: [%a]\n" ^^
                       "[grouping] Move: excl1: [%s]\n" ^^
                       "[grouping] Move: children2 of\t <%a>: [%a]\n" ^^
                       "[grouping] Move: excl2: [%s]")
              nups nd1 nsps children1
              (Xlist.to_string Info.to_string ", " excl1)
              nups nd2 nsps children2
              (Xlist.to_string Info.to_string ", " excl2)];

            begin
              try
                let pnd1 = nd1#initial_parent in
                let pnd2 = nd2#initial_parent in

                [%debug_log "[grouping] parents: %a, %a" nups pnd1 nups pnd2];

(*              let parent_move_not_found = ref true in *)

                List.iter
                  (function
                    | Edit.Move(id, _, (_, _), (i2, _)) ->
                        if Info.get_node i2 == pnd2 then begin
(*                        parent_move_not_found := false; *)

                          if
                            !id = !mid &&
                            not (check_hunk_boundary pnd1 nd1)(*!!!!!*)
                          then begin
                            map_add move_link_map1 pnd1 nd1;
                            map_add move_link_map2 pnd2 nd2
                          end

                        end
                    | _ -> ()
                  ) (edits#find1 pnd1);

(*
                if !parent_move_not_found && !kind = Edit.Modd then begin

                    [%debug_log "kind changed: %d: %s -> %s (group edits)"
                      !mid (Edit.move_kind_to_string !kind) (Edit.move_kind_to_string Edit.Mnormal)];

                  kind := Edit.Mnormal
                end
*)
              with
                Otree.Parent_not_found _ -> ()
            end;

            begin %debug_block
              [%debug_log "[grouping] move_exclude_map1: added: %a -> [%s]"
                nups nd1 (Xlist.to_string Info.to_string ", " excl1)];
              [%debug_log "[grouping] move_exclude_map2: added: %a -> [%s]"
                nups nd2 (Xlist.to_string Info.to_string ", " excl2)]
            end;

            Nodetbl.add move_exclude_map1 nd1 excl1;
            Nodetbl.add move_exclude_map2 nd2 excl2
      ); (* end of group edits *)


    let to_be_filtered1 = Xset.create 0 in
    let to_be_filtered2 = Xset.create 0 in

    let add_to_be_filtered to_be_filtered edtag nd nds =

      [%debug_log "%s: %a -> [%a]" (edtag_to_string edtag) nups nd nsps nds];

      List.iter
        (fun n ->
          if n == nd then
            ()
          else
            Xset.add to_be_filtered (edtag, n)
        ) nds
    in

    let add_to_be_filtered1 = add_to_be_filtered to_be_filtered1 in
    let add_to_be_filtered2 = add_to_be_filtered to_be_filtered2 in

(*
    let remove_to_be_filtered to_be_filtered edtag nd =

      [%debug_log "%a" nups nd];

      Xset.remove to_be_filtered (edtag, nd)
    in

    let remove_to_be_filtered1 = remove_to_be_filtered to_be_filtered1 in
    let remove_to_be_filtered2 = remove_to_be_filtered to_be_filtered2 in
*)

    let mem_to_be_filtered to_be_filtered (edtag, n) =
      Xset.mem to_be_filtered (edtag, n)
    in
    let mem_to_be_filtered1 = mem_to_be_filtered to_be_filtered1 in
    let mem_to_be_filtered2 = mem_to_be_filtered to_be_filtered2 in


    (* filtering out redundant edits *)

    let prev_rel2_lm2 = ref GI.dummy in
    let prev_rel2 = ref GI.dummy in

    let prev_mov2_lm2 = ref GI.dummy in
    let prev_mov2 = ref GI.dummy in

    edits#iter_topdown
      (fun ed ->

        [%debug_log "filter: %s" (Editop.to_string ed)];

        match ed with
        | Edit.Delete(whole, info, excludes) -> begin
            if not whole || split_hunk_flag(*!!!!!*) then begin
              let nd = Info.get_node info in
              if mem_to_be_filtered1 (Edel, nd) then
                ()
              else begin
                excludes := get_excludes delete_exclude_map delete_link_map nd;
                add_to_be_filtered1 Edel nd (trace_link delete_link_map nd)
              end
            end
        end
        | Edit.Insert(whole, info, excludes) -> begin
            if not whole || split_hunk_flag(*!!!!!*) then begin
              let nd = Info.get_node info in
              if mem_to_be_filtered2 (Eins, nd) then
                ()
              else begin
                excludes := get_excludes insert_exclude_map insert_link_map nd;
                add_to_be_filtered2 Eins nd (trace_link insert_link_map nd)
              end
            end
        end
        | Edit.Relabel(_, (info1, excludes1), (info2, excludes2)) -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            if options#group_relabels_flag then begin
              let gid2 = nd2#gindex in

              let no_swap =
                if !prev_rel2_lm2 = GI.dummy && !prev_rel2 = GI.dummy then
                  false
                else
                  !prev_rel2_lm2 <= gid2 && gid2 < !prev_rel2
              in

              begin %debug_block
                let nd1 = Info.get_node info1 in
                let gid1 = nd1#gindex in
                [%debug_log "filter: relabel: %a-%a" gps gid1 gps gid2];
                [%debug_log "prev_rel2_lm2=%a prev_rel2=%a" gps !prev_rel2_lm2 gps !prev_rel2];
                [%debug_log "filter: no_swap=%B" no_swap];
              end;

              if no_swap && mem_to_be_filtered1 (Erel, nd1) then
                ()
              else begin
                excludes1 :=
                  get_excludes relabel_exclude_map1 relabel_link_map1 nd1;
                add_to_be_filtered1 Erel nd1 (trace_link relabel_link_map1 nd1)
              end;
              if no_swap && mem_to_be_filtered2 (Erel, nd2) then
                ()
              else begin
                excludes2 :=
                  get_excludes relabel_exclude_map2 relabel_link_map2 nd2;
                add_to_be_filtered2 Erel nd2 (trace_link relabel_link_map2 nd2)
              end;

              prev_rel2_lm2 := (tree2#initial_leftmost nd2)#gindex;
              prev_rel2 := gid2

            end
            else begin
              excludes1 := List.map Info.make (Array.to_list nd1#initial_children);
              excludes2 := List.map Info.make (Array.to_list nd2#initial_children);
            end
        end
        | Edit.Move(mid, _, (info1, excludes1), (info2, excludes2)) -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in

            let gid2 = nd2#gindex in

            let no_swap =
              if !prev_mov2_lm2 = GI.dummy && !prev_mov2 = GI.dummy then
                false
              else
                !prev_mov2_lm2 <= gid2 && gid2 < !prev_mov2
            in

            begin %debug_block
              let nd1 = Info.get_node info1 in
              let gid1 = nd1#gindex in
              [%debug_log "filter: move: %a-%a" gps gid1 gps gid2];
              [%debug_log "prev_mov2_lm2=%a prev_mov2=%a" gps !prev_mov2_lm2 gps !prev_mov2];
              [%debug_log "filter: no_swap=%B" no_swap];
            end;

            if no_swap && mem_to_be_filtered1 (Emov, nd1) then
              ()
            else begin
              excludes1 := get_excludes move_exclude_map1 move_link_map1 nd1;
              let nds1 = trace_link move_link_map1 nd1 in
              List.iter (fun n -> n#data#set_mid !mid) nds1;
              add_to_be_filtered1 Emov nd1 nds1
            end;
            if no_swap && mem_to_be_filtered2 (Emov, nd2) then
              ()
            else begin
              excludes2 := get_excludes move_exclude_map2 move_link_map2 nd2;
              let nds2 = trace_link move_link_map2 nd2 in
              List.iter (fun n -> n#data#set_mid !mid) nds2;
              add_to_be_filtered2 Emov nd2 nds2
            end;
            prev_mov2_lm2 := (tree2#initial_leftmost nd2)#gindex;
            prev_mov2 := gid2
        end
      );


    begin %debug_block
      [%debug_log "EDITS BEFORE FILTERING:\n%s\n" edits#to_string];
      [%debug_log ("to_be_filtered1: [%s]\n" ^^
                    "to_be_filtered2: [%s]")
        (Xlist.to_string
           (fun (tag, n) -> Printf.sprintf "%a(%s)" nups n (edtag_to_string tag))
           ";" (Xset.to_list to_be_filtered1))
        (Xlist.to_string
           (fun (tag, n) -> Printf.sprintf "%a(%s)" nups n (edtag_to_string tag))
           ";" (Xset.to_list to_be_filtered2))];
    end;

    edits#filter
      (function
        | Edit.Delete(_, i, _) -> not (mem_to_be_filtered1 (Edel, Info.get_node i))
        | Edit.Insert(_, i, _) -> not (mem_to_be_filtered2 (Eins, Info.get_node i))
        | Edit.Relabel(_, (i1, _), (i2, _)) -> begin
            if options#group_relabels_flag then
              not (mem_to_be_filtered1 (Erel, Info.get_node i1)) ||
              not (mem_to_be_filtered2 (Erel, Info.get_node i2))
            else
              true
        end
        | Edit.Move(_, _, (i1, _), (i2, _)) -> begin
            not (mem_to_be_filtered1 (Emov, Info.get_node i1)) ||
            not (mem_to_be_filtered2 (Emov, Info.get_node i2))
        end
      );


    [%debug_log "EDITS AFTER FILTERING:\n%s\n" edits#to_string];


    let sort_excludes =
      List.fast_sort
        (fun i1 i2 -> compare (Info.get_gindex i1) (Info.get_gindex i2))
    in

    let mids = Hashtbl.create 0 in

    edits#iter_topdown
      (function
        | Edit.Delete(_, info, excludes) as del -> begin
            let _ = del in
            [%debug_log "%s" (Editop.to_string del)];
            let nd = Info.get_node info in
            let nds = List.map Info.get_node !excludes in
            let size = tree1#size_of_initial_cluster (nd, nds) in
            Info.set_size info size;
            excludes := sort_excludes !excludes;
        end
        | Edit.Insert(_, info, excludes) as ins -> begin
            let _ = ins in
            [%debug_log "%s" (Editop.to_string ins)];
            let nd = Info.get_node info in
            let nds = List.map Info.get_node !excludes in
            let size = tree2#size_of_initial_cluster (nd, nds) in
            Info.set_size info size;
            excludes := sort_excludes !excludes;
        end
        | Edit.Relabel(_, (info1, excludes1), (info2, excludes2)) as rel -> begin
            let _ = rel in
            [%debug_log "%s" (Editop.to_string rel)];
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            let nds1 = List.map Info.get_node !excludes1 in
            let size1 = tree1#size_of_initial_cluster (nd1, nds1) in
            let nds2 = List.map Info.get_node !excludes2 in
            let size2 = tree2#size_of_initial_cluster (nd2, nds2) in

            assert (size1 = size2);

            Info.set_size info1 size1;
            Info.set_size info2 size2;
            excludes1 := sort_excludes !excludes1;
            excludes2 := sort_excludes !excludes2;
        end
        | Edit.Move(mid, _, (info1, excludes1), (info2, excludes2)) as mov -> begin
            let _ = mov in
            [%debug_log "%s" (Editop.to_string mov)];
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            let nds1 = List.map Info.get_node !excludes1 in
            let size1 = tree1#size_of_initial_cluster (nd1, nds1) in
            let nds2 = List.map Info.get_node !excludes2 in
            let size2 = tree2#size_of_initial_cluster (nd2, nds2) in

            [%debug_log "size1=%d size2=%d" size1 size2];
            assert (size1 = size2);

            Info.set_size info1 size1;
            Info.set_size info2 size2;

            if Hashtbl.mem mids !mid then
              Hashtbl.replace mids !mid (size1 + (Hashtbl.find mids !mid))
            else begin
              Hashtbl.add mids !mid size1
            end;

            excludes1 := sort_excludes !excludes1;
            excludes2 := sort_excludes !excludes2;
        end
      );

    begin %debug_block
      let total = ref 0 in
      [%debug_log "* size of moves:"];
      let list =
        List.fast_sort (fun (m1, _) (m2, _) -> Stdlib.compare m1 m2)
          (Hashtbl.fold (fun mid sz l -> (mid, sz)::l) mids [])
      in
      List.iter
        (fun (mid, sz) ->
          total := !total + sz;
          [%debug_log "%a --> %d node%s" MID.ps mid sz (if sz = 1 then "" else "s")]
        ) list;
      [%debug_log "total=%d" !total];
    end
    (* end of func fixup_edits *)



end (* of module Postprocessing.F *)
]
