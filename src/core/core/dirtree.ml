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

[%%prepare_logger]

module Xfile = Diffast_misc.Xfile
module Edit = Diffast_misc.Edit
module Mapping = Diffast_misc.Mapping
module Otreelib = Diffast_misc.Otreelib


include Dirtree_base

let tree_width_limit = ref 50

let tree_size_limit = ref 256

let modified_files_list_file_name = "modified"

let modified_files_csv   = "modified.csv"
let unmodified_files_csv = "unmodified.csv"
let renamed_files_csv    = "renamed.csv"
let moved_files_csv      = "moved.csv"
let removed_files_csv    = "removed.csv"
let added_files_csv      = "added.csv"
let copied_files_csv     = "copied.csv"
let glued_files_csv      = "glued.csv"


class node_map = object (self : 'self)
  val set = Xset.create 0

  method add n1 n2 = Xset.add set (n1, n2)

  method add_list = List.iter (fun (n1, n2) -> self#add n1 n2)

  method add_map (m : 'self) = m#iter (fun n1 n2 -> Xset.add set (n1, n2))

  method iter (f : node_t -> node_t -> unit) =
    Xset.iter (fun (n1, n2) -> f n1 n2) set

  method size =
    let c = ref 0 in
    self#iter (fun _ _ -> incr c);
    !c

  method map : 'a. (node_t -> node_t -> 'a) -> 'a list = fun f ->
    let l = ref [] in
    self#iter
      (fun n1 n2 ->
        l := (f n1 n2) :: !l
      );
    !l

  method split =
    let l1, l2 = ref [], ref [] in
    self#iter
      (fun n1 n2 ->
        l1 := n1 :: !l1;
        l2 := n2 :: !l2
      );
    !l1, !l2

end (* of class node_map *)

[%%capture_path
let pp0 tree1 tree2 dtbl1 dtbl2 tbl1 tbl2 =

  let del tbl nd =
    match nd#data#content_digest with
    | Some d -> begin
        try
          let nds = Hashtbl.find tbl d in
          Hashtbl.replace tbl d (Xlist.subtractq nds [nd])
        with
          Not_found -> ()
    end
    | _ -> ()
  in
  let del1 = del tbl1 in
  let del2 = del tbl2 in

  let iter_mem_pairs nmap nd1 nd2 =
    let mems1, mems2 = ref [], ref [] in
    tree1#fast_scan_whole_initial_subtree nd1
      (fun n ->
        if n#data#is_file then begin
          mems1 := n :: !mems1;
          del1 n
        end
      );
    tree2#fast_scan_whole_initial_subtree nd2
      (fun n ->
        if n#data#is_file then begin
          mems2 := n :: !mems2;
          del2 n
        end
      );
    List.iter2 nmap#add !mems1 !mems2
  in

  let unmodified = new node_map in
  let renamed    = new node_map in
  let moved      = new node_map in

  Hashtbl.iter
    (fun d nds1 ->
      try
        let nds2 = Hashtbl.find dtbl2 d in

        match nds1, nds2 with
        | [nd1], [nd2] -> begin

            if nd1#data#label = nd2#data#label then begin
              if nd1#data#path = nd2#data#path then begin

                [%debug_log "[ISO] %s -> %s"
                  nd1#data#to_string nd2#data#to_string];

                iter_mem_pairs unmodified nd1 nd2
              end
              else begin

                [%debug_log "[MOVE] %s -> %s"
                  nd1#data#to_string nd2#data#to_string];

                iter_mem_pairs moved nd1 nd2
              end
            end
            else begin
              [%debug_log "[RENAME] %s -> %s"
                nd1#data#to_string nd2#data#to_string];

              iter_mem_pairs renamed nd1 nd2
            end;

            nd1#prune;
            nd2#prune
        end
        | _ -> ()
      with
      | Not_found -> ()
      | _ -> assert false

    ) dtbl1;
  unmodified, renamed, moved
]

[%%capture_path
let pp1 tbl1 tbl2 =
  let classify nodes1 nodes2 =

    let unmodified = ref [] in
    let renamed    = ref [] in
    let moved      = ref [] in

    let copied     = ref [] in
    let glued      = ref [] in

    let not_resolved1 = ref [] in
    let not_resolved2 = ref [] in

    begin %debug_block
      List.iter
      (fun n ->
        [%debug_log "nodes1: %s" n#data#to_string]
      ) nodes1;
      List.iter
      (fun n ->
        [%debug_log "nodes2: %s" n#data#to_string]
      ) nodes2
    end;

    begin
      match nodes1, nodes2 with
      | _, [] -> not_resolved1 := nodes1
      | [], _ -> not_resolved2 := nodes2

      | [nd1], [nd2] ->
          if nd1#data#label = nd2#data#label then
            if nd1#data#path = nd2#data#path then begin

              [%debug_log "[ISO] %s -> %s"
                nd1#data#to_string nd2#data#to_string];

              unmodified := (nd1, nd2) :: !unmodified

            end
            else begin

              [%debug_log "[MOVE] %s -> %s"
                nd1#data#to_string nd2#data#to_string];

              moved := (nd1, nd2) :: !moved

            end
          else begin
            [%debug_log "[RENAME] %s -> %s"
              nd1#data#to_string nd2#data#to_string];

            renamed := (nd1, nd2) :: !renamed

          end

      | _ ->
          let name_tbl1 = split (fun n -> n#data#label) nodes1 in
          let name_tbl2 = split (fun n -> n#data#label) nodes2 in

          let rpath_tbl2 = Hashtbl.create 0 in
          List.iter
            (fun nd ->
              Hashtbl.add rpath_tbl2 nd#data#path nd;
            ) nodes2;

          Hashtbl.iter
            (fun name nds1 ->
              try
                let nds2 = Hashtbl.find name_tbl2 name in (* nds1 and nds2 share name *)

                let rest1 = ref [] in

                List.iter
                  (fun nd1 ->
                    let rpath1 = nd1#data#path in

                    try
                      let nd2 = Hashtbl.find rpath_tbl2 rpath1 in

                      [%debug_log "[ISO] %s -> %s"
                        nd1#data#to_string nd2#data#to_string];

                      unmodified := (nd1, nd2) :: !unmodified

                    with
                      Not_found -> rest1 := nd1 :: !rest1

                  ) nds1;

                let rest2 =
                  let _, p = List.split !unmodified in
                  List.filter (fun n -> not (List.mem n p)) nds2
                in

                match !rest1, rest2 with
                | [], [] -> ()

                | [], nds -> (* copy from unmodified? *)
                    begin
                      match nds1 with
                      | nd1::_ ->

                          [%debug_log "[COPY] %s -> [%s]"
                            nd1#data#to_string
                            (Xlist.to_string (fun n -> n#data#to_string) ";" nds)];

                          copied := (nd1, nds) :: !copied;
                          Hashtbl.remove name_tbl1 name;
                          Hashtbl.remove name_tbl2 name

                      | [] -> ()
                    end

                | nds, [] -> (* glue to unmodified? *)
                    begin
                      match nds2 with
                      | nd2::_ ->

                          [%debug_log "[GLUE] [%s] -> %s"
                            (Xlist.to_string (fun n -> n#data#to_string) ";" nds)
                            nd2#data#to_string];

                          glued := (nds, nd2) :: !glued;
                          Hashtbl.remove name_tbl1 name;
                          Hashtbl.remove name_tbl2 name

                      | [] -> ()
                    end

                | [nd1], [nd2] ->

                    [%debug_log "[MOVE] %s -> %s"
                      nd1#data#to_string nd2#data#to_string];

                    moved := (nd1, nd2) :: !moved;

                    Hashtbl.remove name_tbl1 name;
                    Hashtbl.remove name_tbl2 name

                | _ -> (* settle later *)
                    Hashtbl.replace name_tbl1 name !rest1;
                    Hashtbl.replace name_tbl2 name rest2

              with
                Not_found -> () (* renamed? *)

            ) name_tbl1;

          Hashtbl.iter
            (fun _ nds1 ->
              not_resolved1 := nds1 @ !not_resolved1
            ) name_tbl1;
          Hashtbl.iter
            (fun _ nds2 ->
              not_resolved2 := nds2 @ !not_resolved2
            ) name_tbl2
    end;

(*
    Xprint.message "classify: nr1:%d nr2:%d u:%d r:%d m:%d c:%d g:%d"
      (List.length !not_resolved1)
      (List.length !not_resolved2)
      (List.length !unmodified)
      (List.length !renamed)
      (List.length !moved)
      (List.length !copied)
      (List.length !glued);
*)
    !not_resolved1, !not_resolved2,
    !unmodified,
    !renamed,
    !moved,
    !copied,
    !glued

  in (* end of func classify *)

  let unmodified = new node_map in
  let renamed    = new node_map in
  let moved      = new node_map in
  let copied     = ref [] in
  let glued      = ref [] in

  Hashtbl.iter
    (fun d nds1 ->
      try
        let nds2 = Hashtbl.find tbl2 d in

        let not_resolved1, not_resolved2,
          u, r, m, c, g
            = classify nds1 nds2
        in
        unmodified#add_list u;
        renamed#add_list r;
        moved#add_list m;
        copied     := c @ !copied;
        glued      := g @ !glued;

        List.iter
          (fun p ->
            List.iter
              (fun (n1, n2) ->
                n1#prune;
                n2#prune
              ) p
          ) [u; r; m];
        List.iter (fun (_, ns) -> List.iter (fun n -> n#prune) ns) c;
        List.iter (fun (ns, _) -> List.iter (fun n -> n#prune) ns) g;

        if not_resolved1 = [] then
          Hashtbl.remove tbl1 d
        else
          Hashtbl.replace tbl1 d not_resolved1;

        if not_resolved2 = [] then
          Hashtbl.remove tbl2 d
        else
          Hashtbl.replace tbl2 d not_resolved2
      with
      | Not_found -> ()
(*      | _ -> assert false *)

    ) tbl1;

  unmodified, renamed, moved, !copied, !glued
(* end of fun pp1 *)
]


let rec path_split path =
  let bn = Filename.basename path in
  if bn = path then
    [path]
  else
    List.concat [path_split (Filename.dirname path); [bn]]


let compute_dissimilarity s1 s2 =

  let len1 = String.length s1 in
  let len2 = String.length s2 in
  let a1 = Array.make len1 ' ' in
  let a2 = Array.make len2 ' ' in
  for i = 0 to len1 - 1 do
    a1.(i) <- s1.[i]
  done;
  for i = 0 to len2 - 1 do
    a2.(i) <- s2.[i]
  done;
(*
  let a1 = Array.of_list (path_split s1) in
  let a2 = Array.of_list (path_split s2) in
*)
  let mat, rel, del, ins = Adiff.adiff a1 a2 in
  let nmap = (List.length mat) + (List.length rel) in
  let nchan = (List.length rel) + (List.length del) + (List.length ins) in
  let res = (float nchan) /. float(nmap) in
  res

let find_rename_pats1 path1 path2 =
  let a1 = Array.of_list (path_split path1) in
  let a2 = Array.of_list (path_split path2) in
  let _, rel, _, _ = Adiff.adiff a1 a2 in
  List.map (fun (i, j) -> String.lowercase_ascii a1.(i), String.lowercase_ascii a2.(j)) rel

let find_rename_pats path_pair_list =
  let freq_tbl = Hashtbl.create 0 in
  List.iter
    (fun (p1, p2) ->
      List.iter
        (fun src_dst ->
          try
            Hashtbl.replace freq_tbl src_dst ((Hashtbl.find freq_tbl src_dst)+1)
          with Not_found ->
            Hashtbl.add freq_tbl src_dst 1
        ) (find_rename_pats1 p1 p2)
    ) path_pair_list;
  let l =
    Hashtbl.fold
      (fun src_dst freq l ->
        if freq > 1 then
          (src_dst, freq)::l
        else
          l
      ) freq_tbl []
  in
  List.fast_sort (fun (_, i) (_, j) -> Stdlib.compare i j) l

let hyphen_pat = Str.regexp_string "-"
let repl_hyphen = Str.global_replace hyphen_pat Filename.dir_sep

[%%capture_path
let pp2 tbl1 tbl2 =
  let modified = ref [] in

  let conv_tbl tbl =
    let new_tbl = Hashtbl.create 0 in
    Hashtbl.iter
      (fun _ nds ->
        List.iter
          (fun nd ->
            Hashtbl.add new_tbl (repl_hyphen (String.lowercase_ascii nd#data#path)) nd
          ) nds
      ) tbl;
    new_tbl
  in

  let tbl1 = conv_tbl tbl1 in
  let tbl2 = conv_tbl tbl2 in

  Hashtbl.iter
    (fun rpath nd1 ->
      let d1 = nd1#data#content_digest in
      try
        let nd2 = Hashtbl.find tbl2 rpath in
        let d2 = nd2#data#content_digest in
        if d1 <> d2 then begin

          modified := (nd1, nd2) :: !modified;

          nd1#prune;
          nd2#prune;

          Hashtbl.remove tbl1 rpath;
          Hashtbl.remove tbl2 rpath
        end
      with
        Not_found -> ()
    ) tbl1;

  let conv_tbl tbl =
    let new_tbl = Hashtbl.create 0 in
    Hashtbl.iter
      (fun _ n ->
        let name = String.lowercase_ascii n#data#label in
        try
          let ns = Hashtbl.find new_tbl name in
          Hashtbl.replace new_tbl name (n::ns)
        with
          Not_found -> Hashtbl.add new_tbl name [n]
      ) tbl;
    new_tbl
  in

  let tbl1 = conv_tbl tbl1 in
  let tbl2 = conv_tbl tbl2 in

  Hashtbl.iter
    (fun name nds1 ->
      try
        let nds2 = Hashtbl.find tbl2 name in

        match nds1, nds2 with
          [], _ | _, [] -> ()
        | [nd1], [nd2] -> begin
            let d1 = nd1#data#content_digest in
            let d2 = nd2#data#content_digest in
            if d1 <> d2 then begin
              modified := (nd1, nd2) :: !modified;

              nd1#prune;
              nd2#prune
            end
          end
        | _ ->
            let len1 = List.length nds1 in
            let len2 = List.length nds2 in

            [%debug_log "matching for \"%s\": len1=%d len2=%d" name len1 len2];

            let mat = Array.make_matrix len1 len2 0.0 in

            let min_tbl1 = Array.make len1 0 in

            for i = 0 to len1 - 1 do
              let min = ref infinity in
              let rpath1 = (List.nth nds1 i)#data#path in
              for j = 0 to len2 - 1 do
                let rpath2 = (List.nth nds2 j)#data#path in
                let dissim = compute_dissimilarity rpath1 rpath2 in
                mat.(i).(j) <- dissim;

                if dissim < !min then begin
                  min := dissim;
                  min_tbl1.(i) <- j
                end

              done
            done;

            let min_tbl2 = Array.make len2 0 in

            let pruned1, pruned2 = ref [], ref [] in

            for j = 0 to len2 - 1 do
              let min = ref infinity in
              for i = 0 to len1 - 1 do
                let dissim = mat.(i).(j) in

                if dissim < !min then begin
                  min := dissim;
                  min_tbl2.(j) <- i
                end

              done;

              let i' = min_tbl2.(j) in

              if min_tbl1.(i') = j then begin

                let nd1 = List.nth nds1 i' in
                let nd2 = List.nth nds2 j in

                let d1 = nd1#data#content_digest in
                let d2 = nd2#data#content_digest in
                if d1 <> d2 then begin
                  modified := (nd1, nd2) :: !modified;

                  [%debug_log "%s ->\n\t%s\n" nd1#data#to_string nd2#data#to_string];

                  nd1#prune;
                  nd2#prune;

                  pruned1 := nd1 :: !pruned1;
                  pruned2 := nd2 :: !pruned2;
                end
              end
            done;

            let nds1' = List.filter (fun n -> not (List.mem n !pruned1)) nds1 in
            let nds2' = List.filter (fun n -> not (List.mem n !pruned2)) nds2 in

            begin
              match nds1', nds2' with
                [nd1], [nd2] ->
                  let d1 = nd1#data#content_digest in
                  let d2 = nd2#data#content_digest in
                  if d1 <> d2 then begin
                    modified := (nd1, nd2) :: !modified;

                    [%debug_log "%s ->\n\t%s\n" nd1#data#to_string nd2#data#to_string];

                    nd1#prune;
                    nd2#prune;
                  end
              | _ -> ()
            end

      with
        Not_found -> ()
    ) tbl1;

  !modified
(* end of func pp2 *)
]


[%%capture_path
let analyze tree1 tree2 eds mapping (*iso*)_ =
  let subs = ref [] in
  let modified_pairs = ref [] in
  let expand1 = ref [] in
  let expand2 = ref [] in
  let renamed_pairs = ref [] in
  let unmodified_pairs = ref [] in
  let unmodified_pairs_sub = ref [] in (* not pruned *)

  let dir_pairs_to_be_pruned = ref [] in

  let relabels = ref [] in

  let mk_subtree_pairs nd1 nd2 =

    [%debug_log "%s<content_digest:%s><digest:%s> - %s<content_digest:%s><digest:%s>"
      nd1#data#path nd1#data#content_digest_string nd1#data#digest_string
      nd2#data#path nd2#data#content_digest_string nd2#data#digest_string];

    let l1, l2 = ref [], ref [] in
    let f l nd = if nd#data#is_file then l := nd::!l in
    tree1#scan_subtree nd1 (f l1);
    tree2#scan_subtree nd2 (f l2);
    if (List.length !l1) <> (List.length !l2) then begin
      [%fatal_log "list length mismatch"];
      exit 1
    end
    else
      let res = List.combine !l1 !l2 in

      begin %debug_block
        List.iter
          (fun (n1, n2) ->
            [%debug_log "[UNMODIFIED(SUB)] %s - %s" n1#data#path n2#data#path]
          ) res
      end;

      res
  in

  let proc_one = function
    | Edit.Relabel(i1, i2) ->
        relabels := (i1, i2)::!relabels;
        let nd1, nd2 = tree1#get i1, tree2#get i2 in
        let lab1, lab2 = nd1#data#label, nd2#data#label in
        let dig1, dig2 = nd1#data#digest, nd2#data#digest in
(*      let path1, path2 = (tree1#path i1), (tree2#path i2) in *)

        if lab1 = lab2 then
          if dig1 = dig2 then begin (* impossible: relabel concerns label + digest *)
            [%fatal_log "impossible: %s<%s> %s<%s>"
              lab1 nd1#data#digest_string lab2 nd2#data#digest_string];
            exit 1
          end
          else (* modified? *)

            if
              nd1#data#is_dir && nd2#data#is_dir then begin
                if nd1 != tree1#root && nd2 != tree2#root then begin

                  [%debug_log "[SUB] \"%s(%s)\" --> \"%s(%s)\""
                    (tree1#path i1) (UID.to_string nd1#uid)
                    (tree2#path i2) (UID.to_string nd2#uid)];

                  subs := (nd1, nd2)::!subs
                end
            end
            else
              if nd1#is_collapsed then
                expand1 := nd1::!expand1
              else
                if nd2#is_collapsed then
                  expand2 := nd2::!expand2
                else begin (* impossible: digest of expanded node is cleared *)
                  [%fatal_log "impossible %s<%s> %s<%s>"
                    lab1 nd1#data#digest_string lab2 nd2#data#digest_string];
                  exit 1
                end

        else (* label has changed *)
          if dig1 = dig2 then (* renamed *)
            if dig1 = None then
              if nd1#data#is_file && nd2#data#is_file then
                if nd1#data#content_digest = nd2#data#content_digest then begin

                  [%debug_log "[RENAMED] \"%s\" --> \"%s\""
                    (tree1#path i1) (tree2#path i2)];

                  renamed_pairs := (nd1, nd2)::!renamed_pairs
                end
                else
                  () (* different files *)

              else begin
                if nd1#is_collapsed then expand1 := nd1::!expand1;
                if nd2#is_collapsed then expand2 := nd2::!expand2
              end

            else begin (* both are collapsed directories *)
              expand1 := nd1::!expand1;
              expand2 := nd2::!expand2
            end

          else
            if nd1#is_collapsed && nd2#is_collapsed then begin
              if nd1 != tree1#root && nd2 != tree2#root then begin

                (* this trial may result in a waste of time... *)
                [%debug_log "[SUB] \"%s(%a)\" --> \"%s(%a)\""
                  (tree1#path i1) UID.ps nd1#uid
                  (tree2#path i2) UID.ps nd2#uid];

                subs := (nd1, nd2)::!subs
              end
            end
            else begin
              if nd1#is_collapsed then expand1 := nd1::!expand1;
              if nd2#is_collapsed then expand2 := nd2::!expand2
            end

    | Edit.Delete i ->
        let nd = tree1#get i in

        [%debug_log "[REMOVED] \"%s\"" (tree1#path i)];

        if nd#is_collapsed then expand1 := nd::!expand1

    | Edit.Insert(i, _) ->
        let nd = tree2#get i in

        [%debug_log "[ADDED] \"%s\"" (tree2#path i)];

        if nd#is_collapsed then expand2 := nd::!expand2
  in
  Edit.seq_iter proc_one eds;

  [%debug_log "analyzing from the mapping..."];

  Mapping.iter
    (fun i j ->
      let nd1, nd2 = tree1#get i, tree2#get j in
      let c1, c2 = nd1#data#content_digest, nd2#data#content_digest in

      if nd1#data#is_file && nd2#data#is_file then
        if List.mem (i, j) !relabels then () (* already processed above *)
        else
          if c1 = c2 then begin

            [%debug_log "[UNMODIFIED] %s - %s"
              (tree1#path i) (tree2#path j)];

            unmodified_pairs := (nd1, nd2)::!unmodified_pairs
          end
          else begin

            [%debug_log "[MODIFIED] %s - %s"
              (tree1#path i) (tree2#path j)];

            modified_pairs := (nd1, nd2)::!modified_pairs
          end
      else
        if nd1#data#is_dir && nd2#data#is_dir then
          if nd1#is_collapsed && nd2#is_collapsed then
            if nd1#data#equals nd2#data then begin
              (* all children are unmodified *)
              dir_pairs_to_be_pruned := (nd1, nd2)::!dir_pairs_to_be_pruned;
              unmodified_pairs_sub
              := (mk_subtree_pairs nd1 nd2) @ !unmodified_pairs_sub
            end
    ) mapping;

(* isomorphic nodes(leaves) are already processed above *)
(*
  let iso1, iso2 = iso, List.map (fun i -> Mapping.find i mapping) iso in

  [%debug_log "prune(isomorphic): tree1[%s] tree2:[%s]"
  (Xlist.to_string string_of_int "," iso1)
  (Xlist.to_string string_of_int "," iso2)];

  if iso1 = [tree1#root#index]
  then tree1#root#prune_all_children
  else tree1#prune iso1;

  if iso2 = [tree2#root#index]
  then tree2#root#prune_all_children
  else tree2#prune iso2;
*)

  begin %debug_block
    [%debug_log "MODIFIED:"];
    List.iter (fun (nd1, nd2) -> printf "%s -- %s\n"
        nd1#data#to_string nd2#data#to_string) !modified_pairs;
    [%debug_log "UNMODIFIED:"];
    List.iter (fun (nd1, nd2) -> printf "%s -- %s\n"
        nd1#to_string nd2#to_string) !unmodified_pairs;

    [%debug_log "UNMODIFIED(SUB):"];
    List.iter (fun (nd1, nd2) -> printf "%s -- %s\n"
        nd1#to_string nd2#to_string) !unmodified_pairs_sub;
    [%debug_log "RENAMED:"];
    List.iter (fun (nd1, nd2) -> printf "%s -- %s\n"
        nd1#to_string nd2#to_string) !renamed_pairs;
  end;

  let to_be_pruned =
    !modified_pairs @
    !unmodified_pairs @
    !renamed_pairs @
    !dir_pairs_to_be_pruned
  in
  let prn1, prn2 = List.split to_be_pruned in

  [%debug_log "prune: tree1[\n%s\n]\n tree2:[\n%s\n]"
    (Xlist.to_string (fun nd -> nd#to_string) "\n" prn1)
    (Xlist.to_string (fun nd -> nd#to_string) "\n" prn2)];

  tree1#prune_nodes prn1;
  tree2#prune_nodes prn2;

  !subs,
  !modified_pairs,
  !expand1,
  !expand2,
  !unmodified_pairs @ !unmodified_pairs_sub,
  !renamed_pairs
(* end of func analyze *)
]


exception Found

[%%capture_path
let compare_node_lists options tree1 tree2 nl1 nl2 =
  let isos = ref [] in
  let subs = ref [] in
  let modified_pairs       = ref [] in
  let unmodified_pairs     = ref [] in
  let modified_pairs_iso   = ref [] in
  let unmodified_pairs_iso = ref [] in
  let renamed_pairs        = ref [] in

  let check_iso (nd1, nd2) =
    let t1 = new c options nd1 false in
    let t2 = new c options nd2 false in

    let leaves1 = t1#get_whole_initial_leaves in
    let leaves2 = t2#get_whole_initial_leaves in
    let len1, len2 = List.length leaves1, List.length leaves2 in
    if len1 <> len2 then begin
      [%fatal_log "nleaves: %d != %d" len1 len2];
      exit 1
    end;
    List.iter2
      (fun lf1 lf2 ->
        if lf1#data#content_digest = lf2#data#content_digest then
          unmodified_pairs_iso := (lf1, lf2)::!unmodified_pairs_iso
        else modified_pairs_iso := (lf1, lf2)::!modified_pairs_iso
      ) leaves1 leaves2
  in

  List.iter
    (fun nd1 ->
      try
        List.iter
          (fun nd2 ->
            let dat1, dat2 = nd1#data, nd2#data in
            let lab1, lab2 = dat1#label, dat2#label in
            let ctt1, ctt2 = dat1#content_digest, dat2#content_digest in

            if dat1#is_file && dat2#is_file then
              if ctt1 = ctt2 then
                if lab1 = lab2 then begin

                  [%debug_log "[UNMODIFIED] \"%s\"--\"%s\"" nd1#data#path nd2#data#path];

                  unmodified_pairs := (nd1, nd2)::!unmodified_pairs;
                  raise Found
                end
                else begin

                  [%debug_log "[RENAMED] \"%s\" --> \"%s\"" nd1#data#path nd2#data#path];

                  renamed_pairs := (nd1, nd2)::!renamed_pairs;
                  raise Found
                  end
              else
                if lab1 = lab2 then begin

                  [%debug_log "[MODIFIED] \"%s\" --> \"%s\"" nd1#data#path nd2#data#path];

                  modified_pairs := (nd1, nd2)::!modified_pairs;
                  raise Found
                end
                else
                  () (* different files *)
            else
              if dat1#is_dir && dat2#is_dir then
                if nd1#is_collapsed && nd2#is_collapsed then
                  if dat1#digest = dat2#digest then begin

                    [%debug_log "[ISO] \"%s\" --> \"%s\"" nd1#data#path nd2#data#path];

                    isos := (nd1, nd2)::!isos;
                    raise Found
                  end
                  else
                    if lab1 = lab2 then begin

                      [%debug_log "[SUB] \"%s\" --> \"%s\"" nd1#data#path nd2#data#path];

                      subs := (nd1, nd2)::!subs;
                      raise Found
                    end
                    else ()
                else ()

          ) nl2
      with Found -> ()
    ) nl1;

  List.iter check_iso !isos;
  List.iter (fun (nd1, nd2) -> nd1#prune; nd2#prune) !isos;

  begin %debug_block
    [%debug_log "after iso prune"];
    [%debug_log "T1:\n%s" tree1#to_string];
    [%debug_log "T2:\n%s" tree2#to_string];
    [%debug_log "MODIFIED:"];
    List.iter (fun (nd1, nd2) -> printf "%s -- %s\n" nd1#to_string nd2#to_string)
      !modified_pairs;
    [%debug_log "UNMODIFIED:"];
    List.iter (fun (nd1, nd2) -> printf "%s -- %s\n" nd1#to_string nd2#to_string)
      !unmodified_pairs;
    [%debug_log "RENAMED:"];
    List.iter (fun (nd1, nd2) -> printf "%s -- %s\n" nd1#to_string nd2#to_string)
      !renamed_pairs;
  end;

  let extend pairs pairs0 =
    List.fold_left
      (fun ps p ->
        let _, nd = p in
        let _, nds = List.split ps in
        if List.memq nd nds then ps
        else p::ps
      ) pairs pairs0
  in

  let to_be_pruned =
    extend (extend !unmodified_pairs !renamed_pairs) !modified_pairs
  in

  [%debug_log "to_be_pruned: [%s]"
    (Xlist.to_string
       (fun (n1, n2) ->
         sprintf "%a-%a" UID.ps n1#uid UID.ps n2#uid) "; " to_be_pruned)];

  let prn1, prn2 = List.split to_be_pruned in
  tree1#prune_nodes prn1;
  tree2#prune_nodes prn2;

  modified_pairs := !modified_pairs @ !modified_pairs_iso;
  unmodified_pairs := !unmodified_pairs @ !unmodified_pairs_iso;


  let subs1, subs2 = List.split !subs in
  let isos1, isos2 = List.split !isos in
  let expnd1 =
    List.filter
      (fun nd ->
        nd#is_collapsed && not (List.memq nd subs1) && not (List.memq nd isos1)
      ) nl1
  in
  let expnd2 =
    List.filter
      (fun nd ->
        nd#is_collapsed && not (List.memq nd subs2) && not (List.memq nd isos2)
      ) nl2
  in
  !subs, !modified_pairs, expnd1, expnd2, !unmodified_pairs, !renamed_pairs
(* end of func compare_node_lists *)
]


let counter = new Misc.counter (* how many times is campare_subtree called? *)


[%%capture_path
let rec compare_subtree options dot_dir (tree1, tree2) =
  counter#incr;
  let uid1 = UID.to_string tree1#root#uid in
  let uid2 = UID.to_string tree2#root#uid in
  let cid = uid1^"-"^uid2 in

  [%debug_log "%d COMPARING (SUB)TREE PAIR [%s]" counter#value cid];

  if options#dots_flag then begin
    tree1#save_dot "Old:" [] (Filename.concat dot_dir (sprintf "old_dir%s.dot" uid1));
    tree2#save_dot "New:" [] (Filename.concat dot_dir (sprintf "new_dir%s.dot" uid2))
  end;

  let chldrn1 = Array.to_list tree1#root#children in
  let chldrn2 = Array.to_list tree2#root#children in
  let nchldrn1, nchldrn2 = List.length chldrn1, List.length chldrn2 in

  begin %debug_block
    [%debug_log "|T1|=%d |T2|=%d" tree1#size tree2#size];
    [%debug_log "nchildren1:%d nchildren2:%d" nchldrn1 nchldrn2];
    [%debug_log "tree_width_limit = %d" !tree_width_limit];
    [%debug_log "tree_size_limit = %d" !tree_size_limit];

    [%debug_log "T1:\n%s" tree1#to_string];
    [%debug_log "T2:\n%s" tree2#to_string]
  end;

  let subs, modified_pairs, expnd1, expnd2, unmodified_pairs, renamed_pairs =
    if
      nchldrn1 > !tree_width_limit || nchldrn2 > !tree_width_limit ||
      tree1#size > !tree_size_limit || tree2#size > !tree_size_limit
    then begin
      [%debug_log "doing list comparison..."];
      compare_node_lists options tree1 tree2 chldrn1 chldrn2
    end
    else begin
      [%debug_log "doing tree comparison..."];
      let edits, mapping, iso =
        if tree1#is_flat && tree2#is_flat
        then
          Flattreediff.find ~rely_on_rel:false tree1 tree2
        else
          Treediff.find tree1 tree2
      in
      if options#dots_flag then
        Otreelib.to_dot
          (Filename.concat dot_dir (sprintf "%d.%s.dir.dot" counter#value cid))
          tree1 tree2 edits mapping [];

      analyze tree1 tree2 edits mapping iso
    end
  in

  let subtrees =
    List.map
      (fun (nd1, nd2) ->
        let t1, t2 = new c options nd1 false, new c options nd2 false in
        t1#expand_root; t1#root#hide_parent; t1#init;
        t2#expand_root; t2#root#hide_parent; t2#init;
        t1, t2
      ) subs
  in
  let sub_modified_pairs_l, sub_unmodified_pairs_l, sub_renamed_pairs_l =
    Xlist.split3 (List.map (compare_subtree options dot_dir) subtrees)
  in
  let sub_modified_pairs, sub_unmodified_pairs, sub_renamed_pairs =
    List.flatten sub_modified_pairs_l,
    List.flatten sub_unmodified_pairs_l,
    List.flatten sub_renamed_pairs_l
  in


  tree1#init; tree2#init;

  [%debug_log "[%s]" cid];

  let expand1, expand2 = ref expnd1, ref expnd2 in

  let modified   = ref modified_pairs in
  let unmodified = ref unmodified_pairs in
  let renamed    = ref renamed_pairs in

  while !expand1 <> [] || !expand2 <> [] do
    counter#incr;

    [%debug_log "expand1:\n%s"
      (Xlist.to_string (fun nd -> nd#data#to_string) "\n" !expand1)];

    [%debug_log "expand2:\n%s"
      (Xlist.to_string (fun nd -> nd#data#to_string) "\n" !expand2)];



    [%debug_log "%d COMPARING AGAIN [%s]" counter#value cid];

    List.iter (fun nd -> nd#expand) !expand1;
    List.iter (fun nd -> nd#expand) !expand2;

    tree1#init; tree2#init;

    let chldrn1 = Array.to_list tree1#root#children in
    let chldrn2 = Array.to_list tree2#root#children in
    let nchldrn1, nchldrn2 = List.length chldrn1, List.length chldrn2 in

    begin %debug_block
      [%debug_log "|T1|=%d |T2|=%d" tree1#size tree2#size];
      [%debug_log "nchildren1:%d nchildren2:%d" nchldrn1 nchldrn2];
      [%debug_log "tree_width_limit = %d" !tree_width_limit];
      [%debug_log "tree_size_limit = %d" !tree_size_limit]
    end;

    let (*subs*)_, modified_pairs, expnd1, expnd2, unmodified_pairs, renamed_pairs =
      if
        nchldrn1 > !tree_width_limit || nchldrn2 > !tree_width_limit ||
        tree1#size > !tree_size_limit || tree2#size > !tree_size_limit
      then begin
        [%debug_log "doing list comparison..."];
        compare_node_lists options tree1 tree2 chldrn1 chldrn2
      end
      else begin
        [%debug_log "doing tree comparison..."];
        let edits, mapping, iso =
          if tree1#is_flat && tree2#is_flat
          then
            Flattreediff.find ~rely_on_rel:false tree1 tree2
          else
            Treediff.find tree1 tree2
        in
        let _ =
          if options#dots_flag then
            Otreelib.to_dot
              (Filename.concat dot_dir
                 (sprintf "%d.%s.dir.dot" counter#value cid))
              tree1 tree2 edits mapping []
        in
        analyze tree1 tree2 edits mapping iso
      end
    in
    modified   := !modified @ modified_pairs;
    unmodified := !unmodified @ unmodified_pairs;
    renamed    := !renamed @ renamed_pairs;

    expand1 := expnd1; expand2 := expnd2;

  done;

  [%debug_log "finished"];

  !modified @ sub_modified_pairs,
  !unmodified @ sub_unmodified_pairs,
  !renamed @ sub_renamed_pairs
(* end of func compare_subtree *)
]


let save_modified_list fname list =
  let csv = [
    "original(path)"; "modified(path)";
    "original(digest)"; "modified(digest)";
    "change ratio";
    "unmodified rate";
    "deletes(groups)"; "inserts(groups)"; "relabels(groups)"; "moves(groups)";
    "total changes";
    "mapping size";
    "similarity";
    "units";
    "unmodified units";
    "size of structure preserving strict mapping";
    "average hunk size"
  ] ::
    (List.map
       (fun (o, n, od, nd, cr, ur, d, dg, i, ig, r, rg, m, mg, tc, ms, sim, u, uu, spsm, ahs) ->
         [o; n; od; nd; cr; ur;
          sprintf "%d(%d)" d dg;
          sprintf "%d(%d)" i ig;
          sprintf "%d(%d)" r rg;
          sprintf "%d(%d)" m mg;
          sprintf "%d" tc;
          sprintf "%d" ms;
          sim;
          sprintf "%d" u;
          sprintf "%d" uu;
          sprintf "%d" spsm;
          ahs;
        ]
       ) list
    )
  in
  Csv.save fname csv


let save_files_list1N fname list =
  let csv =
    ["old"; "new..."] ::
    (List.map (fun (o, ns) -> o#path :: (List.map (fun n -> n#path) ns)) list)
  in
  Csv.save fname csv

let save_files_listN1 fname list =
  let csv =
    ["old..."; "new"] ::
    (List.map (fun (os, n) -> (List.map (fun o -> o#path) os) @ [n#path]) list)
  in
  Csv.save fname csv


let save_files_list2 fname list =
  let csv = ["old"; "new"]::(List.map (fun (o, n) -> [o#path; n#path]) list) in
  Csv.save fname csv


let save_files_list lab fname list =
  Xfile.dump fname
    (fun ch ->
      fprintf ch "%s\n" lab;
      List.iter (fun f -> fprintf ch "%s\n" f#path) list)


[%%capture_path
let save_result dir modified_files =
  let fname = Filename.concat dir modified_files_list_file_name in

  [%debug_log "saving: \"%s\"" fname];

  let och = open_out_gen [Open_creat; Open_wronly] 0o644 fname in
  fprintf och "%d\n" (List.length modified_files);
  List.iter
    (fun (o, n) ->
      if o#path = n#path then
        fprintf och "%s\n" o#path
      else
        fprintf och "%s - %s\n" o#path n#path
    ) modified_files;
  close_out och
]

type info = { i_cache_path         : string;
              i_dtree1             : c;
              i_dtree2             : c;
              mutable i_modified   : (Storage.file * Storage.file) list;
              mutable i_unmodified : (Storage.file * Storage.file) list;
              i_renamed            : (Storage.file * Storage.file) list;
              i_moved              : (Storage.file * Storage.file) list;
              i_removed            : Storage.file list;
              i_added              : Storage.file list;
              i_copied             : (Storage.file * Storage.file list) list;
              i_glued              : (Storage.file list * Storage.file) list;
            }


[%%capture_path
let save_extra_result options ?get_cache_name
    { i_cache_path = dir;
      i_modified   = modified;
      i_unmodified = unmodified;
      i_renamed    = renamed;
      i_moved      = moved;
      i_removed    = removed;
      i_added      = added;
      i_copied     = copied;
      i_glued      = glued;
      _
    }
    =
  Xprint.verbose options#verbose_flag "saving extra information...";

  let fname_modified   = Filename.concat dir modified_files_csv in
  let fname_unmodified = Filename.concat dir unmodified_files_csv in
  let fname_renamed    = Filename.concat dir renamed_files_csv in
  let fname_moved      = Filename.concat dir moved_files_csv in
  let fname_removed    = Filename.concat dir removed_files_csv in
  let fname_added      = Filename.concat dir added_files_csv in
  let fname_copied     = Filename.concat dir copied_files_csv in
  let fname_glued      = Filename.concat dir glued_files_csv in

  [%debug_log "saving: \"%s\"" fname_modified];

  let modified', extra_unmodified =
    List.fold_left
      (fun (m, u) (o, n) ->
        try
          let cache_path =
            match get_cache_name with
            | Some f -> Cache.create_cache_path options (f o n)
            | None -> options#get_cache_path_for_file2 o n
          in

          [%debug_log "cache_path: \"%s\"" cache_path];

          let stat_paths =
            (Cache.search_cache :
               ?fuzzy:bool ->
               ?completion:bool ->
                 ?local_cache_name:string ->
                   string -> string -> Cache.search_result list)

              ~fuzzy:options#fuzzy_cache_flag
              ~local_cache_name:options#local_cache_name
              cache_path
              S.stat_file_name
          in

          let s =
            SF.scan_diff_stat ~max_retry_count:options#max_retry_count stat_paths
          in
          if s.SF.s_total_changes > 0 then
            let od = Xhash.to_hex o#digest in
            let nd = Xhash.to_hex n#digest in
            (o#path, n#path, od, nd,
             s.SF.s_change_ratio,
             s.SF.s_unmodified_rate,
             s.SF.s_deletes,
             s.SF.s_deletes_gr,
             s.SF.s_inserts,
             s.SF.s_inserts_gr,
             s.SF.s_relabels,
             s.SF.s_relabels_gr,
             s.SF.s_moves,
             s.SF.s_moves_gr,
             s.SF.s_total_changes,
             s.SF.s_mapping,
             s.SF.s_similarity,
             s.SF.s_units,
             s.SF.s_unmodified_units,
             s.SF.s_SPSM,
             s.SF.s_AHS
            ) :: m,
            u
          else
            m, (o, n)::u
        with
        | S.Stat_not_found | Failure _ | Sys_error _ | Lang_base.Error _ ->
            [%debug_log "cache not found: %s - %s" o#path n#path];
            let od = Xhash.to_hex o#digest in
            let nd = Xhash.to_hex n#digest in
            (o#path, n#path, od, nd, "-", "-", -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, "-", -1, -1, -1, "-")
            ::m,
            u
      ) ([], []) modified
  in

  let unmodified' = unmodified @ extra_unmodified in

  save_modified_list fname_modified modified';

  [%debug_log "saving: \"%s\"" fname_unmodified];
  save_files_list2 fname_unmodified unmodified';

  [%debug_log "saving: \"%s\"" fname_renamed];
  save_files_list2 fname_renamed renamed;

  [%debug_log "saving: \"%s\"" fname_moved];
  save_files_list2 fname_moved moved;

  [%debug_log "saving: \"%s\"" fname_removed];
  save_files_list "removed" fname_removed removed;

  [%debug_log "saving: \"%s\"" fname_added];
  save_files_list "added" fname_added added;

  [%debug_log "saving: \"%s\"" fname_copied];
  save_files_list1N fname_copied copied;

  [%debug_log "saving: \"%s\"" fname_glued];
  save_files_listN1 fname_glued glued;

  Xprint.verbose options#verbose_flag "done."
]

exception Cache_not_found

(*
let load_result dir =
  let fname = Filename.concat dir modified_files_list_file_name in
  let res = ref [] in
  let length = ref 0 in
  let count = ref 0 in
  try
    let ich = open_in fname in
    let f = fun s1 s2 -> res := (s1, s2)::!res in
    let _ =
      try
        length := int_of_string(input_line ich)
      with
        Failure "int_of_string" ->
          begin close_in ich; raise Cache_not_found end
      | End_of_file -> begin close_in ich; raise Cache_not_found end
    in
    let result =
      try
        while true do
          Scanf.sscanf (input_line ich) "%s - %s" f;
          incr count;
        done; []
      with End_of_file -> !res
    in
    close_in ich;
    if !length <> !count then raise Cache_not_found;
    result
  with Sys_error s ->
    if s = (sprintf "\"%s\": no such file or directory" fname)
    then raise Cache_not_found
    else error "%s" s
 *)


let dump_diff_stat options old_tree new_tree =
  let cache_path = get_cache_path_for_dir2 options old_tree new_tree in
  SD.dump_diff_stat cache_path





class diff_result
    ~(cache_path:string)
    ~(all_leaves1:node_t list)
    ~(all_leaves2:node_t list)
    ~(removed:node_t list)
    ~(added:node_t list)
    ~(modified:node_map)
    ~(renamed:node_map)
    ~(moved:node_map)
    ~(copied:(node_t * node_t list) list)
    ~(glued:(node_t list * node_t) list)
    =
  object
    method cache_path  = cache_path
    method all_leaves1 = all_leaves1
    method all_leaves2 = all_leaves2
    method removed     = removed
    method added       = added
    method modified    = modified
    method renamed     = renamed
    method moved       = moved
    method copied      = copied
    method glued       = glued
  end

let null_fact_extractor _ _ = ()


(* comparing directory structures *)
[%%capture_path
let compare_trees ?(fact_extractor=null_fact_extractor) options tree1 tree2 =
  try
    let dtree1, tbl1 = of_tree options true tree1 in
    let dtree2, tbl2 = of_tree options true tree2 in

    let cache_path = get_cache_path2 options dtree1 dtree2 in

    Xprint.verbose options#verbose_flag "cache: %s" cache_path;

    let dtbl1 = collapse_tree dtree1 in
    let dtbl2 = collapse_tree dtree2 in

(*
    try
      raise Cache_not_found;

      let result = load_result cache_path in
      if !viewer_flag then
        printf "%c%c%c%!"
          Options.viewer_mode_status_OK (char_of_int 0) (char_of_int 0);
      result
    with
      Cache_not_found ->
*)
        if not options#viewer_flag then
          printf "comparing directory structures...\n";

        let _ = Cache.prepare_cache_dir options cache_path in

        let _ = (dtree1#expand_all : node_t -> bool) in
        let _ = (dtree2#expand_all : node_t -> bool) in

        let _unmodified0, _renamed0, _moved0 =
          pp0 dtree1 dtree2 dtbl1 dtbl2 tbl1 tbl2
        in

        let unmodified0, renamed0, moved0, copied, glued =
          pp1 tbl1 tbl2
        in

        let modified0 = pp2 tbl1 tbl2 in

        dtree1#init;
        dtree2#init;

        [%debug_log "T1:\n%s\n" dtree1#to_string];
        [%debug_log "T2:\n%s\n" dtree2#to_string];

        let _ = collapse_tree dtree1 in
        let _ = collapse_tree dtree2 in

        let _modified, unmodified, renamed =
          compare_subtree options cache_path (dtree1, dtree2)
        in

        let _modified = union [_modified; modified0] in
        let modified = new node_map in
        modified#add_list _modified;

        unmodified0#add_map _unmodified0;
        unmodified0#add_list unmodified;
        let unmodified = unmodified0  in

        renamed0#add_map _renamed0;
        renamed0#add_list renamed;
        let renamed = renamed0 in

        moved0#add_map _moved0;
        let moved = moved0 in

        let dnps = ref [] in

        let pr1 = try options#fact_proj_roots.(0) with _ -> "" in
        let pr2 = try options#fact_proj_roots.(1) with _ -> "" in
        List.iter
          (fun (n1, n2) ->
            let p1 = Triple.get_proj_rel_path pr1 n1#data#path in
            let p2 = Triple.get_proj_rel_path pr2 n2#data#path in
            if p1 <> p2 then begin
              let dn1 = Filename.dirname p1 in
              let dn2 = Filename.dirname p2 in
              if dn1 <> dn2 then begin
                moved#add n1 n2;
                dnps := (dn1, dn2)::!dnps
              end;
              if (Filename.basename p1) <> (Filename.basename p2) then
                renamed#add n1 n2;
            end
          ) _modified;

        let all_leaves1 = dtree1#get_whole_initial_leaves in
        let all_leaves2 = dtree2#get_whole_initial_leaves in

        let subtract l l0 =
          let s = Xset.from_list l in
          List.iter (Xset.remove s) l0;
          Xset.to_list s
        in

        let glued1 =
          let glu1, _ = List.split glued in
          List.flatten glu1
        in
        let copied2 =
          let _, cop2 = List.split copied in
          List.flatten cop2
        in

        let get_removed_and_added () =
          let mapped1, mapped2 =
            let mod1, mod2 = modified#split in
            let sta1, sta2 = unmodified#split in
            let ren1, ren2 = renamed#split in
            let mov1, mov2 = moved#split in

            mod1 @ sta1 @ ren1 @ mov1 @ glued1,
            mod2 @ sta2 @ ren2 @ mov2 @ copied2
          in
          let removed = subtract all_leaves1 mapped1 in
          let added   = subtract all_leaves2 mapped2 in
          removed, added
        in
        let removed, added = get_removed_and_added() in

        let elaborated_flag = ref false in

        let get_dns pr =
          List.map
            (fun n ->
              let p = Triple.get_proj_rel_path pr n#data#path in
              Filename.dirname p, n
            )
        in
        (*let dnps1, dnps2 = List.split !dnps in*)
        let cands1 = (*List.filter (fun (dn, _) -> List.mem dn dnps1)*) (get_dns pr1 removed) in
        let cands2 = (*List.filter (fun (dn, _) -> List.mem dn dnps2)*) (get_dns pr2 added) in

        if cands1 <> [] && cands2 <> [] then begin
          let rename_pats = find_rename_pats !dnps in
          if rename_pats <> [] then begin
            printf "%d rename pattern(s) found:\n" (List.length rename_pats);
            List.iter
              (fun ((src, dst), freq) ->
                printf "%s -> %s (%d)\n" src dst freq
              ) rename_pats;
            let substl =
              List.map
                (fun ((src, dst), _) ->
                  Str.regexp_string src, dst
                  ) rename_pats
            in
            let apply_subst dn_opt bn =
              List.fold_left
                (fun n (re, dst) ->
                  if
                    match dn_opt with
                    | Some dn -> begin
                        try
                          let _ = Str.search_forward re dn 0 in
                          true
                        with Not_found -> false
                    end
                    | None -> true
                  then
                    Str.global_replace re dst n
                  else
                    n
                ) bn substl
            in
            let is_renamed p1 p2 =
              let dn1 = Filename.dirname p1 in
              let dn2 = Filename.dirname p2 in
              let bn1 = Filename.basename p1 in
              let bn2 = Filename.basename p2 in
              let dn_opt =
                if dn1 = dn2 then
                  None
                else
                  Some dn1
              in
              apply_subst dn_opt bn1 = bn2
            in
            List.iter
              (fun (_, cand1) ->
                List.iter
                  (fun (_, cand2) ->
                    let p1 = Triple.get_proj_rel_path pr1 cand1#data#path in
                    let p2 = Triple.get_proj_rel_path pr2 cand2#data#path in
                    if is_renamed (String.lowercase_ascii p1) (String.lowercase_ascii p2) then begin
                      printf "rename candidate: %s -> %s\n" p1 p2;
                      modified#add cand1 cand2;
                      if (Filename.dirname p1) <> (Filename.dirname p2) then
                        moved#add cand1 cand2;
                      renamed#add cand1 cand2;
                      elaborated_flag := true
                    end
                  ) cands2
              ) cands1
          end
        end;

        let removed, added =
          if !elaborated_flag then
            get_removed_and_added()
          else
            removed, added
        in

        (*if options#viewer_flag then begin
          let len = modified#size in
          let mm = (len land 0xff00) lsr 8 in
          let ll = (len land 0x00ff) in
          printf "%c%!" Const.viewer_mode_status_OK;
          printf "%c%c%!" (char_of_int mm) (char_of_int ll)
        end
        else*)
          printf "done.\n";

        (*let mkfiles2 = List.map (fun (nd1, nd2) -> mkfile tree1 nd1, mkfile tree2 nd2) in*)
        let mkfiles1N =
          List.map (fun (nd1, nds) -> mkfile tree1 nd1, List.map (mkfile tree2) nds)
        in
        let mkfilesN1 =
          List.map (fun (nds, nd2) -> List.map (mkfile tree1) nds, mkfile tree2 nd2)
        in
        let mkfilepair n1 n2 = mkfile tree1 n1, mkfile tree2 n2 in

        let modified_files   = modified#map mkfilepair in

        let unmodified_files = unmodified#map mkfilepair in
        let renamed_files    = renamed#map mkfilepair in
        let moved_files      = moved#map mkfilepair in
        let copied_files     = mkfiles1N copied in
        let glued_files      = mkfilesN1 glued in


        let all_files1 = mkfiles tree1 all_leaves1 in
        let all_files2 = mkfiles tree2 all_leaves2 in

        begin %debug_block
          printf "All files in \"%s\"\n" dtree1#id;
          let paths = List.map (fun f -> f#path) all_files1 in
          let paths = List.fast_sort Stdlib.compare paths in
          List.iter (fun p -> printf " %s\n" p) paths
        end;

        let removed_files = mkfiles tree1 removed in
        let added_files   = mkfiles tree2 added in


        save_result cache_path modified_files;

        let diff_result =
          new diff_result ~cache_path
            ~all_leaves1 ~all_leaves2
            ~removed ~added ~modified ~renamed
            ~moved ~copied ~glued
        in
        fact_extractor options diff_result;


        if not options#viewer_flag then begin
          let nfiles1 = List.length all_files1 in
          let nfiles2 = List.length all_files2 in

          Xprint.message "%d/%d modified files:" modified#size nfiles1;
          begin %debug_block
          modified#iter
            (fun n1 n2 ->
              [%debug_log "[MOD] %s -> %s" n1#data#to_string n2#data#to_string]
            )
          end;

          Xprint.message "%d/(%d) added files:" (List.length added) nfiles2;
          begin %debug_block
          List.iter
            (fun n ->
              [%debug_log "[ADD] %s" n#data#to_string]
            ) added
          end;

          Xprint.message "%d/%d removed files:" (List.length removed) nfiles1;
          begin %debug_block
          List.iter
            (fun n ->
              [%debug_log "[REM] %s" n#data#to_string]
            ) removed
          end;

          Xprint.message "%d/%d renamed files:" renamed#size nfiles1;
          begin %debug_block
          renamed#iter
            (fun n1 n2 ->
              [%debug_log "[REN] %s -> %s" n1#data#to_string n2#data#to_string]
            )
          end;

          Xprint.message "%d/%d moved files:" moved#size nfiles1;
          begin %debug_block
          moved#iter
            (fun n1 n2 ->
              [%debug_log "[MOV] %s -> %s" n1#data#to_string n2#data#to_string]
            )
          end;

          Xprint.message "%d/(%d) copied files:" (List.length copied2) nfiles2;
          begin %debug_block
          List.iter
            (fun (n1, ns2) ->
              [%debug_log "[CPY] %s ->" n1#data#to_string];
              List.iter (fun n -> [%debug_log "[CPY]   %s" n#data#to_string]) ns2
            ) copied
          end;

          Xprint.message "%d/%d glued files:" (List.length glued1) nfiles1;
          begin %debug_block
          List.iter
            (fun (ns1, n2) ->
              List.iter (fun n -> [%debug_log "[GLU] %s" n#data#to_string]) ns1;
              [%debug_log "[GLU]   -> %s" n2#data#to_string]
            ) glued
          end;

          Xprint.message "%d/%d unmodified files:" unmodified#size nfiles1;
          begin %debug_block
          unmodified#iter
            (fun n1 n2 ->
              [%debug_log "[UNM] %s - %s" n1#data#to_string n2#data#to_string]
            )
          end;

        end;

        let info =
          { i_cache_path = cache_path;
            i_dtree1     = dtree1;
            i_dtree2     = dtree2;
            i_modified   = modified_files;
            i_unmodified = unmodified_files;
            i_renamed    = renamed_files;
            i_moved      = moved_files;
            i_removed    = removed_files;
            i_added      = added_files;
            i_copied     = copied_files;
            i_glued      = glued_files;
          }
        in
        info
  with
    To_be_skipped -> begin
      Xprint.message "no relevant source files found.";
      exit 0
    end
]


let fact_extractor options info =
  if options#fact_flag then begin
    try
      let pr1 = try options#fact_proj_roots.(0) with _ -> "" in
      let kv1 = try options#fact_versions.(0) with _ -> Entity.unknown_version in

      let pr2 = try options#fact_proj_roots.(1) with _ -> "" in
      let kv2 = try options#fact_versions.(1) with _ -> Entity.unknown_version in

      let mkfent1 = fent_of_nd options pr1 kv1 in
      let mkfent2 = fent_of_nd options pr2 kv2 in

      let mkfid1 = fid_of_nd options pr1 kv1 in
      let mkfid2 = fid_of_nd options pr2 kv2 in

      let need_locent = Entity.is_FD_encoding options#fact_enc in
      let mklocent1 = fent_of_nd ~force_PVF:true options pr1 kv1 in
      let mklocent2 = fent_of_nd ~force_PVF:true options pr2 kv2 in


      let into_virtuoso = options#fact_into_virtuoso <> "" in
      let into_directory = options#fact_into_directory <> "" in

      let map_path = ref "" in
      let changes_path = ref "" in
      (*let delta_path = ref "" in*)

      let fact_buf = create_fact_buf options ~into_virtuoso ~into_directory info#cache_path in

      let fact_buf_for_mapping, fact_buf_for_changes(*, fact_buf_for_delta*) =
        if into_virtuoso || into_directory then begin
          fact_buf, fact_buf(*, fact_buf*)
        end
        else begin
          let mkfbuf path_ref file_name =
            let path = Filename.concat info#cache_path (file_name^".nt") in
            let _ = path_ref := path in
            let fbuf =
              try
                new T.buffer ~overwrite:false options path
              with
              | T.File_exists s ->
                  let _ = s in
                  [%warn_log "file exists: \"%s\"" s];
                  T.dummy_buffer
            in
            fbuf
          in
          let map_fbuf = mkfbuf map_path Stat.map_file_name in
          let changes_fbuf = mkfbuf changes_path Stat.changes_file_name in
          (*let delta_fbuf = mkfbuf delta_path Stat.delta_file_name in*)
          map_fbuf, changes_fbuf(*, delta_fbuf*)
        end
      in

      let stree_id1, stree_ent1 = _extract_fact fact_buf options pr1 kv1 info#all_leaves1 in
      let stree_id2, stree_ent2 = _extract_fact fact_buf options pr2 kv2 info#all_leaves2 in

      let stree_pair_ent = T.make_entity_pair stree_id1 stree_id2 in

      fact_buf#add (stree_pair_ent, T.p_is_a, T.c_srctree_pair);
      fact_buf#add (stree_pair_ent, T.p_orig_srctree, stree_ent1);
      fact_buf#add (stree_pair_ent, T.p_mod_srctree, stree_ent2);


      if options#fact_for_mapping_flag then begin
        if into_virtuoso then
          Xprint.verbose options#verbose_flag "dumping map fact into virtuoso..."
        else if into_directory then
          Xprint.verbose options#verbose_flag
            "dumping map fact into directory \"%s\"..." options#fact_into_directory
        else
          Xprint.verbose options#verbose_flag "dumping map fact to \"%s\"..." !map_path;

        info#modified#iter
          (fun f1 f2 ->
            let fid1, fid2 = mkfid1 f1, mkfid2 f2 in
            let fent1, fent2 = T.mkent fid1, T.mkent fid2 in
            fact_buf_for_mapping#add (fent1, T.p_mapped_neq_to, fent2);
            let fpent = T.make_entity_pair fid1 fid2 in
            fact_buf_for_mapping#add (fpent, T.p_is_a, T.c_file_pair);
            fact_buf_for_mapping#add (fpent, T.p_srctree_pair, stree_pair_ent);
            fact_buf_for_mapping#add (stree_pair_ent, T.p_file_pair, fpent);
            fact_buf_for_mapping#add (fpent, T.p_orig_file, fent1);
            fact_buf_for_mapping#add (fpent, T.p_mod_file, fent2);
          )
      end;

      if options#fact_for_changes_flag then begin
        if into_virtuoso then
          Xprint.verbose options#verbose_flag "dumping changes fact into virtuoso..."
        else if into_directory then
          Xprint.verbose options#verbose_flag
            "dumping changes fact into directory \"%s\"..." options#fact_into_directory
        else
          Xprint.verbose options#verbose_flag "dumping changes fact to \"%s\"..." !changes_path;


        let vent1 = T.make_version_entity kv1 in
        let vent2 = T.make_version_entity kv2 in

        let vent1_ok = not (T.is_ghost_node vent1) in
        let vent2_ok = not (T.is_ghost_node vent2) in

        let get_locent tbl mklocent vent vent_ok n =
          try
            Hashtbl.find tbl n
          with
            Not_found ->
              let locent = mklocent n in
              Hashtbl.add tbl n locent;
              fact_buf_for_changes#add (locent, T.p_is_a, T.c_loc);
              fact_buf_for_changes#add (locent, T.p_path, T.make_literal n#data#path);
              if vent_ok then
                fact_buf_for_changes#add (locent, T.p_version, vent);
              locent
        in
        let locent_tbl1 = Hashtbl.create 0 in
        let locent_tbl2 = Hashtbl.create 0 in

        let get_locent1 = get_locent locent_tbl1 mklocent1 vent1 vent1_ok in
        let get_locent2 = get_locent locent_tbl2 mklocent2 vent2 vent2_ok in

        List.iter
          (fun n ->
            fact_buf_for_changes#add (mkfent1 n, T.p_pruned_from, stree_ent2);

            if need_locent then begin
              fact_buf_for_changes#add (get_locent1 n, T.p_pruned_from, stree_ent2)
            end

          ) info#removed;

        List.iter
          (fun n ->
            fact_buf_for_changes#add (mkfent2 n, T.p_grafted_onto, stree_ent1);

            if need_locent then begin
              fact_buf_for_changes#add (get_locent2 n, T.p_grafted_onto, stree_ent1)
            end

          ) info#added;

        info#modified#iter
          (fun n1 n2 ->
            fact_buf_for_changes#add (mkfent1 n1, T.p_modified, mkfent2 n2);

            if need_locent then begin
              fact_buf_for_changes#add (get_locent1 n1, T.p_modified, get_locent2 n2)
            end

          );

        info#renamed#iter
          (fun n1 n2 ->
            fact_buf_for_changes#add (mkfent1 n1, T.p_renamed, mkfent2 n2);

            if need_locent then begin
              fact_buf_for_changes#add (get_locent1 n1, T.p_renamed, get_locent2 n2)
            end

          );

        info#moved#iter
          (fun n1 n2 ->
            fact_buf_for_changes#add (mkfent1 n1, T.p_moved_to, mkfent2 n2);

            if need_locent then begin
              fact_buf_for_changes#add (get_locent1 n1, T.p_moved_to, get_locent2 n2)
            end

          );

        List.iter
          (fun (f1, fs2) ->
            List.iter
              (fun f2 ->
                fact_buf_for_changes#add (mkfent2 f2, T.p_copied_from, mkfent1 f1);

                if need_locent then begin
                  fact_buf_for_changes#add (get_locent1 f1, T.p_copied_from, get_locent2 f2)
                end

              ) fs2
          ) info#copied;

        List.iter
          (fun (fs1, f2) ->
            List.iter
              (fun f1 ->
                fact_buf_for_changes#add (mkfent1 f1, T.p_glued_to, mkfent2 f2);

                if need_locent then begin
                  fact_buf_for_changes#add (get_locent1 f1, T.p_glued_to, get_locent2 f2)
                end

              ) fs1
          ) info#glued
      end;
(*
      if options#fact_for_delta_flag then begin
        if into_virtuoso then
          Xprint.verbose options#verbose_flag "dumping delta fact into virtuoso..."
        else if into_directory then
          Xprint.verbose options#verbose_flag
            "dumping delta fact into directory \"%s\"..." options#fact_into_directory
        else
          Xprint.verbose options#verbose_flag "dumping delta fact to \"%s\"..." !delta_path;

        let make_chg_inst tag ln1 ln2 =
          let ln = String.concat Entity.sep [ln1; ln2; Editop.tag_to_string tag] in
          T.mkchginst ln
        in
        let triple_add chg xml cls ent1 ent2 =
          fact_buf_for_delta#add (chg, T.p_is_a, cls);
          fact_buf_for_delta#add (chg, T.p_xml, T.make_literal xml);
          fact_buf_for_delta#add (chg, T.p_entity1, ent1);
          fact_buf_for_delta#add (chg, T.p_entity2, ent2);
        in
        List.iter
          (fun n ->
            let chg = make_chg_inst Editop.Tdel (mkfid1 n) stree_id2 in
            let xml = Delta_base.make_remove_file_elem n#data#path in
            triple_add chg xml T.c_del (mkfent1 n) stree_ent2
          ) info#removed;

        List.iter
          (fun n ->
            let chg = make_chg_inst Editop.Tins stree_id1 (mkfid2 n) in
            let cch = n#data#get_content_channel_for_xml() in
            let xml = Delta_base.make_add_file_elem n#data#path cch in
            cch#close_in();
            triple_add chg xml T.c_ins stree_ent1 (mkfent2 n)
          ) info#added;

        info#renamed#iter
          (fun n1 n2 ->
            let chg = make_chg_inst Editop.Trel (mkfid1 n1) (mkfid2 n2) in
            let xml = Delta_base.make_rename_file_elem n1#data#path n2#data#path in
            triple_add chg xml T.c_rel (mkfent1 n1) (mkfent2 n2)
          );

        info#moved#iter
          (fun n1 n2 ->
            let chg = make_chg_inst Editop.Tmov (mkfid1 n1) (mkfid2 n2) in
            let xml = Delta_base.make_move_file_elem n1#data#path n2#data#path in
            triple_add chg xml T.c_mov (mkfent1 n1) (mkfent2 n2)
          );

        info#modified#iter
          (fun n1 n2 ->
            if n1#data#is_auxfile && n2#data#is_auxfile then begin
              let chg = make_chg_inst Editop.Trel (mkfid1 n1) (mkfid2 n2) in
              let cch = n2#data#get_content_channel_for_xml() in
              let xml = Delta_base.make_change_file_elem n2#data#path cch in
              cch#close_in();
              triple_add chg xml T.c_rel (mkfent1 n1) (mkfent2 n2)
            end
          );

      end;
*)
      fact_buf#close;

      fact_buf_for_mapping#close;

      fact_buf_for_changes#close;

      (*fact_buf_for_delta#close*)

    with
      T.Lock_failed ->
        Xprint.warning "fact buffer is already locked."

  end (* if options#fact_flag *)


let compare_dirs options dir1 dir2 = (* comparing directory structures *)
  let mkprefix d = if Filename.is_relative d then Filename.concat (Unix.getcwd()) d else d in
  let prefix1 = mkprefix dir1 in
  let prefix2 = mkprefix dir2 in
  let tree1 = new Fs.tree options prefix1 in
  let tree2 = new Fs.tree options prefix2 in
  compare_trees options tree1 tree2


let compare_trees options tree1 tree2 =
  compare_trees ~fact_extractor options tree1 tree2
