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
(*
 * tree matching algorithm by Zhang and Shasha
 *
 * ZS.ml
 *
 * derived from
 * 'Simple Fast Algorithms for the Editing Distance Between Trees and Related Problems'
 * K.Zhang and D.Shasha,
 * SIAM J.Comput. vol.18, no.6, pp.1245-1262, 1989.
 *
 *)

[%%prepare_logger]


module Effect = struct
  type t =
    | Edit of Edit.t
    | Mapping_elem of Mapping.elem

  let relabel (i, j) = Edit (Edit.Relabel(i, j))
  let insert i = Edit (Edit.Insert(i, ref []))
  let delete i = Edit (Edit.Delete i)
  let mapping_elem elem = Mapping_elem elem

  let get_edits_and_mapping efs =
    let edits, mapping = ref Edit.empty_seq, ref Mapping.empty in
    List.iter
      (function
        | Edit ed -> edits := Edit.seq_add ed !edits
        | Mapping_elem elem -> mapping := Mapping.add elem !mapping
      ) efs;
    !edits, !mapping

end (* of module Effect *)



[%%capture_path
module F (W : Weight.T) = struct

  let minn_do l =
    let min, act =
      List.fold_left
        (fun ((m, (*a*)_) as acc) ((x, (*f*)_) as xf) ->
          if W.lt x m then xf else acc
        ) (W.max, fun () -> ()) l
    in
    act();
    min


  let treedist cost_func treedist_array tree1 tree2 i j =
    let cost i j = cost_func tree1 tree2 i j in

    let li, lj = tree1#leftmost i, tree2#leftmost j in

    let forestdist_array =
      Array.make_matrix (i - li + 2) (j - lj + 2) (W.min, [])
    in

    let conv ((li, i1, lj, j1) as x) =
      let bi = li > i1 in
      let bj = lj > j1 in
      if bi then
        if bj then
          (1, 0, 1, 0)
        else
          (1, 0, lj, j1)
      else
        if bj then
          (li, i1, 1, 0)
        else
          x
    in
    let set_forestdist_array x n efs =
      let li, i1, lj, j1 = conv x in
      forestdist_array.(i1 - li + 1).(j1 - lj + 1) <- (n, efs)
    in
    let forestdist x =
      let li, i1, lj, j1 = conv x in
      forestdist_array.(i1 - li + 1).(j1 - lj + 1)
    in

    let compute_treedist() =
      forestdist_array.(0).(0) <- (W.zero, []);

      for i1 = li to i do
        let n, efs = forestdist (li, i1 - 1, 1, 0) in
        set_forestdist_array
          (li, i1, 1, 0) (W.plus n (cost i1 0)) ((Effect.delete i1)::efs)
      done;

      for j1 = lj to j do
        let n, efs = forestdist (1, 0, lj, j1 - 1) in
        set_forestdist_array
          (1, 0, lj, j1) (W.plus n (cost 0 j1)) ((Effect.insert j1)::efs)
      done;

      for i1 = li to i do
        for j1 = lj to j do
          let li1, lj1 = tree1#leftmost i1, tree2#leftmost j1 in

          if li1 = li && lj1 = lj then
            let _ =
              minn_do
                [
                 (
                  let c = cost i1 0 in
                  let n, efs = forestdist (li, i1 - 1, lj, j1) in
                  (W.plus n c,
                   (fun () ->
                     let efs' = (Effect.delete i1)::efs in
                     set_forestdist_array (li, i1, lj, j1) (W.plus n c) efs'))
                 );
                 (
                  let c = cost 0 j1 in
                  let n, efs = forestdist (li, i1, lj, j1 - 1) in
                  (W.plus n c,
                   (fun () ->
                     let efs' = (Effect.insert j1)::efs in
                     set_forestdist_array (li, i1, lj, j1) (W.plus n c) efs'))
                 );
                 (
                  let c = cost i1 j1 in
                  let n, efs = forestdist (li, i1 - 1, lj, j1 - 1) in
                  (W.plus n c,
                   (fun () ->
                     let efs' = (Effect.mapping_elem(i1, j1))::efs in
                     let efs' =
                       if not ((tree1#get i1)#data#equals (tree2#get j1)#data) then
                         (Effect.relabel(i1, j1))::efs'
                       else
                         efs'
                     in
                     set_forestdist_array (li, i1, lj, j1) (W.plus n c) efs'))
                 )
               ]
            in
            treedist_array.(i1 - 1).(j1 - 1) <- (forestdist(li, i1, lj, j1));
          else
            let _ =
              minn_do
                [
                 (
                  let c = cost i1 0 in
                  let n, efs = forestdist (li, i1 - 1, lj, j1) in
                  (W.plus n c,
                   (fun () ->
                     let efs' = (Effect.delete i1)::efs in
                     set_forestdist_array (li, i1, lj, j1) (W.plus n c) efs'))
                 );
                 (
                  let c = cost 0 j1 in
                  let n, efs = forestdist (li, i1, lj, j1 - 1) in
                  (W.plus n c,
                   (fun () ->
                     let efs' = (Effect.insert j1)::efs in
                     set_forestdist_array (li, i1, lj, j1) (W.plus n c) efs'))
                 );
                 (
                  let n, efs = forestdist (li, li1 - 1, lj, lj1 - 1) in
                  let n0, efs0 = treedist_array.(i1 - 1).(j1 - 1) in
                  (W.plus n n0,
                   (fun () ->
                     let efs' = efs @ efs0 in
                     set_forestdist_array (li, i1, lj, j1) (W.plus n n0) efs'))
                 )
               ]
            in ()
        done
      done
    in
    compute_treedist();

    [%debug_log "(%d,%d):\n%s" i j
      (
       let buf = Buffer.create 0 in
       for ii = 0 to i - li + 1 do
         for jj = 0 to j -lj + 1 do
           let n, _ = forestdist_array.(ii).(jj) in
           Buffer.add_string buf (Printf.sprintf "%s " (W.to_string n))
         done;
         Buffer.add_string buf "\n"
       done;
       Buffer.contents buf
      )];

    treedist_array.(i - 1).(j - 1)


  exception Subtree

(* finds roots of isomorphic subtrees *)
  let find_isomorphic_subtrees treedist_array tree1 (*tree2*)_ mapping =
    (* assumes sorted (in descending order) mapping *)
    let res = ref [] in
    List.iter
      (fun (x, y) ->
        let n, (*efs*)_ = treedist_array.(x - 1).(y - 1) in
        if n = W.zero then
          try
            List.iter
              (fun i ->
                if (tree1#leftmost i) <= x && x < i then raise Subtree
              ) !res;
            res := x::!res
          with
            Subtree -> ()
      ) mapping;

    [%debug_log "roots of isomorphic subtrees of T1: [%s]"
      (Xlist.to_string string_of_int "," !res)];

    !res


  let find cost_func tree1 tree2 =

    let cost_tbl = Array.make_matrix (tree1#size + 1) (tree2#size + 1) W.zero in
    for i = 0 to tree1#size do
      for j = 0 to tree2#size do
        cost_tbl.(i).(j) <- (cost_func tree1 tree2 i j)
      done
    done;
    let cost_func (*tree1*)_ (*tree2*)_ i j = cost_tbl.(i).(j) in

    let keyroots1 = tree1#keynodes in
    let keyroots2 = tree2#keynodes in
    let nkeyroots1 = List.length keyroots1 in
    let nkeyroots2 = List.length keyroots2 in

    let treedist_array = Array.make_matrix tree1#size tree2#size (W.min, []) in

    for ii = 1 to nkeyroots1 do
      for jj = 1 to nkeyroots2 do
        let i = List.nth keyroots1 (ii - 1) in
        let j = List.nth keyroots2 (jj - 1) in
        let _, _ = treedist cost_func treedist_array tree1 tree2 i j in
        ()
      done
    done;

    [%debug_log "DISTANCE MATRIX:\n%s"
      (
       let buf = Buffer.create 0 in
       for i = 0 to tree1#size - 1 do
         for j = 0 to tree2#size - 1 do
           let n, (*efs*)_ = treedist_array.(i).(j) in
           Buffer.add_string buf (Printf.sprintf "%s " (W.to_string n))
         done;
         Buffer.add_string buf "\n"
       done;
       Buffer.contents buf
      )];


    let (*n*)_, efs = treedist_array.(tree1#size - 1).(tree2#size - 1) in
    let edits, mapping = Effect.get_edits_and_mapping efs in

    let mapping = Mapping.descent_sort mapping in
    let iso = find_isomorphic_subtrees treedist_array tree1 tree2 mapping in
    edits, mapping, iso

end (* of functor ZS.F *)
]

module Int = F(Weight.Int)
module Float = F(Weight.Float)

