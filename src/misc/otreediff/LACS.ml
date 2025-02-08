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
 * LACS (Largest Approximately Common Substructures)
 *
 * LACS.ml
 *
 * derived from
 * 'Finding the Largest Approximately Common Substructures of Two Trees'
 * J.T.L.Wang, B.A.Shapiro, D.Shasha, K.Zhang, and K.M.Currey,
 * IEEE Trans. Pattern Analysis And Machine Intelligence,
 * vol.20, no.8, pp.889-895, 1998.
 *
 *)

[%%prepare_logger]

open Common
open Otree


let array3_create x y z ini =
  let a = Array.make z (Array.make_matrix 0 0 ini) in
  for i = 0 to z - 1 do
    let mat = Array.make_matrix x y ini in
    a.(i) <- mat
  done;
  a

let array3_set a (i, j, k) v = a.(k).(i).(j) <- v
let array3_get a (i, j, k) = a.(k).(i).(j)


let conv(li, s, lj, t) =
  let li, s = if li > s then 1, 0 else li, s in
  let lj, t = if lj > t then 1, 0 else lj, t in
  li, s, lj, t


(*** Cuts ***)
module Cut =
  struct
    type t = index list
    let empty = []
    let add cut cut' = cut @ cut'
    let to_string cut =
      "["^(Xlist.to_string string_of_int "," cut)^"]"
  end

(*** Effects ***)
module Effect =
  struct
    type t =
        Edit of Edit.t
      | Mapping_elem of Mapping.elem
      | Cut1 of Cut.t
      | Cut2 of Cut.t

    let relabel(i, j) = Edit(Edit.Relabel(i, j))
    let insert i = Edit(Edit.Insert(i, ref []))
    let delete i = Edit(Edit.Delete i)
    let mapping_elem elem = Mapping_elem elem
    let cut1 c = Cut1 c
    let cut2 c = Cut2 c

    let get_edits_and_mapping_and_cuts efs =
      let edits, mapping = ref Edit.empty_seq, ref Mapping.empty in
      let cut1, cut2 = ref Cut.empty, ref Cut.empty in
      List.iter
        (function
            Edit ed -> edits := Edit.seq_add ed !edits
          | Mapping_elem elem -> mapping := Mapping.add elem !mapping
          | Cut1 c -> cut1 := Cut.add c !cut1
          | Cut2 c -> cut2 := Cut.add c !cut2
        ) efs;
      !edits, !mapping, !cut1, !cut2

  end


let find_largest_1 beta_array psi_array tree1 tree2 (i, j) =
  let li, lj = tree1#leftmost i, tree2#leftmost j in

(*
  let psi_array = Array.make_matrix (i - li + 2) (j - lj + 2) (-1, []) in

  let set_psi_array (li, s, lj, t) n efs =
    let li, s, lj, t = conv(li, s, lj, t) in
    psi_array.(s - li + 1).(t - lj + 1) <- (n, efs)
  in
  let psi(li, s, lj, t) =
    let li, s, lj, t = conv(li, s, lj, t) in
    psi_array.(s - li + 1).(t - lj + 1)
  in
*)

  let set_psi_array (li, s, lj, t) n efs =
    let li, s, lj, t = conv(li, s, lj, t) in
    array3_set psi_array (s - li + 1, t - lj + 1, 0) (n, efs)
  in
  let psi(li, s, lj, t) =
    let li, s, lj, t = conv(li, s, lj, t) in
    array3_get psi_array (s - li + 1, t - lj + 1, 0)
  in

  set_psi_array (1, 0, 1, 0) 0 [];

  for s = li to i do (* Lemma 3.1 *)
    set_psi_array(li, s, 1, 0) 0
      [Effect.cut1 (tree1#get_roots_of_forest li s)]
  done;
  for t = lj to j do
    set_psi_array(1, 0, lj, t) 0
      [Effect.cut2 (tree2#get_roots_of_forest lj t)]
  done;

  for s = li to i do
    for t = lj to j do
      let ls, lt = tree1#leftmost s, tree2#leftmost t in
      if li <> ls || lj <> lt then begin (* Lemma 3.3 *)
        let _ =
          maxn_do
            [
             (
              let n, efs = psi(li, ls - 1, lj, t) in
              n,
              (fun () ->
                let efs' = (Effect.cut1 [s])::efs in
                set_psi_array (li, s, lj, t) n efs')
             );
             (
              let n, efs = psi(li, s, lj, lt - 1) in
              n,
              (fun () ->
                let efs' = (Effect.cut2 [t])::efs in
                set_psi_array (li, s, lj, t) n efs')
             );
             (
              let n, efs = psi(li, ls - 1, lj, lt - 1) in
              let n0, efs0 = array3_get beta_array (s - 1, t - 1, 0) in
              let n' = n + n0 in
              n',
              (fun () ->
                let efs' = efs @ efs0 in
                set_psi_array (li, s, lj, t) n' efs')
             );
           ]
        in ()
      end
      else begin (* Lemma 3.4 *)
        let n, efs = psi(li, s - 1, lj, t - 1) in
        let n', efs' =
          if (tree1#get s)#data#equals (tree2#get t)#data then
            n + 2, (Effect.mapping_elem(s, t))::efs
          else 0, [Effect.cut1 (tree1#get_roots_of_forest li s);
                   Effect.cut2 (tree2#get_roots_of_forest lj t)] @ efs
        in
        set_psi_array (li, s, lj, t) n' efs';

        array3_set beta_array (s - 1, t - 1, 0) (n', efs')
      end
    done
  done



let find_largest_2 beta_array psi_array tree1 tree2 (i, j) d =
  let li, lj = tree1#leftmost i, tree2#leftmost j in

(*
  let psi_array = array3_create (i - li + 2) (j - lj + 2) (d + 1) (-1, []) in
*)
  let set_psi_array (li, s, lj, t, k) n efs =
    let li, s, lj, t = conv(li, s, lj, t) in
    array3_set psi_array (s - li + 1, t - lj + 1, k) (n, efs)
  in
  let psi(li, s, lj, t, k) =
    let li, s, lj, t = conv(li, s, lj, t) in
    array3_get psi_array (s - li + 1, t - lj + 1, k)
  in

  for k = 1 to d do
    array3_set psi_array (0, 0, k) (0, []);
  done;

  for k = 1 to d do
    for s = li to i do (* Lemma 3.2(ii) *)
      let _ =
      maxn_do
          [
           (
            let n, efs = psi(li, s - 1, 1, 0, k - 1) in
            let n' = n + 1 in
            n',
            (fun () ->
              let efs' = (Effect.delete s)::efs in
              set_psi_array (li, s, 1, 0, k) n' efs')
           );
           (
            let ls = tree1#leftmost s in
            let n, efs = psi(li, ls - 1, 1, 0, k) in
            n,
            (fun () ->
              let efs' = (Effect.cut1 [s])::efs in
              set_psi_array (li, s, 1, 0, k) n efs')
           );
         ]
      in ()
    done
  done;

  for k = 1 to d do
    for t = lj to j do (* Lemma 3.2(iii) *)
      let _ =
      maxn_do
          [
           (
            let n, efs = psi(1, 0, lj, t - 1, k - 1) in
            let n' = n + 1 in
            n',
            (fun () ->
              let efs' = (Effect.insert t)::efs in
              set_psi_array (1, 0, lj, t, k) n' efs')
           );
           (
            let lt = tree2#leftmost t in
            let n, efs = psi(1, 0, lj, lt - 1, k) in
            n,
            (fun () ->
              let efs' = (Effect.cut2 [t])::efs in
              set_psi_array (1, 0, lj, t, k) n efs')
           );
         ]
      in ()
    done
  done;

  for k = 1 to d do
    for s = li to i do
      for t = lj to j do
        let ls, lt = tree1#leftmost s, tree2#leftmost t in
        if li <> ls || lj <> lt then begin (* Lemma 3.5 *)
          let _ =
            maxn_do
              [
               (
                let n, efs = psi(li, ls - 1, lj, t, k) in
                n,
                (fun () ->
                  let efs' = (Effect.cut1 [s])::efs in
                  set_psi_array (li, s, lj, t, k) n efs')
               );
               (
                let n, efs = psi(li, s, lj, lt - 1, k) in
                n,
                (fun () ->
                  let efs' = (Effect.cut2 [t])::efs in
                  set_psi_array (li, s, lj, t, k) n efs')
               );

               (
                let n, efs = psi(li, s - 1, lj, t, k - 1) in
                let n' = n + 1 in
                n',
                (fun () ->
                  let efs' = (Effect.delete s)::efs in
                  set_psi_array (li, s, lj, t, k) n' efs')
               );
               (
                let n, efs = psi(li, s, lj, t - 1, k - 1) in
                let n' = n + 1 in
                n',
                (fun () ->
                  let efs' = (Effect.insert t)::efs in
                  set_psi_array (li, s, lj, t, k) n' efs')
               );

               (
                let max = ref min_int in
                let f = ref (fun () -> ()) in
                for h = 0 to k do
                  let n, efs = psi(li, ls - 1, lj, lt - 1, k - h) in
                  let n0, efs0 = array3_get beta_array (s - 1, t - 1, h) in
                  let n' = n + n0 in
                  if n' > !max then begin
                    max := n';
                    f :=
                      (fun () ->
                        let efs' = efs @ efs0 in
                        set_psi_array (li, s, lj, t, k) n' efs')
                  end
                done;
                !max, !f
               );
             ]
          in ()
        end
        else begin (* Lemma 3.6 *)
          let _ =
            maxn_do
              [
               (
                let n, efs = psi(li, s - 1, lj, t, k - 1) in
                let n' = n + 1 in
                n',
                (fun () ->
                  let efs' = (Effect.delete s)::efs in
                  set_psi_array (li, s, lj, t, k) n' efs')
               );
               (
                let n, efs = psi(li, s, lj, t - 1, k - 1) in
                let n' = n + 1 in
                n',
                (fun () ->
                  let efs' = (Effect.insert t)::efs in
                  set_psi_array (li, s, lj, t, k) n' efs')
               );
               (
                let c =
                  if (tree1#get s)#data#equals (tree2#get t)#data then 0
                  else 1
                in
                let n, efs = psi(li, s - 1, lj, t - 1, k - c) in
                let n' = n + 2 in
                n',
                (fun () ->
                  let efs' =
                    (if c = 0 then [] else [Effect.relabel(s, t)]) @
                    (Effect.mapping_elem(s, t))::efs
                  in
                  set_psi_array (li, s, lj, t, k) n' efs')
               );
             ]
          in
          array3_set beta_array (s - 1, t - 1, k) (psi(li, s, lj, t, k))
        end
      done
    done
  done


let compute_gamma beta_array tree1 tree2 d =
  let sz1, sz2 = tree1#size, tree2#size in
  let gamma_array = Array.make_matrix sz1 sz2 (-1, []) in

  let compute i j d =
    let ll =
      let cis = (tree1#get i)#children_indexes in
      if cis = [] then (0, [])
      else begin
        let max = ref min_int in
        let effects = ref [] in
        List.iter
          (fun iu ->
            let n, efs = gamma_array.(iu - 1).(j - 1) in
            if n > !max then begin max := n; effects := efs end
          ) cis;
        !max, !effects
      end
    in
    let rr =
      let cis = (tree2#get j)#children_indexes in
      if cis = [] then (0, [])
      else begin
        let max = ref min_int in
        let effects = ref [] in
        List.iter
          (fun jv ->
            let n, efs = gamma_array.(i - 1).(jv - 1) in
            if n > !max then begin max := n; effects := efs end
          ) cis;
        !max, !effects
      end
    in
    let nn, effects = ref 0, ref [] in
    let _ =
      maxn_do
        [
         (let n, efs = array3_get beta_array (i - 1, j - 1, d) in n,
         fun () -> nn := n; effects := efs);
         (let n, efs = ll in n,
         fun () -> nn := n; effects := efs);
         (let n, efs = rr in n,
         fun () -> nn := n; effects := efs)
       ]
    in
    gamma_array.(i - 1).(j - 1) <- (!nn, !effects)
  in
  for i = 1 to sz1 do
    for j = 1 to sz2 do
      compute i j d
    done
  done;
  gamma_array.(sz1 - 1).(sz2 - 1)


exception Subtree

[%%capture_path
let find_isomorphic_subtrees beta_array tree1 tree2 mapping =
  (* assumes sorted(in descending order) mapping *)
  let res = ref [] in
  List.iter
    (fun (x, y) ->
      let n, (*efs*)_ = array3_get beta_array (x - 1, y - 1, 0) in
      if n = (tree1#size_of_subtree x) + (tree2#size_of_subtree y)
      then
        try
          List.iter
            (fun i ->
              if (tree1#leftmost i) <= x && x < i then raise Subtree
            ) !res;
          res := x::!res
        with Subtree -> ()
    ) mapping;

  [%debug_log "roots of isomorphic subtree of T1: [%s]"
     (Xlist.to_string string_of_int "," !res)];

  !res
]

[%%capture_path
let find_largest beta_array psi_array tree1 tree2 d =
  let keynodes1, keynodes2 = tree1#keynodes, tree2#keynodes in
  let nkeynodes1, nkeynodes2 = List.length keynodes1, List.length keynodes2 in
  for i' = 1 to nkeynodes1 do
    for j' = 1 to nkeynodes2 do
      let i = List.nth keynodes1 (i' - 1) in
      let j = List.nth keynodes2 (j' - 1) in
      find_largest_1 beta_array psi_array tree1 tree2 (i, j);
      find_largest_2 beta_array psi_array tree1 tree2 (i, j) d
    done
  done;
  let n, efs = compute_gamma beta_array tree1 tree2 d in
  let edits, mapping, cut1, cut2 = Effect.get_edits_and_mapping_and_cuts efs in

  [%debug_log "distance=%d --> %d" d n];

  [%debug_log "edit seq:\n%s\nmapping:\n%s\ncut1:\n%s\ncut2:\n%s"
    (Edit.seq_to_string edits) (Mapping.to_string mapping)
    (Cut.to_string cut1) (Cut.to_string cut2)];

  n, edits, mapping, cut1, cut2
]

exception Reached of (Edit.seq
                        * Mapping.t
                        * (int * Effect.t list) array array array)

let find tree1 tree2 =
  let sz1, sz2 = tree1#size, tree2#size in
  let total = sz1 + sz2 in

  let distance = ref 0 in

  let edits, mapping, array =
    try
      while true do
        let beta_array =
          array3_create sz1 sz2 (!distance + 1) (-1, [])
        in
        let psi_array =
          array3_create (sz1 + 1) (sz2 + 1) (!distance + 1) (-1, [])
        in
        let max, edits, mapping, (*cut1*)_, (*cut2*)_ =
          find_largest beta_array psi_array tree1 tree2 !distance
        in
        if max = total then
          raise (Reached(edits, mapping, beta_array))
        else incr distance
      done;
      Edit.empty_seq, Mapping.empty, (array3_create 0 0 0 (0, []))
    with Reached (e, m, a) -> e, m, a
  in
  let mapping = Mapping.descent_sort mapping in
  let iso = find_isomorphic_subtrees array tree1 tree2 mapping in
  edits, mapping, iso
