(*
   Copyright 2012-2023 Codinuum Software Lab <https://codinuum.com>

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
 * Heaviest Increasing/Common Subsequence Problem
 * based on Guy Jacobson and Kiem-Phong Vo,
 * Combinational Pattern Matching, LNCS644, 1992
 *)


module F (W : Weight.T) = struct

  exception Found of int * W.t
  exception Break

(*
  let pair_le (u, v) (x, y) =
    u < x || (u = x && v <= y)

  let pair_eq (u, v) (x, y) =
    u = x && v = y

  let pair_lt (u, v) (x, y) =
    u < x

  let comp_pair p q =
    if pair_eq p q then
      0
    else if pair_lt p q then
      -1
    else
      1
*)
  let comp_pair (u, v) (x, y) =
    if u = x && v = y then
      0
    else if u < x then
      -1
    else
      1

  let ptos (i, w) = Printf.sprintf "(%d, %s)" i (W.to_string w)

  let insert lref p =
(*    Printf.printf "insert: %s\n" (ptos p); *)
    lref := p::!lref

  let delete lref p =
(*    Printf.printf "delete: %s\n" (ptos p); *)
    lref := List.filter (fun q -> q <> p) !lref

  let phi_pair = (-1, W.zero)

  let prev decr_sorted_list (x, y) =
    if (x, y) = phi_pair then
      match decr_sorted_list with
      | [] -> phi_pair
      | p::_ -> p
    else
      try
        List.iter
          (fun (u, v) ->
            if (*pair_lt (u, v) (x, y)*) u < x then
              raise (Found (u, v))
          ) decr_sorted_list;
        phi_pair
      with
        Found (u, v) -> u, v

  let next incr_sorted_list (x, y) =
    if (x, y) = phi_pair then
      match incr_sorted_list with
      | [] -> phi_pair
      | p::_ -> p
    else
      try
        List.iter
          (fun (u, v) ->
            if (*pair_lt (x, y) (u, v)*) x < u then
              raise (Found (u, v))
          ) incr_sorted_list;
        phi_pair
      with
        Found (u, v) -> u, v



  let compute
      (get_weight : int -> int -> 'a -> W.t)
      (a1 : 'a array)
      (a2 : 'a array)
      =
    let len1 = Array.length a1 in
    let len2 = Array.length a2 in

    if len1 * len2 = 0 then
      raise (Invalid_argument "HIS.compute");

    let poss_tbl = Hashtbl.create 0 in

    for j = 0 to len2 - 1 do
      try
        let p = Hashtbl.find poss_tbl a2.(j) in
        Hashtbl.replace poss_tbl a2.(j) (j::p)
      with
        Not_found -> Hashtbl.add poss_tbl a2.(j) [j]
    done;

    let get_poss a =
      try
        Hashtbl.find poss_tbl a
      with
        Not_found -> []
    in

    let workL = ref [] in

    let max_pair = ref phi_pair in

    let node_tbl = Hashtbl.create 0 in
    let node_add (u, v) c =
      let (*x*)_, y = !max_pair in
      if v > y then
        max_pair := (u, v);
      Hashtbl.add node_tbl (u, v) c
    in
    let node_find p =
      if p = phi_pair then
        []
      else
        try
          Hashtbl.find node_tbl p
        with
          Not_found -> []
    in

    for i = 0 to len1 - 1 do
      let p = get_poss a1.(i) in
      List.iter
        (fun j ->
          let sorted_workL =
            List.fast_sort comp_pair !workL
          in
          let s, v = prev (List.rev sorted_workL) (j, W.zero) in
          let t_w = ref (next sorted_workL (s, v)) in
          let ijw = get_weight i j a1.(i) in
          let vijw = W.plus v ijw in
          begin
            try
              while !t_w <> phi_pair do
                let t, w = !t_w in
                if vijw < w then
                  raise Break;

                delete workL (t, w);
                t_w := next (List.fast_sort comp_pair !workL) (t, w)
              done
            with
              Break -> ()
          end;
          let t, (*w*)_ = !t_w in
          if !t_w = phi_pair || j < t then begin
            insert workL (j, vijw);
            node_add (j, vijw) ((i, j)::(node_find (s, v)))
          end
        )
        (List.fast_sort (fun x y -> Stdlib.compare y x) p)
    done;

    let seq = node_find !max_pair in

    seq


end (* of functor HIS.F *)


module Int = F(Weight.Int)
module Float = F(Weight.Float)
module IntInt = F(Weight.IntInt)
module IntIntInt = F(Weight.IntIntInt)
module IntFloat = F(Weight.IntFloat)
module FloatInt = F(Weight.FloatInt)
module FloatFloat = F(Weight.FloatFloat)
module FloatIntInt = F(Weight.FloatIntInt)
