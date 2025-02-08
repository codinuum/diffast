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
(* HCS: Heaviest Common Subsequence *)
(* A simple DP algorithm *)


module F (W : Weight.T) = struct

  type result = { seq : (int * int) list;
                  del : int list;
                  ins : int list;
                }

  type direction = Dnone | Dleft | Dup | Dupper_left | Dleft_or_up
  type elem = { weight:W.t; direction:direction; }

  let mkelem w d = { weight=w; direction=d; }
  let mkres s d i = { seq=s; del=d; ins=i; }

  let default_eq x y = x = y

  let compute
      ?(eq=default_eq)
      (get_weight : int -> int -> 'a -> W.t)
      (a1 : 'a array)
      (a2 : 'a array)
      =

    let len1 = Array.length a1 in
    let len2 = Array.length a2 in

    if len1 * len2 = 0 then
      raise (Invalid_argument "HCS.compute");

    let mat =
      Array.make_matrix (len1 + 1) (len2 + 1) (mkelem W.zero Dnone)
    in

    let maxlu lelem uelem =
      let l = lelem.weight in
      let u = uelem.weight in
      if l = u then
        mkelem l Dleft_or_up
      else if l > u then
        mkelem l Dleft
      else
        mkelem u Dup
    in

    for j = 1 to len2 do
      for i = 1 to len1 do
        let c1 = a1.(i-1) in
        let c2 = a2.(j-1) in
        if eq c1 c2 then
          let w = W.plus (mat.(i-1).(j-1).weight) (get_weight (i-1) (j-1) c1) in
          if w > mat.(i-1).(j).weight && w > mat.(i).(j-1).weight then
            mat.(i).(j) <- mkelem w Dupper_left
          else
            mat.(i).(j) <- maxlu mat.(i-1).(j) mat.(i).(j-1)
        else
          mat.(i).(j) <- maxlu mat.(i-1).(j) mat.(i).(j-1)
      done
    done;

(*
  let pr_elem {weight=w; direction=d } =
  Printf.printf "%2d:%s" w
  (match d with
  | Dnone -> "0"
  | Dleft -> "<"
  | Dup -> "^"
  | Dupper_left -> "\\"|Dleft_or_up -> ";")
  in
  for j = 0 to len2 do
  for i = 0 to len1 do
  pr_elem mat.(i).(j);
  print_string " "
  done;
  print_newline();
  done;
 *)

    let seq = ref [] in
    let del = ref [] in
    let ins = ref [] in

    let rec scan i j =
      if i > 0 && j > 0 then
        match mat.(i).(j).direction with
        | Dupper_left ->
            scan (i-1) (j-1);
            seq := (i-1, j-1) :: !seq
        | Dleft | Dleft_or_up ->
            scan (i-1) j;
            del := (i-1) :: !del
        | Dup ->
            scan i (j-1);
            ins := (j-1) :: !ins
        | _ -> assert false

      else if i = 0 then
        for x = 0 to j-1 do
          ins := x :: !ins
        done
      else if j = 0 then
        for x = 0 to i-1 do
          del := x :: !del
        done
    in
    scan len1 len2;

    mkres !seq !del !ins


end (* of functor HCS.F *)

module Int = F(Weight.Int)
module Float = F(Weight.Float)
