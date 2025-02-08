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
(* An Algorithm for Longest Common Subsequence Problem *)

(*
let lcs a1 a2 =
  let max2 ((l0, _, _, _, _) as t0) ((l1, _, _, _, _) as t1) =
    if l0 >= l1 then t0 else t1
  in
  let n1 = Array.length a1 in
  let n2 = Array.length a2 in
  let mat = Array.make_matrix (n1+1) (n2+1) (-1, -1, -1, -1, -1) in
  for i = 0 to n1 do mat.(i).(0) <- (0, -1, -1, -1, -1) done;
  for j = 0 to n2 do mat.(0).(j) <- (0, -1, -1, -1, -1) done;
  for i = 1 to n1 do
    for j = 1 to n2 do
      if a1.(i-1) = a2.(j-1) then begin
        let (l, s1, e1, s2, e2) = mat.(i-1).(j-1) in
        let st1, st2 =
          if s1 < 0 && s2 < 0 then i-1, j-1 else s1, s2
        in
        let ed1, ed2 = i-1, j-1 in
        mat.(i).(j) <- (1 + l, st1, ed1, st2, ed2)
      end
      else
        mat.(i).(j) <- max2 mat.(i-1).(j) mat.(i).(j-1)
    done
  done;
  mat.(n1).(n2)
*)

let lcs ?(eq=(=)) a1 a2 = (* 'a array -> 'a array ->
                  (int(nmatches) * int(st_pos1) * int(ed_pos1) * int(st_pos2) * int(ed_pos2)) *)
  let max2 ((l0, _, _, _, _) as t0) ((l1, _, _, _, _) as t1) =
    if l0 >= l1 then t0 else t1
  in
  let n1 = Array.length a1 in
  let n2 = Array.length a2 in

  let mat_set, mat_get =
    if max n1 n2 > 65535 then
      let mkmat() =
        Bigarray.Array2.create Bigarray.int Bigarray.c_layout (n1+1) (n2+1)
      in
      let mat, mat_s1, mat_e1, mat_s2, mat_e2 = mkmat(), mkmat(), mkmat(), mkmat(), mkmat() in
      let set x y (n, s1, e1, s2, e2) =
        mat.{x, y} <- n;
        mat_s1.{x, y} <- s1;
        mat_e1.{x, y} <- e1;
        mat_s2.{x, y} <- s2;
        mat_e2.{x, y} <- e2
      in
      let get x y = (mat.{x,y}, mat_s1.{x,y}, mat_e1.{x,y}, mat_s2.{x,y}, mat_e2.{x,y}) in
      set, get
    else

      let mkmat() =
        Bigarray.Array2.create Bigarray.int16_unsigned Bigarray.c_layout (n1+1) (n2+1)
      in
      let mat, mat_s1, mat_e1, mat_s2, mat_e2 = mkmat(), mkmat(), mkmat(), mkmat(), mkmat() in
      let set x y (n, s1, e1, s2, e2) =
        mat.{x, y} <- n + 1;
        mat_s1.{x, y} <- s1 + 1;
        mat_e1.{x, y} <- e1 + 1;
        mat_s2.{x, y} <- s2 + 1;
        mat_e2.{x, y} <- e2 + 1
      in
      let get x y =
        (mat.{x,y}-1, mat_s1.{x,y}-1, mat_e1.{x,y}-1, mat_s2.{x,y}-1, mat_e2.{x,y}-1)
      in
      set, get
  in
  for i = 0 to n1 do mat_set i 0 (0, -1, -1, -1, -1) done;
  for j = 0 to n2 do mat_set 0 j (0, -1, -1, -1, -1) done;
  for i = 1 to n1 do
    for j = 1 to n2 do
      if eq a1.(i-1) a2.(j-1) then begin
        let (l, s1, (*e1*)_, s2, (*e2*)_) = mat_get (i-1) (j-1) in
        let st1, st2 =
          if s1 < 0 && s2 < 0 then i-1, j-1 else s1, s2
        in
        let ed1, ed2 = i-1, j-1 in
        mat_set i j (1 + l, st1, ed1, st2, ed2)
      end
      else
        mat_set i j (max2 (mat_get (i-1) j) (mat_get i (j-1)))
    done
  done;
  mat_get n1 n2


let lcs_string s1 s2 =
  let n1 = String.length s1 in
  let n2 = String.length s2 in
  let a1 = Array.make n1 'a' in
  let a2 = Array.make n2 'a' in
  for i = 0 to n1 - 1 do a1.(i) <- s1.[i] done;
  for i = 0 to n2 - 1 do a2.(i) <- s2.[i] done;
  lcs a1 a2

