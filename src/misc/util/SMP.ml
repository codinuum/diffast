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
(* stable marriage problem (SMP) *)

(* based on Gale and Shapley's algorithm *)


module Comparator (W : Weight.T) = struct

  class ['a] c
      (score_f : 'a -> 'a -> W.t)
      (array1 : 'a array)
      (array2 : 'a array)
      =
    let sz1 = Array.length array1 in
    let sz2 = Array.length array2 in

    object

      val score_matrix = Array.make_matrix sz1 sz2 W.zero

      initializer
        for i = 0 to sz1 - 1 do
          for j = 0 to sz2 - 1 do
            score_matrix.(i).(j) <- score_f array1.(i) array2.(j)
          done
        done

      method compare_LR i x y =
        let a = score_matrix.(i).(x) in
        let b = score_matrix.(i).(y) in
        if W.eq a b then
          0
        else if W.lt a b then
          -1
        else
          1

      method compare_RL j x y =
        let a = score_matrix.(y).(j) in
        let b = score_matrix.(x).(j) in
        if W.eq a b then
          0
        else if W.lt a b then
          -1
        else
          1

    end (* of class comparator *)

end (* of functor SMP.Comparator *)


type stat = Sfinished | Sfree | Sengaged of int

let stat_to_string = function
  | Sfinished  -> "FINISHED"
  | Sfree      -> "FREE"
  | Sengaged i -> Printf.sprintf "ENGAGED(%d)" i

exception Failed of int * int


let get_stable_matches ?(check=false) cmpr array1 array2 =

    let sz1 = Array.length array1 in
    let sz2 = Array.length array2 in

  (* setup preference stack for array1 *)
  let pref_array1 = Array.make sz1 (Stack.create()) in
  for i = 0 to sz1 - 1 do
    let stack = Stack.create() in
    pref_array1.(i) <- stack;
    List.iter
      (fun x -> Stack.push x stack)
      (List.fast_sort (cmpr#compare_LR i) (Xlist.range sz2))
  done;

(*
  Array.iteri
  (fun i stack ->
  Printf.printf "pref_array1[%d]" i;
  Stack.iter (fun j -> Printf.printf " %d" j) stack;
  Printf.printf "\n"
  ) pref_array1;
 *)

  (* setup status arrays *)
  let stat_array1 = Array.make sz1 Sfree in
  let stat_array2 = Array.make sz2 Sfree in

  (* main loop *)
  let finished = ref false in

  while not !finished do
(*
  Printf.printf "-----\n";
  Array.iteri (fun i stat -> Printf.printf "stat1[%d]: %s\n" i (stat_to_string stat)) stat_array1;
 *)
    (* submit application *)
    for i = 0 to sz1 - 1 do
      if stat_array1.(i) = Sfree then
        try
          let most_preferred = Stack.pop pref_array1.(i) in

          match stat_array2.(most_preferred) with
          | Sfree ->
              stat_array2.(most_preferred) <- Sengaged i;
              stat_array1.(i) <- Sengaged most_preferred

          | Sengaged i' ->
              if cmpr#compare_RL most_preferred i i' < 0 then begin
                stat_array2.(most_preferred) <- Sengaged i;
                stat_array1.(i) <- Sengaged most_preferred;
                stat_array1.(i') <- Sfree
              end

          | _ -> assert false
        with
          Stack.Empty -> stat_array1.(i) <- Sfinished
    done;
(*
  Printf.printf "-----\n";
  Array.iteri (fun i stat -> Printf.printf "stat1[%d]: %s\n" i (stat_to_string stat)) stat_array1;
 *)
    finished :=
      List.for_all
        (fun stat ->
          match stat with
          | Sfinished | Sengaged _ -> true
          | _ -> false
        ) (Array.to_list stat_array1)

  done;
  let pairs =
    List.filter
      (fun (i, _) -> i >= 0)
      (List.map
         (fun j ->
           (match stat_array2.(j) with
           | Sengaged i -> i
           | _ -> -1),
           j
         ) (Xlist.range sz2)
      )
  in
  if check then begin
    try
      List.iter
        (fun (i, j) ->
          List.iter
            (fun j' ->
              if j' <> j then
                let cond1 = cmpr#compare_LR i j j' < 0 in
                let cond2 =
                  match stat_array2.(j') with
                  | Sengaged i' -> cmpr#compare_RL j' i i' < 0
                  | _ -> false
                in
                if cond1 && cond2 then
                  raise (Failed (i, j'))
            ) (Xlist.range sz2)
        ) pairs;
      Printf.printf "check: STABLE\n"
    with
      Failed (i, j) -> Printf.printf "check: UNSTABLE: ex. (%d,%d)\n" i j
  end;
  List.map (fun (i, j) -> array1.(i), array2.(j)) pairs


module ComparatorInt         = Comparator(Weight.Int)
module ComparatorFloat       = Comparator(Weight.Float)
module ComparatorFloatInt    = Comparator(Weight.FloatInt)
module ComparatorFloatIntInt = Comparator(Weight.FloatIntInt)
module ComparatorIntFloat    = Comparator(Weight.IntFloat)
