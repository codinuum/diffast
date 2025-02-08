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
(* adiff.ml *)

module Mldiff = Diffast_misc.Mldiff


let adiff a1 a2 =
  let a1i = Mldiff.make_indexer a1 a2 in
  let a2i = Mldiff.make_indexer a2 a1 in
  let n1 = Array.length a1i in
  let n2 = Array.length a2i in
  let chng1, chng2 = Mldiff.diff_loop a1 a1i a2 a2i n1 n2 in

  let matched, relabeled, deleted, inserted =
    ref [], ref [], ref [], ref []
  in
  let mkadder lr = fun x -> lr := x::!lr in
  let add_match = mkadder matched in
  let add_relabel = mkadder relabeled in
  let add_delete = mkadder deleted in
  let add_insert = mkadder inserted in

  let rec loop i j =
(*
    debug "Adiff.adiff: loop %d %d" i j;
*)
    if i = Array.length a1 || j = Array.length a2 then
      if i < Array.length a1 then begin (* deleted *)
        add_delete i; (* i vs j *)
        loop (i + 1) j
      end
      else if j < Array.length a2 then begin (* inserted *)
        add_insert j; (* i vs j *)
        loop i (j + 1)
      end
      else ()
    else begin
      match chng1.(i), chng2.(j) with
       true, true -> begin (* may be relabeled *)
          let i2 =
            let rec loop i =
              if i = Array.length a1 || not chng1.(i) then i
              else loop (i + 1)
            in
            loop (i + 1)
          in
          let j2 =
            let rec loop j =
              if j = Array.length a2 || not chng2.(j) then j
              else loop (j + 1)
            in
            loop (j + 1)
          in

          if i2 - i <> j2 - j then begin
            for i = i to i2 - 1 do add_delete i done;
            for j = j to j2 - 1 do add_insert j done;
            loop i2 j2
          end
          else begin (* i..i2-1 vs j..j2-1 *)
            let j' = ref j in
            for i = i to i2 - 1 do
              add_relabel (i, !j');
              incr j'
            done;
            loop i2 j2
          end

        end
      | true, false -> begin (* deleted *)
          let i2 =
            let rec loop i =
              if i = Array.length a1 || not chng1.(i) then i
              else loop (i + 1)
            in
            loop (i + 1)
          in
          for i = i to i2 - 1 do add_delete i done; (* i..j2-1 vs j *)
          loop i2 j
        end
      | false, true -> begin (* inserted *)
          let j2 =
            let rec loop j =
              if j = Array.length a2 || not chng2.(j) then j
              else loop (j + 1)
            in
            loop (j + 1)
          in
          for j = j to j2 - 1 do add_insert j done; (* i vs j..j2-1 *)
          loop i j2
        end
      | false, false -> (* matched *)
          let a1i, a2j = a1.(i), a2.(j) in
          if a1i <> a2j then begin
            [%fatal_log "malformed match"];
            exit 1
          end
          else begin
            add_match (i, j);
            loop (i + 1) (j + 1)
          end
    end
  in
  let result =
    try
      loop 0 0;
      !matched, !relabeled, !deleted, !inserted
    with
      Invalid_argument s ->
        [%fatal_log "%s" s];
        failwith s
  in
  result

