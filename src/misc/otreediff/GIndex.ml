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

type t = int

let of_int (i : int) = (i : t)

let to_int (g : t) = (g : int)

let dummy = (0 : t)

let unknown = (-1 : t)

let is_valid (g : t) = g > 0

let offset (g : t) o = g + o

let to_string g = "#"^(string_of_int g)^"G"

let to_raw g = string_of_int g

let p ch (g : t) = Stdlib.output_string ch (to_string g)

let r ch (g : t) = Stdlib.output_string ch (to_raw g)

let ps () (g : t) = to_string g

let rs () (g : t) = to_raw g

let list_to_string l = (* assume that l is not a multiset *)
  let l = List.fast_sort Stdlib.compare l in

  let get_last s =
    if s = "" then 'x' else String.get s ((String.length s) - 1)
  in
  let __result, last =
    match l with
    | [] -> ";", -1
    | top::_ ->
        List.fold_left
          (fun (s, o) i ->
            if (get_last s) = '-' then
              if i = o + 1 then
                s, i
              else
                s ^ (string_of_int o) ^ ";" ^ (string_of_int i), i
            else
              if i = o + 1 then
                s ^ "-", i
              else
                s ^ ";" ^ (string_of_int i), i

          ) ("", top) l
  in
  let _result = String.sub __result 1 ((String.length __result) - 1) in
  let result =
    if (get_last _result) = '-' then
      _result ^ (string_of_int last)
    else
      _result
  in
  result
