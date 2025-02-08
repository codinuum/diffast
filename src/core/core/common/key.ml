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

type t =
  | Kany
  | Kpair of Obj.t * Obj.t

let any_key = Kany

let make_pair_key nd1 nd2 = Kpair (nd1#data#_label, nd2#data#_label)

let is_any_key k = match k with Kany -> true | _ -> false

let is_pair_key k = match k with Kpair _ -> true | _ -> false

let to_string ?(opr=(fun _ -> "")) = function
  | Kany    -> "ANY_KEY"
  | Kpair (o1, o2) ->
      let s1 = opr o1 in
      let s2 = opr o2 in
      "PAIR_KEY"^(if s1 = "" && s2 = "" then "" else "("^s1^","^s2^")")


