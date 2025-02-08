(*
   Copyright 2012-2024 Codinuum Software Lab <https://codinuum.com>

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

type node_t = Spec.node_t

module M = struct
  type t = node_t
  let equal n1 n2 = n1 == n2
  let hash n = n#hash(*lnot n#uid*)
end

module Tbl = Hashtbl.Make (M)

type t = Tbl.key

type 'a cenv_t =
    <
    get_adjacency_score : ?anchor:((node_t * node_t) option) -> t -> t -> float;
    _get_adjacency_score : ?anchor:((node_t * node_t) option) -> t -> t -> float * (t * t) list;
    ..> as 'a


