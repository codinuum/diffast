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

type 'a t
val create : int -> 'a t
val clear : 'a t -> unit
val length : 'a t -> int
val size : 'a t -> int
val is_empty : 'a t -> bool
val iter : ('a -> unit) -> 'a t -> unit
val add : 'a t -> 'a -> unit
val add_set : 'a t -> 'a t -> unit
val remove : 'a t -> 'a -> unit
val remove_set : 'a t -> 'a t -> unit
val mem : 'a t -> 'a -> bool
val copy : 'a t -> 'a t
val to_list : 'a t -> 'a list
val from_list : 'a list -> 'a t
val for_all : ('a -> bool) -> 'a t -> bool
val exists : ('a -> bool) -> 'a t -> bool
val subset_eq : 'a t -> 'a t -> bool
val equals : 'a t -> 'a t -> bool
val map : ('a -> 'b) -> 'a t -> 'b t
val filter : ('a -> bool) -> 'a t -> 'a t
val filter_map : ('a -> 'b option) -> 'a t -> 'b t
val filter_inplace : ('a -> bool) -> 'a t -> unit
