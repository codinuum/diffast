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

val to_string : ('a -> string) -> string -> 'a list -> string
val uniq : 'a list -> 'a list
val uniqq : 'a list -> 'a list
val union : 'a list -> 'a list -> 'a list
val unionq : 'a list -> 'a list -> 'a list
val intersection : 'a list -> 'a list -> 'a list
val intersectionq : 'a list -> 'a list -> 'a list
val overlap : 'a list -> 'a list -> bool
val overlapq : 'a list -> 'a list -> bool
val subtract : 'a list -> 'a list -> 'a list
val subtractq : 'a list -> 'a list -> 'a list
val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
val max : 'a list -> 'a
val min : 'a list -> 'a
val first : 'a list -> 'a
val last : 'a list -> 'a
val firstn : int -> 'a list -> 'a list
val lastn : int -> 'a list -> 'a list
val balance : 'a list * 'b list -> 'a list * 'b list
val range : int -> int list
val filter_map : ('a -> 'b option) -> 'a list -> 'b list
val partition_at_last : 'a list -> 'a list * 'a
