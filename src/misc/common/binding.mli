(*
   Copyright 2012-2025 Codinuum Software Lab <https://codinuum.com>

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


module ID : sig
  type t = Local of int | Global of string
  val compare : 'a -> 'a -> int
  val succ : int -> int
  val pred : int -> int
  val make_global : string -> t
  val is_global : t -> bool
  val is_local : t -> bool
  val to_raw : t -> string
  val to_string : t -> string
  val dummy : t
  val is_dummy : t -> bool

  class generator : object
    method gen : t
    method reset : unit
  end

  val p : out_channel -> t -> unit
  val r : out_channel -> t -> unit
  val ps : unit -> t -> string
end

type use_count = Used of int | Unknown

val use_count_to_string : use_count -> string

type is_local = bool

type t = NoBinding | Def of ID.t * use_count ref * is_local | Use of ID.t * (UID.t * Loc.t) option

val to_string : t -> string
val make_def : ID.t -> use_count -> is_local -> t
val make_used_def : ID.t -> int -> is_local -> t
val make_unused_def : ID.t -> is_local -> t
val make_unknown_def : ID.t -> is_local -> t
val make_use : ?loc_opt:(UID.t * Loc.t) option -> ID.t -> t
val is_none : t -> bool
val is_use : t -> bool
val is_def : t -> bool
val is_local_def : t -> bool
val is_non_local_def : t -> bool
val is_used_def : t -> bool
val is_unused_def : t -> bool
val get_bid : t -> ID.t
val get_bid_opt : t -> ID.t option
val get_use_count : t -> int
val get_loc : t -> Loc.t
val get_uid : t -> UID.t
val has_loc : t -> bool
val incr_use : t -> unit
