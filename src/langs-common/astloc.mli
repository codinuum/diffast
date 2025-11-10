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
    { mutable filename : string;
      start_offset : int;
      end_offset   : int;
      start_line   : int;
      start_char   : int;
      end_line     : int;
      end_char     : int;
    }

val dummy : t
val make : ?fname:string -> int -> int -> int -> int -> int -> int -> t
val copy : t -> t
val interchange : t -> t
val is_valid : ?weak:bool -> t -> bool
val is_dummy : t -> bool
val encode_path : string -> string
val decode_path : string -> string
val to_rep : t -> string
val from_rep : string -> t
val is_extended : t -> bool
val get_stripped : t -> t
val get_extended : ?cache:Fname.ext_cache_t -> t -> string -> t
val extend : ?cache:Fname.ext_cache_t -> t -> string -> unit
val to_string : ?show_ext:bool -> ?short:bool -> ?prefix:string -> ?suffix:string -> t -> string
val start_to_string : ?show_ext:bool -> ?short:bool -> ?prefix:string -> ?suffix:string -> t -> string
val end_to_string : ?show_ext:bool -> ?short:bool -> ?prefix:string -> ?suffix:string -> t -> string
val normalize_fname : string -> string
val merge : t -> t -> t
val collapse_forward : ?len:int -> t -> t
val collapse_backward : ?len:int -> t -> t
val widen : t -> int -> t
val is_contained : t -> t -> bool
val to_offsets : t -> (int * int)
val dump_locs : t list -> unit
val lines_of_locs : t list -> int
val mklexpos : ?fname:string -> ?lnum:int -> ?bol:int -> int -> Lexing.position
val of_lexpos : Lexing.position -> t
val of_lexposs : Lexing.position -> Lexing.position -> t
val incr_n_lexpos : int -> Lexing.position -> Lexing.position
val decr_n_lexpos : int -> Lexing.position -> Lexing.position
val incr_lexpos : Lexing.position -> Lexing.position
val decr_lexpos : Lexing.position -> Lexing.position
val gt_lexpos : Lexing.position -> Lexing.position -> bool
val lt_lexpos : Lexing.position -> Lexing.position -> bool
val ge_lexpos : Lexing.position -> Lexing.position -> bool
val le_lexpos : Lexing.position -> Lexing.position -> bool
val dummy_lexpos : Lexing.position
val to_start_lexpos : t -> Lexing.position
val to_end_lexpos : t -> Lexing.position
val to_lexposs : t -> Lexing.position * Lexing.position
val lexpos_to_string : Lexing.position -> string
