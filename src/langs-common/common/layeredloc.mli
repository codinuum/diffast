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
class loc_stack : object
  method get_layers : Astloc.t ref list
  method get_level : int
  method init : unit
  method pop : unit
  method push : Astloc.t -> unit
  method to_string : string
end

(*val sep : string*)
(*val sep_pat : Str.regexp*)
val encode_layers : Astloc.t ref list -> string
val decode_layers : string -> Astloc.t ref list

class c : ?layers:Astloc.t ref list -> Astloc.t -> object
  method collapse_backward : unit
  method get_layers : int -> Astloc.t ref list
  method get_level : int
  method get_loc : Astloc.t
  method get_loc_of_level : int -> Astloc.t
  method get_orig_loc : Astloc.t
  method size : int
  method to_loc : ?cache:(Fname.ext_cache_t option) -> unit -> Astloc.t
  method to_string : ?short:bool -> unit -> string
end

val dummy : c
val layers_eq : Astloc.t ref list -> Astloc.t ref list -> bool
val get_common_layers : c -> c -> Astloc.t ref list
val get_common_level : c -> c -> int
val merge : c -> c -> c
val dump_llocs : c list -> unit
val lines_of_llocs : c list -> int
val of_loc : Astloc.t -> c
val of_lexpos : Lexing.position -> c
