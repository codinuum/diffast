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

val lexing_pos_start : Sedlexing.lexbuf -> Lexing.position
val lexing_pos_end : Sedlexing.lexbuf -> Lexing.position
val get_lc : Lexing.position -> int * int

class manager : string -> object
  method filename : string
  method set_filename : string -> unit
  method feed : int -> unit
  method feedline : int -> unit
  method get_current_position : int * int
  method get_position : int -> int * int
  method lines_read : int
  method _offsets_to_loc : int -> int -> int -> int -> int -> int -> Astloc.t
  method offsets_to_loc : int -> int -> Astloc.t
  method lexposs_to_loc : ?get_position:bool -> Lexing.position -> Lexing.position -> Astloc.t
  method reset : unit
  method show_status : unit
  method to_string : string
end
