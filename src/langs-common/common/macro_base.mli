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
module Loc = Astloc
type stat = Unresolved | Resolved of Obj.t

val stat_to_string : stat -> string
val stat_resolved : stat -> bool
val tok_of_stat : stat -> 'a

type line = {
  ln_raw : string;
  mutable ln_stat : stat;
  mutable ln_conditional : bool;
  ln_loc : Loc.t;
}

val mk_line : ?loc:Loc.t -> ?raw:string -> ?conditional:bool -> ('a -> 'b) -> 'a -> line
val line_to_string : line -> string
val tok_of_line : line -> 'a
val _resolve_line : line -> Obj.t -> unit
val resolve_line : line -> 'a -> unit
val line_resolved : line -> bool
type body = Object of line | Function of string list * line
val mk_obj_body : ?loc:Loc.t -> ?stat:stat -> ?conditional:bool -> string -> body
val mk_fun_body : ?loc:Loc.t -> ?stat:stat -> ?conditional:bool -> string list -> string -> body
val line_of_body : body -> line
val body_to_string : body -> string
val body_to_rep : body -> string
val body_length : body -> int
val _resolve_body : Obj.t -> body -> unit
val resolve_body : 'a -> body -> unit
val body_is_conditional : body -> bool
val body_set_conditional : body -> unit
val body_clear_conditional : body -> unit

class table : string -> object
  method name : string
  method clear : unit
  method define : ?conditional:bool -> string -> body -> unit
  method expose : string -> unit
  method find : string -> body
  method find_all : string -> body list
  method hide : string -> unit
  method is_defined : string -> bool
  method is_unconditionally_defined : string -> bool
  method is_undefined : string -> bool
  method is_uniquely_defined : string -> bool
  method readonly : bool
  method set_readonly : unit
  method undefine : string -> unit
end
