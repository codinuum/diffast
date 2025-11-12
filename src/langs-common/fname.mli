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
type ext_cache_t = (string * string, string) Hashtbl.t

val ext_sep : char
val ext_sep_pat : Str.regexp
val dir_sep : string
val dir_sep_pat : Str.regexp
val loc_sep : string
val loc_sep_pat : Str.regexp
val is_extended : string -> bool
val extend : ?cache:ext_cache_t -> ?force:bool -> string -> string -> string
val strip : string -> string
val get_extension : string -> string
val escape : string -> string
val to_string : ?show_ext:bool -> ?short:bool -> string -> string
