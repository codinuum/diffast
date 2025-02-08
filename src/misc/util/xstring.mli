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

val startswith : string -> string -> bool
val endswith : string -> string -> bool
val rstrip : ?strs:(string list) -> string -> string
val lstrip : ?strs:(string list) -> string -> string
val strip : ?strs:(string list) -> string -> string
val to_int_array : string -> int array
val to_char_array : string -> char array
val encode : string -> string
val decode : string -> string
val escaped : string -> string
val ntriples_escaped : string -> string
val remove_quotes : string -> string
