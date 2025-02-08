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

val to_string : ('a -> string) -> ?prefix:string -> ?suffix:string -> 'a option -> string
val to_list : 'a option -> 'a list
val list_to_list : 'a option list -> 'a list
val list_opt_to_list : 'a list option -> 'a list
val map : ('a -> 'b) -> 'a option -> 'b option
val to_list_map : ('a -> 'b) -> 'a option -> 'b list
val iter : ('a -> unit) -> 'a option -> unit
