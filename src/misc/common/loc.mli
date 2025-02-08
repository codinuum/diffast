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

type t = {
  mutable filename : string;
  start_offset : int;
  end_offset : int;
  start_line : int;
  start_char : int;
  end_line : int;
  end_char : int;
}

val dummy : t
val ghost : t
val make : ?fname:string -> int -> int -> int -> int -> int -> int -> t
val _merge : t -> t -> t
val lines : t -> int
val to_offsets : t -> int * int
val is_contained : t -> t -> bool
val merge : t -> t -> t
val extend_end : t -> int -> t
val to_string : ?long:bool -> t -> string
val to_attr_value : t -> string
val compare : t -> t -> int
val meet : t -> t -> t
