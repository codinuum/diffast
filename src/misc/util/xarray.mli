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

val to_string : ('a -> string) -> string -> 'a array -> string
val filter : ('a -> bool) -> 'a array -> 'a array
val exists : ('a -> bool) -> 'a array -> bool
val for_all : ('a -> bool) -> 'a array -> bool
val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit

exception Index_out_of_bounds of int

class ['a] array_list : int -> object
  method clear : unit
  method add : 'a -> unit
  method get : int -> 'a
  method set : int -> 'a -> unit
  method is_empty : bool
  method iter : ('a -> unit) -> unit
  method iteri : (int -> 'a -> unit) -> unit
  method length : int
  method to_string : ('a -> string) -> string
end

module A = Bigarray.Array1

val kind : (int, Bigarray.int_elt) Bigarray.kind
val layout : Bigarray.c_layout Bigarray.layout

class int_array_list : int -> object
  method clear : unit
  method add : int -> unit
  method get : int -> int
  method set : int -> int -> unit
  method is_empty : bool
  method iter : (int -> unit) -> unit
  method iteri : (int -> int -> unit) -> unit
  method length : int
  method to_string : string
end
