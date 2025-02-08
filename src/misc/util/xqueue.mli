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

exception Empty
type 'a cell = { mutable content : 'a; mutable next : 'a cell; }
type 'a t = { mutable length : int; mutable tail : 'a cell; }
class ['a] c : object ('c)
  method add : 'a -> unit
  method clear : unit
  method copy : 'c
  method filter : ('a -> bool) -> unit
  method fold : ('b -> 'a -> 'b) -> 'b -> 'b
  method is_empty : bool
  method iter : ('a -> unit) -> unit
  method length : int
  method peek : 'a
  method peek_last : 'a
  method peek_nth : int -> 'a
  method prepend : 'a -> unit
  method prepend_from : 'c -> unit
  method remove_last : unit
  method replace : ('a -> 'a) -> unit
  method repr : 'a t
  method take : 'a
  method transfer : 'c -> unit
end
