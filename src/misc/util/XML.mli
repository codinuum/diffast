(*
   Copyright 2012-2024 Codinuum Software Lab <https://codinuum.com>

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

exception Attr_not_found of string

val sprintf : ('a, unit, string) format -> 'a
val header : string
(*val _encode_string : string -> string
val _decode_string : string -> string*)
val encode_string : string -> string
val decode_string : string -> string
val get_local_part : string -> string

type name = string * string

class node :
    ?name:name ->
    ?attr_list:((name * string) list) ->
    ?children:('self list) ->
    ?text:(string list) ->
    ?lc:(int * int) ->
    unit ->
      object ('self)
        method localname : string
        method tag : string
        method raw_attr_list : (name * string) list
        method attr_list : (string * string) list
        method data : string
        method raw_data : string list
        method children : 'self list
        method iter_children  : ('self -> unit) -> unit
        method get_attr : string -> string
        method to_string : string
        method lc : int * int
      end

class ns_manager : object
  method reset : unit -> unit
  method add_ns : string -> string -> unit
  method find : string -> string option
end

val parse_xchannel : ?ns:ns_manager -> Xchannel.in_channel -> node

val parse_file : ?ns:ns_manager -> string -> node
