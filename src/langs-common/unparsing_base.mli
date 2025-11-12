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

module type FMTR = sig
  val formatter : Format.formatter
end

module Make : functor (_ : FMTR) -> sig

type block_style = BSshort | BStall
type box = B of int | Bh | Bv of int | Bhv of int | Bhov of int
val sprintf : ('a, unit, string) format -> 'a
val box_to_string : box -> string

val pr_string : string -> unit
val pr_break : int -> int -> unit
val pr_space : unit -> unit
val pr_newline : unit -> unit
val pr_cut : unit -> unit
val pr_int : int -> unit
val pr_float : float -> unit
val pr_char : char -> unit
val pr_bool : bool -> unit
val pr_flush : unit -> unit
val _pr_comma : unit -> unit
val _pr_eq : unit -> unit
val pr_comma : unit -> unit
val pr_eq : unit -> unit
val pr_lparen : unit -> unit
val pr_rparen : unit -> unit
val pr_lbracket : unit -> unit
val pr_rbracket : unit -> unit
val pr_lbrace : unit -> unit
val pr_rbrace : unit -> unit
val pr_dot : unit -> unit
val pr_ellipsis : unit -> unit
val pr_amp : unit -> unit
val pr_colon : unit -> unit
val pr_semicolon : unit -> unit
val pr_bor : unit -> unit
val pr_none : unit -> unit
val force_newline : unit -> unit
val pad : int -> unit
val pad1 : unit -> unit
val pr_name : string -> unit
val pr_id : string -> unit
val pr_option : ('a -> unit) -> 'a option -> unit
class ppbox : object
  method boxing_flag : bool
  method enable_boxing : unit -> unit
  method disable_boxing : unit -> unit
  method private checkpoint_box : unit -> box list
  method close_box : unit -> unit
  method disable_backslash_newline : unit -> unit
  method enable_backslash_newline : unit -> unit
  method private enter_box : box -> unit
  method private exit_box : unit -> unit
  method indent : int
  method open_box : int -> unit
  method open_hbox : unit -> unit
  method open_vbox : int -> unit
  method open_hvbox : int -> unit
  method open_hovbox : int -> unit
  method pr_a : ?head:(unit -> unit) -> ?tail:(unit -> unit) ->
    (unit -> unit) -> ('a -> unit) -> 'a array -> unit
  method pr_block_begin : block_style -> unit
  method pr_block_begin_short : unit -> unit
  method pr_block_begin_tall : unit -> unit
  method pr_block_end : unit -> unit
  method pr_ha : ?head:(unit -> unit) -> ?tail:(unit -> unit) ->
          (unit -> unit) -> ('a -> unit) -> 'a array -> unit
  method pr_va : ?head:(unit -> unit) -> ?tail:(unit -> unit) ->
          (unit -> unit) -> ('a -> unit) -> 'a array -> unit
  method pr_hova : ?head:(unit -> unit) -> ?tail:(unit -> unit) ->
          (unit -> unit) -> ('a -> unit) -> 'a array -> unit
  method pr_hva : ?head:(unit -> unit) -> ?tail:(unit -> unit) ->
          (unit -> unit) -> ('a -> unit) -> 'a array -> unit
  method private reset_box : unit -> unit
  method private restore_box : box list -> unit
end
val apply_nth : ('a -> unit) -> 'a array -> int -> unit

end
