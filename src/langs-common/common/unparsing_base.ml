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

[%%prepare_logger]


module type FMTR = sig
  val formatter : Format.formatter
end

[%%capture_path
module Make (Fmtr : FMTR) = struct

let fmtr = Fmtr.formatter

type block_style = BSshort | BStall

type box =
  | B of int
  | Bh
  | Bv of int
  | Bhv of int
  | Bhov of int

let sprintf = Printf.sprintf

let box_to_string = function
  | B i    -> sprintf "B(%d)" i
  | Bh     -> sprintf "Bh"
  | Bv i   -> sprintf "Bv(%d)" i
  | Bhv i  -> sprintf "Bhv(%d)" i
  | Bhov i -> sprintf "Bhov(%d)" i

let pr_string      = Format.pp_print_string fmtr
let pr_break       = Format.pp_print_break fmtr
let pr_space       = Format.pp_print_space fmtr
let pr_newline     = Format.pp_print_newline fmtr
let pr_cut         = Format.pp_print_cut fmtr
let pr_int         = Format.pp_print_int fmtr
let pr_float       = Format.pp_print_float fmtr
let pr_char        = Format.pp_print_char fmtr
let pr_bool        = Format.pp_print_bool fmtr
let pr_flush       = Format.pp_print_flush fmtr

let _pr_comma()    = pr_string ","
let _pr_eq()       = pr_string "="
let pr_comma()     = pr_string ","; pr_space()
let pr_eq()        = pr_string " = "

let pr_lparen()    = pr_string "("
let pr_rparen()    = pr_string ")"
let pr_lbracket()  = pr_string "["
let pr_rbracket()  = pr_string "]"

let pr_lbrace()    = pr_string "{"
let pr_rbrace()    = pr_string "}"
let pr_dot()       = pr_string "."
let pr_ellipsis()  = pr_string "..."
let pr_amp()       = pr_string "&"
let pr_colon()     = pr_string ":"
let pr_semicolon() = pr_string ";"
let pr_bor()       = pr_string "|"
let pr_none()      = ()

let force_newline = Format.pp_force_newline fmtr

let pad i = pr_string (String.make i ' ')
let pad1() = pad 1

let pr_name name = pr_string name
let pr_id id = pr_string id

let pr_option : 'a. ('a -> unit) -> 'a option -> unit =
  fun pr -> function Some x -> pr x | None -> ()


class ppbox = object (self)

  val mutable boxing_flag = true

  val mutable indent = 2

  val mutable orig_functions = Format.pp_get_formatter_out_functions fmtr ()

  val box_stack = Stack.create()

  method indent = indent

  method boxing_flag = boxing_flag
  method disable_boxing() = boxing_flag <- false
  method enable_boxing() = boxing_flag <- true

  method private enter_box b = Stack.push b box_stack
  method private exit_box()  = ignore (Stack.pop box_stack)
  method private reset_box() = Stack.clear box_stack

  method private checkpoint_box() =
    let l = ref [] in
    Stack.iter (fun x -> l := x :: !l) box_stack;
    [%debug_log "[%s]" (String.concat ";" (List.map box_to_string !l))];
    !l

  method private restore_box stat =
    self#reset_box();
    List.iter
      (function
        | B i    -> self#open_box i; if i > 0 then pad i
        | Bh     -> self#open_hbox()
        | Bv i   -> self#open_vbox i; if i > 0 then pad i
        | Bhv i  -> self#open_hvbox i; if i > 0 then pad i
        | Bhov i -> self#open_hovbox i; if i > 0 then pad i
      ) stat

  method open_box i    = self#enter_box (B i); if boxing_flag then Format.pp_open_box fmtr i
  method open_hbox()   = self#enter_box Bh; if boxing_flag then Format.pp_open_hbox fmtr ()
  method open_vbox i   = self#enter_box (Bv i); if boxing_flag then Format.pp_open_vbox fmtr i
  method open_hvbox i  = self#enter_box (Bhv i); if boxing_flag then Format.pp_open_hvbox fmtr i
  method open_hovbox i = self#enter_box (Bhov i); if boxing_flag then Format.pp_open_hovbox fmtr i
  method close_box()   = self#exit_box(); if boxing_flag then Format.pp_close_box fmtr ()

  method enable_backslash_newline() =
    orig_functions <- Format.get_formatter_out_functions();

    let out_string = orig_functions.Format.out_string in

    let out_newline() =
      out_string "\\" 0 1;
      orig_functions.Format.out_newline()
    in

    let fs = { Format.out_string  = out_string;
               Format.out_flush   = orig_functions.Format.out_flush;
               Format.out_newline = out_newline;
               Format.out_spaces  = orig_functions.Format.out_spaces;
               Format.out_indent  = orig_functions.Format.out_indent;
             }
    in
    let stat = self#checkpoint_box() in
    pr_newline();
    self#restore_box stat;
    Format.pp_set_formatter_out_functions fmtr fs

  method disable_backslash_newline() =
    let stat = self#checkpoint_box() in
    pr_flush();
    self#restore_box stat;
    Format.pp_set_formatter_out_functions fmtr orig_functions



  method pr_block_begin = function
    | BStall  -> pr_cut(); pr_lbrace(); self#open_vbox indent; pr_cut()
    | BSshort -> pr_lbrace(); force_newline(); self#open_vbox indent; pad indent

  method pr_block_begin_short() = self#pr_block_begin BSshort
  method pr_block_begin_tall()  = self#pr_block_begin BStall

  method pr_block_end() = self#close_box(); force_newline(); pr_rbrace()

  method pr_a : 'a. ?head:(unit->unit) -> ?tail:(unit->unit) -> (unit->unit) -> ('a -> unit) -> 'a array -> unit
      =
    fun ?(head=pr_none) ?(tail=pr_none) pr_sep pr a ->
      if (Array.length a) > 0 then begin
        head();
        Array.iteri (fun i x -> if i > 0 then pr_sep(); pr x) a;
        tail()
      end

  method pr_ha : 'a. ?head:(unit->unit) -> ?tail:(unit->unit) -> (unit->unit) -> ('a -> unit) -> 'a array -> unit
      =
    fun ?(head=pr_none) ?(tail=pr_none) pr_sep pr a ->
      if (Array.length a) > 0 then begin
        self#open_hbox();
        self#pr_a ~head ~tail pr_sep pr a;
        self#close_box()
      end

  method pr_va : 'a. ?head:(unit->unit) -> ?tail:(unit->unit) -> (unit->unit) -> ('a -> unit) -> 'a array -> unit
      =
    fun ?(head=pr_none) ?(tail=pr_none) pr_sep pr a ->
    if (Array.length a) > 0 then begin
      self#open_vbox 0;
      self#pr_a ~head ~tail pr_sep pr a;
      self#close_box()
    end

  method pr_hva : 'a. ?head:(unit->unit) -> ?tail:(unit->unit) -> (unit->unit) -> ('a -> unit) -> 'a array -> unit
      =
    fun ?(head=pr_none) ?(tail=pr_none) pr_sep pr a ->
      if (Array.length a) > 0 then begin
        self#open_hvbox 0;
        self#pr_a ~head ~tail (fun () -> pr_sep(); pr_cut()) pr a;
        self#close_box();
      end

  method pr_hova : 'a. ?head:(unit->unit) -> ?tail:(unit->unit) -> (unit->unit) -> ('a -> unit) -> 'a array -> unit
      =
    fun ?(head=pr_none) ?(tail=pr_none) pr_sep pr a ->
      if (Array.length a) > 0 then begin
        self#open_hovbox 0;
        self#pr_a ~head ~tail (fun () -> pr_sep(); pr_cut()) pr a;
        self#close_box();
      end

end (* of class Unparsing_base.ppbox *)


let apply_nth f a i =
  try
    f a.(i)
  with
    Invalid_argument _ -> pr_string "___"

end (* of module Make *)
]
