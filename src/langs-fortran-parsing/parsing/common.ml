(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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

(* Author: Masatomo Hashimoto <m.hashimoto@stair.center> *)

(* common.ml *)

[%%prepare_logger]

module Xqueue = Diffast_misc.Xqueue
module Xset = Diffast_misc.Xset
module Xlist = Diffast_misc.Xlist
module Xoption = Diffast_misc.Xoption
module Xprint = Diffast_misc.Xprint

module PB = Langs_common.Parserlib_base
module Loc = Langs_common.Astloc


module DirectiveLine = struct
  type tag =
    | OCL
    | OMP
    | ACC
    | XLF
    | DEC

  type raw = {
      tag        : tag;
      head       : string;
      line       : string;
      queue      : Obj.t Xqueue.c;
      fixed_cont : bool;
      free_cont  : bool;
  }

  let tag_to_string = function
    | OCL -> "OCL"
    | OMP -> "OMP"
    | ACC -> "ACC"
    | XLF -> "XLF"
    | DEC -> "DEC"

  let dummy_queue = new Xqueue.c


  let mkomp line q fixed_cont free_cont = {
    tag        = OMP;
    head       = "!$omp";
    line       = line;
    queue      = q;
    fixed_cont = fixed_cont;
    free_cont  = free_cont;
  }

  let mkacc line fixed_cont free_cont = {
    tag        = ACC;
    head       = "!$acc";
    line       = line;
    queue      = dummy_queue;
    fixed_cont = fixed_cont;
    free_cont  = free_cont;
  }

  let mkocl line = {
    tag        = OCL;
    head       = "!OCL";
    line       = line;
    queue      = dummy_queue;
    fixed_cont = false;
    free_cont  = false;
  }

  let mkdec prefix line = {
    tag        = DEC;
    head       = prefix;
    line       = line;
    queue      = dummy_queue;
    fixed_cont = false;
    free_cont  = false;
  }

  let mkxlf trigger line fixed_cont free_cont = {
    tag        = XLF;
    head       = trigger;
    line       = line;
    queue      = dummy_queue;
    fixed_cont = fixed_cont;
    free_cont  = free_cont;
  }

end

let extensions = [".f";".for";".f90";".f95"]

module LangSpec = struct
  type t = F77 | F90 | F95 | F2003 | F2008

  let to_string = function
    | F77   -> "F77(ISO1539:1980)"
    | F90   -> "F90(ISO/IEC1539:1991)"
    | F95   -> "F95(ISO/IEC1539-1:1997)"
    | F2003 -> "F2003(ISO/IEC1539-1:2004)"
    | F2008 -> "F2008(ISO/IEC1539-1:2010)"

end

module LangExtension = struct
  type t = IBM | Intel | PGI | PGI_CUDA | Fujitsu | Apollo

  let to_string = function
    | Fujitsu  -> "Fujitsu"
    | IBM      -> "IBM XL Fortran"
    | Intel    -> "DEC/Compaq/Intel Fortran"
    | PGI      -> "PGI Fortran"
    | PGI_CUDA -> "PGI CUDA Fortran"
    | Apollo   -> "Apollo/Domain Fortran"

  class set = object
    val exts = Xset.create 0

    method add e =
      Xset.add exts e

    method to_string =
      Xlist.to_string
        (fun s -> "["^s^"]") "" (List.map to_string (Xset.to_list exts))
  end

end

module SourceForm = struct
  type t = Unknown | Fixed | Free | Mixed

  let to_string = function
    | Unknown -> "Unknown"
    | Fixed   -> "Fixed"
    | Free    -> "Free"
    | Mixed   -> "Mixed"

end

[%%capture_path
module LangConfig = struct

  let default_max_line_length_fixed = 72
  let default_max_line_length_free = 132

  class c = object (self)
    val mutable spec = LangSpec.F95
    val exts = new LangExtension.set
    val mutable source_form = SourceForm.Free
    val mutable max_line_length = default_max_line_length_fixed
    val mutable max_line_length_fixed = default_max_line_length_fixed
    val mutable max_line_length_free = default_max_line_length_free


    val mutable parse_d_lines_flag = false

    method parse_d_lines = parse_d_lines_flag
    method _set_parse_d_lines_flag b = parse_d_lines_flag <- b
    method set_parse_d_lines_flag = parse_d_lines_flag <- true
    method clear_parse_d_lines_flag = parse_d_lines_flag <- false

    method spec = spec
    method set_spec s = spec <- s
    method set_spec_F77 = spec <- LangSpec.F77
    method set_spec_F90 = spec <- LangSpec.F90
    method set_spec_F95 = spec <- LangSpec.F95
    method set_spec_F2003 = spec <- LangSpec.F2003
    method set_spec_F2008 = spec <- LangSpec.F2008

    method exts = exts
    method add_ext_Fujitsu  = exts#add LangExtension.Fujitsu
    method add_ext_IBM      = exts#add LangExtension.IBM
    method add_ext_Intel    = exts#add LangExtension.Intel
    method add_ext_PGI      = exts#add LangExtension.PGI
    method add_ext_PGI_CUDA = exts#add LangExtension.PGI_CUDA
    method add_ext_Apollo   = exts#add LangExtension.Apollo

    method source_form = source_form

    method set_source_form sf =
      source_form <- sf;
      match sf with
      | SourceForm.Fixed -> self#set_max_line_length__fixed
      | SourceForm.Free  -> self#set_max_line_length__free
      | _ -> ()

    method set_source_form_fixed =
      self#set_source_form SourceForm.Fixed

    method set_source_form_free =
      self#set_source_form SourceForm.Free

    method is_fixed_source_form =
      let b = source_form = SourceForm.Fixed in
      [%debug_log "%B" b];
      b

    method is_free_source_form =
      let b = source_form  = SourceForm.Free in
      [%debug_log "%B" b];
      b


    method max_line_length = max_line_length

    method _set_max_line_length n =
      [%debug_log "length=%d" n];
      max_line_length <- n

    method set_max_line_length n =
      self#_set_max_line_length n;
      max_line_length_fixed <- n;
      max_line_length_free <- n

    method set_max_line_length_fixed n =
      if max_line_length_fixed < n then begin
        [%debug_log "%d -> %d" max_line_length_fixed n];
        max_line_length_fixed <- n
      end

    method set_max_line_length_free n =
      if max_line_length_free < n then begin
        [%debug_log "%d -> %d" max_line_length_free n];
        max_line_length_free <- n
      end

    method set_max_line_length__fixed =
      self#_set_max_line_length max_line_length_fixed

    method set_max_line_length__free =
      self#_set_max_line_length max_line_length_free


    method conf_F77 =
      self#set_spec_F77;
      self#set_source_form_fixed;
      self#set_max_line_length_fixed

    method conf_F90_free =
      self#set_spec_F90;
      self#set_source_form_free;
      self#set_max_line_length__free

    method conf_F90_fixed =
      self#set_spec_F90;
      self#set_source_form_fixed;
      self#set_max_line_length__fixed

    method conf_F95_free =
      self#set_spec_F95;
      self#set_source_form_free;
      self#set_max_line_length__free

    method conf_F95_fixed =
      self#set_spec_F95;
      self#set_source_form_fixed;
      self#set_max_line_length__fixed

  end

end (* module Lang_config *)
]


exception Undefined


type name = string
type label = string
type var = string


let parse_warning_loc loc = PB.parse_warning_loc ~head:"[Fortran]" loc
let parse_warning spos epos = PB.parse_warning ~head:"[Fortran]" spos epos


exception Parse_error = PB.Parse_error

exception Internal_error of string


let fail_to_parse = PB.fail_to_parse

let string_opt_to_string ?(prefix="") ?(suffix="") s_opt = Xoption.to_string (fun s -> s) ~prefix ~suffix s_opt
let int_opt_to_string ?(prefix="") ?(suffix="") s_opt = Xoption.to_string string_of_int ~prefix ~suffix s_opt
let opt_to_string = Xoption.to_string
let opt_to_list = Xoption.to_list

let opt_to_list_map f o = try Xoption.to_list_map f o with Not_found -> []

let list_opt_to_list = Xoption.list_opt_to_list

let opt_list_to_list = Xoption.list_to_list

let map_opt f o = try Xoption.map f o with Not_found -> None

let string_list_to_string ?(prefix=" ") sep ss =
  match ss with
  | [] -> ""
  | _ -> prefix^(Xlist.to_string (fun x -> x) sep ss)

let int_list_to_string ?(prefix=" ") sep il =
  match il with
  | [] -> ""
  | _ -> prefix^(Xlist.to_string string_of_int sep il)


let num_to_ordinal n =
  let suffix =
    match n mod 10 with
    | 1 -> "st"
    | 2 -> "nd"
    | 3 -> "rd"
    | _ -> "th"
  in
  Printf.sprintf "%d%s" n suffix

let warning_msg = Xprint.warning ~head:"[Fortran]"
