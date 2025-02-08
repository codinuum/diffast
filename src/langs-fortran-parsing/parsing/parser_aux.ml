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

(* parser_aux.ml *)

[%%prepare_logger]

module Xstring = Diffast_misc.Xstring
module Xhash = Diffast_misc.Xhash
module Fname = Langs_common.Fname
module Env_base = Langs_common.Env_base
module Parserlib_base = Langs_common.Parserlib_base

open Printf
open Common
open Labels
open Ast

module L = Label
module I = Pinfo
module N = I.Name
module PB = Parserlib_base
module C = Context
module B = Binding
module BID = Binding.ID


type char_context =
  | CH_NONE
  | CH_SINGLE
  | CH_DOUBLE

let char_context_to_string = function
  | CH_NONE   -> "NONE"
  | CH_SINGLE -> "SINGLE QUOTE"
  | CH_DOUBLE -> "DOUBLE QUOTE"


type state =
    { s_at_bopu     : bool;
      s_symbol_tbl  : (name, N.frame) Hashtbl.t;
      s_stack       : N.frame Stack.t;

      s_in_format_context       : bool;
      s_in_open_context         : bool;
      s_in_close_context        : bool;
      s_in_position_context     : bool;
      s_in_io_control_context   : bool;
      s_in_wait_context         : bool;
      s_in_flush_context        : bool;
      s_in_if_context           : bool;
      s_in_inquire_context      : bool;
      s_in_implicit_context     : bool;
      s_in_letter_context       : bool;
      s_in_intent_context       : bool;
      s_in_result_context       : bool;
      s_in_character_context    : bool;
      s_in_typeof_context       : bool;
      s_in_do_context           : bool;
      s_in_slash_name_context   : bool;
      s_in_allocate_context     : bool;
      s_in_type_spec_context    : bool;
      s_in_bind_context         : bool;
      s_in_contains_context     : bool;
      s_in_access_context       : bool;
      s_in_data_context         : bool;
      s_in_type_guard_context   : bool;
      s_in_procedure_context    : bool;
      s_in_type_context         : bool;
      s_in_only_context         : bool;
      s_in_pu_head_context      : bool;

      s_name_context            : int;
      s_paren_context           : int;
      s_array_ctor_context      : int;
      s_interface_context       : int;
      s_structure_context       : int;
      s_select_type_context     : int;

      s_char_context            : char_context;
    }

let mkstate bopu stbl stack
    in_f in_o in_cl in_po in_io in_w in_fl
    in_if in_inq in_im in_lt in_int in_res in_chr in_tof in_do in_sn in_a in_ts in_b
    in_c in_acc in_d in_tg in_p in_t in_on in_ph
    nc pc ac ic sc stc cc
    =
  { s_at_bopu     = bopu;
    s_symbol_tbl  = stbl;
    s_stack       = stack;

    s_in_format_context       = in_f;
    s_in_open_context         = in_o;
    s_in_close_context        = in_cl;
    s_in_position_context     = in_po;
    s_in_io_control_context   = in_io;
    s_in_wait_context         = in_w;
    s_in_flush_context        = in_fl;
    s_in_if_context           = in_if;
    s_in_inquire_context      = in_inq;
    s_in_implicit_context     = in_im;
    s_in_letter_context       = in_lt;
    s_in_intent_context       = in_int;
    s_in_result_context       = in_res;
    s_in_character_context    = in_chr;
    s_in_typeof_context       = in_tof;
    s_in_do_context           = in_do;
    s_in_slash_name_context   = in_sn;
    s_in_allocate_context     = in_a;
    s_in_type_spec_context    = in_ts;
    s_in_bind_context         = in_b;
    s_in_contains_context     = in_c;
    s_in_access_context       = in_acc;
    s_in_data_context         = in_d;
    s_in_type_guard_context   = in_tg;
    s_in_procedure_context    = in_p;
    s_in_type_context         = in_t;
    s_in_only_context         = in_on;
    s_in_pu_head_context      = in_ph;
    s_name_context            = nc;
    s_paren_context           = pc;
    s_array_ctor_context      = ac;
    s_interface_context       = ic;
    s_structure_context       = sc;
    s_select_type_context     = stc;
    s_char_context            = cc;
  }

let stack_to_string stack =
  let buf = Buffer.create 0 in
  Stack.iter
    (fun frm ->
      Buffer.add_string buf (N.ScopingUnit.to_string frm#scope);
      Buffer.add_string buf "\n";
    ) stack;
  Buffer.contents buf

let stat_to_string {
  s_at_bopu     = bopu;
  s_symbol_tbl  = (*stbl*)_;
  s_stack       = stack;

  s_in_format_context       = in_f;
  s_in_open_context         = in_o;
  s_in_close_context        = in_cl;
  s_in_position_context     = in_po;
  s_in_io_control_context   = in_io;
  s_in_wait_context         = in_w;
  s_in_flush_context        = in_fl;
  s_in_if_context           = in_if;
  s_in_inquire_context      = in_inq;
  s_in_implicit_context     = in_im;
  s_in_letter_context       = in_lt;
  s_in_intent_context       = in_int;
  s_in_result_context       = in_res;
  s_in_character_context    = in_chr;
  s_in_typeof_context       = in_tof;
  s_in_do_context           = in_do;
  s_in_slash_name_context   = in_sn;
  s_in_allocate_context     = in_a;
  s_in_type_spec_context    = in_ts;
  s_in_bind_context         = in_b;
  s_in_contains_context     = in_c;
  s_in_access_context       = in_acc;
  s_in_data_context         = in_d;
  s_in_type_guard_context   = in_tg;
  s_in_procedure_context    = in_p;
  s_in_type_context         = in_t;
  s_in_only_context         = in_on;
  s_in_pu_head_context      = in_ph;
  s_name_context            = nc;
  s_paren_context           = pc;
  s_array_ctor_context      = ac;
  s_interface_context       = ic;
  s_structure_context       = sc;
  s_select_type_context     = stc;
  s_char_context            = cc;
}
    =
  let fmt =
    "stack:\n%s"^^
    "at_BOPU               : %B\n"^^
    "in_format_context     : %B\n"^^
    "in_open_context       : %B\n"^^
    "in_close_context      : %B\n"^^
    "in_position_context   : %B\n"^^
    "in_io_control_context : %B\n"^^
    "in_wait_context       : %B\n"^^
    "in_flush_context      : %B\n"^^
    "in_if_context         : %B\n"^^
    "in_inquire_context    : %B\n"^^
    "in_implicit_context   : %B\n"^^
    "in_letter_context     : %B\n"^^
    "in_intent_context     : %B\n"^^
    "in_result_context     : %B\n"^^
    "in_character_context  : %B\n"^^
    "in_typeof_context     : %B\n"^^
    "in_do_context         : %B\n"^^
    "in_slash_name_context : %B\n"^^
    "in_allocate_context   : %B\n"^^
    "in_type_spec_context  : %B\n"^^
    "in_bind_context       : %B\n"^^
    "in_contains_context   : %B\n"^^
    "in_access_context     : %B\n"^^
    "in_data_context       : %B\n"^^
    "in_type_guard_context : %B\n"^^
    "in_procedure_context  : %B\n"^^
    "in_type_context       : %B\n"^^
    "in_only_context       : %B\n"^^
    "in_pu_head_context    : %B\n"^^
    "name_context       : %d\n"^^
    "paren_context      : %d\n"^^
    "array_ctor_context : %d\n"^^
    "interface_context  : %d\n"^^
    "structure_context  : %d\n"^^
    "select_type_context: %d\n"^^
    "char_context       : %s\n"
  in
  sprintf fmt
    (stack_to_string stack)
    bopu
    in_f in_o in_cl in_po in_io in_w in_fl
    in_if in_inq in_im in_lt in_int in_res
    in_chr in_tof in_do in_sn in_a in_ts in_b
    in_c in_acc in_d in_tg in_p in_t in_on in_ph
    nc pc ac ic sc stc (char_context_to_string cc)




module LineStat = struct
  type t =
    | AssumedBlank
    | Nonblank
    | PureComment
    | MixedComment
    | Continued

  let to_string = function
    | AssumedBlank -> "AssumedBlank"
    | Nonblank     -> "Nonblank"
    | PureComment  -> "PureComment"
    | MixedComment -> "MixedComment"
    | Continued    -> "Continued"

  let is_pure_comment = function
    | PureComment -> true
    | _ -> false

  let is_assumed_blank = function
    | AssumedBlank -> true
    | _ -> false

  let is_continued = function
    | Continued -> true
    | _ -> false

end



type lexer_mode =
  | LEX_NORMAL
  | LEX_QUEUE
  | LEX_QUEUE_THEN_DO of (unit -> Obj.t)

type line_format =
  | LF_FIXED
  | LF_TAB
  | LF_FREE
  | LF_UNKNOWN


let strip_loc loc = loc.Astloc.filename <- (Fname.strip loc.Astloc.filename)

[%%capture_path
class env = object (self)
  inherit [Source.c] Env_base.c as super

  val bidgen = new BID.generator

  val mutable effective_lines_for_source_form_guess = 0
  val mutable ignore_include_flag = false

  val mutable context_enter_flag = false
  val mutable context_activate_flag = false
  val mutable last_active_ofss = (0, 0)
  val mutable partial_parsing_flag = false


  val mutable bol_flag = true (* beginning of line *)
  val mutable bos_flag = false (* beginning of statement *)
  val mutable continuable_flag = false
  val mutable continued_flag = false
  val mutable amp_line_flag = false (* '&' found in the line *)
  val mutable bocl_flag = false (* beginning of continued line *)


  val mutable token_feeded_flag = false (* is Ulexer.token called after encounter with line_terminator *)
  val mutable line_stat = LineStat.AssumedBlank
(*
  val mutable prev_line_stat = LineStat.AssumedBlank
*)

  val mutable pending_EOL_obj = (None : Obj.t option)

  val pending_RAWOMP_obj_queue = (Queue.create() : Obj.t Queue.t)

  val pending_token_obj_queue = (Queue.create() : Obj.t Queue.t)



  val mutable last_lex_qtoken_obj = Obj.repr ()

  val mutable lex_mode = LEX_NORMAL

  val mutable lex_paren_context = 0

  val lex_pp_branch_stack = Stack.create ()

  method lex_enter_pp_branch (br : PpDirective.branch) =
    Stack.push (br, lex_paren_context) lex_pp_branch_stack

  method lex_exit_pp_branch =
    try
      Stack.pop lex_pp_branch_stack
    with
      Stack.Empty -> failwith "Parser_aux.env#lex_exit_pp_branch"

  method lex_current_pp_branch =
    try
      Stack.top lex_pp_branch_stack
    with
      Stack.Empty -> failwith "Parser_aux.env#lex_current_pp_branch"

  val mutable last_char = '\000'

  method set_last_char c = last_char <- c

  method last_char = last_char


  val source_form_tbl = (Hashtbl.create 0 : (string, SourceForm.t) Hashtbl.t)
  method add_source_form path form =
    Hashtbl.replace source_form_tbl path form
  method get_source_form path =
    Hashtbl.find source_form_tbl path


  val mutable discarded_branch_entry_count = 0
  method discarded_branch_entry_count = discarded_branch_entry_count
  method incr_discarded_branch_entry_count =
    [%debug_log "%d -> %d" discarded_branch_entry_count (discarded_branch_entry_count + 1)];
    discarded_branch_entry_count <- discarded_branch_entry_count + 1

  method decr_discarded_branch_entry_count =
    [%debug_log "%d -> %d" discarded_branch_entry_count (discarded_branch_entry_count - 1)];
    discarded_branch_entry_count <- discarded_branch_entry_count - 1

  val loc_stack = new Layeredloc.loc_stack

  val mutable base_file = ""

  method set_base_file p = base_file <- p


  val mutable current_loc_layers = []
  val mutable prev_loc_layers = []
  val mutable current_loc_layers_encoded = ""

  method current_loc_layers = current_loc_layers

  method current_loc_layers_encoded = current_loc_layers_encoded

  method loc_stack_level = loc_stack#get_level

  method push_loc loc =
    [%debug_log "pushing [%s]" (Astloc.to_string ~short:true loc)];
    let loc =
      if Fname.is_extended loc.Astloc.filename then
        Loc.get_stripped loc
      else
        loc
    in
    [%debug_log "loc stack: %s" loc_stack#to_string];
    loc_stack#push loc;
    prev_loc_layers <- current_loc_layers;
    current_loc_layers <- loc_stack#get_layers;
    current_loc_layers_encoded <- Layeredloc.encode_layers current_loc_layers

  method pop_loc =
    loc_stack#pop;
    prev_loc_layers <- current_loc_layers;
    current_loc_layers <- loc_stack#get_layers;
    current_loc_layers_encoded <- Layeredloc.encode_layers current_loc_layers

  method mklloc loc = Layeredloc.of_loc loc

  val mutable predefined_macrotbl = (None : Macro.table option)
  method set_predefined_macrotbl tbl = predefined_macrotbl <- tbl

  val macrotbl = new Macro.table "main"

  method macrotbl = macrotbl

  method define_macro ?(conditional=false) id body =
    [%debug_log "id=%s conditional=%B" id conditional];
    macrotbl#define ~conditional id body

  method undefine_macro id =
    [%debug_log "%s" id];
    macrotbl#undefine id

  method find_macro id =
    [%debug_log "id=%s" id];
    try
      macrotbl#find id
    with
      Not_found ->
        match predefined_macrotbl with
        | Some tbl -> tbl#find id
        | None -> raise Not_found

  method find_all_macros id =
    [%debug_log "id=%s" id];
    let ms = macrotbl#find_all id in
    if ms = [] then
        match predefined_macrotbl with
        | Some tbl -> tbl#find_all id
        | None -> []
    else
      ms

  method macro_defined id =
    try
      let _ = self#find_macro id in
      true
    with
      Not_found -> false


  val lex_macrotbl = new Macro.table "lex"

  method lex_macrotbl = lex_macrotbl

  method lex_define_macro id body =
    [%debug_log "%s" id];
    lex_macrotbl#define id body

  method lex_undefine_macro id =
    [%debug_log "%s" id];
    lex_macrotbl#undefine id

  method lex_find_macro id =
    [%debug_log "id=%s" id];
    try
      lex_macrotbl#find id
    with
      Not_found ->
        match predefined_macrotbl with
        | Some tbl -> tbl#find id
        | None -> raise Not_found

  method lex_find_all_macros id =
    [%debug_log "id=%s" id];
    let ms =
      lex_macrotbl#find_all id
    in
    if ms = [] then
      match predefined_macrotbl with
      | Some tbl -> tbl#find_all id
      | None -> raise Not_found
    else
      ms

  val mutable ignore_case_flag = false

  method ignore_case = ignore_case_flag
  method set_ignore_case_flag = ignore_case_flag <- true
  method clear_ignore_case_flag = ignore_case_flag <- false

  val fname_ext_cache = (Hashtbl.create 0 : Fname.ext_cache_t)
  method fname_ext_cache = fname_ext_cache

  val mutable line_format = LF_UNKNOWN
  method line_format = line_format
  method enter_fixed_line = line_format <- LF_FIXED
  method enter_tab_line   = line_format <- LF_TAB
  method enter_free_line  = line_format <- LF_FREE

  method in_fixed_line = line_format = LF_FIXED
  method in_tab_line   = line_format = LF_TAB

  method fragment_impossible =
    [%debug_log "in_interface_context: %B" self#in_interface_context];
    [%debug_log "in_contains_context : %B" self#in_contains_context];
    [%debug_log "in_pu_head_context  : %B" self#in_pu_head_context];
    [%debug_log "current scope: %s"
      (Pinfo.Name.ScopingUnit.to_string self#current_frame#scope)];
    let b =
      self#in_interface_context ||
      self#in_contains_context ||
      self#in_pu_head_context ||
      (match self#current_frame#scope with
      | Pinfo.Name.ScopingUnit.Program -> false
      | Pinfo.Name.ScopingUnit.MainProgram(_, headed) -> !headed
      | _ -> true
      )
    in
    [%debug_log "%B" b];
    b


(* put in saved states *)
  val mutable bopu_flag = true (* beginning of program unit *)

  val label_tbl = (Hashtbl.create 0 : ((string * int), label * Loc.t) Hashtbl.t)
  val mutable symbol_tbl = Hashtbl.create 0
  val mutable stack = Stack.create()
  val mutable stack_backup = Stack.create()

  val mutable in_format_context     = false
  val mutable in_open_context       = false
  val mutable in_close_context      = false
  val mutable in_position_context   = false
  val mutable in_io_control_context = false
  val mutable in_wait_context       = false
  val mutable in_flush_context      = false
  val mutable in_if_context         = false
  val mutable in_inquire_context    = false
  val mutable in_implicit_context   = false
  val mutable in_letter_context     = false
  val mutable in_intent_context     = false
  val mutable in_result_context     = false
  val mutable in_character_context  = false

  val mutable in_typeof_context     = false
  val mutable in_do_context         = false
  val mutable in_slash_name_context = false
  val mutable in_allocate_context   = false
  val mutable in_type_spec_context  = false
  val mutable in_bind_context       = false
  val mutable in_contains_context   = false
  val mutable in_access_context     = false
  val mutable in_data_context       = false
  val mutable in_type_guard_context = false
  val mutable in_procedure_context  = false
  val mutable in_type_context       = false
  val mutable in_only_context       = false
  val mutable in_pu_head_context    = false

  val mutable in_vfe_context        = false

  val mutable name_context        = 0
  val mutable paren_context       = 0
  val mutable array_ctor_context  = 0
  val mutable interface_context   = 0
  val mutable structure_context   = 0
  val mutable select_type_context = 0

  val mutable char_context = CH_NONE



  val checkpoint_tbl = Hashtbl.create 0 (* C.key_t -> state *)

  val ambiguous_nodes = Xset.create 0

  val toplevel_frame = N.make_toplevel_frame()


(*  val latest_stmt_nodes_stack = (Stack.create() : Ast.node Xset.t Stack.t)*)



(* other methods *)

  method change_stack s =
    [%debug_log "called"];
    stack_backup <- stack;
    stack <- s

  method recover_stack =
    [%debug_log "called"];
    stack <- stack_backup

  method reset_stack =
    [%debug_log "called"];
    stack <- Stack.create();
    ignore (self#_begin_scope N.ScopingUnit.Program);
    ignore (self#_begin_scope (N.ScopingUnit.MainProgram(None, ref false)))


  method genbid lod =
    try
      let loc = N.Spec.loc_of_decl_to_loc lod in
      [%debug_log "filename=\"%s\"" loc.Loc.filename];
      let stree = self#current_source#tree in
      let digest = Xhash.to_hex (stree#get_entry loc.Loc.filename)#file_digest in
      let s = sprintf "%s-%d_%d" digest loc.Loc.start_offset loc.Loc.end_offset in
      BID.make_global s
    with
      Not_found ->
        bidgen#gen

(*
  method latest_stmt_node_set =
    try
      Stack.top latest_stmt_nodes_stack
    with
      Stack.Empty ->
        [%debug_log "stack empty"];
        Xset.create 0

  method add_latest_stmt_node nd =
    try
      let s = Stack.top latest_stmt_nodes_stack in
      Xset.add s nd
    with
      Stack.Empty -> [%debug_log "stack empty"]

  method push_latest_stmt_node_set =
    [%debug_log "called"];
    Stack.push (Xset.create 0) latest_stmt_nodes_stack

  method pop_latest_stmt_node_set =
    [%debug_log "called"];
    try
      let _ = Stack.pop latest_stmt_nodes_stack in
      ()
    with
      Stack.Empty -> [%debug_log "stack empty"]

  method init_latest_stmt_node_set_stack =
    Stack.clear latest_stmt_nodes_stack;
    self#push_latest_stmt_node_set;
    self#push_latest_stmt_node_set
*)

  method context_enter_flag = context_enter_flag
  method set_context_enter_flag = context_enter_flag <- true
  method clear_context_enter_flag = context_enter_flag <- false

  method context_activate_flag = context_activate_flag
  method set_context_activate_flag = context_activate_flag <- true
  method clear_context_activate_flag = context_activate_flag <- false

  method set_partial_parsing_flag = partial_parsing_flag <- true
  method clear_partial_parsing_flag = partial_parsing_flag <- false
  method partial_parsing_flag = partial_parsing_flag

  method get_last_active_ofss = last_active_ofss

  method set_last_active_ofss (st, ed) =
    [%debug_log "%d - %d" st ed];
    last_active_ofss <- (st, ed)


  method lex_mode = lex_mode
  method reset_lex_mode = lex_mode <- LEX_NORMAL
  method set_lex_mode_queue = lex_mode <- LEX_QUEUE
  method set_lex_mode_queue_then_do f = lex_mode <- (LEX_QUEUE_THEN_DO f)


  method at_BOPU =
    [%debug_log "BOPU_flag=%B" bopu_flag];
    bopu_flag

  method set_BOPU =
    [%debug_log "BOPU_flag set"];
    bopu_flag <- true

  method clear_BOPU =
    [%debug_log "BOPU_flag cleared"];
    bopu_flag <- false


  method at_BOL = bol_flag
  method set_BOL =
    [%debug_log "BOL set"];
    bol_flag <- true;
    self#clear_token_feeded;
(*
    let lstat =
      match line_stat with
      | LineStat.AssumedBlank -> LineStat.PureComment
      | _ -> line_stat
    in
    prev_line_stat <- lstat;
    [%debug_log "prev_line_stat: set to %s" (LineStat.to_string prev_line_stat)];
*)
    self#set_line_stat_assumed_blank


  method clear_BOL =
    [%debug_log "BOL cleared"];
    bol_flag <- false

  method at_BOS = bos_flag

  method set_BOS =
    [%debug_log "BOS flag set"];
    bos_flag <- true

  method clear_BOS =
    [%debug_log "BOS flag cleared"];
    bos_flag <- false


  method continuable = continuable_flag
  method set_continuable = continuable_flag <- true
  method clear_continuable = continuable_flag <- false


  method token_feeded = token_feeded_flag
  method set_token_feeded =
    [%debug_log "token feeded flag set"];
    token_feeded_flag <- true
  method clear_token_feeded =
    [%debug_log "token feeded flag cleared"];
    token_feeded_flag <- false

  method line_stat = line_stat
  method set_line_stat s =
    [%debug_log "setting line status to %s" (LineStat.to_string s)];
    line_stat <- s

  method set_line_stat_assumed_blank = self#set_line_stat LineStat.AssumedBlank
  method set_line_stat_nonblank      = self#set_line_stat LineStat.Nonblank
  method set_line_stat_pure_comment  = self#set_line_stat LineStat.PureComment
  method set_line_stat_mixed_comment = self#set_line_stat LineStat.MixedComment
  method set_line_stat_continued     = self#set_line_stat LineStat.Continued

(*
  method prev_line_stat = prev_line_stat
*)

  method continued = continued_flag
  method set_continued =
    [%debug_log "continued flag set"];
    continued_flag <- true

  method clear_continued =
    [%debug_log "continued flag cleared"];
    continued_flag <- false

  method amp_line = amp_line_flag
  method set_amp_line =
    [%debug_log "amp line flag set"];
    amp_line_flag <- true

  method clear_amp_line =
    [%debug_log "amp line flag cleared"];
    amp_line_flag <- false

  method at_BOCL = bocl_flag
  method set_BOCL =
    [%debug_log "BOCL flag set"];
    bocl_flag <- true

  method clear_BOCL =
    [%debug_log "BOCL flag cleared"];
    bocl_flag <- false

  method set_pending_EOL_obj o =
    [%debug_log "set!"];
    pending_EOL_obj <- Some o

  method clear_pending_EOL_obj =
    [%debug_log "cleared!"];
    pending_EOL_obj <- None

  method get_pending_EOL_obj =
    match pending_EOL_obj with
    | Some o -> o
    | _ -> raise Not_found

  method take_pending_EOL_obj =
    match pending_EOL_obj with
    | Some o ->
        pending_EOL_obj <- None;
        o
    | _ -> raise Not_found

  method pending_RAWOMP_obj_queue_length = Queue.length pending_RAWOMP_obj_queue

  method add_pending_RAWOMP_obj o = Queue.add o pending_RAWOMP_obj_queue

  method clear_pending_RAWOMP_obj_queue =
    [%debug_log "called"];
    Queue.clear pending_RAWOMP_obj_queue

  method take_pending_RAWOMP_obj = Queue.take pending_RAWOMP_obj_queue

  method pending_token_obj_queue_length = Queue.length pending_token_obj_queue

  method add_pending_token_obj o = Queue.add o pending_token_obj_queue

  method clear_pending_token_obj_queue =
    [%debug_log "called"];
    Queue.clear pending_token_obj_queue

  method take_pending_token_obj = Queue.take pending_token_obj_queue


  method set_last_lex_qtoken_obj o =
    [%debug_log "called"];
    last_lex_qtoken_obj <- o

  method get_last_lex_qtoken_obj = last_lex_qtoken_obj

  method in_format_context = in_format_context
  method enter_format_context = [%debug_log "entering format context"]; in_format_context <- true
  method exit_format_context = [%debug_log "exiting format context"]; in_format_context <- false

  method in_open_context = in_open_context
  method enter_open_context = [%debug_log "entering open context"]; in_open_context <- true
  method exit_open_context = [%debug_log "exiting open context"]; in_open_context <- false

  method in_close_context = in_close_context
  method enter_close_context = [%debug_log "entering close context"]; in_close_context <- true
  method exit_close_context = [%debug_log "exiting close context"]; in_close_context <- false

  method in_position_context = in_position_context
  method enter_position_context = [%debug_log "entering position context"]; in_position_context <- true
  method exit_position_context = [%debug_log "exiting position context"]; in_position_context <- false

  method in_io_control_context = in_io_control_context
  method enter_io_control_context = [%debug_log "entering io_control context"]; in_io_control_context <- true
  method exit_io_control_context = [%debug_log "exiting io_control context"]; in_io_control_context <- false

  method in_wait_context = in_wait_context
  method enter_wait_context = [%debug_log "entering wait context"]; in_wait_context <- true
  method exit_wait_context = [%debug_log "exiting wait context"]; in_wait_context <- false

  method in_flush_context = in_flush_context
  method enter_flush_context = [%debug_log "entering flush context"]; in_flush_context <- true
  method exit_flush_context = [%debug_log "exiting flush context"]; in_flush_context <- false

  method in_if_context = in_if_context
  method enter_if_context = [%debug_log "entering if context"]; in_if_context <- true
  method exit_if_context = [%debug_log "exiting if context"]; in_if_context <- false

  method in_inquire_context = in_inquire_context
  method enter_inquire_context = [%debug_log "entering inquire context"]; in_inquire_context <- true
  method exit_inquire_context = [%debug_log "exiting inquire context"]; in_inquire_context <- false

  method in_implicit_context = in_implicit_context
  method enter_implicit_context = [%debug_log "entering implicit context"]; in_implicit_context <- true
  method exit_implicit_context = [%debug_log "exiting implicit context"]; in_implicit_context <- false

  method in_letter_context = in_letter_context
  method enter_letter_context = [%debug_log "entering letter context"]; in_letter_context <- true
  method exit_letter_context = [%debug_log "exiting letter context"]; in_letter_context <- false

  method in_intent_context = in_intent_context
  method enter_intent_context = [%debug_log "entering intent context"]; in_intent_context <- true
  method exit_intent_context = [%debug_log "exiting intent context"]; in_intent_context <- false

  method in_result_context = in_result_context
  method enter_result_context = [%debug_log "entering result context"]; in_result_context <- true
  method exit_result_context = [%debug_log "exiting result context"]; in_result_context <- false

  method in_character_context = in_character_context
  method enter_character_context = [%debug_log "entering character context"]; in_character_context <- true
  method exit_character_context = [%debug_log "exiting character context"]; in_character_context <- false

  method in_typeof_context = in_typeof_context
  method enter_typeof_context = [%debug_log "entering typeof context"]; in_typeof_context <- true
  method exit_typeof_context = [%debug_log "exiting typeof context"]; in_typeof_context <- false

  method in_do_context = in_do_context
  method enter_do_context = [%debug_log "entering do context"]; in_do_context <- true
  method exit_do_context = [%debug_log "exiting do context"]; in_do_context <- false

  method in_slash_name_context = in_slash_name_context
  method enter_slash_name_context = [%debug_log "entering slash_name context"]; in_slash_name_context <- true
  method exit_slash_name_context = [%debug_log "exiting slash_name context"]; in_slash_name_context <- false

  method in_allocate_context = in_allocate_context
  method enter_allocate_context = [%debug_log "entering allocate context"]; in_allocate_context <- true
  method exit_allocate_context = [%debug_log "exiting allocate context"]; in_allocate_context <- false

  method in_type_spec_context = in_type_spec_context
  method enter_type_spec_context = [%debug_log "entering type-spec context"]; in_type_spec_context <- true
  method exit_type_spec_context = [%debug_log "exiting type-spec context"]; in_type_spec_context <- false

  method in_bind_context = in_bind_context
  method enter_bind_context = [%debug_log "entering bind context"]; in_bind_context <- true
  method exit_bind_context = [%debug_log "exiting bind context"]; in_bind_context <- false

  method in_interface_context = interface_context > 0

  method enter_interface_context =
    interface_context <- interface_context + 1;
    [%debug_log "entering interface context (->%d)" interface_context]

  method exit_interface_context =
    begin %debug_block
      if interface_context = 0 then
        [%debug_log "unbalanced end of interface"]
    end;
    interface_context <- interface_context - 1;
    [%debug_log "exiting interface context (->%d)" interface_context]

  method in_structure_context = structure_context > 0

  method enter_structure_context =
    structure_context <- structure_context + 1;
    [%debug_log "entering structure context (->%d)" structure_context]

  method exit_structure_context =
    begin %debug_block
      if structure_context = 0 then
        [%debug_log "unbalanced end of structure"]
    end;
    structure_context <- structure_context - 1;
    [%debug_log "exiting structure context (->%d)" structure_context]

  method in_select_type_context = select_type_context > 0

  method enter_select_type_context =
    select_type_context <- select_type_context + 1;
    [%debug_log "entering select-type context (->%d)" select_type_context]

  method exit_select_type_context =
    begin %debug_block
      if select_type_context = 0 then
        [%debug_log "unbalanced end of select-type"]
    end;
    select_type_context <- select_type_context - 1;
    [%debug_log "exiting select-type context (->%d)" select_type_context]

  method in_contains_context = in_contains_context
  method enter_contains_context = [%debug_log "entering contains context"]; in_contains_context <- true
  method exit_contains_context = [%debug_log "exiting contains context"]; in_contains_context <- false

  method in_access_context = in_access_context
  method enter_access_context = [%debug_log "entering access context"]; in_access_context <- true
  method exit_access_context = [%debug_log "exiting access context"]; in_access_context <- false

  method in_data_context = in_data_context
  method enter_data_context = [%debug_log "entering data context"]; in_data_context <- true
  method exit_data_context = [%debug_log "exiting data context"]; in_data_context <- false

  method in_type_guard_context = in_type_guard_context
  method enter_type_guard_context = [%debug_log "entering type-guard context"]; in_type_guard_context <- true
  method exit_type_guard_context = [%debug_log "exiting type-guard context"]; in_type_guard_context <- false

  method in_procedure_context = in_procedure_context
  method enter_procedure_context = [%debug_log "entering procedure context"]; in_procedure_context <- true
  method exit_procedure_context = [%debug_log "exiting procedure context"]; in_procedure_context <- false

  method in_type_context = in_type_context
  method enter_type_context = [%debug_log "entering type context"]; in_type_context <- true
  method exit_type_context = [%debug_log "exiting type context"]; in_type_context <- false

  method in_only_context = in_only_context
  method enter_only_context = [%debug_log "entering only context"]; in_only_context <- true
  method exit_only_context = [%debug_log "exiting only context"]; in_only_context <- false

  method in_pu_head_context = in_pu_head_context
  method enter_pu_head_context = [%debug_log "entering PU-head context"]; in_pu_head_context <- true
  method exit_pu_head_context = [%debug_log "exiting PU-head context"]; in_pu_head_context <- false

  method in_vfe_context = in_vfe_context
  method enter_vfe_context = [%debug_log "entering vfe context"]; in_vfe_context <- true
  method exit_vfe_context = [%debug_log "exiting vfe context"]; in_vfe_context <- false

  method in_array_ctor_context = array_ctor_context > 0

  method enter_array_ctor_context =
    array_ctor_context <- array_ctor_context + 1;
    [%debug_log "entering array constructor context (->%d)" array_ctor_context]

  method exit_array_ctor_context =
    begin %debug_block
      if array_ctor_context = 0 then
        [%debug_log "unbalanced array constructor"]
    end;
    array_ctor_context <- array_ctor_context - 1;
    [%debug_log "exiting array constructor context (->%d)" array_ctor_context]


  method in_char_context = char_context <> CH_NONE

  method char_context = char_context

  method enter_char_single =
    [%debug_log "entering char single context"];
    char_context <- CH_SINGLE

  method enter_char_double =
    [%debug_log "entering char double context"];
    char_context <- CH_DOUBLE

  method exit_char =
    [%debug_log "exiting char context"];
    char_context <- CH_NONE


  method in_paren_context = paren_context > 0

  method enter_paren_context =
    paren_context <- paren_context + 1;
    [%debug_log "entering paren context (->%d)" paren_context]

  method exit_paren_context =
    begin %debug_block
      if paren_context = 0 then
        [%debug_log "unbalanced parentheses"]
    end;
    paren_context <- paren_context - 1;
    [%debug_log "exiting paren context (->%d)" paren_context]

  method in_name_context = name_context > 0

  method enter_name_context =
    name_context <- name_context + 1;
    [%debug_log "entering name context (->%d)" name_context]

  method exit_name_context =
    begin %debug_block
      if name_context = 0 then
        [%debug_log "unbalanced name_context"]
    end;
    name_context <- name_context - 1;
    [%debug_log "exiting name context (->%d)" name_context]

  method lex_in_paren_context = lex_paren_context > 0
  method lex_paren_level = lex_paren_context

  method lex_enter_paren_context =
    lex_paren_context <- lex_paren_context + 1;
    [%debug_log "entering lex paren context (->%d)" lex_paren_context];

  method lex_exit_paren_context =
    begin %debug_block
    if lex_paren_context = 0 then
      [%debug_log "unbalanced parentheses (lexer)"];
    end;
    lex_paren_context <- lex_paren_context - 1;
    [%debug_log "exiting lex paren context (->%d)" lex_paren_context];




  method register_label path line ((lab, loc) as label) =
    let _ = lab in
    let _ = loc in
    [%debug_log "registering: %s:%d -> label:%s[%s]" path line lab (Loc.to_string loc)];
    Hashtbl.add label_tbl (path, line) label

  method find_label path_line =
    Hashtbl.find label_tbl path_line

  method register_ambiguous_node (node : Ast.node) =
    [%debug_log "registering: %s" node#to_string];
    Xset.add ambiguous_nodes (node, self#__copy_stack stack)

  method iter_ambiguous_nodes (f : Ast.node -> unit) =
    let l = Xset.to_list ambiguous_nodes in
    let sorted =
      List.fast_sort
        (fun (n0, _) (n1, _) ->
          Stdlib.compare n1#loc.Loc.start_offset n0#loc.Loc.start_offset)
        l
    in
    List.iter
      (fun (nd, _stk) ->
        let stk = self#_copy_stack _stk in
        self#change_stack stk;
        (*[%debug_log "top frame:\n%s\n" (Stack.top stk)#to_string];*)
        f nd;
        self#recover_stack
      ) sorted



  method checkpoint (key : C.key_t) =
    [%debug_log "key=%s" (C.key_to_string key)];

    let stat =
      mkstate bopu_flag
        (Hashtbl.copy symbol_tbl) (self#__copy_stack stack)
        in_format_context in_open_context in_close_context in_position_context
        in_io_control_context in_wait_context in_flush_context
        in_if_context in_inquire_context in_implicit_context in_letter_context
        in_intent_context in_result_context in_character_context in_typeof_context
        in_do_context in_slash_name_context in_allocate_context in_type_spec_context
        in_bind_context in_contains_context in_access_context in_data_context
        in_type_guard_context in_procedure_context in_type_context in_only_context
        in_pu_head_context name_context paren_context array_ctor_context interface_context
        structure_context select_type_context char_context
    in

    [%debug_log "status:\n%s" (stat_to_string stat)];

(*
    if Hashtbl.mem checkpoint_tbl key then
      [%debug_log "already checkpointed: key=%s" (C.key_to_string key)];
*)
    Hashtbl.add checkpoint_tbl key stat;


  method recover ?(remove=false) key =
    [%debug_log "key=%s remove=%B" (C.key_to_string key) remove];
    try
      let stat = Hashtbl.find checkpoint_tbl key in

      [%debug_log "\n%s" (stat_to_string stat)];

      bopu_flag          <- stat.s_at_bopu;
      symbol_tbl         <- Hashtbl.copy stat.s_symbol_tbl;
      stack              <- self#__copy_stack stat.s_stack;

      in_format_context     <- stat.s_in_format_context;
      in_open_context       <- stat.s_in_open_context;
      in_close_context      <- stat.s_in_close_context;
      in_position_context   <- stat.s_in_position_context;
      in_io_control_context <- stat.s_in_io_control_context;
      in_wait_context       <- stat.s_in_wait_context;
      in_flush_context      <- stat.s_in_flush_context;
      in_if_context         <- stat.s_in_if_context;
      in_inquire_context    <- stat.s_in_inquire_context;
      in_implicit_context   <- stat.s_in_implicit_context;
      in_letter_context     <- stat.s_in_letter_context;
      in_intent_context     <- stat.s_in_intent_context;
      in_result_context     <- stat.s_in_result_context;
      in_character_context  <- stat.s_in_character_context;
      in_typeof_context     <- stat.s_in_typeof_context;
      in_do_context         <- stat.s_in_do_context;
      in_slash_name_context <- stat.s_in_slash_name_context;
      in_allocate_context   <- stat.s_in_allocate_context;
      in_type_spec_context  <- stat.s_in_type_spec_context;
      in_bind_context       <- stat.s_in_bind_context;
      in_contains_context   <- stat.s_in_contains_context;
      in_access_context     <- stat.s_in_access_context;
      in_data_context       <- stat.s_in_data_context;
      in_type_guard_context <- stat.s_in_type_guard_context;
      in_procedure_context  <- stat.s_in_procedure_context;
      in_type_context       <- stat.s_in_type_context;
      in_only_context       <- stat.s_in_only_context;
      in_pu_head_context    <- stat.s_in_pu_head_context;

      name_context          <- stat.s_name_context;
      paren_context         <- stat.s_paren_context;
      array_ctor_context    <- stat.s_array_ctor_context;
      interface_context     <- stat.s_interface_context;
      structure_context     <- stat.s_structure_context;
      select_type_context   <- stat.s_select_type_context;

      char_context          <- stat.s_char_context;

      if remove then
        Hashtbl.remove checkpoint_tbl key
    with
      Not_found ->
	raise (Internal_error (Printf.sprintf "state not found: key=%s" (C.key_to_string key)));

  method remove_checkpoint_key key =
    Hashtbl.remove checkpoint_tbl key

  method reset_stat =
    [%debug_log "resetting..."];
    self#reset_stack;
(*
    bopu_flag          <- stat.s_at_bopu;
    symbol_tbl         <- Hashtbl.copy stat.s_symbol_tbl;
    stack              <- self#_copy_stack stat.s_stack;
*)
    in_format_context     <- false;
    in_open_context       <- false;
    in_close_context      <- false;
    in_position_context   <- false;
    in_io_control_context <- false;
    in_wait_context       <- false;
    in_flush_context      <- false;
    in_if_context         <- false;
    in_inquire_context    <- false;
    in_implicit_context   <- false;
    in_letter_context     <- false;
    in_intent_context     <- false;
    in_result_context     <- false;
    in_character_context  <- false;
    in_typeof_context     <- false;
    in_do_context         <- false;
    in_slash_name_context <- false;
    in_allocate_context   <- false;
    in_type_spec_context  <- false;
    in_bind_context       <- false;
    in_contains_context   <- false;
    in_access_context     <- false;
    in_data_context       <- false;
    in_type_guard_context <- false;
    in_procedure_context  <- false;
    in_type_context       <- false;
    in_only_context       <- false;
    in_pu_head_context    <- false;

    name_context          <- 0;
    paren_context         <- 0;
    array_ctor_context    <- 0;
    interface_context     <- 0;
    structure_context     <- 0;
    select_type_context   <- 0;

    char_context <- CH_NONE

  method effective_lines_for_source_form_guess = effective_lines_for_source_form_guess

  method ignore_include_flag = ignore_include_flag
  method set_ignore_include_flag = ignore_include_flag <- true
  method clear_ignore_include_flag = ignore_include_flag <- false

(*
  method find_symbol id =
    try
      Hashtbl.find symbol_tbl id
    with
      Not_found -> Hashtbl.find base_symbol_tbl id
*)
  method current_frame =
    try
      Stack.top stack
    with
      Stack.Empty -> raise (Internal_error "Parser_aux.get_current_frame: stack empty")

  method private _copy_stack s =
(*    let copy = Stack.copy s in*)

    let copy = Stack.create() in
    let fs = ref [] in
    Stack.iter (fun f -> fs := f#copy :: !fs) s;
    List.iter (fun f -> Stack.push f copy) !fs;

    copy

  method private __copy_stack s =
    let copy = Stack.create() in
    let fs = ref [] in
    Stack.iter (fun f -> fs := f#_copy :: !fs) s;
    List.iter (fun f -> Stack.push f copy) !fs;
    copy

  method private name_implicit_spec_of_ispec_node (node : Ast.node) =
    match node#label with
    | L.ImplicitSpec -> begin
        match node#children with
        | ty::lss -> begin
            let tspec = I.TypeSpec.of_label ty#label in
            [%debug_log "type=%s" (I.TypeSpec.to_string tspec)];
            let ispec = new N.ImplicitSpec.c tspec in
            let lod = N.Spec.loc_of_decl_implicit node#orig_loc in
            let iod = Oo.id node in
            let bid = self#genbid lod in
            node#set_binding (B.make_unknown_def bid true);
            ispec#set_letter_spec_list
              (Xlist.filter_map
                 (fun ls -> N.ImplicitSpec.letter_spec_of_label ls#label) lss);
            ispec#set_loc_of_decl lod;
            ispec#set_id_of_decl iod;
            ispec#set_bid bid;
            Some ispec
        end
        | _ ->
            parse_warning_loc node#loc "empty ImplicitSpec";
            None
    end
    | lab ->
        parse_warning_loc node#loc
          "not an implicit-spec: %s" (L.to_simple_string lab);
        None


  method set_implicit_spec (ispec_nds : Ast.node list) =
    self#current_frame#set_implicit_spec_list
      (Xlist.filter_map self#name_implicit_spec_of_ispec_node ispec_nds)

  method add_implicit_spec (ispec_nds : Ast.node list) =
    self#current_frame#add_implicit_spec_list
      (Xlist.filter_map self#name_implicit_spec_of_ispec_node ispec_nds)

  method default_accessibility =
    self#current_frame#default_accessibility

  method set_default_accessibility_public =
    self#current_frame#set_default_accessibility_public

  method set_default_accessibility_private =
    self#current_frame#set_default_accessibility_private


  method register_used_module mname =
    [%debug_log "%s" mname];
    (*Printf.printf "!!! register_used_module: %s (%s)\n%!"
      mname (N.ScopingUnit.to_string self#current_frame#scope);*)
    self#current_frame#add_used_module mname

  method register_global_name (id : name) spec =
    [%debug_log "[stack size:%d] \"%s\" -> %s (FRM:%s)"
      (Stack.length stack)
      id
      (N.Spec.to_string spec)
      (N.ScopingUnit.to_string toplevel_frame#scope)];
    toplevel_frame#add id spec

  method register_name ?(nth=0) (id : name) spec =
    let len = Stack.length stack in
    let frm = ref self#current_frame in

    if nth > 0 && nth < len then begin
        let count = ref 0 in
        try
          Stack.iter
            (fun f ->
              if !count = nth then begin
                frm := f;
                raise Exit
              end;
              incr count
            ) stack
        with
          Exit -> ()
    end;
    [%debug_log "[stack size:%d][nth=%d] \"%s\" -> %s (FRM:%s)"
        len nth id
        (N.Spec.to_string spec) (N.ScopingUnit.to_string (!frm)#scope)];

    (!frm)#add id spec


  method iter_used_modules f =
    Stack.iter (fun frame -> frame#iter_used_modules f) stack

  method lookup_name ?(allow_implicit=true) ?(afilt=(fun _ -> true)) (id : name) =
    [%debug_log "[stack size:%d] \"%s\"" (Stack.length stack) id];
(*    let id_ = String.lowercase_ascii id in *)
    let all = ref [] in
    let all_filtered = ref [] in
    let has_open_module_use = ref false in
    begin
      Stack.iter
	(fun frame ->
	  [%debug_log "FRM: <%s>" (N.ScopingUnit.to_string frame#scope)];
          if frame#has_open_module_use then
            has_open_module_use := true;
	  try
	    let specs : N.Spec.t list = frame#find_all id in
            if specs <> [] then begin
              [%debug_log "[not filtered] %s ->\n%s" id (Xlist.to_string (N.Spec.to_string) "\n" specs)];
              all := !all @ specs
            end;
	    let filtered = List.filter afilt specs in
	    if filtered <> [] then begin
	      [%debug_log "[filtered] %s ->\n%s" id (Xlist.to_string (N.Spec.to_string) "\n" filtered)];
              all_filtered := !all_filtered @ filtered
            end
	  with
	    Not_found -> ()
	) stack
    end;
    if !all = [] && allow_implicit then begin
      try
        if !has_open_module_use then
          raise Not_found
        else
          let implicit_spec = self#current_frame#post_find id in
          self#register_name id implicit_spec;
          List.filter afilt [implicit_spec]
      with
        Not_found -> begin
          let ext_specs = ref [N.Spec.mkext "" id] in
          Stack.iter
            (fun frame ->
              ext_specs := !ext_specs @ (frame#get_ext_names id)
            ) stack;
          List.iter (fun s -> self#register_name id s) !ext_specs;
          List.filter afilt !ext_specs
        end
    end
    else begin
      !all_filtered
    end

  method _begin_scope scope =
    let frm =
      match scope with
      | N.ScopingUnit.Program -> toplevel_frame
      | N.ScopingUnit.Module _ -> let f = new N.frame scope in f#set_default_accessibility_public; f
      | _ -> new N.frame scope
    in
    [%debug_log "PUSH(%d): FRM: <%s>" (Stack.length stack) (N.ScopingUnit.to_string scope)];
    Stack.push frm stack;
    frm

  method end_scope =
    try
      let frm = (Stack.pop stack) in

      [%debug_log "POP(%d): FRM: <%s>" (Stack.length stack) (N.ScopingUnit.to_string frm#scope)];

      match frm#scope with
(*
      | SKpackage id -> Hashtbl.add symbol_tbl id frm
      | SKclass id -> begin
	  try
	    let a = self#lookup_name id in
	    match a with
	    | (IAclass tblr)::_ -> tblr := frm.f_tbl
	    | _ -> assert false
	  with
	    Not_found -> assert false (* toplevel *)
      end
*)
      | _ -> ()
    with
      Stack.Empty -> raise (Internal_error "Parser_aux.end_scope: stack empty")

  method find_frame_for id =
    try
      Stack.iter
	(fun frame ->
	  try
	    if frame#mem id then
	      raise (N.Frame_found frame)
	  with
	    Not_found -> ()
	) stack;
      raise Not_found
    with
      N.Frame_found frm -> frm


  method! init =
    bidgen#reset;
    super#init;
    Queue.clear pending_RAWOMP_obj_queue;
    Queue.clear pending_token_obj_queue;
    (*self#init_latest_stmt_node_set_stack;*)
    loc_stack#init;
    Hashtbl.clear symbol_tbl;
    Stack.clear stack;
    Hashtbl.clear checkpoint_tbl;
    Hashtbl.clear fname_ext_cache;
(*
    condtbl#reset;
*)
    context_enter_flag    <- false;
    context_activate_flag <- false;
    last_active_ofss      <- (0, 0);
    partial_parsing_flag  <- false

  initializer
    self#init

end (* of class env *)
]

module type STATE_T = sig
  val env           : env
  val context_stack : Context.stack
end


[%%capture_path
module F (Stat : STATE_T) = struct

  open Stat


  let parse_error spos epos : ('a, unit, string, 'b) format4 -> 'a =
    PB.parse_error env
      (fun loc -> new Ast.node ~lloc:(env#mklloc loc) (L.ERROR ""))
      spos epos

  let parse_error_loc loc : ('a, unit, string, 'b) format4 -> 'a =
    PB.parse_error_loc env
      (fun loc -> new Ast.node ~lloc:(env#mklloc loc) (L.ERROR ""))
      loc


  let check_error (node : Ast.node) =
    if not env#partial_parsing_flag then begin
      Ast.visit
	(fun nd ->
	  if L.is_error nd#label && nd#lloc#get_level = 0 then
	    env#missed_regions#add nd#loc
	) node
    end

  let register_unknown name =
    env#register_name name N.Spec.Unknown

  let register_main name =
    env#register_global_name name N.Spec.MainProgram

  let register_associate_name name =
    env#register_name name N.Spec.AssociateName


  let register_object
      ?(nth=0)
      ?(node=Ast.dummy_node)
      ?(attr_handler=fun _ -> ())
      name
      mkspec
      =
    [%debug_log "name=\"%s\"" name];
    let is_dummy_node = Ast.is_dummy_node node in
    let lod, iod =
      if is_dummy_node then
        N.Spec.loc_of_decl_unknown, -1
      else
        N.Spec.loc_of_decl_explicit node#orig_loc, Oo.id node
    in
    let bid = env#genbid lod in

    let ospec = N.Spec.mkobj ~loc_of_decl:lod ~id_of_decl:iod ~bid_opt:(Some bid) () in

    begin
      try
        let a = ospec#attr in

        attr_handler a;

        begin
          match env#lookup_name ~allow_implicit:false name with
          | [] -> a#set_access_spec env#default_accessibility
          | spec::_ -> begin
              try
                a#set_access_spec (N.Spec.get_access_spec spec)
              with
                _ -> a#set_access_spec env#default_accessibility
          end
        end
      with
        Not_found -> assert false
    end;

    let spec = mkspec ospec in

    if is_dummy_node then begin
      node#set_binding (B.make_unknown_def bid true);
      node#set_info (I.mknamespec spec)
    end;

    env#register_name ~nth name spec
(* func register_object *)


  let register_function ?(node=Ast.dummy_node) name =
    register_object ~node name N.Spec.mkfunction

  let register_subroutine ?(node=Ast.dummy_node) name =
    register_object ~node name N.Spec.mksubroutine

  let register_separate_module_subprogram ?(node=Ast.dummy_node) name =
    register_object ~node name N.Spec.mkseparate_module_subprogram

  let register_entry ?(node=Ast.dummy_node) name =
    ignore name;
    match env#current_frame#scope with
    | N.ScopingUnit.FunctionSubprogram n -> register_function ~node n
    | N.ScopingUnit.SubroutineSubprogram n -> register_subroutine ~node n
    | N.ScopingUnit.SeparateModuleSubprogram n -> register_separate_module_subprogram ~node n
    | _ ->
        failwith
          (Printf.sprintf
             "invalid scoping unit: %s" (N.ScopingUnit.to_string env#current_frame#scope))

  let register_generic ?(node=Ast.dummy_node) name =
    register_object ~node name N.Spec.mkgeneric

  let register_namelist_group ?(node=Ast.dummy_node) name =
    register_object ~node name N.Spec.mknamelistgroup

  let register_derived_type ?(node=Ast.dummy_node) aspec_nodes name frm =
    let attr_specs =
      List.fold_left
        (fun l aspec_node ->
          match aspec_node#label with
          | L.TypeAttrSpec a -> a :: l
          | _ -> l
        ) [] aspec_nodes
    in
    let attr_handler a =
      List.iter
        (function
          | TypeAttrSpec.Public    -> a#set_access_spec_public
          | TypeAttrSpec.Private   -> a#set_access_spec_private
          | TypeAttrSpec.Abstract  -> ()
          | TypeAttrSpec.Bind      -> ()
          | TypeAttrSpec.Extends _ -> ()
        ) attr_specs
    in
    register_object ~nth:1 ~node ~attr_handler name
      (N.Spec.mkderivedtype (N.Spec.mkframev ~find:frm#find ~add:frm#add))

  let register_interface_name name =
    env#register_name name (N.Spec.mkiname name)

  let register_module name frm =
    let spec = N.make_module name frm in
    env#register_global_name name spec

  let register_submodule name frm =
    let spec = N.make_module name frm in
    env#register_global_name name spec

  let register_block_data name =
    env#register_global_name name N.Spec.BlockData

  let register_common_block name =
    env#register_global_name name N.Spec.CommonBlock



  let register_external_name name module_name use_name =
    env#register_name name (N.Spec.mkext module_name use_name)

  let rec register_external ?(exclude=Xset.create 0) mod_name nd =
    match nd#label, nd#children with
    | L.Rename, [ln; un] -> begin
        try
          let n = String.lowercase_ascii ln#get_name in
          if not (Xset.mem exclude n) then
            register_external_name n mod_name un#get_name
        with
          Not_found -> ()
    end
    | L.Ambiguous (Ambiguous.GenericSpecOrUseName n), []
    | L.GenericSpec (GenericSpec.Name n), _ ->
        if not (Xset.mem exclude (String.lowercase_ascii n)) then
          register_external_name n mod_name n

    | L.OnlyList, onlys ->
        List.iter (register_external ~exclude mod_name) onlys

    | _ -> ()


  let register_edecl_node type_spec attr_opt node =
    [%debug_log "%s" node#to_string];
    match node#label with
    | L.EntityDecl n | L.ComponentDecl n -> begin
        let a_opt =

          let ds =
            Xlist.filter_map
              (fun x ->
                if L.is_array_spec x#label || L.is_component_array_spec x#label then
                  Some (N.Dimension.of_label x#label)
                else
                  None
              ) node#children
          in
          let cs =
            Xlist.filter_map
              (fun x ->
                if L.is_coarray_spec x#label then
                  Some (N.Codimension.of_label x#label)
                else
                  None
              ) node#children
          in

          let no_attr = attr_opt = None && ds = [] && cs = [] in

          if no_attr then begin
            let a = new N.Attribute.c in
            a#set_access_spec env#default_accessibility;
            Some a
          end
          else begin
            let attr =
              match attr_opt with
              | Some a -> a
              | None -> new N.Attribute.c
            in
            if attr#access_spec_not_set then
              attr#set_access_spec env#default_accessibility;

            List.iter attr#set_dimension ds;
            List.iter attr#set_codimension cs;
            Some attr
          end
        in (* a_opt *)
        let lod = N.Spec.loc_of_decl_explicit node#orig_loc in
        let iod = Oo.id node in
        let bid = env#genbid lod in
        node#set_binding (B.make_unknown_def bid true);

        let spec =
          match env#lookup_name ~afilt:N.Spec.has_data_object_spec n with
          | spc::_ ->
              let dobj = N.Spec.get_data_object_spec spc in
              dobj#set_type_spec type_spec;
              dobj#set_loc_of_decl lod;
              dobj#set_id_of_decl iod;
              dobj#set_bid bid;
              begin
                match a_opt with
                | Some a -> begin
                    try
                      dobj#attr#merge a
                    with
                      Not_found -> dobj#set_attr a
                end
                | None -> ()
              end;
              [%debug_log " --> %s" (N.Spec.to_string spc)];
              spc
          | [] ->
              let spc =
                N.Spec.mkdobj ~loc_of_decl:lod ~id_of_decl:iod ~bid_opt:(Some bid) ~type_spec a_opt
              in
              env#register_name n spc;
              spc
        in
        node#set_info (I.mknamespec spec)
    end
    | _ -> parse_warning_loc node#loc "not an entity-decl or a component-decl"


  let register_pdecl_node aspec_nodes pi node =
    [%debug_log "%s" node#to_string];
    match node#label with
    | L.ProcDecl n -> begin
        let lod = N.Spec.loc_of_decl_explicit node#orig_loc in
        let iod = Oo.id node in
        let bid = env#genbid lod in
        node#set_binding (B.make_unknown_def bid true);

        let pspec = N.Spec.mkproc ~loc_of_decl:lod ~id_of_decl:iod ~bid_opt:(Some bid) pi in

        let a = try pspec#attr with Not_found -> assert false in

        if aspec_nodes <> [] then begin
          let attr_specs =
            List.fold_left
              (fun l aspec_node ->
                match aspec_node#label with
                | L.ProcAttrSpec a -> a :: l
                | _ -> l
              ) [] aspec_nodes
          in
          List.iter
            (function
              | ProcAttrSpec.Public    -> a#set_access_spec_public
              | ProcAttrSpec.Private   -> a#set_access_spec_private
              | ProcAttrSpec.Bind      -> a#set_bind
              | ProcAttrSpec.Intent i  -> a#set_intent_spec (N.IntentSpec.of_ispec_label i)
              | ProcAttrSpec.Optional  -> a#set_optional
              | ProcAttrSpec.Pointer   -> a#set_pointer
              | ProcAttrSpec.Save      -> a#set_save
              | ProcAttrSpec.Protected -> a#set_protected
              | _ -> ()
            ) attr_specs
        end;
        begin
          match env#lookup_name ~allow_implicit:false n with
          | [] -> a#set_access_spec env#default_accessibility
          | spec::_ -> begin
              try
                a#set_access_spec (N.Spec.get_access_spec spec)
              with
                _ -> a#set_access_spec env#default_accessibility
          end
        end;
        let spec = N.Spec.mkprocedure pspec in
        node#set_info (I.mknamespec spec);
        env#register_name n spec
    end
    | _ -> parse_warning_loc node#loc "not a procedure-decl"


  let begin_program_scope()          = ignore (env#_begin_scope N.ScopingUnit.Program)
  let begin_derived_type_def_scope n = env#_begin_scope (N.ScopingUnit.DerivedTypeDef n)

  let begin_headless_main_program_scope() =
    ignore (env#_begin_scope (N.ScopingUnit.MainProgram(None, ref false)))

  let begin_main_program_scope n_opt =
    ignore (env#_begin_scope (N.ScopingUnit.MainProgram(n_opt, ref true)))

  let begin_function_subprogram_scope n =
    ignore (env#_begin_scope (N.ScopingUnit.FunctionSubprogram n))

  let begin_subroutine_subprogram_scope n =
    ignore (env#_begin_scope (N.ScopingUnit.SubroutineSubprogram n))

  let begin_separated_module_subprogram_scope n =
    ignore (env#_begin_scope (N.ScopingUnit.SeparateModuleSubprogram n))

  let begin_module_scope n         = env#_begin_scope (N.ScopingUnit.Module n)
  let begin_submodule_scope n      = env#_begin_scope (N.ScopingUnit.Module n)
  let begin_block_data_scope n_opt =
    ignore (env#_begin_scope (N.ScopingUnit.BlockData n_opt))

  let begin_block_scope n_opt =
    ignore (env#_begin_scope (N.ScopingUnit.BlockConstruct n_opt))

  let begin_structure_decl_scope n_opt = env#_begin_scope (N.ScopingUnit.StructureDecl n_opt)

  let end_scope() = env#end_scope

  let set_headed() =
    [%debug_log "current scope: %s" (N.ScopingUnit.to_string env#current_frame#scope)];
    match env#current_frame#scope with
    | N.ScopingUnit.MainProgram(_, hd) -> hd := true
    | _ -> ()

  let cancel_main_program_scope() =
    [%debug_log "current scope: %s" (N.ScopingUnit.to_string env#current_frame#scope)];
    match env#current_frame#scope with
    | N.ScopingUnit.MainProgram _ -> end_scope()
    | _ -> ()


  let normalize_label lab =
    Xstring.lstrip ~strs:["0"] lab

  let prefix_digits_pat = Str.regexp "^[0-9]+"

  let startswith_digits str = Str.string_match prefix_digits_pat str 0

  let split_data_edit_desc =
    let split s =
      let b = Str.string_match prefix_digits_pat s 0 in
      if b then begin
        let i_str = Str.matched_string s in
        try
          let i = int_of_string i_str in
          let desc = Xstring.lstrip ~strs:[" ";i_str] s in
          Some i, desc
        with
          _ -> assert false
      end
      else
        None, s
    in
    split

  let make_vfe_lab ?(i_opt=None) ?(tail="") str =
    let i_opt', s = split_data_edit_desc str in
    let i_opt'' =
      match i_opt, i_opt' with
      | None, None -> None
      | None, x_opt
      | x_opt, None -> x_opt
      | Some x, Some y ->
          try
            Some (int_of_string ((string_of_int x)^(string_of_int y)))
          with
            _ -> assert false
    in
    L.FormatItem (FormatItem.VariableFormatDesc(i_opt'', s^tail))

  let i_opt_of_r_opt = function
    | None -> None
    | Some r ->
        try
          Some (int_of_string r)
        with
          _ -> assert false





  let at_EOPU() =
    if not env#at_BOPU then begin
      [%debug_log "handling EOPU"];
      begin_headless_main_program_scope();
      context_stack#push (Context.spec__exec());
      env#set_BOPU
    end


  let lloc_of_poss pos0 pos1 =
    let loc = Astloc.of_lexposs pos0 pos1 in
    let layers = env#current_loc_layers in
    new Layeredloc.c ~layers loc


  let make_error_node start_pos end_pos =
    begin %debug_block
        [%debug_log "start_offset=%d, end_offset=%d"
           start_pos.Lexing.pos_cnum end_pos.Lexing.pos_cnum];
      let st, ed = env#get_last_active_ofss in
      [%debug_log "last_active_ofss: %d - %d" st ed];
    end;

    let lloc = lloc_of_poss start_pos end_pos in

    if not env#partial_parsing_flag && lloc#get_level = 0 then
      env#missed_regions#add lloc#get_loc;

    new Ast.node ~lloc (L.ERROR "")


  let local_name_of_rename_node (node : Ast.node) =
    match node#label with
    | L.Rename -> begin
        match node#children with
        | n::_ -> Some n#get_name
        | [] ->
            parse_warning_loc node#loc "malformed rename";
            None
    end
    | _ -> None

  let local_name_list_of_rename_nodes =
    Xlist.filter_map local_name_of_rename_node

  let name_attribute_of_aspec_nodes nodes =
    let attr = new N.Attribute.c in
    List.iter
      (fun node ->
        match node#label with
        | L.AttrSpec a -> begin
            match a with
            | AttrSpec.Parameter   -> attr#set_parameter
            | AttrSpec.Public      -> attr#set_access_spec_public
            | AttrSpec.Private     -> attr#set_access_spec_private
            | AttrSpec.Allocatable -> attr#set_allocatable
            | AttrSpec.Dimension   -> begin
                let d =
                  match node#children with
                  | [a] -> N.Dimension.of_label a#label
                  | _ ->
                      parse_warning_loc node#loc "invalid dimension";
                      N.Dimension.NoDimension
                in
                attr#set_dimension d
            end
            | AttrSpec.Codimension -> begin
                let d =
                  match node#children with
                  | [a] -> N.Codimension.of_label a#label
                  | _ ->
                      parse_warning_loc node#loc "invalid codimension";
                      N.Codimension.NoCodimension
                in
                attr#set_codimension d
            end
            | AttrSpec.External -> attr#set_external
            | AttrSpec.Intent i ->
                attr#set_intent_spec (N.IntentSpec.of_ispec_label i)

            | AttrSpec.Intrinsic -> attr#set_intrinsic
            | AttrSpec.Optional  -> attr#set_optional
            | AttrSpec.Pointer   -> attr#set_pointer
            | AttrSpec.Save      -> attr#set_save
            | AttrSpec.Target    -> attr#set_target

            | AttrSpec.Asynchronous -> attr#set_asynchronous
            | AttrSpec.Bind         -> attr#set_bind
            | AttrSpec.Protected    -> attr#set_protected
            | AttrSpec.Value        -> attr#set_value
            | AttrSpec.Volatile     -> attr#set_volatile
            | AttrSpec.Contiguous   -> attr#set_contiguous

            | AttrSpec.Automatic    -> attr#set_automatic
            | AttrSpec.Static       -> attr#set_static

            | AttrSpec.Device       -> attr#set_device
            | AttrSpec.Managed      -> attr#set_managed
            | AttrSpec.Constant     -> attr#set_constant
            | AttrSpec.Shared       -> attr#set_shared
            | AttrSpec.Pinned       -> attr#set_pinned
            | AttrSpec.Texture      -> attr#set_texture
        end
        | _ -> assert false
      ) nodes;
    attr

  let set_attr_of_data_object
      ?(type_spec=I.TypeSpec.Unknown)
      (setter : N.Attribute.c -> unit)
      name
      =
    [%debug_log "name=\"%s\"" name];
    try
      let attr =
        match env#lookup_name ~afilt:N.Spec.has_data_object_spec name with
        | [] -> begin
            [%debug_log "setting attribute of unknown data object: %s" name];
            let a = new N.Attribute.c in
            let nspec = N.Spec.mkdobj ~type_spec (Some a) in
            env#register_name name nspec;
            a
        end
        | spec::_ -> begin
            try
              N.Spec.get_data_object_attr spec
            with
              Not_found ->
                let a = new N.Attribute.c in
                (N.Spec.get_data_object_spec spec)#set_attr a;
                a
        end
      in
      setter attr;
      [%debug_log "attr --> %s" attr#to_string]
    with
      Not_found -> assert false

  let set_access_attr aspec mkdefault name =
    [%debug_log "name=\"%s\"" name];
    try
      let attr =
        let afilt = N.Spec.has_accessibility_attr in
        match env#lookup_name ~allow_implicit:false ~afilt name with
        | [] -> begin
            mkdefault()
        end
        | spec::_ -> begin
            try
              N.Spec.get_accessibility_attr spec
            with
              Not_found -> assert false
        end
      in
      attr#set_access_spec aspec;
      [%debug_log "attr: %s" attr#to_string]
    with
      Not_found -> assert false


  let set_access_spec_attr aspec node =
    match node#label with
    | L.Name name
    | L.Ambiguous (Ambiguous.Designator name) ->
        set_access_attr aspec
          (fun () ->
            let afilt = N.Spec.has_data_object_spec in
            match env#lookup_name ~allow_implicit:false ~afilt name with
            | [] -> begin
                [%debug_log "setting attribute of unknown data object: %s" name];
                let a = new N.Attribute.c in
                let nspec = N.Spec.mkdobj (Some a) in
                env#register_name name nspec;
                (a :> N.Attribute.accessibility)
            end
            | spec::_ -> begin
                try
                  (N.Spec.get_data_object_attr spec :> N.Attribute.accessibility)
                with
                  Not_found ->
                    let a = new N.Attribute.c in
                    (N.Spec.get_data_object_spec spec)#set_attr a;
                    (a :> N.Attribute.accessibility)
            end
          )
          name

    | L.Ambiguous (Ambiguous.GenericSpecOrUseName name) ->
        set_access_attr aspec
          (fun () ->
            let afilt = N.Spec.has_object_spec in
            match env#lookup_name ~allow_implicit:false ~afilt name with
            | [] -> begin
                [%debug_log "setting attribute of unknown object: %s" name];
                let a = new N.Attribute.accessibility in
                let o = new N.Spec.object_spec() in
                o#set_attr a;
                let nspec = N.Spec.mkobject o in
                env#register_name name nspec;
                a
            end
            | spec::_ -> begin
                try
                  (N.Spec.get_object_attr spec :> N.Attribute.accessibility)
                with
                  Not_found ->
                    let a = new N.Attribute.accessibility in
                    (N.Spec.get_object_spec spec)#set_attr a;
                    a
            end
          )
          name

    | L.GenericSpec (GenericSpec.Name name) ->
        set_access_attr aspec
          (fun () ->
            let nspec = N.Spec.mkobj () in
            env#register_name name (N.Spec.mkgeneric nspec);
            nspec#attr
          )
          name

    | _ -> ()


  let finalize_object_spec ?(multi_bind=false) name node =
    [%debug_log "name=\"%s\"" name];
    [%debug_log "node=%s" node#to_string];
    try
      match env#lookup_name ~allow_implicit:false ~afilt:N.Spec.has_object_spec name with
      | [] -> ()
      | specs ->
          let bid_opt = ref None in
          List.iter
            (fun spec ->
              [%debug_log "spec: %s" (N.Spec.to_string spec)];
              let first_time = !bid_opt = None in
              try
                let ospec = N.Spec.get_object_spec spec in
                [%debug_log "ospec: %s" ospec#to_string];
                let lod = N.Spec.loc_of_decl_explicit node#orig_loc in
                let iod = Oo.id node in
                ospec#set_loc_of_decl lod;
                ospec#set_id_of_decl iod;
                [%debug_log " -> %s" ospec#to_string];
                [%debug_log "ospec#bid=%a" BID.ps ospec#bid];
                let bid =
                  match !bid_opt with
                  | Some bid ->
                      if ospec#bid <> bid then begin
                        [%debug_log "%a -> %a" BID.ps ospec#bid BID.ps bid];
                        ospec#set_bid bid
                      end;
                      bid
                  | None ->
                      bid_opt := Some ospec#bid;
                      ospec#bid
                in
                if multi_bind then begin
                  if first_time then begin
                    [%debug_log "adding %a" BID.ps bid];
                    node#add_binding (B.make_unknown_def bid true);
                    node#add_info (I.mknamespec spec)
                  end
                end
                else begin
                  [%debug_log "setting %a" BID.ps bid];
                  node#set_binding (B.make_unknown_def bid true);
                  node#set_info (I.mknamespec spec)
                end
              with
                Not_found -> ()
            ) (List.rev specs)
    with
      Not_found -> assert false





  let ocl_tuple_to_n_opt_names = OclDirective.ocl_tuple_to_n_opt_names
  let ocl_tuple_to_names       = OclDirective.ocl_tuple_to_names
  let ocl_tuple_to_name        = OclDirective.ocl_tuple_to_name
  let ocl_tuple_opt_to_names   = OclDirective.ocl_tuple_opt_to_names
  let ocl_tuple_opt_to_num_opt = OclDirective.ocl_tuple_opt_to_num_opt
  let ocl_tuple_to_nn          = OclDirective.ocl_tuple_to_nn
  let ocl_tuple_to_num         = OclDirective.ocl_tuple_to_num
  let ocl_tuple_to_nums        = OclDirective.ocl_tuple_to_nums

  let mkn n =
    let name =
      if env#ignore_case then
        String.lowercase_ascii n
      else
        n
    in
    L.Name name



  let finalize_directive nd =
    match nd#children with
    | [d] ->
        d#set_lloc nd#lloc;
        d
    | _ -> nd

  let mark_EOPU ?(ending_scope=true) () =
    [%debug_log "current scope: %s" (N.ScopingUnit.to_string env#current_frame#scope)];
    if ending_scope then begin
      end_scope();
      [%debug_log "  -> %s" (N.ScopingUnit.to_string env#current_frame#scope)]
    end;
    begin
      match env#current_frame#scope with
      | N.ScopingUnit.Program -> begin
          env#exit_contains_context;
      end
      | _ -> ()
    end


  let rec is_xxx_part_construct
      (quantifier : (Ast.node -> bool) -> Ast.node list -> bool)
      label_is_xxx_part_construct
      nd
      =

    let lab = nd#label in
    let b =
      match lab with
      | L.PpSectionIf _
      | L.PpSectionIfdef _
      | L.PpSectionIfndef _
      | L.PpSectionElif _
      | L.PpSectionElse
        -> begin
          quantifier
            (fun n ->
              label_is_xxx_part_construct n#label
            ) nd#children
        end

      | L.PpBranch
      | L.PpBranchDo
      | L.PpBranchForall
      | L.PpBranchIf
      | L.PpBranchSelect
      | L.PpBranchWhere
      | L.PpBranchDerivedType

      | L.PpBranchEndDo
      | L.PpBranchEndForall
      | L.PpBranchEndIf
      | L.PpBranchEndSelect
      | L.PpBranchEndWhere
      | L.PpBranchEndType
        -> begin
          quantifier
            (is_xxx_part_construct quantifier label_is_xxx_part_construct)
            nd#children
        end

      | _ -> label_is_xxx_part_construct lab
    in
    [%debug_log "%s -> %B" (L.to_string lab) b];
    b

  let is_execution_part_construct =
    is_xxx_part_construct List.exists L.is_execution_part_construct


  let is_specification_part_construct =
    is_xxx_part_construct List.for_all L.is_specification_part_construct


  let change_top_uop_into_bop nd =
    let change_label n =
      match n#label with
      | L.IntrinsicOperator op -> begin
          match op with
          | IntrinsicOperator.Id  ->
              n#relab (L.IntrinsicOperator IntrinsicOperator.Add)
          | IntrinsicOperator.Neg ->
              n#relab (L.IntrinsicOperator IntrinsicOperator.Subt)
          | _ -> ()
      end
      | _ -> ()
    in
    let change_section n =
      match n#label with
      | L.PpSectionIf _
      | L.PpSectionIfdef _
      | L.PpSectionIfndef _
      | L.PpSectionElif _
      | L.PpSectionElse -> begin
          List.iter change_label n#children
      end
      | _ -> ()
    in
    match nd#label with
    | L.PpBranch -> begin
        List.iter change_section nd#children
    end
    | _ -> change_section nd


  let ty_of_node node =
    [%debug_log "%s" node#to_string];
    let lab = node#label in
    try
      I.TypeSpec.of_label lab
    with
      Failure _ ->
        let tys = Xset.create 0 in
        match lab with
        | L.PpBranch
        | L.PpSectionIf _
        | L.PpSectionIfdef _
        | L.PpSectionIfndef _
        | L.PpSectionElif _
        | L.PpSectionElse -> begin
            Ast.visit
              (fun nd ->
                match nd#label with
                | L.TypeSpec _ -> Xset.add tys (I.TypeSpec.of_label nd#label)
                | _ -> ()
              ) node;
            I.TypeSpec.PpBranchTypeSpec (Xset.to_list tys)
        end

        | _ -> failwith "Parser_aux.F.ty_of_node"


  let node_to_loc nd =
    nd#lloc#to_loc ?cache:(Some (Some env#fname_ext_cache)) ()

  let node_to_lexposs nd =
    Loc.to_lexposs (node_to_loc nd)

end (* of functor Parser_aux.F *)
]
