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
(* parser_aux.ml *)

[%%prepare_logger]

module Fname = Langs_common.Fname
module Env_base = Langs_common.Env_base

open Printf
open Common
open Ast


module L = Label


type vartype = VTdefault | VTtype


type memtbl = (identifier, identifier_attribute) Hashtbl.t

and identifier_attribute =
  | IAclass of memtbl ref
  | IAcovergroup
  | IApackage
  | IAtype
  | IAproperty
  | IAclocking
  | IAextern_method
  | IAinterface

let iattr_to_str = function
  | IAclass _       -> "IAclass"
  | IAcovergroup    -> "IAcovergroup"
  | IApackage       -> "IApackage"
  | IAtype          -> "IAtype"
  | IAproperty      -> "IAproperty"
  | IAclocking      -> "IAclocking"
  | IAextern_method -> "IAextern_method"
  | IAinterface     -> "IAinterface"

exception Attrs_found of identifier_attribute list

type scope_attribute =
  | SApackage of identifier
  | SAclass of identifier
  | SAfunction of identifier
  | SAother

let sattr_to_str = function
  | SApackage id  -> "SApackage:"^id
  | SAclass id    -> "SAclass:"^id
  | SAfunction id -> "SAfunction:"^id
  | SAother       -> "SAother"

type frame = {
    f_attr : scope_attribute;
    f_tbl  : (identifier, identifier_attribute) Hashtbl.t;
  }

let create_frame sattr = {
  f_attr = sattr;
  f_tbl  = Hashtbl.create 0;
}

let copy_frame frm = {
  f_attr = frm.f_attr;
  f_tbl  = Hashtbl.copy frm.f_tbl;
}


let dummy_tbl = Hashtbl.create 0


let builtin_packages =
  [ "std",
    [ "semaphore", IAclass (ref (Hashtbl.create 0));
      "mailbox",   IAclass (ref (Hashtbl.create 0));
      "process",   IAclass (ref (Hashtbl.create 0));
    ]
  ]



let base_symbol_tbl = Hashtbl.create 0
let _ =
  List.iter
    (fun (pkg, pmems) ->
      let frm = create_frame (SApackage pkg) in
      List.iter
	(fun (id, attr) ->
	  Hashtbl.add frm.f_tbl id attr
	) pmems;
      Hashtbl.add base_symbol_tbl pkg frm
    ) builtin_packages



exception Frame_found of frame

type state =
    { s_symbol_tbl  : (identifier, frame) Hashtbl.t;
      s_stack       : frame Stack.t;
      s_scoped_flag : bool;
      s_pvstate     : int;
      s_vartype     : vartype;
      s_in_table    : bool;
    }

let mkstate stbl stack sco pvs vt in_t =
  { s_symbol_tbl  = stbl;
    s_stack       = stack;
    s_scoped_flag = sco;
    s_pvstate     = pvs;
    s_vartype     = vt;
    s_in_table    = in_t;
  }

let top_key = Loc.dummy



[%%capture_path
class env = object (self)
  inherit [Source.c] Env_base.c as super

  val mutable ignore_include_flag = false

  val mutable context_enter_flag = false
  val mutable context_activate_flag = false
  val mutable last_active_ofss = (0, 0)
  val mutable partial_parsing_flag = false

  val fname_ext_cache = (Hashtbl.create 0 : Fname.ext_cache_t)
  method fname_ext_cache = fname_ext_cache


(* put in saved states *)
  val mutable symbol_tbl = Hashtbl.create 0
  val mutable stack = Stack.create()

  val mutable scoped_flag        = false
  val mutable pvstate            = 0
  val mutable vartype            = VTdefault
  val mutable in_table           = false

  val checkpoint_tbl = Hashtbl.create 0 (* Loc.t -> state *)

  (*val mutable macrotbl = None*)

  val loc_stack = new Layeredloc.loc_stack



(* methods *)

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
    macrotbl#define ~conditional ("`"^id) body

  method undefine_macro id =
    [%debug_log "%s" id];
    macrotbl#undefine ("`"^id)

  method find_macro id =
    try
      macrotbl#find id
    with
      Not_found ->
        match predefined_macrotbl with
        | Some tbl -> tbl#find id
        | None -> raise Not_found

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
    lex_macrotbl#define ("`"^id) body

  method lex_undefine_macro id =
    [%debug_log "%s" id];
    lex_macrotbl#undefine ("`"^id)

  method lex_find_macro id =
    try
      lex_macrotbl#find id
    with
      Not_found ->
        match predefined_macrotbl with
        | Some tbl -> tbl#find id
        | None -> raise Not_found


  method ignore_include_flag = ignore_include_flag
  method set_ignore_include_flag = ignore_include_flag <- true
  method clear_ignore_include_flag = ignore_include_flag <- false

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


  method checkpoint (key : Loc.t) =
    [%debug_log "key=%s" (Loc.to_string key)];

    let stat =
      mkstate (Hashtbl.copy symbol_tbl) (self#_copy_stack stack)
	scoped_flag pvstate vartype in_table
    in
(*
    if Hashtbl.mem checkpoint_tbl key then
      [%warn_log "already checkpointed: key=%s" (Loc.to_string key)];
*)
    Hashtbl.replace checkpoint_tbl key stat;


  method recover ?(remove=false) key =
    [%debug_log "key=%s" (Loc.to_string key)];
    try
      let stat = Hashtbl.find checkpoint_tbl key in
      symbol_tbl         <- Hashtbl.copy stat.s_symbol_tbl;
      stack              <- self#_copy_stack stat.s_stack;
      scoped_flag        <- stat.s_scoped_flag;
      pvstate            <- stat.s_pvstate;
      vartype            <- stat.s_vartype;
      in_table           <- stat.s_in_table;

      if remove then
        Hashtbl.remove checkpoint_tbl key
    with
      Not_found ->
	[%fatal_log "state not found: key=%s" (Loc.to_string key)]; exit 1

  method scoped_flag = scoped_flag
  method set_scoped_flag = scoped_flag <- true
  method clear_scoped_flag = scoped_flag <- false

  method pvstate = pvstate
  method set_pvstate i = pvstate <- i

  method vartype = vartype
  method set_vartype_type = vartype <- VTtype
  method reset_vartype = vartype <- VTdefault

  method in_table = in_table
  method begin_table = in_table <- true
  method end_table = in_table <- false

  method find_symbol id =
    try
      Hashtbl.find symbol_tbl id
    with
      Not_found -> Hashtbl.find base_symbol_tbl id

  method current_frame =
    try
      Stack.top stack
    with
      Stack.Empty -> raise (Internal_error "Parser_aux.get_current_frame: stack empty")

  method private _copy_stack s =
    let copy = Stack.create() in
    let fs = ref [] in
    Stack.iter (fun f -> fs := (copy_frame f) :: !fs) s;
    List.iter (fun f -> Stack.push f copy) !fs;
    copy

  method register_identifier (id : string) attr =
    [%debug_log "REG(%d): \"%s\" -> %s" (Stack.length stack) id (iattr_to_str attr)];
    Hashtbl.add (self#current_frame).f_tbl id attr

  method lookup_identifier ?(afilt=(fun _ -> true)) (id : string) =
    begin %debug_block
      [%debug_log "LKUP(%d): \"%s\"" (Stack.length stack) id];
      Stack.iter
	(fun frame ->
	  [%debug_log "FRM: <%s>[%s]"
	    (sattr_to_str frame.f_attr)
	    (Hashtbl.fold (fun id _ s -> id^";"^s) frame.f_tbl "")];
	) stack;
    end;
    try
      Stack.iter
	(fun frame ->
	  try
	    let attrs = Hashtbl.find_all frame.f_tbl id in
	    let filtered = List.filter afilt attrs in
	    if filtered <> [] then
	      raise (Attrs_found filtered)
	  with
	    Not_found -> ()
	) stack;
      raise Not_found
    with
      Attrs_found attrs ->
	if attrs = [] then
	  raise Not_found
	else
	  attrs

  method _begin_scope sattr =
    [%debug_log "PUSH(%d): FRM: <%s>" (Stack.length stack) (sattr_to_str sattr)];
    Stack.push (create_frame sattr) stack

  method end_scope =
    try
      let frm = (Stack.pop stack) in

      [%debug_log "POP(%d): FRM: <%s>" (Stack.length stack) (sattr_to_str frm.f_attr)];

      match frm.f_attr with
      | SApackage id -> Hashtbl.add symbol_tbl id frm
      | SAclass id -> begin
	  try
	    let a = self#lookup_identifier id in
	    match a with
	    | (IAclass tblr)::_ -> tblr := frm.f_tbl
	    | _ -> assert false
	  with
	    Not_found -> assert false (* toplevel *)
      end
      | _ -> ()
    with
      Stack.Empty -> raise (Internal_error "Parser_aux.end_scope: stack empty")


  method import_one pkg id =
    [%debug_log "IMPORT: %s::%s" pkg id];
    try
      let frm = self#find_symbol pkg in
      try
	self#register_identifier id (Hashtbl.find frm.f_tbl id)
      with
	Not_found -> [%warn_log "id \"%s\" not found in package \"%s\"" id pkg]
    with
      Not_found -> [%warn_log "package \"%s\" not found" pkg]

  method _import_any tbl =
    Hashtbl.iter (fun id attr -> self#register_identifier id attr) tbl

  method import_any pkg =
    [%debug_log "IMPORT_ANY: %s" pkg];
    try
      let frm = self#find_symbol pkg in
      self#_import_any frm.f_tbl
    with
      Not_found -> [%warn_log "package \"%s\" not found" pkg]


  method find_frame_for id =
    try
      Stack.iter
	(fun frame ->
	  try
	    if Hashtbl.mem frame.f_tbl id then
	      raise (Frame_found frame)
	  with
	    Not_found -> ()
	) stack;
      raise Not_found
    with
      Frame_found frm -> frm


  method! init =
    super#init;
    Hashtbl.clear symbol_tbl;
    Stack.clear stack;
    Hashtbl.clear fname_ext_cache;
    scoped_flag <- false;
    in_table    <- false;

    context_enter_flag    <- false;
    context_activate_flag <- false;
    last_active_ofss      <- (0, 0);
    partial_parsing_flag  <- false;

end (* of class env *)
]

module type STATE_T = sig
  val env           : env
  val context_stack : Context.stack
end


[%%capture_path
module F (Stat : STATE_T) = struct

  open Stat

  let lexing_pos_start = Langs_common.Position.lexing_pos_start
  let lexing_pos_end = Langs_common.Position.lexing_pos_end

  let parse_warning = PB.parse_warning

  let parse_error spos epos : ('a, unit, string, 'b) format4 -> 'a =
    PB.parse_error env
      (fun loc -> new Ast.node ~lloc:(env#mklloc loc) L.Error)
      spos epos

  let parse_error_loc loc : ('a, unit, string, 'b) format4 -> 'a =
    PB.parse_error_loc env
      (fun loc -> new Ast.node ~lloc:(env#mklloc loc) L.Error)
      loc

  let parse_failure_loc loc msg =
    let head = sprintf "[%s]" (Loc.to_string loc) in
    fail_to_parse ~head msg


  let get_loc_for_lex lexbuf =
    let start_pos = lexing_pos_start lexbuf in
    let end_pos = lexing_pos_end lexbuf in
    let loc = Loc.of_lexposs start_pos end_pos in
    loc


  let check_error node =
    if not env#partial_parsing_flag then begin
      Ast.visit
	(fun nd ->
	  if L.is_error nd#label then
	    env#missed_regions#add nd#loc
	) node
    end

  let lloc_of_poss pos0 pos1 =
    let loc = Loc.of_lexposs pos0 pos1 in
    let layers = env#current_loc_layers in
    new Layeredloc.c ~layers loc

  let make_error_node start_pos end_pos =
    begin %debug_block
      [%debug_log "start_offset=%d, end_offset=%d"
         start_pos.Lexing.pos_cnum end_pos.Lexing.pos_cnum];
      let st, ed = env#get_last_active_ofss in
      [%debug_log "last_active_ofss: %d - %d" st ed]
    end;

    let lloc = lloc_of_poss start_pos end_pos in

    if not env#partial_parsing_flag && lloc#get_level = 0 then
      env#missed_regions#add lloc#get_loc;

    new node ~lloc L.Error


  let register_vartype ident =
    match env#vartype with
    | VTtype -> env#register_identifier ident IAtype
    | _ -> ()

  let register_class ident =
    env#register_identifier ident (IAclass (ref dummy_tbl))

  let register_type ident =
    env#register_identifier ident IAtype

  let register_package ident =
    env#register_identifier ident IApackage

  let register_property ident =
    env#register_identifier ident IAproperty

  let register_covergroup ident =
    env#register_identifier ident IAcovergroup

  let register_clocking ident =
    env#register_identifier ident IAclocking

  let register_extern_method ident =
    env#register_identifier ident IAextern_method

  let register_interface ident =
    env#register_identifier ident IAinterface

  let begin_package_scope id = env#_begin_scope (SApackage id)
  let begin_class_scope id = env#_begin_scope (SAclass id)
  let begin_function_scope id = env#_begin_scope (SAfunction id)
  let begin_scope() = env#_begin_scope SAother
  let end_scope() = env#end_scope

  let import_one pkg id = env#import_one pkg id
  let import_any pkg = env#import_any pkg

  let lookup_identifier id = env#lookup_identifier id

  let set_vartype_type() = env#set_vartype_type
  let reset_vartype() = env#reset_vartype

  let import_pkg_cls_scope (pkg_opt, cty_list) =

    [%debug_log "pkg=%s, cty_list=[%s]"
      (match pkg_opt with None -> "<none>" | Some id -> id)
      (String.concat ";" cty_list)];

    if cty_list = [] then
      ()
    else begin
      let get_tbl ini_tbl =
	List.fold_left
	  (fun tbl cty ->
	    let a = Hashtbl.find tbl cty in
	    match a with
	    | IAclass tblr -> !tblr
	    | _ -> assert false
	  ) ini_tbl cty_list
      in
      let frm =
	match pkg_opt with
	| Some pkg -> env#find_symbol pkg
	| None     ->
	    match cty_list with
	    | cty::_ -> env#find_frame_for cty
	    | _ -> assert false
      in
      let tbl = get_tbl frm.f_tbl in
      env#_import_any tbl
    end

  let node_to_loc nd =
    nd#lloc#to_loc ?cache:(Some (Some env#fname_ext_cache)) ()

  let node_to_lexposs nd =
    Loc.to_lexposs (node_to_loc nd)

end (* of functor Parser_aux.F *)
]
