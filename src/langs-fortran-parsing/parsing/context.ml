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

(* context.ml *)

[%%prepare_logger]

module Loc = Langs_common.Astloc
module PB = Langs_common.Parserlib_base

type tag =
  | Tunknown
  | Ttoplevel
  | Tprogram_unit
  | Tspec__exec
  | Tspecification_part
  | Texecution_part
  | Tsubprograms
  | Tinterface_spec
  | Tcase_block

  | Tassignment_stmt
  | Ttype_declaration_stmt
  | Tfunction_stmt
  | Tvariable
  | Texpr
  | Tstmts
  | Tdata_stmt_sets
  | Ttype_spec
  | Taction_stmt

  | Tderived_type_def_part

  | Tonlys

  | Ttype_bound_proc_part

  | Tfunction_head
  | Tfunction_stmt_head
  | Tsubroutine_head
  | Tsubroutine_stmt_head

  | Tpu_tail

  | Tin_stmt


let tag_to_string = function
  | Tunknown               -> "unknown"
  | Ttoplevel              -> "toplevel"
  | Tprogram_unit          -> "program_unit"
  | Tspec__exec            -> "spec__exec"
  | Tspecification_part    -> "specification_part"
  | Texecution_part        -> "execution_part"
  | Tsubprograms           -> "subprograms"
  | Tinterface_spec        -> "interface_spec"
  | Tcase_block            -> "case_block"

  | Tassignment_stmt       -> "assignment_stmt"
  | Ttype_declaration_stmt -> "type_declaration_stmt"
  | Tfunction_stmt         -> "function_stmt"
  | Tvariable              -> "variable"
  | Texpr                  -> "expr"
  | Tstmts                 -> "stmts"
  | Tdata_stmt_sets        -> "data_stmt_sets"
  | Ttype_spec             -> "type_spec"
  | Taction_stmt           -> "action_stmt"

  | Tderived_type_def_part -> "derived_type_def_part"

  | Tonlys                 -> "onlys"

  | Ttype_bound_proc_part  -> "type_bound_procedure_part"

  | Tfunction_head         -> "function_head"
  | Tfunction_stmt_head    -> "function_stmt_head"
  | Tsubroutine_head       -> "subroutine_head"
  | Tsubroutine_stmt_head  -> "subroutine_stmt_head"

  | Tpu_tail               -> "pu_tail"

  | Tin_stmt               -> "in_stmt"


type t = { mutable tag       : tag;
	   mutable is_active : bool;
	 }

let mk t b = { tag=t; is_active=b; }

let copy_context c = { tag = c.tag; is_active = c.is_active }

let deactivate_context c = c.is_active <- false

let resolve_into_spec c = c.tag <- Tspecification_part
let resolve_into_exec c = c.tag <- Texecution_part

let to_string { tag=tag; is_active=is_active } =
  Printf.sprintf "%s[%sACTIVE]" (tag_to_string tag) (if is_active then "" else "IN")

let unknown()            = mk Tunknown false
let toplevel()           = mk Ttoplevel true
let program_unit()       = mk Tprogram_unit true
let spec__exec()         = mk Tspec__exec true
let specification_part() = mk Tspecification_part true
let execution_part()     = mk Texecution_part true
let subprograms()        = mk Tsubprograms true
let interface_spec()     = mk Tinterface_spec true
let case_block()         = mk Tcase_block true

let assignment_stmt()       = mk Tassignment_stmt true
let type_declaration_stmt() = mk Ttype_declaration_stmt true
let function_stmt()         = mk Tfunction_stmt true
let variable()              = mk Tvariable true
let expr()                  = mk Texpr true
let stmts()                 = mk Tstmts true
let data_stmt_sets()        = mk Tdata_stmt_sets true
let type_spec()             = mk Ttype_spec true
let action_stmt()           = mk Taction_stmt true
let derived_type_def_part() = mk Tderived_type_def_part true
let onlys()                 = mk Tonlys true
let type_bound_proc_part()  = mk Ttype_bound_proc_part true

let function_head()         = mk Tfunction_head true
let function_stmt_head()    = mk Tfunction_stmt_head true
let subroutine_head()       = mk Tsubroutine_head true
let subroutine_stmt_head()  = mk Tsubroutine_stmt_head true
let pu_tail()               = mk Tpu_tail true

let in_stmt()               = mk Tin_stmt true

let get_tag { tag=tag; is_active=_; } = tag
let is_active { tag=_; is_active=b; } = b

let set_tag c tag = c.tag <- tag

let is_unknown c            = c.tag = Tunknown
let is_toplevel c           = c.tag = Ttoplevel
let is_program_unit c       = c.tag = Tprogram_unit
let is_spec__exec c         = c.tag = Tspec__exec
let is_specification_part c = c.tag = Tspecification_part
let is_execution_part c     = c.tag = Texecution_part
let is_subprograms c        = c.tag = Tsubprograms
let is_interface_spec c     = c.tag = Tinterface_spec
let is_case_block c         = c.tag = Tcase_block

let is_assignment_stmt c       = c.tag = Tassignment_stmt
let is_type_declaration_stmt c = c.tag = Ttype_declaration_stmt
let is_function_stmt c         = c.tag = Tfunction_stmt
let is_variable c              = c.tag = Tvariable
let is_expr c                  = c.tag = Texpr
let is_stmts c                 = c.tag = Tstmts
let is_data_stmt_sets c        = c.tag = Tdata_stmt_sets
let is_type_spec c             = c.tag = Ttype_spec
let is_action_stmt c           = c.tag = Taction_stmt
let is_derived_type_def_part c = c.tag = Tderived_type_def_part
let is_onlys c                 = c.tag = Tonlys
let is_type_bound_proc_part c  = c.tag = Ttype_bound_proc_part

let is_function_head c         = c.tag = Tfunction_head
let is_function_stmt_head c    = c.tag = Tfunction_stmt_head
let is_subroutine_head c       = c.tag = Tsubroutine_head
let is_subroutine_stmt_head c  = c.tag = Tsubroutine_stmt_head
let is_pu_tail c               = c.tag = Tpu_tail

let is_in_stmt c               = c.tag = Tin_stmt

let dummy = unknown()

exception Not_active


type key_t = {
    k_level : int;
    k_loc   : Loc.t;
  }

let mkkey lv loc =
  let loc' = Loc.get_stripped loc in
  { k_level=lv; k_loc=loc'; }

let key_to_string { k_level=lv; k_loc=loc; } =
  let loc_str =
    if loc = Loc.dummy then
      if lv < 0 then
        "TEMP"
      else
        "TOP"
    else
      Loc.to_string loc
  in
  Printf.sprintf "<%d:%s>" lv loc_str

let mktopkey lv = mkkey lv Loc.dummy

let tempkey = mkkey (-1) Loc.dummy


[%%capture_path
class stack env = object (self)
  val checkpoint_tbl = Hashtbl.create 0 (* key_t -> t Stack.t *)

  val mutable stack : t Stack.t = Stack.create()
  val mutable suspended = false

  val push_callback_stack       : (t -> unit) Stack.t = Stack.create()
  val pop_callback_stack        : (t -> unit) Stack.t = Stack.create()
  val activate_callback_stack   : (t -> unit) Stack.t = Stack.create()
  val deactivate_callback_stack : (t -> unit) Stack.t = Stack.create()


  method size = Stack.length stack

  method register_push_callback f       = Stack.push f push_callback_stack
  method register_pop_callback f        = Stack.push f pop_callback_stack
  method register_activate_callback f   = Stack.push f activate_callback_stack
  method register_deactivate_callback f = Stack.push f deactivate_callback_stack

  method unregister_push_callback       = (begin ignore (Stack.pop push_callback_stack) end)[@warning "-5"]
  method unregister_pop_callback        = (begin ignore (Stack.pop pop_callback_stack) end)[@warning "-5"]
  method unregister_activate_callback   = (begin ignore (Stack.pop activate_callback_stack) end)[@warning "-5"]
  method unregister_deactivate_callback = (begin ignore (Stack.pop deactivate_callback_stack) end)[@warning "-5"]

  method clear = Stack.clear stack

  method top = Stack.top stack

  method private call_callbacks stk c =
    Stack.iter (fun f -> f c) stk

  method push_callback c       = self#call_callbacks push_callback_stack c
  method pop_callback c        = self#call_callbacks pop_callback_stack c
  method activate_callback c   = self#call_callbacks activate_callback_stack c
  method deactivate_callback c = self#call_callbacks deactivate_callback_stack c


  method suspended = suspended

  method suspend =
    [%debug_log "called"];
    suspended <- true;

  method resume =
    [%debug_log "called"];
    suspended <- false;

(*
  method _force_pop n stack =
  for i = 1 to n do
  ignore (Stack.pop stack)
  done
 *)

  method checkpoint (key : key_t) =
    [%debug_log "key=%s\n%s" (key_to_string key) self#to_string];
(*
  if Hashtbl.mem checkpoint_tbl key then
  [%debug_log "already checkpointed: key=%s" (key_to_string key)];
 *)
    let copy = self#_copy_stack stack in
    Hashtbl.replace checkpoint_tbl key copy


  method recover ?(remove=false) key =
    [%debug_log "key=%s\nBEFORE:\n%s" (key_to_string key) self#to_string];
    try
      stack <- self#_copy_stack (Hashtbl.find checkpoint_tbl key);
      if remove then
        Hashtbl.remove checkpoint_tbl key;
      [%debug_log "AFTER:\n%s" self#to_string];
    with
      Not_found ->
        [%fatal_log "stack not found: key=%s" (key_to_string key)];
        raise (Common.Internal_error "Context.stack#recover")


  method _copy_stack s =
    let copy = Stack.create() in
    let cs = ref [] in
    Stack.iter
      (fun c ->
	cs := (copy_context c) :: !cs
      ) s;
    List.iter
      (fun c ->
	Stack.push c copy
      ) !cs;
    copy


  method to_string =
    let buf = Buffer.create 0 in
    Stack.iter
      (fun c ->
        Buffer.add_string buf (Printf.sprintf "%s\n" (to_string c))
      ) stack;
    Buffer.contents buf


  method push c =
    [%debug_log "pushing %s" (to_string c)];
    [%debug_log "stack:\n%s" self#to_string];

    if suspended then
      [%debug_log "suspended"]

    else begin
      Stack.push c stack;
      self#push_callback c
    end;

    env#set_context_enter_flag;

    ()


  method pop =
    [%debug_log "stack:\n%s" self#to_string];

    if suspended then
      [%debug_log "suspended"]

    else begin
      ignore (Stack.pop stack);

      let new_top =
	try
	  Stack.top stack
	with
          Stack.Empty -> assert false
      in
      [%debug_log "(new top: %s)" (to_string new_top)];

      self#pop_callback new_top
    end



  method activate_top =
    [%debug_log "suspended=%B" suspended];
    if not suspended then begin
      let c = self#top in

      if not c.is_active then
	[%debug_log "%s" (to_string c)];

      c.is_active <- true
    end;
    env#set_context_activate_flag;
    ()

  method activate_top_no_delay =
    [%debug_log "suspended=%B" suspended];
    if not suspended then begin
      let c = self#top in

      if not c.is_active then
	[%debug_log "%s" (to_string c)];

      c.is_active <- true;
      self#activate_callback c
    end

  method deactivate_top =
    [%debug_log "suspended=%B" suspended];
    if not suspended then begin
      let c = self#top in

      if c.is_active then
	[%debug_log "%s" (to_string c)];

      c.is_active <- false
    end

  method deactivate_top_no_delay =
    [%debug_log "suspended=%B" suspended];
    if not suspended then begin
      let c = self#top in

      if c.is_active then
	[%debug_log "%s" (to_string c)];

      c.is_active <- false;
      self#deactivate_callback c
    end

  method top_is_active =
    let c = self#top in
    c.is_active

  method top_is_unknown =
    let c = self#top in
    is_unknown c

  method reset =
    self#clear;
    Hashtbl.clear checkpoint_tbl;
    self#push (toplevel());
    self#push (program_unit())



  initializer
    self#reset

end (* of class Context.stack *)
]
