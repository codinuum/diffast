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

(*
 * AST for Fortran
 *
 * ast.ml
 *
 *)

[%%prepare_logger]

module Binding = Diffast_misc.Binding
module Layeredloc = Langs_common.Layeredloc
module Astloc = Langs_common.Astloc
module Ast_base = Langs_common.Ast_base

open Printf
open Common
open Labels

module Loc = Astloc
module LLoc = Layeredloc
module I = Pinfo
module B = Binding
module BID = Binding.ID
module L = Label
module C = Context

type name = Label_common.name


class node
    ?(lloc=LLoc.dummy)
    ?(children=[])
    ?(info=I.NoInfo)
    lab
    =
  object (self : 'self)
    val mutable lloc = lloc
    val mutable label = (lab : L.t)
    val mutable children = (children : 'self list)
    val mutable info = info
    val mutable binding = B.NoBinding
    val mutable bindings = []

    method binding = binding
    method set_binding b = binding <- b
    method bindings = bindings
    method add_binding b =
      if not (List.mem b bindings) then
        bindings <- b :: bindings

    method label = label
    method lloc = lloc
    method loc = lloc#get_loc
    method orig_loc = lloc#get_orig_loc
    method children = children
    method info = info

    method set_info i = info <- i

    method add_info i =
      match info with
      | I.NoInfo -> info <- i
      | _ -> info <- I.merge info i

    method children_labels =
      List.map (fun n -> n, n#label) children

    method nchildren = List.length children

    method set_lloc l = lloc <- l
    method set_children c = children <- c

    method relab lab = label <- lab

    method add_children_l c = children <- c @ children

    method add_children_r c = children <- children @ c

    method remove_rightmost_child =
      match children with
      | [] -> ()
      | [_] -> children <- []
      | _ ->
          match (List.rev children) with
          | _ :: t -> children <- (List.rev t)
          | _ -> assert false

    method remove_leftmost_child =
      match (List.rev children) with
      | [] -> ()
      | [_] -> children <- []
      | _ :: t -> children <- t

    method to_string =
      sprintf "<%s>%s%s%s%s"
        (L.to_string label)
        (lloc#to_string ?short:(Some true) ())
        (match info with
        | I.NoInfo -> ""
        | _ -> sprintf ": <<%s>>" (I.to_string info)
        )
        (match binding with
        | B.NoBinding -> ""
        | _ -> sprintf ": %a" BID.ps (B.get_bid binding)
        )
        (
         match bindings with
         | [] -> ""
         | _ ->
             sprintf ": %s"
               (String.concat ";"
                  (List.map (fun b -> sprintf "%a" BID.ps (B.get_bid b)) bindings))
        )

    method to_tag = L.to_tag label

    method get_name = L.get_name label

    method has_name = try let _ = self#get_name in true with _ -> false

    method get_name_opt = L.get_name_opt label

    method get_names = L.get_names label

    method get_label = L.get_label label

    method get_var = L.get_var label

    method get_var_opt = L.get_var_opt label

    method relab_stmt lab =
      label <- L.relabstmt label lab


end (* of class Ast.node *)


let node_opt_to_name_opt = function
  | Some nd -> Some nd#get_name
  | None -> None

let node_list_to_name_list nds = Xlist.filter_map (fun n -> n#get_name_opt) nds


let dummy_node = new node L.DUMMY

let is_dummy_node nd = nd#label = L.DUMMY

let empty_node = new node L.EMPTY

let lloc_of_locs loc0 loc1 =
  let lloc0 = LLoc.of_loc loc0 in
  let lloc1 = LLoc.of_loc loc1 in
  LLoc.merge lloc0 lloc1

let lloc_of_lexposs pos0 pos1 =
  let loc0 = Loc.of_lexpos pos0 in
  let loc1 = Loc.of_lexpos pos1 in
  lloc_of_locs loc0 loc1


[%%capture_path
let mknode (*env*)_ start_pos end_pos ?(info=I.NoInfo) label children =
  [%debug_log "%s" (L.to_string label)];
  let lloc = lloc_of_lexposs start_pos end_pos in
  new node ~lloc ~children ~info label
]

let mkleaf env start_pos end_pos ?(info=I.NoInfo) label =
  mknode env start_pos end_pos ~info label []

[%%capture_path
let reloc (*env*)_ start_pos end_pos node =
  let lloc = lloc_of_lexposs start_pos end_pos in
  [%debug_log "relocating %s: %s -> %s"
    (L.to_string node#label)
    (node#lloc#to_string ?short:(Some true) ()) (lloc#to_string ?short:(Some true) ())];
  node#set_lloc lloc
]

let mkstmtnode env start_pos end_pos ?(info=I.NoInfo) lab children =
  let lloc = lloc_of_lexposs start_pos end_pos in
  let label =
    try
      let (slab, _) =
        let loc = lloc#get_loc in
        env#find_label (loc.Loc.filename, loc.Loc.start_line)
      in
      L.mklabeledstmt slab lab
    with
      Not_found -> L.mkstmt lab
  in
  let nd = new node ~lloc ~children ~info label in
  (*env#add_latest_stmt_node nd;*)
  nd

let mkstmtleaf env start_pos end_pos ?(info=I.NoInfo) lab =
  mkstmtnode env start_pos end_pos ~info lab []


module Partial = struct

  type spec = { mutable length : int;
                mutable tag    : C.tag;
              }

  let spec_to_string s = sprintf "length=%d tag=%s" s.length (C.tag_to_string s.tag)

  let length_of_spec s = s.length

  let tag_of_spec s = s.tag

  let mkspec ?(length=0) ?(tag=C.Tunknown) () = { length=length; tag=tag; }

  type t =
    | Dummy               of spec * node list
    | Program             of spec * node list
    | ProgramUnit         of spec * node
    | Spec_Exec           of spec * node option * node option
    | SpecificationPart   of spec * node list
    | ExecutionPart       of spec * node list
    | Subprograms         of spec * node list
    | InterfaceSpec       of spec * node list
    | CaseBlock           of spec * node list
    | AssignmentStmt      of spec * node
    | TypeDeclarationStmt of spec * node
    | FunctionStmt        of spec * node
    | Variable            of spec * node
    | Expr                of spec * node
    | Stmts               of spec * node list
    | DataStmtSets        of spec * node list
    | TypeSpec            of spec * node
    | ActionStmt          of spec * node
    | DerivedTypeDefPart  of spec * node list
    | Onlys               of spec * node list
    | TypeBoundProcPart   of spec * node list
    | FunctionHead        of spec * node list
    | SubroutineHead      of spec * node list
    | SubroutineStmtHead  of spec * node
    | FunctionStmtHead    of spec * node
    | PuTail              of spec * node list

  let to_string = function
    | Dummy(spec, _)               -> sprintf "Dummy(%s)" (spec_to_string spec)
    | Program(spec, _)             -> sprintf "Program(%s)" (spec_to_string spec)
    | ProgramUnit(spec, _)         -> sprintf "ProgramUnit(%s)" (spec_to_string spec)
    | Spec_Exec(spec, _, _)        -> sprintf "Spec_Exec(%s)" (spec_to_string spec)
    | SpecificationPart(spec, _)   -> sprintf "SpecificationPart(%s)" (spec_to_string spec)
    | ExecutionPart(spec, _)       -> sprintf "ExecutionPart(%s)" (spec_to_string spec)
    | Subprograms(spec, _)         -> sprintf "Subprograms(%s)" (spec_to_string spec)
    | InterfaceSpec(spec, _)       -> sprintf "InterfaceSpec(%s)" (spec_to_string spec)
    | CaseBlock(spec, _)           -> sprintf "CaseBlock(%s)" (spec_to_string spec)
    | AssignmentStmt(spec, _)      -> sprintf "AssignmentStmt(%s)" (spec_to_string spec)
    | TypeDeclarationStmt(spec, _) -> sprintf "TypeDeclarationStmt(%s)" (spec_to_string spec)
    | FunctionStmt(spec, _)        -> sprintf "FunctionStmt(%s)" (spec_to_string spec)
    | Variable(spec, _)            -> sprintf "Variable(%s)" (spec_to_string spec)
    | Expr(spec, _)                -> sprintf "Expr(%s)" (spec_to_string spec)
    | Stmts(spec, _)               -> sprintf "Stmts(%s)" (spec_to_string spec)
    | DataStmtSets(spec, _)        -> sprintf "DataStmtSets(%s)" (spec_to_string spec)
    | TypeSpec(spec, _)            -> sprintf "TypeSpec(%s)" (spec_to_string spec)
    | ActionStmt(spec, _)          -> sprintf "ActionStmt(%s)" (spec_to_string spec)
    | DerivedTypeDefPart(spec, _)  -> sprintf "DerivedTypeDefPart(%s)" (spec_to_string spec)
    | Onlys(spec, _)               -> sprintf "Onlys(%s)" (spec_to_string spec)
    | TypeBoundProcPart(spec, _)   -> sprintf "TypeBoundProcPart(%s)" (spec_to_string spec)
    | FunctionHead(spec, _)        -> sprintf "FunctionHead(%s)" (spec_to_string spec)
    | FunctionStmtHead(spec, _)    -> sprintf "FunctionStmtHead(%s)" (spec_to_string spec)
    | SubroutineHead(spec, _)      -> sprintf "SubroutineHead(%s)" (spec_to_string spec)
    | SubroutineStmtHead(spec, _)  -> sprintf "SubroutineStmtHead(%s)" (spec_to_string spec)
    | PuTail(spec, _)              -> sprintf "PuTail(%s)" (spec_to_string spec)

  let get_spec = function
    | Dummy(spec, _)
    | Program(spec, _)
    | ProgramUnit(spec, _)
    | Spec_Exec(spec, _, _)
    | SpecificationPart(spec, _)
    | ExecutionPart(spec, _)
    | Subprograms(spec, _)
    | InterfaceSpec(spec, _)
    | CaseBlock(spec, _)
    | AssignmentStmt(spec, _)
    | TypeDeclarationStmt(spec, _)
    | FunctionStmt(spec, _)
    | Variable(spec, _)
    | Expr(spec, _)
    | Stmts(spec, _)
    | DataStmtSets(spec, _)
    | TypeSpec(spec, _)
    | ActionStmt(spec, _)
    | DerivedTypeDefPart(spec, _)
    | Onlys(spec, _)
    | TypeBoundProcPart(spec, _)
    | FunctionHead(spec, _)
    | FunctionStmtHead(spec, _)
    | SubroutineHead(spec, _)
    | SubroutineStmtHead(spec, _)
    | PuTail(spec, _)
      -> spec

  let set_length p n = (get_spec p).length <- n
  let set_tag p t = (get_spec p).tag <- t

  let mk_dummy ?(length=0) nds                 = Dummy(mkspec ~length (), nds)
  let mk_program ?(length=0) nds               = Program(mkspec ~length ~tag:C.Ttoplevel (), nds)
  let mk_program_unit ?(length=0) nd           = ProgramUnit(mkspec ~length ~tag:C.Tprogram_unit (), nd)
  let mk_spec_exec ?(length=0) s e             = Spec_Exec(mkspec ~length ~tag:C.Tspec__exec (), s, e)
  let mk_specification_part ?(length=0) nds    = SpecificationPart(mkspec ~length ~tag:C.Tspecification_part (), nds)
  let mk_execution_part ?(length=0) nds        = ExecutionPart(mkspec ~length ~tag:C.Texecution_part (), nds)
  let mk_subprograms ?(length=0) nds           = Subprograms(mkspec ~length ~tag:C.Tsubprograms (), nds)
  let mk_interface_spec ?(length=0) nds        = InterfaceSpec(mkspec ~length ~tag:C.Tinterface_spec (), nds)
  let mk_case_block ?(length=0) nds            = CaseBlock(mkspec ~length ~tag:C.Tcase_block (), nds)
  let mk_assignment_stmt ?(length=0) nd        = AssignmentStmt(mkspec ~length ~tag:C.Tassignment_stmt (), nd)
  let mk_type_declaration_stmt ?(length=0) nd  = TypeDeclarationStmt(mkspec ~length ~tag:C.Ttype_declaration_stmt (), nd)
  let mk_function_stmt ?(length=0) nd          = FunctionStmt(mkspec ~length ~tag:C.Tfunction_stmt (), nd)
  let mk_variable ?(length=0) nd               = Variable(mkspec ~length ~tag:C.Tvariable (), nd)
  let mk_expr ?(length=0) nd                   = Expr(mkspec ~length ~tag:C.Texpr (), nd)
  let mk_stmts ?(length=0) nds                 = Stmts(mkspec ~length ~tag:C.Tstmts (), nds)
  let mk_data_stmt_sets ?(length=0) nds        = DataStmtSets(mkspec ~length ~tag:C.Tdata_stmt_sets (), nds)
  let mk_type_spec ?(length=0) nd              = TypeSpec(mkspec ~length ~tag:C.Ttype_spec (), nd)
  let mk_action_stmt ?(length=0) nd            = ActionStmt(mkspec ~length ~tag:C.Taction_stmt (), nd)
  let mk_derived_type_def_part ?(length=0) nds = DerivedTypeDefPart(mkspec ~length ~tag:C.Tderived_type_def_part (), nds)
  let mk_onlys ?(length=0) nds                 = Onlys(mkspec ~length ~tag:C.Tonlys (), nds)
  let mk_type_bound_proc_part ?(length=0) nds  = TypeBoundProcPart(mkspec ~length ~tag:C.Ttype_bound_proc_part (), nds)
  let mk_function_head ?(length=0) nds         = FunctionHead(mkspec ~length ~tag:C.Tfunction_head (), nds)
  let mk_function_stmt_head ?(length=0) nd     = FunctionStmtHead(mkspec ~length ~tag:C.Tfunction_stmt_head (), nd)
  let mk_subroutine_head ?(length=0) nds       = SubroutineHead(mkspec ~length ~tag:C.Tsubroutine_head (), nds)
  let mk_subroutine_stmt_head ?(length=0) nd   = SubroutineStmtHead(mkspec ~length ~tag:C.Tsubroutine_stmt_head (), nd)
  let mk_pu_tail ?(length=0) nds               = PuTail(mkspec ~length ~tag:C.Tpu_tail (), nds)

  let get_nodes = function
    | Dummy(_, nds)
    | Program(_, nds)

    | SpecificationPart(_, nds)
    | ExecutionPart(_, nds)
    | Subprograms(_, nds)
    | InterfaceSpec(_, nds)
    | CaseBlock(_, nds)
    | Stmts(_, nds)
    | DataStmtSets(_, nds)
    | DerivedTypeDefPart(_, nds)
    | Onlys(_, nds)
    | TypeBoundProcPart(_, nds)
    | FunctionHead(_, nds)
    | SubroutineHead(_, nds)
    | PuTail(_, nds)
      -> nds

    | Spec_Exec(_, nd_opt1, nd_opt2) -> (opt_to_list nd_opt1) @ (opt_to_list nd_opt2)

    | ProgramUnit(_, nd)

    | AssignmentStmt(_, nd)
    | TypeDeclarationStmt(_, nd)
    | FunctionStmt(_, nd)
    | Variable(_, nd)
    | Expr(_, nd)
    | TypeSpec(_, nd)
    | ActionStmt(_, nd)
    | SubroutineStmtHead(_, nd)
    | FunctionStmtHead(_, nd)

      -> [nd]

end (* of module Ast.Partial *)


let is_stmt node = L.is_stmt node#label

let is_constant node = L.is_constant node#label

let get_last_name node_list =
  match List.rev node_list with
  | last::_ -> begin
      try
	last#get_name
      with
        Not_found -> ""
  end
  | _ -> ""


let position_spec_to_inquire_spec nd =
  begin
    match nd#label with
    | L.PositionSpec ps -> nd#relab (L.InquireSpec (PositionSpec.to_inquire_spec ps))
    | _ -> ()
  end;
  nd

let position_spec_to_close_spec nd =
  begin
    match nd#label with
    | L.PositionSpec ps -> nd#relab (L.CloseSpec (PositionSpec.to_close_spec ps))
    | _ -> ()
  end;
  nd

let position_spec_to_io_control_spec nd =
  begin
    match nd#label with
    | L.PositionSpec ps ->
        nd#relab (L.IoControlSpec (PositionSpec.to_io_control_spec ps))
    | _ -> ()
  end;
  nd

let position_spec_to_wait_spec nd =
  begin
    match nd#label with
    | L.PositionSpec ps ->
        nd#relab (L.WaitSpec (PositionSpec.to_wait_spec ps))
    | _ -> ()
  end;
  nd

let position_spec_to_flush_spec nd =
  begin
    match nd#label with
    | L.PositionSpec ps ->
        nd#relab (L.FlushSpec (PositionSpec.to_flush_spec ps))
    | _ -> ()
  end;
  nd

let close_spec_to_connect_spec nd =
  begin
    match nd#label with
    | L.CloseSpec cs -> nd#relab (L.ConnectSpec (CloseSpec.to_connect_spec cs))
    | _ -> ()
  end;
  nd


let lloc_of_nodes = function
  | [] -> failwith "Ast.lloc_of_nodes"
  | [nd] -> nd#lloc
  | nd::rest -> LLoc.merge nd#lloc (Xlist.last rest)#lloc



(* *)

let rec visit f node = (* preorder traversal *)
  f node;
  List.iter (visit f) node#children

let rec visit_post (f : node -> unit) node = (* postorder traversal *)
  List.iter (visit_post f) node#children;
  f node

let size node =
  let sz = ref 0 in
  visit (fun _ -> incr sz) node;
  !sz



class c (root : node) = object (self)
  inherit Ast_base.c

  method root = root

  method visit f = visit f root

  method visit_post f = visit_post f root

  method size = size root

  method count_ambiguous_nodes =
    let count = ref 0 in
    self#visit
      (fun nd ->
        match nd#label with
        | L.Ambiguous _ -> incr count
        | _ -> ()
      );
    !count

  method count_omp_error_nodes =
    let count = ref 0 in
    self#visit
      (fun nd ->
        match nd#label with
        | L.OmpDirective (OmpDirective.ERROR) -> incr count
        | _ -> ()
      );
    !count


end (* of class Ast.c *)


let spec_opt_exec_opt_to_list (sp_nd_opt, ep_nd_opt) =
  (opt_to_list sp_nd_opt) @ (opt_to_list ep_nd_opt)

let spec_opt_exec_opt_to_children_pair (sp_nd_opt, ep_nd_opt) =
  let specs =
    match sp_nd_opt with
    | Some sp_nd -> sp_nd#children
    | None -> []
  in
  let execs =
    match ep_nd_opt with
    | Some ep_nd -> ep_nd#children
    | None -> []
  in
  specs, execs

(* end of Ast *)
