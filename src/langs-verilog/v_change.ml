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
(* verilog/change.ml *)

module Change_base = Diffast_core.Change_base
module Triple = Diffast_core.Triple
module Info = Diffast_core.Info
module Edit = Diffast_core.Edit
module V_label = Verilog_base.V_label

module UID = Diffast_misc.UID

module F (L : V_label.T) = struct

  module I = Info
  module E = Edit


  (*let sprintf = Printf.sprintf*)

  include Change_base

  module CB = F(L)

(* predicates *)

  let getlab = L.getlab

  let is_always_construct nd = L.is_always_construct (getlab nd)
  let is_timing_control nd = L.is_timing_control (getlab nd)
  let is_continuous_assign nd = L.is_continuous_assign (getlab nd)
  let is_blocking_assign nd = L.is_blocking_assign (getlab nd)
  let is_non_blocking_assign nd = L.is_non_blocking_assign (getlab nd)
  let is_if nd = L.is_if (getlab nd)

  let is_case nd = L.is_case (getlab nd)
  let is_case_item nd = L.is_case_item (getlab nd)
  let is_case_cond nd = L.is_case_cond (getlab nd)
  let is_ports nd = L.is_ports (getlab nd)
  let is_port nd = L.is_port (getlab nd)
  let is_port_dir nd = L.is_port_dir (getlab nd)
  let is_net_type nd = L.is_net_type (getlab nd)
  let is_data_type nd = L.is_data_type (getlab nd)
  let is_var_data_type nd = L.is_var_data_type (getlab nd)
  let is_signing nd = L.is_signing (getlab nd)
  let is_ranges nd = L.is_ranges (getlab nd)
  let is_variable_dims nd = L.is_variable_dims (getlab nd)
  let is_inst nd = L.is_inst (getlab nd)
  let is_initial_construct nd = L.is_initial_construct (getlab nd)
  let is_final_construct nd = L.is_final_construct (getlab nd)
  let is_generate_region nd = L.is_generate_region (getlab nd)
  let is_param_port_decl nd = L.is_param_port_decl (getlab nd)
  let is_param_assign nd = L.is_param_assign (getlab nd)
  let is_reg nd = L.is_reg (getlab nd)
  let is_data_decl_var nd = L.is_data_decl_var (getlab nd)
  let is_net_decl nd = L.is_net_decl (getlab nd)
  let is_wire nd = L.is_wire (getlab nd)
  let is_expr nd = L.is_expr (getlab nd)
  let is_stmt nd = L.is_stmt (getlab nd)
  let is_pp_define nd = L.is_pp_define (getlab nd)
  let is_pp_include nd = L.is_pp_include (getlab nd)


  let is_if_cond nd =
    try
      let pnd = nd#initial_parent in
      is_if pnd && is_expr nd
    with _ -> false

  let is_branch nd n =
    try
      let pnd = nd#initial_parent in
      if is_if pnd && is_stmt nd then
	let stmts = List.filter is_stmt (Array.to_list pnd#children) in
	try
	  List.nth stmts n == nd
	with _ ->
	  raise (Invalid_argument "Verilog.Change.F.is_branch")
      else
	false
    with _ -> false

  let is_then_branch nd = is_branch nd 0
  let is_else_branch nd = is_branch nd 1

  let is_port_value nd =
    try
      let pnd = nd#initial_parent in
      is_port pnd && is_expr nd
    with _ -> false

  let is_reg_decl nd =
    if is_data_decl_var nd then
      try
	let head = nd#initial_children.(0) in
	let x = head#initial_children.(head#initial_nchildren-1) in
	is_reg x
      with _ -> false
    else
      false

  let is_wire_decl nd =
    if is_net_decl nd then
      try
	is_wire nd#initial_children.(0)
      with _ -> false
    else
      false

(* *)

  let get_unit tree nd =
    try
      let u = tree#get_nearest_containing_unit nd in
      u#data#label
    with Not_found -> ""


  let ids_to_str ids =
    if ids = [] then "" else sprintf "{%s}" (String.concat "," ids)

  let subtree_to_str tree nd =
    sprintf "[%s]" (tree#subtree_to_simple_string nd#gindex)

  let get_desc1 (*is_whole*)_ tree nd =
    let ids = tree#get_ident_use_list nd#gindex in
    let extra2 =
      if (* is_whole *) true then
	subtree_to_str tree nd
      else
	""
    in
    nd#data#label^(ids_to_str ids)^extra2

  let get_desc2 tree1 tree2 nd1 nd2 =
    let ids1 = tree1#get_ident_use_list nd1#gindex in
    let ids2 = tree2#get_ident_use_list nd2#gindex in
    sprintf "%s%s%s -> %s%s%s"
      nd1#data#label (ids_to_str ids1) (subtree_to_str tree1 nd1)
      nd2#data#label (ids_to_str ids2) (subtree_to_str tree2 nd2)




(* class Change.F.c *)

  class c options tree1 tree2 uidmapping edits get_unit get_desc1 get_desc2 = object(self)
    inherit CB.c options tree1 tree2 uidmapping edits get_unit get_desc1 get_desc2

    method! make_changes_list () =
      let mkt_del = self#mkt_deleted ~category:Triple.ghost in
      let mkt_ins = self#mkt_inserted ~category:Triple.ghost in
      let mkt_mod = self#mkt_modified ~category:Triple.ghost in
(*
      let mkt_chgto = self#mkt_changed_to ~category:Triple.ghost in
      let mkt_ren = self#mkt_renamed ~category:Triple.ghost in
      let mkt_mov = self#mkt_moved_to ~category:Triple.ghost in
      let mkt_chgodr = self#mkt_changed_order ~category:Triple.ghost in
*)
      let mkt_chgcard _ = [] in
      [
(* always-construct *)
	"always-construct removed",  Smedium, (self#make_delete_st is_always_construct), mkt_del;
	"always-construct added",    Smedium, (self#make_insert_st is_always_construct), mkt_ins;
	"timing control modified",   Smedium, (self#aggregate_changes is_timing_control), mkt_mod;

(* continuous assignment *)
	"continuous-assignment removed",  Smedium, (self#make_delete_st is_continuous_assign), mkt_del;
	"continuous-assignment added",    Smedium, (self#make_insert_st is_continuous_assign), mkt_ins;
	"continuous-assignment modified", Smedium, (self#aggregate_changes is_continuous_assign), mkt_mod;

(* blocking assignment *)
	"blocking-assignment removed",  Smedium, (self#make_delete_st is_blocking_assign), mkt_del;
	"blocking-assignment added",    Smedium, (self#make_insert_st is_blocking_assign), mkt_ins;
	"blocking-assignment modified", Smedium, (self#aggregate_changes is_blocking_assign), mkt_mod;

(* non-blocking assignment *)
	"non-blocking-assignment removed",  Smedium, (self#make_delete_st is_non_blocking_assign), mkt_del;
	"non-blocking-assignment added",    Smedium, (self#make_insert_st is_non_blocking_assign), mkt_ins;
	"non-blocking-assignment modified", Smedium, (self#aggregate_changes is_non_blocking_assign), mkt_mod;

(* if-statement *)
	"if-condition modified", Smedium, (self#aggregate_changes is_if_cond), mkt_mod;
	"then-branch deleted",   Smedium, (self#make_delete is_then_branch), mkt_del;
	"then-branch inserted",  Smedium, (self#make_insert is_then_branch), mkt_ins;
	"then-branch removed",   Smedium, (self#make_delete_st is_then_branch), mkt_del;
	"then-branch added",     Smedium, (self#make_insert_st is_then_branch), mkt_ins;

	"else-branch deleted",  Smedium, (self#make_delete is_else_branch), mkt_del;
	"else-branch inserted", Smedium, (self#make_insert is_else_branch), mkt_ins;
	"else-branch removed",  Smedium, (self#make_delete_st is_else_branch), mkt_del;
	"else-branch added",    Smedium, (self#make_insert_st is_else_branch), mkt_ins;

	"case statement modified", Smedium, (self#aggregate_changes is_case), mkt_mod;
	"case-branch removed",     Smedium, (self#make_delete_st is_case_item), mkt_del;
	"case-branch added",       Smedium, (self#make_insert_st is_case_item), mkt_ins;
	"case-condition modified", Smedium, (self#aggregate_changes is_case_cond), mkt_mod;

(* port *)
	"port direction removed",  Smedium, (self#make_delete_st is_port_dir), mkt_del;
	"port direction added",    Smedium, (self#make_insert_st is_port_dir), mkt_ins;
	"port direction modified", Smedium, (self#aggregate_changes is_port_dir), mkt_mod;

	"net type removed",  Smedium, (self#make_delete_st is_net_type), mkt_del;
	"net type added",    Smedium, (self#make_insert_st is_net_type), mkt_ins;
	"net type modified", Smedium, (self#aggregate_changes is_net_type), mkt_mod;

	"data type removed",  Smedium, (self#make_delete_st is_data_type), mkt_del;
	"data type added",    Smedium, (self#make_insert_st is_data_type), mkt_ins;
	"data type modified", Smedium, (self#aggregate_changes is_data_type), mkt_mod;

	"var data type removed",  Smedium, (self#make_delete_st is_var_data_type), mkt_del;
	"var data type added",    Smedium, (self#make_insert_st is_var_data_type), mkt_ins;
	"var data type modified", Smedium, (self#aggregate_changes is_var_data_type), mkt_mod;

	"signing removed",  Smedium, (self#make_delete_st is_signing), mkt_del;
	"signing added",    Smedium, (self#make_insert_st is_signing), mkt_ins;
	"signing modified", Smedium, (self#aggregate_changes is_signing), mkt_mod;

	"ranges removed",  Smedium, (self#make_delete_st is_ranges), mkt_del;
	"ranges added",    Smedium, (self#make_insert_st is_ranges), mkt_ins;
	"ranges modified", Smedium, (self#aggregate_changes is_ranges), mkt_mod;

	"variable dimensions removed",  Smedium, (self#make_delete_st is_variable_dims), mkt_del;
	"variable dimensions added",    Smedium, (self#make_insert_st is_variable_dims), mkt_ins;
	"variable dimensions modified", Smedium, (self#aggregate_changes is_variable_dims), mkt_mod;

	"number of ports changed", Smedium, (self#make_cardinality_change is_port), mkt_chgcard;

(* instantiation *)
	"instantiation removed",  Smedium, (self#make_delete_st is_inst), mkt_del;
	"instantiation added",    Smedium, (self#make_insert_st is_inst), mkt_ins;
	"instantiation modified", Smedium, (self#aggregate_changes is_inst), mkt_mod;

(* initial-construct *)
	"initial-construct removed",  Smedium, (self#make_delete_st is_initial_construct), mkt_del;
	"initial-construct added",    Smedium, (self#make_insert_st is_initial_construct), mkt_ins;
	"initial-construct modified", Smedium, (self#aggregate_changes is_initial_construct), mkt_mod;

(* final-construct *)
	"final-construct removed",  Smedium, (self#make_delete_st is_final_construct), mkt_del;
	"final-construct added",    Smedium, (self#make_insert_st is_final_construct), mkt_ins;
	"final-construct modified", Smedium, (self#aggregate_changes is_final_construct), mkt_mod;

(* generate region *)
	"generate-region removed",  Smedium, (self#make_delete_st is_generate_region), mkt_del;
	"generate-region added",    Smedium, (self#make_insert_st is_generate_region), mkt_ins;
	"generate-region modified", Smedium, (self#aggregate_changes is_generate_region), mkt_mod;

(* parameter *)
	"parameter port declaration removed",  Smedium, (self#make_delete_st is_param_port_decl), mkt_del;
	"parameter port declaration added",    Smedium, (self#make_insert_st is_param_port_decl), mkt_ins;
	"parameter port declaration modified", Smedium, (self#aggregate_changes is_param_port_decl), mkt_mod;

	"parameter assignment removed",  Smedium, (self#make_delete_st is_param_assign), mkt_del;
	"parameter assignment added",    Smedium, (self#make_insert_st is_param_assign), mkt_ins;
	"parameter assignment modified", Smedium, (self#aggregate_changes is_param_assign), mkt_mod;

(* register *)
	"register removed",  Smedium, (self#make_delete_st is_reg_decl), mkt_del;
	"register added",    Smedium, (self#make_insert_st is_reg_decl), mkt_ins;
	"register modified", Smedium, (self#aggregate_changes is_reg_decl), mkt_mod;

(* wire *)
	"wire removed",  Smedium, (self#make_delete_st is_wire_decl), mkt_del;
	"wire added",    Smedium, (self#make_insert_st is_wire_decl), mkt_ins;
	"wire modified", Smedium, (self#aggregate_changes is_wire_decl), mkt_mod;


(* define-directive *)
	"define-directive removed",  Smedium, (self#make_delete_st is_pp_define), mkt_del;
	"define-directive added",    Smedium, (self#make_insert_st is_pp_define), mkt_ins;
	"define-directive modified", Smedium, (self#aggregate_changes is_pp_define), mkt_mod;

(* include-directive *)
	"include-directive removed",  Smedium, (self#make_delete_st is_pp_include), mkt_del;
	"include-directive added",    Smedium, (self#make_insert_st is_pp_include), mkt_ins;
	"include-directive modified", Smedium, (self#aggregate_changes is_pp_include), mkt_mod;

      ]
    (* end of method make_changes_list *)



 end (* of class Change.F.c *)

let extract options tree1 tree2 uidmapping edits =
  let chg = new c options tree1 tree2 uidmapping edits get_unit get_desc1 get_desc2 in
  let res = chg#extract in
  chg#recover_edits;
  res

end (* of functor Change.F *)
