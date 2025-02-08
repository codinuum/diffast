(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2020 Chiba Institude of Technology
   Copyright 2020-2025 Codinuum Software Lab <https://codinuum.com>

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
(* fortran/change.ml *)

module Triple = Diffast_core.Triple
module Change_base = Diffast_core.Change_base
module Info = Diffast_core.Info
module Edit = Diffast_core.Edit
module F_label = Fortran_base.F_label

module UID = Diffast_misc.UID

module F (L : F_label.T) = struct

  module I = Info
  module E = Edit


  (*let sprintf = Printf.sprintf*)

  include Change_base

  module CB = F(L)

(* predicates *)

  let getlab = L.getlab

  let is_named nd              = L.is_named (getlab nd)

  let is_case_construct nd     = L.is_case_construct (getlab nd)
  let is_do_construct nd       = L.is_do_construct (getlab nd)
  let is_forall_construct nd   = L.is_forall_construct (getlab nd)
  let is_if_construct nd       = L.is_if_construct (getlab nd)
  let is_where_construct nd    = L.is_where_construct (getlab nd)
  let is_derived_type_def nd   = L.is_derived_type_def (getlab nd)
  let is_interface_block nd    = L.is_interface_block (getlab nd)

  let is_primary nd            = L.is_primary (getlab nd)
  let is_expr nd               = L.is_expr (getlab nd)
  let is_stmt nd               = L.is_stmt (getlab nd)

  let is_if_stmt nd            = L.is_if_stmt (getlab nd)
  let is_arithmetic_if_stmt nd = L.is_arithmetic_if_stmt (getlab nd)
  let is_if_then_stmt nd       = L.is_if_then_stmt (getlab nd)
  let is_else_if_stmt nd       = L.is_else_if_stmt (getlab nd)
  let is_else_stmt nd          = L.is_else_stmt (getlab nd)

  let is_pp_directive nd       = L.is_pp_directive (getlab nd)
  let is_pp_define nd          = L.is_pp_define (getlab nd)
  let is_pp_include nd         = L.is_pp_include (getlab nd)
  let is_ocl_directive nd      = L.is_ocl_directive (getlab nd)

  let is_program_unit nd       = L.is_program_unit (getlab nd)

  let is_block nd              = L.is_block (getlab nd)

  let is_sect_subscr_list nd   = L.is_section_subscript_list (getlab nd)
  let is_ambiguous nd          = L.is_ambiguous (getlab nd)

  let is_if nd =
    is_if_stmt nd ||
    is_arithmetic_if_stmt nd ||
    is_if_then_stmt nd ||
    is_else_if_stmt nd

  let is_if_cond nd =
    try
      let pnd = nd#initial_parent in
      is_if pnd && is_expr nd
    with
      _ -> false

  let is_then_branch nd =
    try
      let pnd = nd#initial_parent in
      is_if_then_stmt pnd && is_block nd
    with
      _ -> false

  let is_else_if_branch nd =
    try
      let pnd = nd#initial_parent in
      is_else_if_stmt pnd && is_block nd
    with
      _ -> false

  let is_else_branch nd =
    try
      let pnd = nd#initial_parent in
      is_else_stmt pnd && is_block nd
    with
      _ -> false

(* *)

  let get_unit tree nd =
    try
      let u = tree#get_nearest_containing_unit nd in
      u#data#label
    with
      Not_found -> ""


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
      let mkt_chgto = self#mkt_changed_to ~category:Triple.ghost in
      let mkt_ren = self#mkt_renamed ~category:Triple.ghost in
      let mkt_mov = self#mkt_moved_to ~category:Triple.ghost in
      let mkt_odrchg = self#mkt_order_changed ~category:Triple.ghost in
(*      let mkt_chgcard _ = [] in *)
      [
(* case-construct *)
        "case-construct removed",  Smedium, (self#make_delete_st is_case_construct), mkt_del;
        "case-construct added",    Smedium, (self#make_insert_st is_case_construct), mkt_ins;
        "case-construct modified", Smedium, (self#aggregate_changes is_case_construct), mkt_mod;

(* do-construct *)
        "do-construct removed",  Smedium, (self#make_delete_st is_do_construct), mkt_del;
        "do-construct added",    Smedium, (self#make_insert_st is_do_construct), mkt_ins;
        "do-construct modified", Smedium, (self#aggregate_changes is_do_construct), mkt_mod;

(* forall-construct *)
        "forall-construct removed",  Smedium, (self#make_delete_st is_forall_construct), mkt_del;
        "forall-construct added",    Smedium, (self#make_insert_st is_forall_construct), mkt_ins;
        "forall-construct modified", Smedium, (self#aggregate_changes is_forall_construct), mkt_mod;

(* if-construct *)
        "if-construct removed",  Smedium, (self#make_delete_st is_if_construct), mkt_del;
        "if-construct added",    Smedium, (self#make_insert_st is_if_construct), mkt_ins;
        "if-construct modified", Smedium, (self#aggregate_changes is_if_construct), mkt_mod;

(* where-construct *)
        "where-construct removed",  Smedium, (self#make_delete_st is_where_construct), mkt_del;
        "where-construct added",    Smedium, (self#make_insert_st is_where_construct), mkt_ins;
        "where-construct modified", Smedium, (self#aggregate_changes is_where_construct), mkt_mod;

(* derived-type-def *)
        "derived-type-def removed",  Smedium, (self#make_delete_st is_derived_type_def), mkt_del;
        "derived-type-def added",    Smedium, (self#make_insert_st is_derived_type_def), mkt_ins;
        "derived-type-def modified", Smedium, (self#aggregate_changes is_derived_type_def), mkt_mod;

(* interface-block *)
        "interface-block removed",  Smedium, (self#make_delete_st is_interface_block), mkt_del;
        "interface-block added",    Smedium, (self#make_insert_st is_interface_block), mkt_ins;
        "interface-block modified", Smedium, (self#aggregate_changes is_interface_block), mkt_mod;

(* if-construct *)
        "if-condition modified", Smedium, (self#aggregate_changes is_if_cond), mkt_mod;
        "then-branch deleted",   Smedium, (self#make_delete is_then_branch), mkt_del;
        "then-branch inserted",  Smedium, (self#make_insert is_then_branch), mkt_ins;
        "then-branch removed",   Smedium, (self#make_delete_st is_then_branch), mkt_del;
        "then-branch added",     Smedium, (self#make_insert_st is_then_branch), mkt_ins;

        "else-if-branch deleted",  Smedium, (self#make_delete is_else_if_branch), mkt_del;
        "else-if-branch inserted", Smedium, (self#make_insert is_else_if_branch), mkt_ins;
        "else-if-branch removed",  Smedium, (self#make_delete_st is_else_if_branch), mkt_del;
        "else-if-branch added",    Smedium, (self#make_insert_st is_else_if_branch), mkt_ins;

        "else-branch deleted",  Smedium, (self#make_delete is_else_branch), mkt_del;
        "else-branch inserted", Smedium, (self#make_insert is_else_branch), mkt_ins;
        "else-branch removed",  Smedium, (self#make_delete_st is_else_branch), mkt_del;
        "else-branch added",    Smedium, (self#make_insert_st is_else_branch), mkt_ins;

(* define-directive *)
        "define-directive removed",  Smedium, (self#make_delete_st is_pp_define), mkt_del;
        "define-directive added",    Smedium, (self#make_insert_st is_pp_define), mkt_ins;
        "define-directive modified", Smedium, (self#aggregate_changes is_pp_define), mkt_mod;

(* include-directive *)
        "include-directive removed",  Smedium, (self#make_delete_st is_pp_include), mkt_del;
        "include-directive added",    Smedium, (self#make_insert_st is_pp_include), mkt_ins;
        "include-directive modified", Smedium, (self#aggregate_changes is_pp_include), mkt_mod;

(* pp-directive *)
        "pp-directive removed",  Smedium, (self#make_delete_st is_pp_directive), mkt_del;
        "pp-directive added",    Smedium, (self#make_insert_st is_pp_directive), mkt_ins;
        "pp-directive modified", Smedium, (self#aggregate_changes is_pp_directive), mkt_mod;

(* ocl-directive *)
        "ocl-directive removed",  Smedium, (self#make_delete_st is_ocl_directive), mkt_del;
        "ocl-directive added",    Smedium, (self#make_insert_st is_ocl_directive), mkt_ins;
        "ocl-directive modified", Smedium, (self#aggregate_changes is_ocl_directive), mkt_mod;

(* section-subscript-list *)
        "section-subscript-list modified", Smedium, (self#aggregate_changes is_sect_subscr_list), mkt_mod;

(* ambiguous entity *)
        "ambiguous entity modified", Smedium, (self#aggregate_changes is_ambiguous), mkt_mod;

(* others *)
        "(removed)",       Slow, (self#make_delete_st (fun _ -> true)), mkt_del;
        "(added)",         Slow, (self#make_insert_st (fun _ -> true)), mkt_ins;
        "(deleted)",       Slow, (self#make_delete (fun _ -> true)), mkt_del;
        "(inserted)",      Slow, (self#make_insert (fun _ -> true)), mkt_ins;
        "(moved)",         Slow, (self#make_move (fun _ -> true)), mkt_mov;
        "(changed)",       Slow, (self#make_changed_to (fun _ -> true)), mkt_chgto;
        "(renamed)",       Slow, (self#make_renaming is_named), mkt_ren;
        "(order changed)", Slow, (self#make_order_change (fun _ -> true)), mkt_odrchg;

      ]
    (* end of method make_changes_list *)



 end (* of class Change.F.c *)

let extract options tree1 tree2 uidmapping edits =
  let chg = new c options tree1 tree2 uidmapping edits get_unit get_desc1 get_desc2 in
  let res = chg#extract in
  chg#recover_edits;
  res

end (* of functor Change.F *)
