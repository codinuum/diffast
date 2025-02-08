(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2020 Chiba Institude of Technology
   Copyright 2020 Codinuum Software Lab <https://codinuum.com>

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
(* fortran/f_lib.ml *)

module Comparison = Diffast_core.Comparison
module Edit = Diffast_core.Edit
module Lang = Diffast_core.Lang
module F_lib_base = Fortran_base.F_lib_base

include F_lib_base

module Analyzing = Diffast_core.Analyzing.F (Label)
module Change    = F_change.F (Label)

let elaborate_edits
    options
    (cenv : (Tree.node_t, Tree.c) Comparison.c)
    uidmapping
    edits
    =
  if options#rename_rectification_level > 0 then begin
    let mkfilt = Edit.mkfilt Fact.getlab in
    (*let is_type_decl_stmt = mkfilt Label.is_type_decl_stmt in*)
    let is_entity_decl = mkfilt Label.is_entity_decl in
    let is_part_name   = mkfilt Label.is_part_name in
    let is_var_name    = mkfilt Label.is_var_name in

    let filters = [|
      is_entity_decl;
      is_part_name;
      is_var_name;
    |]
    in
    let max_count = 2 in
    let handle_weak = not options#dump_delta_flag in
    let count = ref 0 in
    let modified = ref true in
    while !modified && !count < max_count do
      incr count;
      [%debug_log "%d-th execution of rename rectification" !count];
      modified := Edit.rectify_renames_u ~handle_weak options cenv uidmapping edits filters;
    done
  end

let _ =
  Lang.register Sfortran.parser_name
    (new Lang.c
       ~make_tree_comparator:(new Analyzing.tree_comparator)
       ~make_tree_builder:(new tree_builder)
       ~extract_change:Change.extract
       ~extract_fact:Fact.extract
       ~node_filter:Fact.node_filter
       ~node_pair_filter:Fact.node_pair_filter
       ~elaborate_edits:(Some elaborate_edits)
    )
