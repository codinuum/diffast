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
(* py_lib.ml *)

[%%prepare_logger]

module Xset = Diffast_misc.Xset
module Delta_format = Diffast_core.Delta_format
module Comparison = Diffast_core.Comparison
module Edit = Diffast_core.Edit
module Lang = Diffast_core.Lang
module Py_lib_base = Python_base.Py_lib_base

include Py_lib_base

module Analyzing = Diffast_core.Analyzing.F (Label)
module DF        = Delta_format.Format

let extract_change (*options*)_ (*tree1*)_ (*tree2*)_ (*uidmapping*)_ (*edits*)_ =
  [], [], [], (Xset.create 0) (* not yet *)

[%%capture_path
let elaborate_edits
    options
    (cenv : (Tree.node_t, Tree.c) Comparison.c)
    uidmapping
    edits
    =
  if options#rename_rectification_level > 0 then begin
    let mkfilt = Edit.mkfilt Fact.getlab in
    let is_assign = mkfilt Label.is_assign in
    let is_attrref = mkfilt Label.is_attrref in
    let is_param = mkfilt Label.is_param in
    let is_name = mkfilt Label.is_name in

    let filters = [|
      is_assign;
      is_attrref;
      is_param;
      is_name;
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
]

class tree_patcher options tree_factory = object
  inherit Lang.tree_patcher

  method _patch = DF._patch options tree_factory

  method patch = DF.patch options tree_factory

end

let _ =
  Lang.register Spython.parser_name
    (new Lang.c
       ~make_tree_comparator:(new Analyzing.tree_comparator)
       ~make_tree_builder:(new tree_builder)
       ~extract_change:extract_change
       ~extract_fact:extract_fact
       ~elaborate_edits:(Some elaborate_edits)
       ~make_tree_patcher:(new tree_patcher)
    )
