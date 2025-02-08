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
(* cpp/cpp_lib.ml *)

[%%prepare_logger]

module Comparison = Diffast_core.Comparison
module Edit = Diffast_core.Edit
module Lang = Diffast_core.Lang
module Cpp_lib_base = Cpp_base.Cpp_lib_base

include Cpp_lib_base

module Analyzing = Diffast_core.Analyzing.F (Label)
module Change    = Cpp_change.F (Label)

[%%capture_path
let elaborate_edits
    options
    (cenv : (Tree.node_t, Tree.c) Comparison.c)
    uidmapping
    edits
    =
  if options#rename_rectification_level > 0 then begin
    let mkfilt = Edit.mkfilt Fact.getlab in
    (*let is_type_decl_stmt = mkfilt Label.is_type_decl_stmt in*)
    let is_named = mkfilt Label.is_named in

    let filters = [|
      is_named;
    |]
    in
    let max_count = 2 in
    let handle_weak = not options#dump_delta_flag in
    let count = ref 0 in
    let modified = ref true in
    while !modified && !count < max_count do
      incr count;
      [%debug_log "%d-th execution of rename rectification" !count];
      modified := Edit.rectify_renames_u ~handle_weak options cenv uidmapping edits filters
    done
  end
]

let _ =
  Lang.register Scpp.parser_name
    (new Lang.c
       ~make_tree_comparator:(new Analyzing.tree_comparator)
       ~make_tree_builder:(new tree_builder)
       ~extract_change:Change.extract
       ~extract_fact:Fact.extract
       ~node_filter:Fact.node_filter
       ~node_pair_filter:Fact.node_pair_filter
       ~elaborate_edits:(Some elaborate_edits)
    )
