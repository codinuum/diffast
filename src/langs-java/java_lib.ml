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
(* java_lib.ml *)

[%%prepare_logger]

module Java_lib_base = Java_base.Java_lib_base

include Java_lib_base

module Comparison = Diffast_core.Comparison
module Edit = Diffast_core.Edit
module Lang = Diffast_core.Lang
module Analyzing = Diffast_core.Analyzing.F (Label)
module Change    = Java_change.F (Label)
module PP        = Diffast_core.Postprocessing.F (Label)
module DF        = Diffast_core.Delta_format.Format

let sprintf = Printf.sprintf

[%%capture_path
let elaborate_edits
    options
    (cenv : (Tree.node_t, Tree.c) Comparison.c)
    nmapping
    edits
    =
  if options#rename_rectification_level > 0 then begin
    [%debug_log "START!"];
    let mkfilt = Edit.mkfilt Fact.getlab in
    let is_import_single       = mkfilt Label.is_import_single in
    let is_field               = mkfilt Label.is_field in
    let is_variabledeclarator  = mkfilt Label.is_variabledeclarator in
    let is_field_access        = mkfilt Label.is_fieldaccess in
    let is_variabledeclaration = mkfilt Label.is_localvariabledecl in
    let is_parameter           = mkfilt Label.is_parameter in
    let is_name                = mkfilt Label.is_name in

    let filters = [|
      is_import_single;
      is_field;
      is_variabledeclarator;
      is_field_access;
      is_variabledeclaration;
      is_parameter;
      is_name;
    |]
    in
    let max_count = 2 in
    let handle_weak = not (*options#dump_delta_flag*)false in
    let count = ref 0 in
    let modified = ref true in
    while !modified && !count < max_count do
      incr count;
      [%debug_log "%d-th execution of rename rectification" !count];
      modified := Edit.rectify_renames_u ~handle_weak options cenv nmapping edits filters;
    done
  end
]


class tree_patcher options tree_factory = object
  inherit Lang.tree_patcher

  method _patch = DF._patch options tree_factory

  method patch = DF.patch options tree_factory

end

let _ =
  Lang.register Sjava.parser_name
    (new Lang.c
       ~make_tree_comparator:(new Analyzing.tree_comparator)
       ~make_tree_builder:(new tree_builder)
       ~extract_change:Change.extract
       ~extract_fact:Fact.extract
       ~node_filter:Fact.node_filter
       ~node_pair_filter:Fact.node_pair_filter
       ~elaborate_edits:(Some elaborate_edits)
       ~make_tree_patcher:(new tree_patcher)
    )
