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
(* astml/lib.ml *)

module Xset = Diffast_misc.Xset
module Lang = Diffast_core.Lang
module Lib_base = Astml_base.Lib_base
module Label = Astml_base.Label

include Lib_base

module Analyzing = Diffast_core.Analyzing.F (Label)
module ChangeCCX = Change.CCX (Label)


let extract_change (*options*)_ (*tree1*)_ (*tree2*)_ (*nmapping*)_ (*edits*)_ =
  [], [], [], (Xset.create 0)(* not yet *)

let make_comparator = new Analyzing.tree_comparator

let _ =
  Lang.register Sastml.parser_name
    (new Lang.c
       ~make_tree_comparator:make_comparator
       ~make_tree_builder:(new tree_builder)
       ~get_cache_key:file_digest_hex
       ~extract_change:extract_change
       ~extract_fact:extract_fact
    )

(* for external parsers *)

let _ =
  Lang.register_external Sastml.parser_name Sastml.xparser_name_ccx
    (fun subname name ->
      new Lang.c
        ~subname
        ~make_tree_comparator:make_comparator
        ~make_tree_builder:(new ext_tree_builder subname)
        ~get_cache_key:ext_file_digest_hex
        ~extract_change:ChangeCCX.extract
        ~extract_fact:FactCCX.extract
        ~node_filter:FactCCX.node_filter
        ~node_pair_filter:FactCCX.node_pair_filter
        name
    )
