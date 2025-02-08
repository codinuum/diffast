(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>
   Copyright 2020-2025 Chiba Institute of Technology

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

(* cpp/cpp_lib_base.ml *)

module Xprint = Diffast_misc.Xprint
module Sourcecode = Diffast_core.Sourcecode
module Lang_base = Diffast_core.Lang_base
module Parserlib_base = Langs_common.Parserlib_base
module Lib = Cpp_parsing.Lib

module Label = Cpp_label

module Tree = Sourcecode.Tree (Label)
module Fact = Cpp_fact.F (Label)

class tree_builder options =
  let _parser = new Lib.parser_c in
  object
    inherit Lang_base.tree_builder

    method from_xnode = Tree.of_xnode options

    method build_tree file =
      Xprint.verbose options#verbose_flag "parsing \"%s\"...%!" file#fullpath;
      _parser#add_search_path file#dirname;
      try
        let ast = _parser#parse_file file in
        let tree = Cpp_tree.of_ast options ast in
        tree#set_source_info file;
        tree#set_parser_name Scpp.parser_name;
        tree
      with
        Parserlib_base.Parse_error(head, msg) ->
          raise (Lang_base.Parse_error ("[Cpp]"^head, msg))

    method! extra_source_files = _parser#extra_source_files


    initializer
      _parser#_set_verbose_flag options#verbose_flag;
      _parser#_set_keep_going_flag options#keep_going_flag;

      _parser#set_search_path_list options#search_path_list;

      (*_parser#set_ignore_include_flag*)

  end
