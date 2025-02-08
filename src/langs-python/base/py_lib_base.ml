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
(* py_lib_base.ml *)

module Xprint = Diffast_misc.Xprint
module Sourcecode = Diffast_core.Sourcecode
module Fact_base = Diffast_core.Fact_base
module Lang_base = Diffast_core.Lang_base
module Common = Python_parsing.Common
module Lib = Python_parsing.Lib

module Label = Py_label

module Tree = Sourcecode.Tree (Label)
module Fact = Fact_base.F (Label)

let sprintf = Printf.sprintf

let extract_fact (*options*)_ (*cache_path*)_ (*tree*)_ = (* not yet *)
(*
  try
  let extractor = new Fact.extractor_base cache_path options tree in
  extractor#set_lang_prefix Astml.python_prefix;
  extractor#extract
  | Triple.File_exists s -> Common.warning_msg "file exists: \"%s\"" s
  | Triple.Lock_failed -> Common.warning_msg "fact buffer is already locked."
*)
()

class tree_builder options =
  let _parser = new Lib.parser_c in
  object
    inherit Lang_base.tree_builder

    method from_xnode = Tree.of_xnode options

    method build_tree file =
      Xprint.verbose options#verbose_flag "parsing \"%s\"..." file#path;
      try
        let ast = _parser#parse_file file in
        let tree = Py_tree.of_ast options file#path ast in
        tree#set_source_info file;
        tree#set_parser_name Spython.parser_name;
        tree
      with
        Common.Parse_error(head, msg) ->
          raise (Lang_base.Parse_error
                   (sprintf "[Python]%s" head, sprintf "%s: %s" msg file#path))

    initializer
      _parser#_set_verbose_flag options#verbose_flag;
      _parser#set_search_path_list options#search_path_list;
      if options#python_with_stmt_disabled_flag then
        _parser#disable_with_stmt;
      _parser#_set_keep_going_flag options#keep_going_flag;
      _parser#_set_ignore_comment_flag options#python_ignore_comment_flag

  end
