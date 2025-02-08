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

module Lang_base = Diffast_core.Lang_base
module Java_lib_base = Java_base.Java_lib_base
module Java_fact = Java_base.Java_fact


let _ =
  Lang_base.register Sjava.parser_name
    (new Lang_base.c
       ~make_tree_builder:(new Java_lib_base.tree_builder)
       ~extract_fact:Java_fact.extract
       ~node_filter:Java_fact.node_filter
    )
