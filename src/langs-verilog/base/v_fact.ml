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
(* fact extractor *)

module Astml = Diffast_core.Astml
module Triple = Diffast_core.Triple
module Fact_base = Diffast_core.Fact_base
module Common = Verilog_parsing.Common


module F (L : V_label.T) = struct

  module FB = Fact_base.F(L)
  open FB

  let p_in_module     = mkvres "inModule"
  let p_in_statement  = mkvres "inStatement"


  let node_filter options nd = (* filter out inactive nodes *)
    if options#fact_restricted_flag then
      let lab = getlab nd in
      L.is_stmt lab ||
      L.is_module_decl lab ||
      L.is_always_construct lab ||
      L.is_initial_construct lab ||
      L.is_final_construct lab ||
      L.is_inst lab
    else
      true

  let node_pair_filter options nd1 nd2 =
    (node_filter options nd1) && (node_filter options nd2)


  class extractor options cache_path tree = object (self)
    inherit extractor_base options cache_path tree

    method! id = "Verilog"

    method! scanner_body_after_subscan nd (*lab*)_ entity =

      if node_filter options nd then begin

	self#add (entity, p_is_a, mkvres nd#data#get_category);
(*	self#add (entity, p_file_digest, tree#encoded_source_digest); *)

	self#add_surrounding_xxx L.is_module_decl nd entity p_in_module;
	self#add_surrounding_xxx L.is_stmt nd entity p_in_statement;

      end;


  end (* of class Verilog.Fact.extractor *)


  (* main function *)
  let extract options cache_path tree =
    try
      let extractor = new extractor options cache_path tree in
      extractor#set_lang_prefix Astml.verilog_prefix;
      extractor#extract
    with
    | Triple.File_exists s -> Common.warning_msg "file exists: \"%s\"" s
    | Triple.Lock_failed -> Common.warning_msg "fact buffer is already locked."

end (* of functor Verilog.Fact.F *)
