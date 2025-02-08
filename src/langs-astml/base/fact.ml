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

[%%prepare_logger]

module Fact_base = Diffast_core.Fact_base
module Triple = Diffast_core.Triple
module A = Diffast_core.Astml

[%%capture_path
module CCX (L : Label.T) = struct

  module FB = Fact_base.F(L)
  open FB

  let getlab = getlab

  let p_in_decl    = mkccxres "inDeclaration"
  let p_in_fun_def = mkccxres "inFunctionDefinition"
  let p_in_stmt    = mkccxres "inStatement"
  let p_in_if_stmt = mkccxres "inIfStatement"

  let p_name       = mkccxres "name"
  let p_value      = mkccxres "value"
  let p_operator   = mkccxres "operator"

  let node_filter options (*nd*)_ =
    if options#fact_restricted_flag then
(*      let lab = getlab nd in *)
      true
    else
      true

  let node_pair_filter options nd1 nd2 =
    (node_filter options nd1) && (node_filter options nd2)


  class extractor options cache_path tree = object (self)
    inherit extractor_base options cache_path tree

    method! id = "Astml"

    method! scanner_body_after_subscan nd lab entity =

      if node_filter options nd then begin

	self#add (entity, p_is_a, mkccxres nd#data#get_category);

        if L.CCX.is_decl lab || L.CCX.is_translation_unit lab then begin
          self#add (entity, p_in_file, self#fileentity);
          self#set_version entity
        end;

        begin
          try
            self#add (entity, p_name, mklit (L.get_name lab))
          with
            Not_found -> ()
        end;

        begin
          try
            self#add (entity, p_value, mklit (L.get_value lab))
          with
            Not_found -> ()
        end;

        begin
          try
            self#add (entity, p_operator, mklit (L.get_operator lab))
          with
            Not_found -> ()
        end;

        self#add_surrounding_xxx L.CCX.is_decl nd entity p_in_decl;
        self#add_surrounding_xxx L.CCX.is_fun_def nd entity p_in_fun_def;
        self#add_surrounding_xxx L.CCX.is_stmt nd entity p_in_stmt;

      end

  end (* of class Astml.Fact.CCX.extractor *)

  (* main function *)
  let extract options cache_path tree =
    try
      let extractor = new extractor options cache_path tree in
      [%debug_log "setting lang prefix to %s" A.ccx_prefix];
      extractor#set_lang_prefix A.ccx_prefix;
      [%debug_log "extracting..."];
      extractor#extract
    with
    | Triple.File_exists s -> Common.warning_msg "file exists: \"%s\"" s
    | Triple.Lock_failed -> Common.warning_msg "fact buffer is already locked."


end (* of functor Astml.Fact.CCX *)
]
