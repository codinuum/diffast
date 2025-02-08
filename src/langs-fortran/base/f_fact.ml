(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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

(* fact extractor *)

module Binding = Diffast_misc.Binding
module Astml = Diffast_core.Astml
module Triple = Diffast_core.Triple
module Fact_base = Diffast_core.Fact_base
module Common = Fortran_parsing.Common
module Pinfo = Fortran_parsing.Pinfo

module Label = F_label
module Tree = F_tree

module A = Astml
module B = Binding

module F (L : Label.T) = struct

  module FB = Fact_base.F(L)
  open FB

  let getlab = getlab

  let p_in_module         = mkfres "inModule"
  let p_in_ext_function   = mkfres "inFunctionExternalSubprogram"
  let p_in_ext_subroutine = mkfres "inSubroutineExternalSubprogram"
  let p_in_mod_function   = mkfres "inFunctionModuleSubprogram"
  let p_in_mod_subroutine = mkfres "inSubroutineModuleSubprogram"
  let p_in_int_function   = mkfres "inFunctionInternalSubprogram"
  let p_in_int_subroutine = mkfres "inSubroutineInternalSubprogram"
  let p_in_main_program   = mkfres "inMainProgram"
  let p_in_block_data     = mkfres "inBlockData"
  let p_in_stmt           = mkfres "inStmt"
  let p_in_fragment       = mkfres "inFragment"
  let p_in_execution_part = mkfres "inExecutionPart"
  let p_in_subprogram_part = mkfres "inSubprogramPart"

  let p_in_do_construct          = mkfres "inDoConstruct"
  let p_in_case_construct        = mkfres "inCaseConstruct"
  let p_in_forall_construct      = mkfres "inForallConstruct"
  let p_in_if_construct          = mkfres "inIfConstruct"
  let p_in_where_construct       = mkfres "inWhereConstruct"
  let p_in_select_type_construct = mkfres "inSelectTypeConstruct"
  let p_in_associate_construct   = mkfres "inAssociateConstruct"
  let p_in_block_construct       = mkfres "inBlockConstruct"
  let p_in_critical_construct    = mkfres "inCriticalConstruct"

  let p_in_derived_type_def = mkfres "inDerivedTypeDef"
  let p_in_interface_block  = mkfres "inInterfaceBlock"

  let p_in_if_then_block    = mkfres "inIfThenBlock"
  let p_in_else_block       = mkfres "inElseBlock"
  let p_in_else_if_block    = mkfres "inElseIfBlock"
  let p_in_where_block      = mkfres "inWhereBlock"
  let p_in_case_block       = mkfres "inCaseBlock"
  let p_in_type_guard_block = mkfres "inTypeGuardBlock"
  let p_in_do_block         = mkfres "inDoBlock"

  let p_in_pp_branch            = mkfres "inPpBranch"
  let p_in_pp_branch_do         = mkfres "inPpBranchDo"
  let p_in_pp_branch_end_do     = mkfres "inPpBranchEndDo"
  let p_in_pp_branch_if         = mkfres "inPpBranchIf"
  let p_in_pp_branch_end_if     = mkfres "inPpBranchEndIf"
  let p_in_pp_branch_forall     = mkfres "inPpBranchForall"
  let p_in_pp_branch_end_forall = mkfres "inPpBranchEndForall"
  let p_in_pp_branch_where      = mkfres "inPpBranchWhere"
  let p_in_pp_branch_end_where  = mkfres "inPpBranchEndWhere"
  let p_in_pp_branch_select     = mkfres "inPpBranchSelect"
  let p_in_pp_branch_end_select = mkfres "inPpBranchEndSelect"

  let p_in_pp_section_ifdef  = mkfres "inPpSectionIfdef"
  let p_in_pp_section_ifndef = mkfres "inPpSectionIfndef"
  let p_in_pp_section_if     = mkfres "inPpSectionIf"
  let p_in_pp_section_elif   = mkfres "inPpSectionElif"
  let p_in_pp_section_else   = mkfres "inPpSectionElse"

  let p_in_omp_construct = mkfres "inOmpConstruct"
  let p_in_acc_construct = mkfres "inAccConstruct"

  let p_in_container_unit = mkfres "inContainerUnit"
  let p_in_pu_or_fragment = mkfres "inProgramUnitOrFragment"
  let p_in_pu_or_sp       = mkfres "inProgramUnitOrSubprogram"

  let p_name      = mkfres "name"
  let p_label     = mkfres "label"
  let p_slabel    = mkfres "slabel"
  let p_regexp    = mkfres "regexp"
  let p_value     = mkfres "value"
  let p_variable  = mkfres "variableName"
  let p_rank      = mkfres "rank"
  let p_requires  = mkfres "requires"
  let p_provides  = mkfres "provides"
  let p_type_spec = mkfres "typeSpec"
  let p_path      = mkfres "path"
  let p_body      = mkfres "body"

  let node_filter options nd = (* filter out inactive nodes *)
    if options#fact_restricted_flag then
      let lab = getlab nd in
      L.is_stmt lab ||
      L.is_program_unit lab ||
      L.is_case_construct lab ||
      L.is_do_construct lab ||
      L.is_forall_construct lab ||
      L.is_if_construct lab ||
      L.is_where_construct lab ||
      L.is_derived_type_def lab ||
      L.is_interface_block lab
    else
      true

  let node_pair_filter options nd1 nd2 =
    (node_filter options nd1) && (node_filter options nd2)

  let name_sep_pat = Str.regexp_string ";"

  let conv_pat =
    let pat_conv_tbl = [
      Str.regexp_string "\\(", "(";
      Str.regexp_string "\\)", ")";
      Str.regexp_string "\\|", "|";
    ]
    in
    fun x ->
      List.fold_left
        (fun s (re, rpl) ->
          Str.global_replace re rpl s
        ) x pat_conv_tbl

  let mkpat n = "^"^(conv_pat (String.lowercase_ascii n))^"$"

  let is_pat x = String.contains x '|'

  let rec has_subprogram nd =
    if L.is_subprogram (getlab nd) then
      true
    else
      Array.exists has_subprogram nd#initial_children


  class extractor options cache_path tree = object (self)
    inherit extractor_base options cache_path tree as super

    method! id = "Fortran"


    method! mkextname n = super#mkextname (String.lowercase_ascii n)

    method! scanner_body_after_subscan nd lab entity =

      if node_filter options nd then begin

	self#add (entity, p_is_a, mkfres nd#data#get_category);
(*	self#add (entity, p_file_digest, tree#encoded_source_digest); *)

        begin
          let a = (Obj.obj nd#data#_annotation : Label.annotation) in
          Label.Annotation.iter
            (function
              | Label.Annotation.Require ns ->
                  List.iter
                    (fun n ->
                      let en = self#mkextname n in
                      self#add (en, p_is_a, Triple.c_external_name);
                      self#add (en, p_name, mklit n);
                      self#add (entity, p_requires, en)
                    ) ns

              | Label.Annotation.Provide ns ->
                  List.iter
                    (fun _n ->
                      List.iter
                        (fun n ->
                          let en = self#mkextname n in
                          self#add (en, p_is_a, Triple.c_external_name);
                          if is_pat n then
                            self#add (en, p_regexp, mklit (mkpat n))
                          else
                            self#add (en, p_name, mklit n);
                          self#add (entity, p_provides, en)
                        ) (Str.split name_sep_pat _n)
                    ) ns

              | Label.Annotation.Spec nspec -> begin
                  begin
                    try
                      let spec = Pinfo.Name.Spec.get_data_object_spec nspec in
                      let tspec = spec#type_spec in
                      if Pinfo.TypeSpec.is_resolved tspec then begin
                        let tspec_lit = mklit (Pinfo.TypeSpec.to_string tspec) in
                        self#add (entity, p_type_spec, tspec_lit)
                      end;
                      let a = spec#attr in
                      try
                        let rank_lit = mklit ~ty:lit_ty_nn_int (string_of_int a#get_rank) in
                        self#add (entity, p_rank, rank_lit)
                      with
                        Failure _ -> ()
                    with
                      Not_found -> ()
                  end;
                  begin
                    try
                      let mnd = get_nearest_surrounding_xxx L.is_module nd in
                      if Pinfo.Name.Spec.is_public nspec then begin
                        try
                          List.iter
                            (fun x ->
                              let n = Tree.make_local_name (L.get_name (getlab mnd)) x in
                              let en = self#mkextname n in
                              self#add (en, p_is_a, Triple.c_external_name);
                              self#add (en, p_name, mklit n);
                              self#add (entity, p_provides, en)
                            ) (Str.split name_sep_pat (L.get_name lab))
                        with
                          _ -> ()
                      end
                    with
                      _ -> ()
                  end
              end
            ) a
        end;

        if
          L.is_program_unit lab ||
          L.is_program lab ||
          L.is_fragment lab ||
          L.is_subroutine lab ||
          L.is_function lab ||
          (L.is_pp_branch lab && has_subprogram nd)
        then begin
          let fent =
            let fid = nd#data#source_fid in
            if fid = "" then
              self#fileentity
            else
              Triple.mkent (Triple.___make_file_entity (Triple.get_enc_str options ()) fid)
          in
          self#add (entity, p_in_file, fent);
          self#set_version entity
        end;

        begin
          match L.to_tag lab with
          | "PpDefine", attrs -> begin
              try
                let body = List.assoc "body" attrs in
                self#add (entity, p_body, mklit body)
              with
                Not_found -> ()
          end
          | _ -> ()
        end;

        begin
          try
            let path = L.get_pp_include_path lab in
            self#add (entity, p_path, mklit path)
          with
            Not_found -> ()
        end;

        begin
          try
            List.iter
              (fun n ->
                self#add (entity, p_name, mklit n)
              ) (Str.split name_sep_pat (L.get_name lab))
          with
            Not_found -> ()
        end;

        begin
          try
            self#add (entity, p_label, mklit (L.get_label lab))
          with
            Not_found -> ()
        end;

        begin
          try
            self#add (entity, p_slabel, mklit (L.get_stmt_label lab))
          with
            Not_found -> ()
        end;

        begin
          try
            self#add (entity, p_variable, mklit (L.get_var lab))
          with
            Not_found -> ()
        end;


        let remove_kind s =
          try
            let p = String.index s '_' in
            String.sub s 0 p
          with
            Not_found -> s
        in
        let conv_int s = remove_kind s in
        let conv_real s =
          let s' = remove_kind s in
          String.map
            (function
              | 'D' | 'd' -> 'e'
              | x -> x
            ) s'
        in
        begin
          try
            let ty, v =
              if L.is_int_literal lab then
                lit_ty_int, conv_int (L.get_value lab)
              else if L.is_real_literal lab then
                lit_ty_real, conv_real (L.get_value lab)
              else
                lit_ty_string, (L.get_value lab)
            in
            self#add (entity, p_value, mklit ~ty:ty v)
          with
            Not_found -> ()
        end;

        (*let is_included =
          try
            nd#data#src_loc.Loc.filename <> tree#root#data#src_loc.Loc.filename
          with
            _ -> false
        in
        let loc_opt =
          if is_included then
            Some nd#data#src_loc
          else
            None
        in*)
        [%debug_log "nd=%s" nd#to_string];
        begin
          let b = nd#data#binding in
          match b with
          | B.Def(bid, _, _) ->
              [%debug_log "%a" B.ID.ps bid];
              self#add (entity, p_binding, self#mkbinding (*~loc_opt*) bid)
          | B.Use(bid, (*loc_opt*)_) ->
              [%debug_log "%a" B.ID.ps bid];
              self#add (entity, p_binding, self#mkbinding (*~loc_opt*) bid)
          | _ -> ()
        end;
        begin
          List.iter
            (fun b ->
              match b with
              | B.Def(bid, _, _) ->
                  [%debug_log "%a" B.ID.ps bid];
                  self#add (entity, p_binding, self#mkbinding (*~loc_opt*) bid)
              | B.Use(bid, (*loc_opt*)_) ->
                  [%debug_log "%a" B.ID.ps bid];
                  self#add (entity, p_binding, self#mkbinding (*~loc_opt*) bid)
              | _ -> ()
            ) nd#data#bindings
        end;

	self#add_surrounding_xxx L.is_fragment nd entity p_in_fragment;

	self#add_surrounding_xxx L.is_execution_part nd entity p_in_execution_part;

	self#add_surrounding_xxx L.is_subprogram_part nd entity p_in_subprogram_part;

	self#add_surrounding_xxx L.is_module nd entity p_in_module;
	self#add_surrounding_xxx L.is_main_program nd entity p_in_main_program;

	self#add_surrounding_xxx L.is_ext_function nd entity p_in_ext_function;
	self#add_surrounding_xxx L.is_ext_subroutine nd entity p_in_ext_subroutine;

	self#add_surrounding_xxx L.is_int_function nd entity p_in_int_function;
	self#add_surrounding_xxx L.is_int_subroutine nd entity p_in_int_subroutine;

	self#add_surrounding_xxx L.is_mod_function nd entity p_in_mod_function;
	self#add_surrounding_xxx L.is_mod_subroutine nd entity p_in_mod_subroutine;

	self#add_surrounding_xxx L.is_block_data nd entity p_in_block_data;
	self#add_surrounding_xxx L.is_stmt nd entity p_in_stmt;

	self#add_surrounding_xxx L.is_do_construct nd entity p_in_do_construct;
	self#add_surrounding_xxx L.is_case_construct nd entity p_in_case_construct;
	self#add_surrounding_xxx L.is_forall_construct nd entity p_in_forall_construct;
	self#add_surrounding_xxx L.is_if_construct nd entity p_in_if_construct;
	self#add_surrounding_xxx L.is_where_construct nd entity p_in_where_construct;
	self#add_surrounding_xxx L.is_select_type_construct nd entity p_in_select_type_construct;
	self#add_surrounding_xxx L.is_associate_construct nd entity p_in_associate_construct;
	self#add_surrounding_xxx L.is_block_construct nd entity p_in_block_construct;
	self#add_surrounding_xxx L.is_critical_construct nd entity p_in_critical_construct;

	self#add_surrounding_xxx L.is_derived_type_def nd entity p_in_derived_type_def;
	self#add_surrounding_xxx L.is_interface_block nd entity p_in_interface_block;

        self#add_surrounding_xxx L.is_if_then_block nd entity p_in_if_then_block;
        self#add_surrounding_xxx L.is_else_block nd entity p_in_else_block;
        self#add_surrounding_xxx L.is_else_if_block nd entity p_in_else_if_block;
        self#add_surrounding_xxx L.is_where_block nd entity p_in_where_block;
        self#add_surrounding_xxx L.is_case_block nd entity p_in_case_block;
        self#add_surrounding_xxx L.is_type_guard_block nd entity p_in_type_guard_block;
        self#add_surrounding_xxx L.is_do_block nd entity p_in_do_block;

        self#add_surrounding_xxx L.is_pp_branch nd entity p_in_pp_branch;
        self#add_surrounding_xxx L.is_pp_branch_do nd entity p_in_pp_branch_do;
        self#add_surrounding_xxx L.is_pp_branch_end_do nd entity p_in_pp_branch_end_do;
        self#add_surrounding_xxx L.is_pp_branch_if nd entity p_in_pp_branch_if;
        self#add_surrounding_xxx L.is_pp_branch_end_if nd entity p_in_pp_branch_end_if;
        self#add_surrounding_xxx L.is_pp_branch_forall nd entity p_in_pp_branch_forall;
        self#add_surrounding_xxx L.is_pp_branch_end_forall nd entity p_in_pp_branch_end_forall;
        self#add_surrounding_xxx L.is_pp_branch_where nd entity p_in_pp_branch_where;
        self#add_surrounding_xxx L.is_pp_branch_end_where nd entity p_in_pp_branch_end_where;
        self#add_surrounding_xxx L.is_pp_branch_select nd entity p_in_pp_branch_select;
        self#add_surrounding_xxx L.is_pp_branch_end_select nd entity p_in_pp_branch_end_select;

        self#add_surrounding_xxx L.is_pp_section_ifdef nd entity p_in_pp_section_ifdef;
        self#add_surrounding_xxx L.is_pp_section_ifndef nd entity p_in_pp_section_ifndef;
        self#add_surrounding_xxx L.is_pp_section_if nd entity p_in_pp_section_if;
        self#add_surrounding_xxx L.is_pp_section_elif nd entity p_in_pp_section_elif;
        self#add_surrounding_xxx L.is_pp_section_else nd entity p_in_pp_section_else;

        self#add_surrounding_xxx L.is_omp_construct nd entity p_in_omp_construct;
        self#add_surrounding_xxx L.is_acc_construct nd entity p_in_acc_construct;

        self#add_surrounding_xxx L.is_container_unit nd entity p_in_container_unit;

        self#add_surrounding_xxx L.is_program_unit_or_fragment nd entity p_in_pu_or_fragment;
        self#add_surrounding_xxx L.is_program_unit_or_subprogram nd entity p_in_pu_or_sp;
      end;


  end (* of class Fortran.Fact.F.extractor *)


  (* main function *)
  let extract options cache_path tree =
    try
      let extractor = new extractor options cache_path tree in
      extractor#set_lang_prefix Astml.fortran_prefix;
      extractor#extract
    with
    | Triple.File_exists s -> Common.warning_msg "file exists: \"%s\"" s
    | Triple.Lock_failed -> Common.warning_msg "fact buffer is already locked."


end (* of functor Fortran.Fact.F *)
