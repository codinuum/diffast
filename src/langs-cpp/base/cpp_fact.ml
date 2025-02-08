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

(* fact extractor *)

[%%prepare_logger]

module Xset = Diffast_misc.Xset
module Xprint = Diffast_misc.Xprint
module Binding = Diffast_misc.Binding
module Sourcecode = Diffast_core.Sourcecode
module Fact_base = Diffast_core.Fact_base
module Triple = Diffast_core.Triple
module Astml = Diffast_core.Astml

module Label = Cpp_label
module Tree = Cpp_tree

module A = Astml
module B = Binding

[%%capture_path
module F (L : Label.T) = struct

  module FB = Fact_base.F(L)
  open FB

  let getlab = getlab

  let p_in_translation_unit = mkcppres "inTranslationUnit"
  let p_in_decl             = mkcppres "inDeclaration"
  let p_in_simple_decl      = mkcppres "inSimpleDeclaration"
  let p_in_func             = mkcppres "inFunctionDefinition"
  let p_in_stmt             = mkcppres "inStatement"
  let p_in_decl_stmt        = mkcppres "inDeclarationStatement"
  let p_in_comp_stmt        = mkcppres "inCompoundStatement"
  let p_in_try_block        = mkcppres "inTryBlock"
  let p_in_if               = mkcppres "inIfStatement"
  let p_in_switch           = mkcppres "inSwitchStatement"
  let p_in_while            = mkcppres "inWhileStatement"
  let p_in_do               = mkcppres "inDoStatement"
  let p_in_for              = mkcppres "inForStatement"
  let p_in_ranged_for       = mkcppres "inRangeBasedForStatemennt"

  let p_in_container_unit   = mkcppres "inContainerUnit"

  let p_in_pp_if_section    = mkcppres "inPpIfSection"
  let p_in_pp_group         = mkcppres "inPpGroup"
  let p_in_pp_if_group      = mkcppres "inPpIfGroup"
  let p_in_pp_elif_group    = mkcppres "inPpElifGroup"
  let p_in_pp_else_group    = mkcppres "inPpElseGroup"

  let p_in_return           = mkcppres "inReturnStatement"
  let p_in_call             = mkcppres "inCall"
  let p_in_parameters       = mkcppres "inParameters"
  let p_in_arguments        = mkcppres "inArguments"

  let p_lhs                 = mkcppres "lhs"
  let p_rhs                 = mkcppres "rhs"

  let p_cond_of             = mkcppres "conditionOf"
  let p_then_part_of        = mkcppres "thenPartOf"
  let p_else_part_of        = mkcppres "elsePartOf"

  let p_name      = mkcppres "name"
  let p_path      = mkcppres "path"
  let p_regexp    = mkcppres "regexp"
  let p_value     = mkcppres "value"

  let p_type_spec   = mkcppres "typeSpecifier"
  let p_member      = mkcppres "member"
  let p_member_name = mkcppres "memberName"

  let p_type      = mkcppres "type"

  let p_requires  = mkcppres "requires"
  let p_provides  = mkcppres "provides"

  let p_declared_by = mkcppres "declaredBy"
  let p_refers_to   = mkcppres "refersTo"

  let p_successor   = mkcppres "successor"


  let node_filter options nd = (* filter out inactive nodes *)
    if options#fact_restricted_flag then
      let lab = getlab nd in
      L.is_decl lab ||
      L.is_func lab ||
      false
    else
      true

  let node_pair_filter options nd1 nd2 =
    (node_filter options nd1) && (node_filter options nd2)

  let get_params nd =
    let params = ref [] in
    begin
      try
	Array.iter
	  (fun cnd ->
	    if L.is_dtor (getlab cnd) then
	      let pnd = find_node L.is_param_decl_clause cnd in
	      params := Array.to_list pnd#initial_children
	  ) nd#initial_children
      with
	Not_found -> ()
    end;
    !params

  let is_static nd =
    try
      ignore (find_node L.is_static nd);
      true
    with
      Not_found -> false

  let is_extern nd =
    try
      ignore (find_node L.is_extern nd);
      true
    with
      Not_found -> false


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


  class extractor options cache_path tree = object (self)
    inherit extractor_base options cache_path tree as super

    method! id = "Cpp"


    method! mkextname n = super#mkextname n

    method! scanner_body_after_subscan nd lab entity =

      if node_filter options nd then begin

	self#add (entity, p_is_a, mkcppres nd#data#get_category);
(*	self#add (entity, p_file_digest, tree#encoded_source_digest); *)

        begin
          try
            Array.iteri
              (fun i c ->
                let nth = nd#data#get_ordinal i in
                self#add (entity, p_childx nth, self#mkentity c)
              ) nd#initial_children
          with
            Not_found ->
              Array.iter
                (fun c ->
                  self#add (entity, p_child0, self#mkentity c)
                ) nd#initial_children
        end;

        begin
          Xset.iter
            (fun succ ->
              self#add (entity, p_successor, self#mkentity succ)
            ) nd#data#successors
        end;

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
              | Label.Annotation.Type s ->
                  self#add (entity, p_type, mklit s)
            ) a
        end;

        if
          L.is_translation_unit lab
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
          try
            let path = L.get_pp_include_path lab in
            self#add (entity, p_path, mklit path)
          with
            Not_found -> ()
        end;

        if L.is_named_orig lab then begin
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
            let ty, v =
              if L.is_int_literal lab then
                lit_ty_int, (L.get_value lab)
              else if L.is_real_literal lab then
                lit_ty_real, (L.get_value lab)
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

        (*if L.is_func lab then begin
          let func_name = nd#data#get_name in
          self#add (entity, p_provides, mklit func_name);
        end;*)

        self#add_surrounding_xxx L.is_translation_unit nd entity p_in_translation_unit;

        self#add_surrounding_xxx L.is_decl nd entity p_in_decl;
        self#add_surrounding_xxx L.is_func nd entity p_in_func;

        self#add_surrounding_xxx L.is_for nd entity p_in_for;
        self#add_surrounding_xxx L.is_ranged_for nd entity p_in_ranged_for;
        self#add_surrounding_xxx L.is_do nd entity p_in_do;
        self#add_surrounding_xxx L.is_while nd entity p_in_while;
        self#add_surrounding_xxx L.is_switch nd entity p_in_switch;
        self#add_surrounding_xxx L.is_if nd entity p_in_if;
        self#add_surrounding_xxx L.is_return nd entity p_in_return;
        self#add_surrounding_xxx L.is_decl_stmt nd entity p_in_decl_stmt;
        self#add_surrounding_xxx L.is_comp_stmt nd entity p_in_comp_stmt;
        self#add_surrounding_xxx L.is_stmt nd entity p_in_stmt;

        self#add_surrounding_xxx L.is_try_block nd entity p_in_try_block;
        self#add_surrounding_xxx L.is_simple_decl nd entity p_in_simple_decl;

        self#add_surrounding_xxx L.is_container_unit nd entity p_in_container_unit;

        self#add_surrounding_xxx L.is_pp_if_section nd entity p_in_pp_if_section;
        self#add_surrounding_xxx L.is_pp_if_group nd entity p_in_pp_if_group;
        self#add_surrounding_xxx L.is_pp_elif_group nd entity p_in_pp_elif_group;
        self#add_surrounding_xxx L.is_pp_else_group nd entity p_in_pp_else_group;

      end;


  end (* of class Cpp.Fact.F.extractor *)

  let warning_msg = Xprint.warning ~head:"[Cpp]"

  (* main function *)
  let extract options cache_path tree =
    try
      let extractor = new extractor options cache_path tree in
      extractor#set_lang_prefix Astml.cpp_prefix;
      extractor#extract
    with
    | Triple.File_exists s -> warning_msg "file exists: \"%s\"" s
    | Triple.Lock_failed -> warning_msg "fact buffer is already locked."


end (* of functor Fortran.Fact.F *)
]
