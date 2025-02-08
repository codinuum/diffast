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

module Xlist = Diffast_misc.Xlist
module Xset = Diffast_misc.Xset
module Loc = Diffast_misc.Loc
module Astml = Diffast_core.Astml
module Fact_base = Diffast_core.Fact_base
module Sourcecode = Diffast_core.Sourcecode
module Triple = Diffast_core.Triple
module L = Java_label
module Tree = Java_tree

module Common = Java_parsing.Common

module FB = Fact_base.F(L)
open FB

let p_provides       = mkjres "provides"
let p_fqn            = mkjres "fullyQualifiedName"
let p_uqn            = mkjres "unqualifiedName"
let p_in_class       = mkjres "inClass"
let p_in_interface   = mkjres "inInterface"
let p_in_method      = mkjres "inMethod"
let p_in_constructor = mkjres "inConstructor"
let p_in_statement   = mkjres "inStatement"
let p_in_invocation  = mkjres "inInvocation"
let p_in_instance_creation = mkjres "inInstanceCreation"
let p_in_method_invocation = mkjres "inMethodInvocation"
let p_in_ctor_invocation   = mkjres "inCtorInvocation"
let p_in_field       = mkjres "inField"
let p_in_enum        = mkjres "inEnum"
let p_in_extends     = mkjres "inExtends"
let p_in_throws      = mkjres "inThrows"
let p_in_return_type = mkjres "inReturnType"
let p_in_variable_declaration = mkjres "inVariableDeclaration"
let p_in_parameter   = mkjres "inParameter"
let p_in_staticinit  = mkjres "inStaticInitializer"
let p_in_instanceinit = mkjres "inInstanceInitializer"
let p_cond_of        = mkjres "conditionOf"
let p_then_part_of   = mkjres "thenPartOf"
let p_else_part_of   = mkjres "elsePartOf"
let p_name           = mkjres "name"
let p_dimensions     = mkjres "dimensions"
let p_extended_name  = mkjres "extendedName"
let p_signature      = mkjres "signature"
let p_initializer    = mkjres "initializer"
let p_declared_by    = mkjres "declaredBy"
let p_requires       = mkjres "requires"
let p_successor      = mkjres "successor"

let p_nparams    = mkjres "nParameters"
let p_nargs      = mkjres "nArguments"
let p_is_va_meth = mkjres "isVariableArityMethod"
let p_is_abst    = mkjres "isAbstract"

let p_identifier = mkjres "identifier"
let p_qualifier  = mkjres "qualifier"

let p_id_offset = mkjres "identOffset"
let p_id_length = mkjres "identLength"
let p_expr_offset = mkjres "exprOffset"
let p_expr_length = mkjres "exprLength"

let getlab = getlab

let node_filter options nd = (* filter out inactive nodes *)
  if options#fact_restricted_flag then
    let lab = getlab nd in
(*      L.is_statement lab || *)
(*      L.is_block lab || *)
(*      L.is_class lab || *)
(*      L.is_interface lab || *)
(*      L.is_enum lab || *)
    L.is_method lab ||
    L.is_field lab ||
    L.is_ctor lab ||
(*      L.is_staticinit lab || *)
(*      L.is_instanceinit lab || *)
(*      L.is_invocation_or_instance_creation lab *)
    false

  else
    true


let xxx_to_simple_name c n =
  try
    let i = String.index n c in
    String.sub n 0 i
  with
    Not_found -> n

let signature_to_simple_name n =
  xxx_to_simple_name '(' n

let extended_name_to_simple_name n =
  xxx_to_simple_name '#' n


let node_pair_filter options nd1 nd2 =
  (if options#fact_restricted_flag then
    (try
      let plab = getlab nd2#initial_parent in
      L.is_variabledeclarator plab && nd2#pos = 0
    with
      _ -> false
    )
  else
    true
  ) ||
  ((node_filter options nd1) && (node_filter options nd2))


let get_fqn = Tree.get_fqn

let is_argument nd =
  try
    L.is_arguments (getlab nd#initial_parent)
  with
    _ -> false

let find is_xxx children =
  let idx = ref (-1) in
  begin
    try
      Array.iteri
        (fun i nd ->
          if is_xxx (getlab nd) then begin
            idx := i;
            raise Exit
          end
        ) children
    with
      Exit -> ()
  end;
  if !idx >= 0 then
    children.(!idx)
  else
    raise Not_found

let get_logical_nth_child nd nth =
  let l = ref [] in
  Array.iteri
    (fun i x ->
      if (nd#data#get_ordinal i) = nth then
        l := x :: !l
    ) nd#initial_children;
  List.rev !l

[%%capture_path
class extractor options cache_path tree = object (self)
  inherit extractor_base options cache_path tree(* as super*)

  method! id = "Java"

  val mutable package_name = ""

  val stack = new Sourcecode.stack


  method! scanner_body_before_subscan nd lab (*entity*)_ =
    if L.is_scope_creating lab then
      stack#push nd;

    if L.is_packagedeclaration lab then
      package_name <- L.get_name lab


  method! scanner_body_after_subscan nd lab entity =
    if L.is_scope_creating lab then
      stack#pop;

    if node_filter options nd then begin
      self#add (entity, p_is_a, mkjres nd#data#get_category);
      (* self#add (entity, p_file_digest, tree#encoded_source_digest); *)

      begin
        let id_loc = nd#data#id_loc in
        if id_loc != Loc.dummy then begin
          let offset = id_loc.Loc.start_offset in
          let length = id_loc.Loc.end_offset - offset + 1 in
          self#add (entity, p_id_offset, Triple.make_nn_int_literal offset);
          self#add (entity, p_id_length, Triple.make_nn_int_literal length);
        end
      end;
      if L.is_expression lab then begin
        let loc = nd#data#src_loc in
        if loc != Loc.dummy then begin
          let offset = loc.Loc.start_offset in
          let length = loc.Loc.end_offset - offset + 1 in
          self#add (entity, p_expr_offset, Triple.make_nn_int_literal offset);
          self#add (entity, p_expr_length, Triple.make_nn_int_literal length);
        end
      end;

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

      if L.is_compilationunit lab then begin
        self#add (entity, p_in_file, self#fileentity);
      end;

      if L.is_typedeclaration lab then begin
        self#add (entity, p_in_file, self#fileentity);
        self#add (entity, p_name, mklit (L.get_name lab));
        let fqn = get_fqn package_name nd lab in
        self#add (entity, p_fqn, mklit fqn);
        let en = self#mkextname fqn in
        self#add (en, p_is_a, Triple.c_external_name);
        self#add (entity, p_provides, en);
        self#set_version entity;
(*
  stack#register_global fqn nd
 *)
      end;

      begin
        try
          let c_or_i = get_nearest_surrounding_xxx L.is_class_or_interface nd in
          if L.is_class (getlab c_or_i) then
            self#add (entity, p_in_class, self#mkentity c_or_i)
          else
            self#add (entity, p_in_interface, self#mkentity c_or_i)
        with
          Not_found -> ()
      end;

      if L.is_method lab || L.is_ctor lab then begin
        let signature = L.annotation_to_string (Tree.get_annotation nd) in
        self#add (entity, p_signature, mklit signature);
        let name =
          if L.is_ctor lab then
            "<init>"
          else
            L.get_name lab
        in
        self#add (entity, p_name, mklit name);

        let nparams = ref 0 in
        let is_va = ref false in
        begin
          try
            Array.iter
              (fun c ->
                if L.is_parameters (getlab c) then begin
                  nparams := Array.length c#initial_children;
                  let last_param = c#initial_children.(!nparams - 1) in
                  is_va := L.is_va_parameter (getlab last_param);
                  raise Exit
                end
              ) nd#initial_children
          with
            Exit -> ()
        end;

        self#add (entity, p_nparams, Triple.make_nn_int_literal !nparams);
        self#add (entity, p_extended_name, mklit (Printf.sprintf "%s#%d" name !nparams));
        if !is_va then
          self#add (entity, p_is_va_meth, Triple.l_true);

        begin
          let is_abst =
            L.is_method lab &&
            try
              match Sourcecode.get_logical_nth_child nd 6 with
              | [||] -> true
              | _ -> false
            with _ -> true
          in
          if is_abst then
            self#add (entity, p_is_abst, Triple.l_true);
        end;

(*
  stack#register name nd;
 *)
        let fqn = get_fqn package_name nd lab in
        self#add (entity, p_fqn, mklit fqn);
        let en = self#mkextname fqn in
        self#add (en, p_is_a, Triple.c_external_name);
        self#add (entity, p_provides, en);
(*
  stack#register_global fqn nd
 *)
      end
      else begin
        self#add_surrounding_xxx L.is_method nd entity p_in_method;
        self#add_surrounding_xxx L.is_ctor nd entity p_in_constructor;
      end;

      if (L.is_field lab) then begin
        let name = L.get_name lab in
        self#add (entity, p_name, mklit name);

        let is_private =
          List.exists
            (fun n ->
              [%debug_log "%s" n#data#label];
              match getlab n with
              | L.Modifiers _ -> begin
                  Array.exists
                    (fun c ->
                      match getlab c with
                      | L.Modifier L.Modifier.Private -> true
                      | _ -> false
                    ) n#initial_children
              end
              | _ -> false
            ) (get_logical_nth_child nd 0)
        in
        [%debug_log "name=\"%s\" is_private=%B" name is_private];
        if is_private then
          stack#register name nd
        else begin
          let fqn = get_fqn package_name nd lab in
          self#add (entity, p_fqn, mklit fqn);
          let en = self#mkextname fqn in
          self#add (en, p_is_a, Triple.c_external_name);
          self#add (entity, p_provides, en)
        end;
(*
  stack#register_global fqn nd
 *)
      end
      else
        self#add_surrounding_xxx L.is_field nd entity p_in_field;

      self#add_surrounding_xxx L.is_statement nd entity p_in_statement;

      self#add_surrounding_xxx L.is_parameter nd entity p_in_parameter;

      self#add_surrounding_xxx L.is_invocation nd entity p_in_invocation;
      self#add_surrounding_xxx L.is_instance_creation nd entity p_in_instance_creation;
(*
  self#add_surrounding_xxx L.is_method_invocation nd entity p_in_method_invocation;
  self#add_surrounding_xxx L.is_ctor_invocation nd entity p_in_ctor_invocation;
 *)
      if L.is_invocation_or_instance_creation lab(* && L.is_named lab*) then begin
        let ename = try L.get_name lab with Not_found -> "" in
        if ename <> "" then begin
          self#add (entity, p_extended_name, mklit ename);
          let esn = extended_name_to_simple_name ename in
          self#add (entity, p_name, mklit esn);
          if String.contains esn '.' then
            self#add (entity, p_uqn, mklit (Xlist.last (String.split_on_char '.' esn)))
        end;

        let n =
          try
            let i = String.index ename '#' in
            String.sub ename (i+1) ((String.length ename) - i - 1)
          with
            _ ->
              try
                let args = find L.is_arguments nd#initial_children in
                string_of_int (Array.length args#initial_children)
              with
                _ -> ""
        in
        if n <> "" then
          self#add (entity, p_nargs, Triple.make_literal ~ty:Triple.LT_int n)
      end;

      if L.is_parameter lab || is_argument nd then begin
        self#add (entity, Triple.p_nth, Triple.make_nn_int_literal nd#initial_pos)
      end;

      if L.is_parameter lab || L.is_catch_parameter lab then begin
        self#add (entity, p_dimensions, Triple.make_nn_int_literal (L.get_dims lab))
      end;

      if not (L.is_enum lab) then
        self#add_surrounding_xxx L.is_enum nd entity p_in_enum;

      if not (L.is_extends lab) then
        self#add_surrounding_xxx L.is_extends nd entity p_in_extends;

      if not (L.is_throws lab) then
        self#add_surrounding_xxx L.is_throws nd entity p_in_throws;

      if not (L.is_localvariabledecl lab) then
        self#add_surrounding_xxx L.is_localvariabledecl nd entity
          p_in_variable_declaration;

      if L.is_fieldaccess lab then
        self#add (entity, p_name, mklit (L.get_name lab));

      if L.is_qualifier lab && L.is_name lab then
        self#add (entity, p_name, mklit (L.get_name lab));

      if L.is_parameter lab then begin
        let name = L.get_name lab in
        stack#register name nd;
        self#add (entity, p_name, mklit name)
      end;

      if L.is_if lab then begin
        self#add (self#mkentity nd#initial_children.(0), p_cond_of, entity);
        let then_nd = nd#initial_children.(1) in
        self#add (self#mkentity then_nd, p_then_part_of, entity);
        if nd#initial_nchildren > 2 then
          let else_nd = nd#initial_children.(2) in
          self#add (self#mkentity else_nd, p_else_part_of, entity)
      end;

      if L.is_variabledeclarator lab then begin
        if L.is_localvariabledecl (getlab nd#initial_parent) then begin
          let name = L.get_name lab in
          stack#register name nd
        end;
        if nd#initial_nchildren > 0 then
          let rhs_nd = nd#initial_children.(0) in
          self#add (entity, p_initializer, self#mkentity rhs_nd);
      end;

      (*if L.is_resource lab then begin
        let name = L.get_name lab in
        stack#register name nd
      end;*)

      if L.is_primaryname lab then begin
        let name = L.get_name lab in
        try
          self#add (entity, p_declared_by, self#mkentity (stack#lookup name))
        with
          Not_found ->
            let en = self#mkextname name in
            self#add (en, p_is_a, Triple.c_external_name);
            self#add (entity, p_requires, en)
      end;

      if L.is_named lab && L.is_type lab then begin
        let n = L.get_name lab in
        self#add (entity, p_name, mklit n);

        let s =
          try
            String.sub n 0 (String.index n '<')
          with
            _ -> n
        in
        let ln0 = Xlist.last (String.split_on_char '.' s) in
        let ln = Xlist.last (String.split_on_char '$' ln0) in
        self#add (entity, p_uqn, mklit ln);

      end;

      if L.is_type lab then begin
        let dims = L.get_dimensions lab in
        if dims > 0 then
          self#add (entity, p_dimensions, Triple.make_nn_int_literal dims)
      end;

      if L.is_named_orig lab then
        if L.is_method lab || L.is_ctor lab || L.is_invocation_or_instance_creation lab then
          ()
        else
          self#add (entity, p_name, mklit (L.get_name lab));

      if L.is_ambiguous_name lab then begin
        let n = L.get_name lab in
        let q, i =
          match List.rev (String.split_on_char '.' n) with
          | [] | [_] -> "", n
          | h0 :: h1 :: _ -> h1, h0
        in
        self#add (entity, p_identifier, mklit i);
        if q <> "" then
          self#add (entity, p_qualifier, mklit q);
      end;

      self#add_surrounding_xxx L.is_staticinit nd entity p_in_staticinit;
      self#add_surrounding_xxx L.is_instanceinit nd entity p_in_instanceinit;
    end

end (* of class Java.Fact.extractor *)
]

(* main function *)
let extract options cache_path tree =
  try
    let extractor = new extractor options cache_path tree in
    extractor#set_lang_prefix Astml.java_prefix;
    extractor#extract
  with
  | Triple.File_exists s -> Common.warning_msg "file exists: \"%s\"" s
  | Triple.Lock_failed -> Common.warning_msg "fact buffer is already locked."
