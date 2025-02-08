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

(* Disambiguate AST *)

[%%prepare_logger]

module Loc = Diffast_misc.Loc
module UID = Diffast_misc.UID


[%%capture_path
module F (Stat : Parser_aux.STATE_T) = struct

  module Loc_ = Loc

  open Stat
  open Ast
  open Common
  open Labels

  module L = Label
  module I = Pinfo
  module N = I.Name
  module Aux = Parser_aux.F(Stat)

  let sprintf = Printf.sprintf

  let loc_to_str = Astloc.to_string ~short:false

  let get_part_names =
    Xlist.filter_map
      (fun nd ->
        match nd#label with
        | L.PartName n -> Some n
        | _ -> None
      )

  let get_name_of_part_names nodes =
    String.concat "%" (get_part_names nodes)


  let separate_image_selectors node_list = (* image-selectors * others *)
    List.partition
      (fun nd ->
        match nd#label with
        | L.ImageSelector -> true
        | _ -> false
      ) node_list


  let lookup_structure_component node_list =
    let names = Xlist.filter_map (fun nd -> nd#get_name_opt) node_list in
    [%debug_log "searching \"%s\"" (Xlist.to_string (fun x -> x) "%" names)];

    let lookup f name =
      let dspec =
        try
          f name
        with
          Not_found ->
            match env#lookup_name ~afilt:N.Spec.is_data_object_spec name with
            | [] -> raise Not_found
            | s::_ -> s
      in
      let f' =
        try
          let tname = I.TypeSpec.get_name (N.Spec.get_data_object_spec dspec)#type_spec in
          let tspec =
            try
              f tname
            with
              Not_found ->
                match env#lookup_name ~afilt:N.Spec.is_derived_type tname with
                | [] -> raise Not_found
                | ts::_ -> ts
          in
          N.Spec.get_finder tspec
        with
          Not_found -> (fun _ -> raise Not_found)
      in
      (Some dspec), f'
    in
    let spec_opt, _ =
      List.fold_left (fun (_, f) n -> lookup f n) (None, fun _ -> raise Not_found) names
    in
    match spec_opt with
    | Some spec -> spec
    | None -> raise Not_found


  let set_binding_of_subobject node =
    let last_part_name_node = ref None in
    List.iter
      (fun nd ->
        match nd#label with
        | L.PartName _ -> last_part_name_node := Some nd
        | _ -> ()
      ) node#children;
    match !last_part_name_node with
    | Some nd -> node#set_binding nd#binding
    | _ -> ()


  let set_binding node =
    try
      let name = node#get_name in
      match env#lookup_name ~afilt:N.Spec.is_data_object_spec name with
      | [] -> node#set_info (I.make (env#lookup_name name))
      | spec::_ as specs ->
          begin
            try
              let dospec = N.Spec.get_data_object_spec spec in
              match dospec#bid_opt with
              | Some bid -> node#set_binding (B.make_use bid)
              | _ -> ()
            with
              Not_found -> node#set_info (I.make specs)
          end
    with
      Not_found -> ()

  let conv_loc
      { Ast.Loc.filename     = fn;
        Ast.Loc.start_offset = so;
        Ast.Loc.end_offset   = eo;
        Ast.Loc.start_line   = sl;
        Ast.Loc.start_char   = sc;
        Ast.Loc.end_line     = el;
        Ast.Loc.end_char     = ec;
      } =
    Loc_.make ~fname:fn so eo sl sc el ec

  let set_binding_of_subprogram_reference ?(defer=true) node =
    [%debug_log "defer=%B" defer];
    try
      let name = node#get_name in
      [%debug_log "name=\"%s\"" name];
      let allow_implicit = not defer in
      match env#lookup_name ~allow_implicit ~afilt:N.Spec.has_object_spec name with
      | [] -> begin
          if defer then begin
            env#register_ambiguous_node node
          end
          else begin
            match env#lookup_name ~afilt:N.Spec.is_external name with
            | [] -> node#set_info (I.mkext "" name)
            | specs -> node#set_info (I.make specs)
          end
      end
      | spec::_ -> begin
          [%debug_log "spec=%s" (N.Spec.to_string spec)];
          let ospec = N.Spec.get_object_spec spec in
          [%debug_log "ospec=%s" ospec#to_string];
          try
            match ospec#bid_opt with
            | Some bid -> begin
                let b =
                  try
                    let loc_def = N.Spec.loc_of_decl_to_loc ospec#loc_of_decl in
                    let id_def = ospec#id_of_decl in
                    [%debug_log "node#loc: %s" (Loc.to_string node#loc)];
                    if loc_def <> node#loc then begin
                      B.make_use ~loc_opt:(Some (UID.of_int id_def, conv_loc loc_def)) bid
                    end
                    else
                      B.make_use bid
                  with
                    Not_found -> B.make_use bid
                in
                node#set_binding b
            end
            | _ -> if defer then env#register_ambiguous_node node
          with
            Not_found -> if defer then env#register_ambiguous_node node
      end
    with
      Not_found -> ()


  let rec find_resolved_spec = function
    | [] -> raise Not_found
    | spec::rest ->
        let resolved = N.Spec.is_resolved spec in
        [%debug_log "spec: %s (%sresolved)" (N.Spec.to_string spec) (if resolved then "" else "not ")];
        if resolved then
          spec
        else
          find_resolved_spec rest


  let get_rank_of_name name =
    let filt s =
      N.Spec.has_data_object_attr s || N.Spec.has_decl s || N.Spec.is_function s
    in
    match env#lookup_name ~afilt:filt name with
    | [] -> I.Rank.unknown
    | spec::_ -> begin
        [%debug_log "spec: %s" (N.Spec.to_string spec)];
        try
          let dim = (N.Spec.get_data_object_attr spec)#dimension in
          try
            I.Rank.mk (N.Dimension.get_rank dim)
          with
            Failure _ -> I.Rank.unknown
        with
          Not_found ->
            match spec with
            | N.Spec.IntrinsicFunction pspec ->
                pspec#rank
            | _ ->
                if N.Spec.has_decl spec then
                  I.Rank.zero
                else
                  I.Rank.unknown
    end

  let get_rank_of_structure_component node_list =
    [%debug_log "%s" (Xlist.to_string (fun n -> L.to_string n#label) "%" node_list)];
    let rank =
      try
        let spec = lookup_structure_component node_list in
        [%debug_log "spec found: %s" (N.Spec.to_string spec)];
        try
          let dim = (N.Spec.get_data_object_attr spec)#dimension in
          try
            I.Rank.mk (N.Dimension.get_rank dim)
          with
            Failure _ -> I.Rank.unknown
        with
          Not_found ->
            match spec with
            | N.Spec.IntrinsicFunction pspec ->
                pspec#rank
            | _ ->
                if N.Spec.has_decl spec then
                  I.Rank.zero
                else
                  I.Rank.unknown
      with
        Not_found -> I.Rank.unknown
    in
    [%debug_log "rank --> %s" (I.Rank.to_string rank)];
    rank

  let is_name_part nd = nd#has_name && nd#nchildren = 0
  let is_list_part nd = nd#nchildren > 0

  let rec get_rank node =
    [%debug_log "getting rank of %s" node#to_string];
    let rec get node =
      match node#label with
      | L.ArrayElement _ -> I.Rank.zero

      | L.ArraySection _
      | L.Ambiguous Ambiguous.Subobject
        -> get_rank_of_part_ref_elems node#children

      | L.Constant (Constant.BozLiteralConstant _
      | Constant.CharLiteralConstant _
      | Constant.ComplexLiteralConstant _
      | Constant.IntLiteralConstant _
      | Constant.LogicalLiteralConstant _
      | Constant.RealLiteralConstant _ ) -> I.Rank.zero

      | L.Name name
      | L.PartName name
      | L.VariableName name
      | L.FunctionReference name
      | L.Constant (Constant.NamedConstant name) -> get_rank_of_name name

      | L.ParenExpr | L.StartingPoint | L.EndingPoint -> begin
          match node#children with
          | [nd] -> get nd
          | _ -> assert false
      end
      | L.ArrayConstructor -> begin
          match node#children with
          | [] -> I.Rank.unknown
          | _  -> I.Rank.mk 1
      end
      | L.IntrinsicOperator _ -> begin
          match node#children with
          | [x] -> get x
          | [x0; x1] ->
              let r0 = get x0 in
              if I.Rank.is_zero r0 then
                get x1
              else if I.Rank.is_non_zero r0 then
                r0
              else
                I.Rank.unknown
          | _ -> assert false
      end
      | L.DefinedOperator _ -> begin
          I.Rank.unknown
      end
      | L.StructureComponent _ -> begin
          get_rank_of_part_ref_elems node#children
      end
      | _ -> I.Rank.unknown
    in
    let r = get node in
    [%debug_log "%s --> %s" node#to_string (I.Rank.to_string r)];
    r

(*
  In an array-section with no section-subscript-list,
   the rank of the array is the rank of the part-ref with nonzero rank;

  otherwise,
   the rank of the array section is the number of subscript triplets and
   vector subscripts in the section subscript list.
 *)
  and get_rank_of_part_ref_elems nds =
    let rec get = function
      | x0::(x1::rest as l) -> begin
          [%debug_log "[0] %s: is_name_part -> %B" x0#to_string (is_name_part x0)];

          if is_name_part x0 then begin
            [%debug_log "[1] %s: is_name_part -> %B" x1#to_string (is_name_part x1)];

            if is_name_part x1 then begin (* <name-part><name-part> *)
              let r0 = get_rank x0 in
              if I.Rank.is_non_zero r0 then
                r0
              else
                let r1 = get_rank x1 in
                if I.Rank.is_non_zero r0 then
                  r1
                else
                  get l
            end
            else begin (* <name-part><list-part> *)
              let count =
                List.fold_left
                  (fun c nd ->
                    let cond, err =
                      if L.is_subscript_triplet nd#label then
                        true, false
                      else
                        let r = get_rank nd in
                        if I.Rank.is_non_zero r then
                          true, false
                        else
                          if I.Rank.is_zero r then
                            false, false
                          else
                            false, true
                    in
                    if cond then
                      c + 1
                    else
                      if err then
                        raise Exit
                      else
                        c
                  ) 0 x1#children
              in
              if count > 0 then
                I.Rank.mk count
              else
                get rest
            end
          end
          else
            get l
      end
      | [_]
      | [] -> I.Rank.mk 0
    in
    let rank =
      try
        get nds
      with
        Exit -> I.Rank.unknown
    in
    [%debug_log "rank=%s" (I.Rank.to_string rank)];
    rank


  let is_assumed_size_spec aspec =
    if aspec#children = [] then
      false
    else begin
      let last = Xlist.last aspec#children in
      match last#label with
      | L.Ambiguous Ambiguous.AssumedSize -> true
      | _ -> false
    end


  let contain_allocatable_or_pointer attr_specs =
    try
      List.iter
        (fun a ->
          match a#label with
          | L.AttrSpec s -> begin
              match s with
              | AttrSpec.Allocatable
              | AttrSpec.Pointer     ->  raise Exit
              | _ -> ()
          end
          | l -> begin
              let _ = l in
              [%warn_log "invalid label: %s" (L.to_string l)];
              assert false
          end
        ) attr_specs;
      false
    with
      Exit -> true


  let disambiguate_subscript_triplet node =
    if L.is_ambiguous_triplet_or_range node#label then begin
      node#relab L.SubscriptTriplet;
      List.iter
        (fun nd ->
          match nd#label with
          | L.Ambiguous Ambiguous.First -> nd#relab L.FirstSubscript
          | L.Ambiguous Ambiguous.Second -> nd#relab L.SecondSubscript
          | _ -> ()
        ) node#children
    end


  let disambiguate_part_ref_elem nd =
    [%debug_log "disambiguating: %s" nd#to_string];
    match nd#label with
    | L.Ambiguous a -> begin
        match a with
        | Ambiguous.Designator n ->
            nd#relab (L.PartName n);
            set_binding nd

        | Ambiguous.Tuple -> begin
            nd#relab (L.SectionSubscriptList "");
            List.iter disambiguate_subscript_triplet nd#children
        end
        | _ -> begin
            [%warn_log "invalid label: %s (%s)" (L.to_string nd#label) (loc_to_str nd#loc)];
            assert false
        end
    end
    | _ -> ()


  let _disambiguate_substring_range node =
    match node#label with
    | L.Ambiguous Ambiguous.Tuple -> begin
        node#relab L.SubstringRange;
        List.iter
          (fun nd ->
            match nd#label with
            | L.Ambiguous a -> begin
                match a with
                | Ambiguous.First -> nd#relab L.StartingPoint
                | Ambiguous.Second -> nd#relab L.EndingPoint
                | _ -> begin
                    [%warn_log "invalid label: %s (%s)" (L.to_string nd#label) (loc_to_str nd#loc)];
                    assert false
                end
            end
            | _ -> ()
          ) node#children
    end
    | _ -> ()

  let disambiguate_substring_range node =
    if L.is_ambiguous node#label then begin
      match node#children with
      | [sr] -> begin
          node#set_children sr#children;
          _disambiguate_substring_range node
      end
      | _ -> assert false
    end

  let disambiguate_data_object
      ?(mklab=fun n -> L.Name n)
      ?(defer=true)
      ?(check_const=false)
      name node
      =
    [%debug_log "disambiguating: %s (defer=%B check_const=%B)" node#to_string defer check_const];

    let default_lab =
      if check_const then
        L.Ambiguous (Ambiguous.NamedDataObject name)
      else if env#macro_defined name then
        L.PpMacroId name
      else
        mklab name
    in
    let afilt x =
      N.Spec.has_data_object_spec x ||
      N.Spec.has_procedure_spec x ||
      N.Spec.has_object_spec x ||
      N.Spec.is_intrinsic_procedure x
    in
    let allow_implicit = not defer in
    let lab =
      match env#lookup_name ~allow_implicit ~afilt name with
      | spec::_ -> begin
          [%debug_log "spec: %s" (N.Spec.to_string spec)];
          node#set_info (I.mknamespec spec);
          begin
            try
              let dospec = N.Spec.get_data_object_spec spec in
              match dospec#bid_opt with
              | Some bid -> node#set_binding (B.make_use bid)
              | _ -> ()
            with
              Not_found -> ()
          end;
          begin
            try
              let pspec = N.Spec.get_procedure_spec spec in
              match pspec#bid_opt with
              | Some bid -> node#set_binding (B.make_use bid)
              | _ -> ()
            with
              Not_found -> ()
          end;
          begin
            try
              let ospec = N.Spec.get_object_spec spec in
              match ospec#bid_opt with
              | Some bid -> node#set_binding (B.make_use bid)
              | _ -> ()
            with
              Not_found -> ()
          end;
          if check_const then begin
            try
              if (N.Spec.get_data_object_attr spec)#is_parameter then
                L.Constant (Constant.NamedConstant name)
              else if env#macro_defined name then
                L.PpMacroId name
              else
                mklab name
            with
              Not_found ->
                if env#macro_defined name then
                  L.PpMacroId name
                else
                  mklab name
          end
          else begin
            if N.Spec.has_decl spec then
              if env#macro_defined name then
                L.PpMacroId name
              else
                mklab name
            else if N.Spec.is_namelist_group spec then
              L.Name name
            else if N.Spec.is_procedure spec then
              L.Name name
            else if N.Spec.is_intrinsic_procedure spec then
              L.Name name
            else
              default_lab
          end
      end
      | [] ->
          [%debug_log "spec not found"];
          default_lab
    in
    node#relab lab;
    node#set_children [];
    begin
      match lab with
      | L.Ambiguous _ ->
          if defer then
            env#register_ambiguous_node node
          else begin
            node#set_info (I.make (env#lookup_name name))
          end
      | _ -> ()
    end


  let relab_subobject mklab node =
    let name = get_name_of_part_names node#children in
    node#relab (mklab name)


  let disambiguate_array_element node =
    List.iter disambiguate_part_ref_elem node#children;
    relab_subobject (fun n -> L.ArrayElement n) node;
    set_binding_of_subobject node


  let disambiguate_allocate_shape_spec_list node =
    match node#label with
    | L.Ambiguous Ambiguous.Tuple -> begin
        node#relab L.AllocateShapeSpecList;
        List.iter
          (fun spec ->
            match spec#label with
            | L.Ambiguous (Ambiguous.TripletOrRange) -> begin
                spec#relab L.AllocateShapeSpec;
                match spec#children_labels with
                | [lower,L.Ambiguous Ambiguous.First;upper,L.Ambiguous Ambiguous.Second] ->
                    spec#set_children (lower#children @ upper#children)
                | _ -> ()
            end
            | _ -> ()
          ) node#children
    end
    | _ -> ()


  let disambiguate_bounds_list node =
    match node#label with
    | L.Ambiguous Ambiguous.Tuple -> begin
        let spec_flag = ref false in
        let remapping_flag = ref false in
        List.iter
          (fun spec ->
            if L.is_ambiguous spec#label then begin
              match spec#children_labels with
              | [_] ->
                  spec_flag := true;
                  spec#relab L.BoundsSpec

              | [lower,L.Ambiguous Ambiguous.First;upper,L.Ambiguous Ambiguous.Second] ->
                  remapping_flag := true;
                  spec#relab L.BoundsRemapping;
                  spec#set_children (lower#children @ upper#children)

              | [_;_] ->
                  remapping_flag := true;
                  spec#relab L.BoundsRemapping

              | _ -> parse_warning_loc spec#loc "invalid bounds"

            end
          ) node#children;

        if !spec_flag && not !remapping_flag then
          node#relab L.BoundsSpec
        else if !remapping_flag && not !spec_flag then
          node#relab L.BoundsRemapping
    end
    | _ -> ()


  let disambiguate_pointer_object node =
    List.iter disambiguate_part_ref_elem node#children;
    relab_subobject (fun n -> L.StructureComponent n) node


  let disambiguate_allocation node =
    if L.is_ambiguous node#label then begin
      match node#children_labels with
      | [] -> failwith "Disambg.disambiguate_allocation"
      | [_,L.Ambiguous (Ambiguous.Designator n)] -> begin
          disambiguate_data_object ~mklab:(fun n -> L.VariableName n) n node
      end
      | [d,(L.Ambiguous (Ambiguous.Designator n) as dl);tpl,L.Ambiguous Ambiguous.Tuple] -> begin
          let nd =
            new Ast.node ~lloc:node#lloc ~children:[d] ~info:node#info dl
          in
          disambiguate_data_object n nd;
          disambiguate_allocate_shape_spec_list tpl;
          node#relab (L.Allocation n);
          node#set_children [nd; tpl]
      end
      | l -> begin
          let compo_nd, tpl_opt, img_opt =
            let children, tpl_opt, img_opt =
              let xs, last = Xlist.partition_at_last l in
              match last with
              | img,L.ImageSelector -> begin
                  try
                    let xs2, last2 = Xlist.partition_at_last xs in
                    match last2 with
                    | tpl,L.Ambiguous Ambiguous.Tuple -> List.map fst xs2, Some tpl, Some img
                    | _ -> List.map fst xs, None, Some img
                  with
                    Failure _ -> List.map fst xs, None, Some img
              end
              | tpl,L.Ambiguous Ambiguous.Tuple -> List.map fst xs, Some tpl, None
              | _ -> node#children, None, None
            in
            new Ast.node ~lloc:node#lloc ~children ~info:node#info (L.StructureComponent ""),
            tpl_opt,
            img_opt
          in
          List.iter disambiguate_part_ref_elem compo_nd#children;
          relab_subobject (fun n -> L.StructureComponent n) compo_nd;
          let tpll =
            match tpl_opt with
            | Some tpl -> disambiguate_allocate_shape_spec_list tpl; [tpl]
            | None -> []
          in
          let imgl =
            match img_opt with
            | Some img -> begin
                List.iter (fun x -> x#relab L.AllocateCoshapeSpec) img#children;
                img#relab L.AllocateCoarraySpec;
                [img]
            end
            | None -> []
          in
          node#relab (L.Allocation compo_nd#get_name);
          node#set_children (compo_nd :: tpll @ imgl)
      end
    end

  let disambiguate_data_pointer_object node =
    if L.is_ambiguous node#label then begin
      match node#children_labels with
      | [] -> failwith "Disambg.disambiguate_data_pointer_object"
      | [_,L.Ambiguous (Ambiguous.Designator n)] -> begin
          disambiguate_data_object ~mklab:(fun n -> L.VariableName n) n node
      end
      | [d,(L.Ambiguous (Ambiguous.Designator n) as dl);tpl,L.Ambiguous Ambiguous.Tuple] -> begin
          let nd =
            new Ast.node ~lloc:node#lloc ~children:[d] ~info:node#info dl
          in
          disambiguate_data_object n nd;
          disambiguate_bounds_list tpl;
          node#relab (L.DataPointerObject n);
          node#set_children [nd; tpl]
      end
      | l -> begin
          let compo_nd, tpl_opt =
            let children, tpl_opt =
              let xs, last = Xlist.partition_at_last l in
              match last with
              | tpl,L.Ambiguous Ambiguous.Tuple -> begin
                  List.map (fun (x, _) -> x) xs, Some tpl
              end
              | _ -> node#children, None
            in
            new Ast.node ~lloc:node#lloc ~children ~info:node#info (L.StructureComponent ""),
            tpl_opt
          in
          List.iter disambiguate_part_ref_elem compo_nd#children;
          relab_subobject (fun n -> L.StructureComponent n) compo_nd;
          let tpll =
            match tpl_opt with
            | Some tpl -> disambiguate_bounds_list tpl; [tpl]
            | None -> []
          in
          node#relab (L.DataPointerObject compo_nd#get_name);
          node#set_children (compo_nd :: tpll)
      end
    end

  let disambiguate_equivalence_object node =
    [%debug_log "disambiguating: %s" node#to_string];
    if L.is_ambiguous node#label then begin
      match node#children_labels with
      | [] -> failwith "Disambg.disambiguate_equivalence_object"
      | [_,L.Ambiguous (Ambiguous.Designator n)] -> begin
          disambiguate_data_object ~mklab:(fun n -> L.VariableName n) n node
      end
      | [_,L.Constant _; x,_] -> begin
          match x#label with
          | L.Ambiguous Ambiguous.Tuple -> begin
              node#relab L.Substring;
              x#relab L.SubstringRange
          end
          | L.SubstringRange -> node#relab L.Substring
          | _ -> begin
              [%warn_log "invalid label: %s (%s)" (L.to_string x#label) (loc_to_str x#loc)];
              assert false
          end
      end
      | _ -> begin
          List.iter disambiguate_part_ref_elem node#children;
          relab_subobject (fun n -> L.ArrayElement n) node;
          set_binding_of_subobject node

      end
    end

  let disambiguate_component_array_spec is_deferred aspec =
    [%debug_log "disambiguating: %s (is_deferred=%B)" aspec#to_string is_deferred];

    let rank = List.length aspec#children in

    if L.is_ambiguous aspec#label then begin

      if is_deferred then begin
        List.iter (fun spec -> spec#relab L.DeferredShapeSpec) aspec#children;
        let lab = L.DeferredShapeComponentArray rank in
        [%debug_log "disambiguated: %s" (L.to_string lab)];
        aspec#relab lab
      end
      else begin
        List.iter
          (fun spec ->
            match spec#label with
            | L.Ambiguous a -> begin
                match a with
                | Ambiguous.Deferred -> spec#relab L.DeferredShapeSpec
                | Ambiguous.Assumed ->
                    parse_warning_loc spec#loc "component-array-spec shall not contain assumed-shape-spec"
                | Ambiguous.AssumedSize ->
                    parse_warning_loc spec#loc "component-array-spec shall not contain assumed-size-spec"
                | _ -> begin
                    [%warn_log "invalid label: %s (%s)" (L.to_string spec#label) (loc_to_str spec#loc)];
                    assert false
                end
            end
            | _ -> ()
          ) aspec#children;

        let lab =
          if (List.for_all (fun n -> n#label = L.ExplicitShapeSpec) aspec#children) then
            L.ExplicitShapeComponentArray rank

          else if (List.for_all (fun n -> n#label = L.DeferredShapeSpec) aspec#children) then
            L.DeferredShapeComponentArray rank

          else begin
            parse_warning_loc aspec#loc "invalid component-array-spec";
            L.ComponentArraySpec rank
          end
        in
        [%debug_log "disambiguated: %s" (L.to_string lab)];
        aspec#relab lab
      end
    end


  let disambiguate_component_decl is_deferred (aspec_opt, cspec_opt, cd) =
    [%debug_log "disambiguating: %s (is_deferred=%B)" cd#to_string is_deferred];
    cd#relab (L.ComponentDecl cd#get_name);
    begin
      match cspec_opt with
      | Some cspec -> begin
          cd#add_children_l [cspec]
      end
      | None -> ();
    end;
    begin
      match aspec_opt with
      | Some aspec -> begin
          disambiguate_component_array_spec is_deferred aspec;
          cd#add_children_l [aspec]
      end
      | None -> ()
    end;
    cd


  let disambiguate_array_spec is_deferred aspec =
    [%debug_log "disambiguating: %s (is_deferred=%B)" aspec#to_string is_deferred];
    if L.is_ambiguous aspec#label then begin
      let lab =
        if is_assumed_size_spec aspec then begin
          [%debug_log "is assumed-size-spec"];
          let r = ref 0 in
          let new_children =
            Xlist.filter_map
              (fun spec ->
                match spec#label with
                | L.Ambiguous a -> begin
                    match a with
                    | Ambiguous.Deferred    ->
                        parse_warning_loc spec#loc "assumed-size-spec shall not contain deferred-shape-spec";
                        Some spec
                    | Ambiguous.Assumed     -> begin
                        match spec#children with
                        | [e] -> Some e
                        | _ -> assert false
                    end
                    | Ambiguous.AssumedSize -> None
                    | _ -> begin
                        [%warn_log "invalid label: %s (%s)" (L.to_string spec#label) (loc_to_str spec#loc)];
                        assert false
                    end
                end
                | L.ExplicitShapeSpec -> incr r; Some spec
                | _ -> Some spec
              ) aspec#children
          in
          aspec#set_children new_children;
          L.AssumedSizeArray (!r + 1)
        end
        else begin
          [%debug_log "is not assumed-size-spec"];
          List.iter
            (fun spec ->
              match spec#label with
              | L.Ambiguous a -> begin
                  match a with
                  | Ambiguous.Deferred    ->
                      if is_deferred then
                        spec#relab L.DeferredShapeSpec
                      else
                        spec#relab L.AssumedShapeSpec

                  | Ambiguous.Assumed -> spec#relab L.AssumedShapeSpec

                  | Ambiguous.AssumedSize ->
                      parse_warning_loc spec#loc "'*' shall not occur except in assumed-size-spec"

                  | _ -> begin
                      [%warn_log "invalid label: %s (%s)" (L.to_string spec#label) (loc_to_str spec#loc)];
                      assert false
                  end
              end
              | _ -> ()
            ) aspec#children;

          let rank = List.length aspec#children in

          if (List.for_all (fun n -> n#label = L.DeferredShapeSpec) aspec#children) then
            L.DeferredShapeArray rank

          else if (List.for_all (fun n -> n#label = L.AssumedShapeSpec) aspec#children) then
            L.AssumedShapeArray rank

          else if (List.for_all (fun n -> n#label = L.ExplicitShapeSpec) aspec#children) then
            L.ExplicitShapeArray rank

          else begin
            parse_warning_loc aspec#loc "invalid array-spec";
            L.ArraySpec rank
          end
        end
      in
      [%debug_log "disambiguated: %s" (L.to_string lab)];
      aspec#relab lab
    end


  let disambiguate_entity_decl is_deferred (aspec_opt, cspec_opt, ed) =
    [%debug_log "disambiguating: %s" ed#to_string];
    ed#relab (L.EntityDecl ed#get_name);
    begin
      match cspec_opt with
      | Some cspec -> begin
          ed#add_children_l [cspec]
      end
      | None -> ();
    end;
    begin
      match aspec_opt with
      | Some aspec -> begin
          disambiguate_array_spec is_deferred aspec;
          ed#add_children_l [aspec]
      end
      | None -> ();
    end;
    ed


  let disambiguate_attr_specs is_deferred attr_specs =
    List.iter
      (fun attr_spec ->
        [%debug_log "disambiguating: %s" attr_spec#to_string];
        match attr_spec#label with
        | L.AttrSpec AttrSpec.Dimension -> begin
            match attr_spec#children with
            | [aspec] -> disambiguate_array_spec is_deferred aspec
            | _ -> parse_warning_loc attr_spec#loc "invalid dimension attribute"
        end
        | _ -> ()
      ) attr_specs


  let disambiguate_component_attr_specs is_deferred attr_specs =
    List.iter
      (fun attr_spec ->
        [%debug_log "disambiguating: %s" attr_spec#to_string];
        match attr_spec#label with
        | L.AttrSpec AttrSpec.Dimension ->
          List.iter (disambiguate_component_array_spec is_deferred) attr_spec#children
        | _ -> ()
      ) attr_specs


  let disambiguate_data_i_do_object node =
    [%debug_log "disambiguating: %s" node#to_string];
    match node#label with
    | L.DataImpliedDo -> ()
    | L.Ambiguous Ambiguous.Tuple -> begin
        node#relab L.DataIDoObject;
        List.iter disambiguate_part_ref_elem node#children
    end
    | _ -> begin
        [%warn_log "invalid label: %s (%s)" (L.to_string node#label) (loc_to_str node#loc)];
        assert false
    end


  (*
    (C623) array-element:
    Every part-ref shall have rank zero and the last part-ref shall contain a subscript-list.

    (C624) array-section:
    Exactly one part-ref shall have nonzero rank, and either the final part-ref shall have
    a section- subscript-list with nonzero rank, another part-ref shall have nonzero rank,
    or the complex-part-designator shall be an array.
   *)
  let check_part_ref_elems nds =
    let rec check (is_elem, is_sect) = function
      | x0::(x1::rest as l) -> begin
          [%debug_log "[0] %s: is_name_part -> %B" x0#to_string (is_name_part x0)];

          if is_name_part x0 then begin
            [%debug_log "[1] %s: is_name_part -> %B" x1#to_string (is_name_part x1)];

            if is_name_part x1 then begin (* <name-part><name-part>) *)
              let r = get_rank x0 in
              check (is_elem && I.Rank.is_zero r, is_sect || I.Rank.is_non_zero r) l
            end
            else begin (* <name-part><list-part>) *)
              let is_zero, is_non_zero =
                try
                  List.fold_left
                    (fun (is_z, is_n) nd ->
                      if L.is_subscript_triplet nd#label then
                        raise Exit
                      else
                        let r = get_rank nd in
                        (is_z && (I.Rank.is_zero r), is_n || (I.Rank.is_non_zero r))
                    ) (true, false) x1#children
                with
                  Exit -> (false, true)
              in
              [%debug_log "is_zero:%B is_non_zero:%B" is_zero is_non_zero];
              assert (not is_zero || not is_non_zero);
              check (is_elem && is_zero, is_sect || is_non_zero) rest
            end
          end
          else
            check (is_elem, is_sect) l
      end
      | [_] | [] -> is_elem, is_sect
    in
    let nds = snd (separate_image_selectors nds) in
    let is_elem, is_sect =
      match nds with
      | [_] | [] -> false, false
      | _ ->
          check (true, false) nds
    in
    [%debug_log "is_elem:%B is_sect:%B" is_elem is_sect];
    is_elem, is_sect


  let disambiguate_named_constant node =
    [%debug_log "disambiguating: %s" node#to_string];
    match node#label with
    | L.Ambiguous _ -> begin
        if L.is_ambiguous_data_stmt_constant node#label then
          match node#children_labels with
          | [] -> () (* assert false *)
          | [_,L.Ambiguous (Ambiguous.Designator n)] -> begin
              node#relab (L.Constant (Constant.mknamed n));
              node#set_children []
          end
          | _ -> () (* assert false *)
    end
    | _ -> ()


  let mkdesig = function
    | [] -> "", []
    | p ->
        let n =
          let lnd = Xlist.last p in
            try
              lnd#get_name
            with
              _ ->
                parse_warning_loc lnd#loc "invalid procedure-designator";
                ""
          in
          let pn = get_name_of_part_names p in
          [%debug_log "pn=%s n=%s" pn n];
          if (List.length p) = 1 then
            n, []
          else
            n, [new Ast.node ~lloc:(lloc_of_nodes p) ~children:p (L.ProcedureDesignator pn)]


  let disambiguate_variable ?(mklab=fun n -> L.Name n) ?(defer=true) node =
    begin %debug_block
      [%debug_log "disambiguating: %s (defer=%B)" node#to_string defer];
      List.iteri
        (fun i x -> [%debug_log "disambiguating: child[%d]: %s" i x#to_string])
        node#children;
    end;

    let _, others = separate_image_selectors node#children in

    match List.map (fun x -> x, x#label) others with
    | [] -> begin
        match node#label with
        | L.PpMacroVariable _ -> ()
        | _ -> assert false
    end
    | [_,L.Ambiguous (Ambiguous.Designator n)] -> begin
        disambiguate_data_object ~mklab ~defer n node
    end
    | [_] -> assert false
    | l -> begin
        let _ = l in

        let prefix, last = Xlist.partition_at_last others in

        List.iter disambiguate_part_ref_elem prefix;
        begin
          match last#label with
          | L.Ambiguous (Ambiguous.Designator _) | L.PartName _ -> begin
              disambiguate_part_ref_elem last;
              relab_subobject (fun n -> L.StructureComponent n) node
          end
          | L.Ambiguous Ambiguous.Tuple -> begin (* array-element or array-section or substring *)
              [%debug_log "array-element or array-section or substring"];
              let is_section_subscript lab =
                let b =
                  L.is_subscript_triplet lab || not (L.is_ambiguous_triplet_or_range lab)
                in
                [%debug_log "is_section_subscript: %s -> %B" (L.to_string lab) b];
                b
              in
              if
                (List.length last#children) > 1 ||
                List.exists (fun n -> is_section_subscript n#label) last#children
              then begin (* last -> part-name or section-subscript *)
                [%debug_log "the last is part-name or section-subscript"];
                disambiguate_part_ref_elem last
              end
              else begin

                let last2 = Xlist.last prefix in
                [%debug_log "last2: %s" last2#to_string];
                match last2#label with
                | L.SectionSubscriptList _ -> disambiguate_substring_range last

                | L.PartName pn -> begin
                    let r = get_rank_of_structure_component prefix in

                    if I.Rank.is_non_zero r then begin
                      disambiguate_part_ref_elem last
                    end
                    else if I.Rank.is_zero r then begin
                      if node#nchildren = 2 then
                        last2#relab (L.VariableName pn);

                      disambiguate_substring_range last
                    end
                end
                | _ -> begin
                    [%warn_log "invalid label: %s (%s)"
                      (L.to_string last2#label) (loc_to_str last2#loc)];
                    assert false
                end

              end
          end
          | _ -> ()
        end;

        let default_lab = L.Ambiguous Ambiguous.Subobject in

        let default ?(label=default_lab) () =
          if defer then
            env#register_ambiguous_node node
          else
            node#relab label
        in

        let _prefix0, _last0 = Xlist.partition_at_last node#children in
        let prefix0, last0, imgs =
          match _last0#label with
          | L.ImageSelector ->
              let prefix1, last1 = Xlist.partition_at_last _prefix0 in
              prefix1, last1, [_last0]
          | _ -> _prefix0, _last0, []
        in

        match last0#label with
        | L.Ambiguous (Ambiguous.Designator _) -> begin
            default()
        end
        | L.Ambiguous Ambiguous.Tuple -> begin (* array-element or array-section or substring *)
            [%debug_log "array-element or array-section or substring"];
            default()
        end
        | L.SubstringRange -> begin (* array-section or substring *)
            [%debug_log "array-section or substring"];
            let is_elem, is_sect = check_part_ref_elems prefix0 in
            if is_elem then begin
              node#relab L.Substring;
              let aname = get_name_of_part_names prefix0 in
              let parent =
                new Ast.node
                  ~lloc:(lloc_of_nodes prefix) ~children:prefix0 (L.ArrayElement aname)
              in
              set_binding_of_subobject parent;
              node#set_children (parent :: last0 :: imgs)
            end
            else if is_sect then begin
              relab_subobject (fun n -> L.ArraySection n) node;
              set_binding_of_subobject node
            end
            else begin
              match prefix0 with
              | [] -> default()
              | [x] ->
                  node#relab L.Substring;
                  set_binding_of_subobject x;
                  node#set_children (x :: last0 :: imgs)
              | _ ->
                  node#relab L.Substring;
                  let cname = get_name_of_part_names prefix0 in
                  let parent =
                    new Ast.node
                      ~lloc:(lloc_of_nodes prefix) ~children:prefix0 (L.StructureComponent cname)
                  in
                  set_binding_of_subobject parent;
                  node#set_children (parent :: last0 :: imgs)
            end
        end
        | L.SectionSubscriptList _ -> begin (* array-element or array-section *)
            [%debug_log "array-element or array-section"];
            let is_elem, is_sect = check_part_ref_elems node#children in
            if is_elem then begin
              relab_subobject (fun n -> L.ArrayElement n) node;
              set_binding_of_subobject node
            end
            else if is_sect then begin
              relab_subobject (fun n -> L.ArraySection n) node;
              set_binding_of_subobject node
            end
            else
              let aaname = get_name_of_part_names node#children in
              default ~label:(L.Ambiguous (Ambiguous.ArrayAccess aaname)) ()
        end
        | L.PartName _ -> ()

        | L.ActualArgSpecList _ -> begin (* procedure-designator (Fortran2003) *)
            let n, desig = mkdesig prefix0 in
            if n = "" || imgs <> [] then
              parse_warning_loc node#loc "invalid procedure-designator";

            node#relab (L.FunctionReference n);
            node#set_children (desig @ last0#children)
        end

        | last_label -> begin
            [%warn_log "%s" (Xlist.to_string (fun (_, x) -> L.to_string x) ";" l)];
            failwith
              (sprintf "Disambg.disambiguate_variable: invalid label: %s [%s]"
                 (L.to_string last_label) (loc_to_str last#loc))
        end
    end
  (* disambiguate_variable *)


  let disambiguate_proc_desig node = (* procedure-designator (Fortran2003) *)
    [%debug_log "disambiguating: %s" node#to_string];

    let prefix, last = Xlist.partition_at_last node#children in

    [%debug_log "last: %s" (L.to_string last#label)];

    match last#label with
    | L.Ambiguous (Ambiguous.Designator n) | L.PartName n -> begin
        let _, d = mkdesig node#children in
        n, d, []
    end
    | L.Ambiguous Ambiguous.Tuple | L.ActualArgSpecList _ -> begin
        let n, d = mkdesig prefix in
        if n = "" then
          parse_warning_loc node#loc "invalid procedure-designator";
        n, d, last#children
    end
    | last_label -> begin
        let _ = last_label in
        [%warn_log "invalid label: %s (%s)" (L.to_string last_label) (loc_to_str last#loc)];
        [%warn_log "%s" (Xlist.to_string (fun (_, x) -> L.to_string x) ";" node#children_labels)];
        assert false
    end


  let rec get_num_constant_literal node =
    match node#label with
    | L.Constant c -> begin
        match c with
        | Constant.IntLiteralConstant i -> i
        | Constant.RealLiteralConstant r -> r
        | _ -> raise Not_found
    end
    | L.IntrinsicOperator op -> begin
        let sign =
          match op with
          | IntrinsicOperator.Add -> "+"
          | IntrinsicOperator.Subt -> "-"
          | _ -> raise Not_found
        in
        match node#children with
        | [x] -> sign^(get_num_constant_literal x)
        | _ -> raise Not_found
    end
    | _ -> raise Not_found



  let disambiguate_linda_actual node =
    match node#label with
    | L.Ambiguous Ambiguous.TripletOrRange -> begin
        node#relab L.LindaActual;
        match node#children_labels with
        | [nd0,L.Ambiguous Ambiguous.First;nd1,L.Ambiguous Ambiguous.Second] -> begin
            nd1#relab L.LindaLength;
            node#set_children (nd0#children @ [nd1]);
            env#current_source#add_ext_PGI
        end
        | [nd0,L.Ambiguous Ambiguous.First] -> begin
            node#set_children (nd0#children @ [nd0]);
            nd0#relab L.LindaLength;
            nd0#set_children [];
            nd0#lloc#collapse_backward;
            env#current_source#add_ext_PGI
        end
        | _ -> ()
    end
    | _ -> ()

  let find_linda_keyword =
    let keyword_list =
      [
        "in",      LindaCall.In;
        "inp",     LindaCall.Inp;
        "rd",      LindaCall.Rd;
        "rdp",     LindaCall.Rdp;
        "out",     LindaCall.Out;
        "eval",    LindaCall.Eval;
      ] in
    let keyword_table = Hashtbl.create (List.length keyword_list) in
    let _ =
      List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
        keyword_list
    in
    let find s =
      Hashtbl.find keyword_table (String.lowercase_ascii s)
    in
    find

  let disambiguate_linda_call node =
    match node#children_labels with
    | [_,L.Ambiguous (Ambiguous.Designator n);tpl,L.Ambiguous Ambiguous.Tuple]
    | [_,L.PartName n;tpl,L.SectionSubscriptList _]
      -> begin
        try
          let ct = find_linda_keyword n in
          node#relab (L.mklinda ct);
          List.iter disambiguate_linda_actual tpl#children;
          node#set_children tpl#children;
          env#current_source#add_ext_PGI
        with
          Not_found -> ()
    end
    | _ -> ()


  let disambiguate_primary ?(defer=true) node =
    begin %debug_block
      [%debug_log "disambiguating: %s (defer=%B)" node#to_string defer];
      List.iteri
        (fun i x -> [%debug_log "disambiguating: child[%d] %s" i x#to_string])
        node#children
    end;

    match node#label with
    | L.Ambiguous _ -> begin
        let contain_linda_formal =
          try
            visit
              (fun nd ->
                match nd#label with
                | L.LindaFormal -> raise Exit
                | _ -> ()
              ) node;
            false
          with
            Exit -> true
        in

        if contain_linda_formal then begin
          disambiguate_linda_call node
        end
        else
          let alab = L.Ambiguous Ambiguous.Primary in
          match node#children_labels with
          | [nd,L.Ambiguous Ambiguous.Tuple] -> begin
              [%debug_log "may be complex-literal-constant"];
              match nd#children with
              | [x; y] -> begin
                  try
                    let lx = get_num_constant_literal x in
                    let ly = get_num_constant_literal y in
                    let lab = L.Constant (Constant.ComplexLiteralConstant(lx, ly)) in
                    node#relab lab;
                    node#set_children []
                  with
                    Not_found -> node#relab alab
              end
              | _ -> node#relab alab
          end
          | [_,L.Ambiguous Ambiguous.Designator n] -> begin
              [%debug_log "data-object"];
              disambiguate_data_object ~defer ~check_const:true n node
          end
          | [_,_] -> begin
              node#relab alab
          end
          | [_,L.Constant _; x,_] -> begin
              match x#label with
              | L.Ambiguous Ambiguous.Tuple -> begin
                  [%debug_log "constant-substring"];
                  node#relab L.Substring;
                  x#relab L.SubstringRange
              end
              | L.SubstringRange -> begin
                  [%debug_log "constant-substring"];
                  node#relab L.Substring
              end
              | _ -> begin
                  [%warn_log "invalid label: %s (%s)" (L.to_string x#label) (loc_to_str x#loc)];
                  assert false
              end
          end
          | [_,L.Ambiguous Ambiguous.Designator n;a,L.ActualArgSpecList _] -> begin
              [%debug_log "function-reference"];
              node#relab (L.FunctionReference n);
              node#set_children a#children;
              set_binding_of_subprogram_reference ~defer node
          end
          | [_,L.Ambiguous Ambiguous.Designator n;
             t,L.Ambiguous Ambiguous.Tuple] -> begin
               [%debug_log "function-reference or variable"];
               let allow_implicit = not defer in
               match env#lookup_name ~allow_implicit ~afilt:N.Spec.is_resolved n with
               | [] -> begin
                   if defer then begin
                     node#relab alab;
                     env#register_ambiguous_node node
                   end
(*
                   else
                     disambiguate_variable ~defer node
*)
               end
               | spec::rest -> begin
                   [%debug_log "spec: %s" (N.Spec.to_string spec)];

                   if defer && rest = [] && N.Spec.is_intrinsic_procedure spec then begin
                     env#register_ambiguous_node node
                   end;

                   if N.Spec.is_procedure spec then begin
                     [%debug_log "procedure"];
                     begin
                       try
                         match (N.Spec.get_object_spec spec)#bid_opt with
                         | Some bid -> node#set_binding (B.make_use bid)
                         | _ -> ()
                       with
                         Not_found -> ()
                     end;
                     node#relab (L.FunctionReference n);
                     node#set_children t#children
                   end
                   else if N.Spec.is_derived_type spec then begin
                     [%debug_log "derived_type"];
                     node#relab (L.StructureConstructor n);
                     node#set_children t#children
                   end
                   else if N.Spec.is_data_object_spec spec then begin
                     let dspec = N.Spec.get_data_object_spec spec in
                     [%debug_log "data_object: %s" dspec#to_string];
                     match dspec#type_spec with
                     | I.TypeSpec.Unknown | I.TypeSpec.Character -> begin
                         if defer then begin
                           node#relab alab;
                           env#register_ambiguous_node node
                         end
                         else
                           disambiguate_variable ~defer node
                     end
                     | _ -> begin
                         try
                           let attr = dspec#attr in
                           try
                             [%debug_log "rank=%d" attr#get_rank];
                             if attr#get_rank = 0 then begin
                               node#relab (L.FunctionReference n);
                               node#set_children t#children;
                               set_binding_of_subprogram_reference ~defer node
                             end
                             else begin
                               disambiguate_variable ~defer node
                             end
                           with
                             Failure _ -> disambiguate_variable ~defer node
                         with
                           Not_found -> begin
                             node#relab (L.FunctionReference n);
                             node#set_children t#children;
                             set_binding_of_subprogram_reference ~defer node
                         end
                     end
                   end
                   else begin (* procedures may follow the surrounding program unit! *)
                     if defer then begin
                       node#relab alab;
                       env#register_ambiguous_node node
                     end
                     else
                       disambiguate_variable ~defer node
                   end
               end
             end
          | _ -> disambiguate_variable ~defer node
    end
    | _ -> ()

  let disambiguate_data_stmt_constant node =
    disambiguate_named_constant node;
    disambiguate_primary node


  let disambiguate_generic_spec_OR_use_name ?(defer=true) node =
    [%debug_log "disambiguating: %s" node#to_string];
    match node#label with
    | L.Ambiguous (Ambiguous.GenericSpecOrUseName name) -> begin
        match N.Spec.filter_out_ambiguous (env#lookup_name ~allow_implicit:false name) with
        | [] -> begin
            if defer then
              env#register_ambiguous_node node
        end
        | specs -> begin
            if N.Spec.contain_generic specs then begin
              [%debug_log "a generic name: %s" name];
              node#relab (L.GenericSpec (GenericSpec.Name name))
            end
            else begin (* named variable, procedure, derived type, named contant, or namelist group *)
              [%debug_log "a use name: %s" name];
              node#relab (L.Name name)
            end
        end
    end
    | L.GenericSpec (GenericSpec.Name name) -> begin
        match N.Spec.filter_out_ambiguous (env#lookup_name ~allow_implicit:false name) with
        | [] -> ()
        | specs -> begin
            if not (N.Spec.contain_generic specs) then begin
              [%debug_log "not a generic name: %s" name];
              node#relab (L.Name name)
            end
        end
    end
    | _ -> ()

  let get_complex_part_str node =
    match node#label with
    | L.Constant c -> begin
        match c with
        | Constant.IntLiteralConstant s
        | Constant.RealLiteralConstant s -> s
        | _ -> raise Not_found
    end
    | L.IntrinsicOperator op -> begin
        let sign =
          match op with
          | IntrinsicOperator.Add -> "+"
          | IntrinsicOperator.Subt -> "-"
          | _ -> raise Not_found
        in
        match node#children with
        | [nd] -> begin
            match nd#label with
            | L.Constant Constant.IntLiteralConstant s
            | L.Constant Constant.RealLiteralConstant s -> sign^s
            | _ -> raise Not_found
        end
        | _ -> raise Not_found
    end
    | _ -> raise Not_found

  let disambiguate_primary_tuple node =
      match node#label with
      | L.Ambiguous Ambiguous.Tuple -> begin
          match node#children with
          | [_] -> node#relab L.ParenExpr
          | [nd0; nd1] -> begin
              try
                let r = get_complex_part_str nd0 in
                let i = get_complex_part_str nd1 in
                node#relab (L.Constant (Constant.mkcomp(r, i)));
                node#set_children []
              with
                Not_found -> ()
          end
          | _ -> ()
      end
      | _ -> ()


  let disambiguate_ac_value_or_io_item
      implied_do_lab
      mk_implied_do_control_lab
      node
      =
    [%debug_log "disambiguating:\n%s" (Printer.subtree_to_string node)];
    let nds_to_str = Xlist.to_string (fun n -> L.to_string n#label) ";" in
    let _ = nds_to_str in
    let rec doit node =
      if L.is_ambiguous_tuple node#label then begin
        let found, list, nl_opt, control =
          List.fold_left
            (fun (flag, lst, opt, cnt) nd ->
              [%debug_log "flag=%B lst=[%s] cnt=[%s]" flag (nds_to_str lst) (nds_to_str cnt)];
              if flag then
                (flag, lst, opt, cnt @ [nd])
              else
                match nd#label with
                | L.ActualArgSpec (Some n) -> begin
                    (true, lst, Some (n, nd#lloc), nd#children)
                end
                | _ -> (flag, lst @ [nd], None, [])
            ) (false, [], None, []) node#children
        in
        match found, nl_opt with
        | true, Some(n, l) -> begin
            [%debug_log "list=[%s] control=[%s]" (nds_to_str list) (nds_to_str control)];
            node#relab implied_do_lab;
            List.iter doit list;
            let lloc = Layeredloc.merge l (lloc_of_nodes control) in
            let control_nd = new Ast.node ~lloc ~children:control (mk_implied_do_control_lab n) in
            node#set_children (list @ [control_nd])
        end
        | _ -> ()
      end
    in
    doit node


  let disambiguate_ac_value node =
    disambiguate_ac_value_or_io_item
      L.AcImpliedDo
      (fun v -> L.AcImpliedDoControl v)
      node

  let disambiguate_io_item node =
    disambiguate_ac_value_or_io_item
      L.IoImpliedDo
      (fun v -> L.IoImpliedDoControl v)
      node


  let disambiguate_call node =
    match node#label with
    | L.Stmt stmt -> begin
        if Stmt.is_call_stmt stmt then
          set_binding_of_subprogram_reference node
    end
    | _ -> ()


  let propagate_binding ?(defer=true) node =
    match node#label with
    | L.Stmt stmt -> begin
        [%debug_log "%s (defer=%B)" node#to_string defer];
        try
          let from_node, to_node =
            match Stmt.get_stmt stmt with
            | Stmt.PointerAssignmentStmt
            | Stmt.AssignmentStmt -> begin
                match node#children with
                | [lhs; rhs] -> rhs, lhs
                | _ -> raise Not_found
            end
            | _ -> raise Not_found
          in
          [%debug_log "from: %s" from_node#to_string];
          [%debug_log "to:   %s" to_node#to_string];
          let from_name = from_node#get_name in
          let allow_implicit = not defer in
          let afilt = N.Spec.has_object_spec in
          begin
            match env#lookup_name ~allow_implicit ~afilt from_name with
            | [] -> begin
                if defer then begin
                  env#register_ambiguous_node node
                end
                else begin
                  match env#lookup_name ~afilt:N.Spec.is_external from_name with
                  | [] -> to_node#add_info (I.mkext "" from_name)
                  | specs -> to_node#add_info (I.make specs)
                end
            end
            | spec::_ -> begin
                try
                  match (N.Spec.get_object_spec spec)#bid_opt with
                  | Some bid -> begin
                      if B.is_none from_node#binding then begin
                        from_node#set_binding (B.make_use bid);
                        from_node#set_info (I.mknamespec spec)
                      end
                  end
                  | _ -> ()
                with
                  Not_found -> ()
            end
          end;
          if not defer && L.is_ambiguous from_node#label then begin
            [%debug_log "from_node#label is ambiguous"];
            let to_name = to_node#get_name in
            let name = from_node#get_name in
            match env#lookup_name ~allow_implicit:false to_name with
            | [] -> ()
            | spec::_ -> begin
                if
                  N.Spec.is_namelist_group spec ||
                  N.Spec.is_procedure spec ||
                  N.Spec.is_intrinsic_procedure spec
                then
                  from_node#relab (L.Name name)
            end
          end
        with
          Not_found -> ()
    end
    | _ -> ()


  let disambiguate_deferred() =
    env#iter_ambiguous_nodes
      (fun node ->
        [%debug_log "disambiguating: %s" node#to_string];
        let defer = false in
        match node#label with
        | L.Ambiguous Ambiguous.Primary ->
            disambiguate_primary ~defer node

        | L.Ambiguous (Ambiguous.NamedDataObject name) ->
            disambiguate_data_object ~defer ~check_const:true name node

        | L.Ambiguous (Ambiguous.GenericSpecOrUseName _) ->
            disambiguate_generic_spec_OR_use_name ~defer node

        | L.FunctionReference _ ->
            set_binding_of_subprogram_reference ~defer node

        | L.Stmt stmt -> begin
            match Stmt.get_stmt stmt with
            | Stmt.CallStmt _ -> set_binding_of_subprogram_reference ~defer node
            | Stmt.PointerAssignmentStmt
            | Stmt.AssignmentStmt -> propagate_binding ~defer node
            | _ -> ()
        end
        | L.DefinedOperator _ ->
            set_binding_of_subprogram_reference ~defer node

        | L.Ambiguous _ ->
            disambiguate_variable ~defer node

        | L.ProcName _ -> set_binding_of_subprogram_reference ~defer node

        | _ -> ()
      )


  let disambiguate_pp_section f pp_section_node =
    List.iter f pp_section_node#children

  let disambiguate_pp_branch f pp_branch_node =
    List.iter (disambiguate_pp_section f) pp_branch_node#children

  let disambiguate_internal_subprogram subprogram_part_node =
    let rec doit node =
      match node#label with
      | L.ProgramUnit pu -> begin
          match pu with
          | ProgramUnit.FunctionSubprogram n ->
              node#relab
                (L.InternalSubprogram (InternalSubprogram.FunctionSubprogram n))
          | ProgramUnit.SubroutineSubprogram n ->
              node#relab
                (L.InternalSubprogram (InternalSubprogram.SubroutineSubprogram n))
          | _ -> ()
      end
      | L.ModuleSubprogram is -> begin (* impossible? *)
          match is with
          | ModuleSubprogram.FunctionSubprogram n ->
              node#relab
                (L.InternalSubprogram (InternalSubprogram.FunctionSubprogram n))
          | ModuleSubprogram.SubroutineSubprogram n ->
              node#relab
                (L.InternalSubprogram (InternalSubprogram.SubroutineSubprogram n))
          | _ -> ()
      end
      | L.PpBranch -> begin
          disambiguate_pp_branch doit node
      end
      | L.PpSectionIf _ | L.PpSectionIfdef _ | L.PpSectionIfndef _ | L.PpSectionElif _ | L.PpSectionElse -> begin
          disambiguate_pp_section doit node
      end
      | _ -> ()
    in
    List.iter doit subprogram_part_node#children

  let disambiguate_module_subprogram subprogram_part_node =
    let rec doit node =
      match node#label with
      | L.ProgramUnit pu -> begin
          match pu with
          | ProgramUnit.FunctionSubprogram n ->
              node#relab (L.ModuleSubprogram (ModuleSubprogram.FunctionSubprogram n))

          | ProgramUnit.SubroutineSubprogram n ->
              node#relab (L.ModuleSubprogram (ModuleSubprogram.SubroutineSubprogram n))
          | _ -> ()
      end
      | L.InternalSubprogram is -> begin (* impossible? *)
          match is with
          | InternalSubprogram.FunctionSubprogram n ->
              node#relab
                (L.ModuleSubprogram (ModuleSubprogram.FunctionSubprogram n))
          | InternalSubprogram.SubroutineSubprogram n ->
              node#relab
                (L.ModuleSubprogram (ModuleSubprogram.SubroutineSubprogram n))
      end
      | L.PpBranch -> begin
          disambiguate_pp_branch doit node
      end
      | L.PpSectionIf _ | L.PpSectionIfdef _ | L.PpSectionIfndef _ | L.PpSectionElif _ | L.PpSectionElse -> begin
          disambiguate_pp_section doit node
      end
      | _ -> ()
    in
    List.iter doit subprogram_part_node#children

  let disambiguate_derived_type_spec node =
    match node#children_labels with
    | [_,L.Ambiguous (Ambiguous.Designator n)] -> begin
        node#relab (L.TypeSpec (TypeSpec.Derived n));
        node#set_children []
    end
    | [_,L.Ambiguous (Ambiguous.Designator n);tpl,L.Ambiguous Ambiguous.Tuple] -> begin
        node#relab (L.TypeSpec (TypeSpec.Derived n));
        node#set_children tpl#children
    end
    | _ -> ()


  let disambiguate_func_ref node =
    if L.is_ambiguous node#label then begin
      match node#children_labels with
      | [] -> failwith "Disambg.disambiguate_func_ref"
      | [_,L.Ambiguous (Ambiguous.Designator n)] -> begin
          node#relab (L.Name n);
          node#set_children []
      end
      | _ -> begin
          let prefix, last = Xlist.partition_at_last node#children in
          match last#label with
          | L.Ambiguous Ambiguous.Tuple | L.ActualArgSpecList _ -> begin
              let n, desig = mkdesig prefix in
              if n = "" then
                parse_warning_loc node#loc "invalid procedure-designator";

              node#relab (L.FunctionReference n);
              node#set_children (desig @ last#children)
          end
          | _ -> parse_warning_loc node#loc "incomplete disambiguation"
      end
    end

  let get_do_label lab =
    try
      L.get_label lab
    with
      Not_found -> ""

  exception Outermost of node list

  let elaborate_execution_part ep_nd =
    let not_parsing_partially = not env#partial_parsing_flag in

    let blk_to_string blk =
      sprintf "%s(%x)" (L.to_string blk#label) (Hashtbl.hash blk)
    in
    let lv_to_string lv = "<"^(Xlist.to_string (fun x -> x) ":" lv)^">" in

    let tpl_to_string (dc, nd, lv, blk, b_opt, lab) =
      sprintf "(%s, %s, %s, %s, %s, %s)"
        dc#to_string
        nd#to_string
        (lv_to_string lv) (* nonblock do level *)
        (blk_to_string blk)
        (match b_opt with Some b -> b#to_string | None -> "<none>")
        lab
    in
    let _ = tpl_to_string in
    let lv_has_lab lv lab =
      match lv with
      | [] -> false
      | x::_ -> x = lab
    in

    let add_to_blk blk nd =
      [%debug_log "adding %s to %s" nd#to_string (blk_to_string blk)];
      blk#add_children_r [nd];
      let lloc' =
        if blk#lloc == Layeredloc.dummy then
          nd#lloc
        else
          Layeredloc.merge blk#lloc nd#lloc
      in
      blk#set_lloc lloc'
    in
    let stack = Stack.create() in


    let push tpl =
      [%debug_log "PUSH! %s" (tpl_to_string tpl)];
      Stack.push tpl stack
    in
    let pop() =
      let tpl = Stack.pop stack in
      [%debug_log "POP! %s" (tpl_to_string tpl)];
      let (_, _, _, blk, b_opt, _) = tpl in
      match b_opt with
      | Some b -> b#set_lloc (Layeredloc.merge b#lloc blk#lloc)
      | _ -> ()
    in

    let new_blocks = ref [] in

    let add_new_block parent blk =
      new_blocks := (parent, blk) :: !new_blocks
    in

    let add_elaborated l nd =
      [%debug_log "adding %s" nd#to_string];
      l @ [nd]
    in

    let change_top_block ?(child_opt=None) blk =
      let ((c, nd, lv, b, b0_opt, l) as tpl0) = Stack.pop stack in
      let _ = tpl0 in
      begin
        match b0_opt with
        | Some b0 -> b0#set_lloc (Layeredloc.merge b0#lloc b#lloc)
        | _ -> ()
      end;
      let child =
        match child_opt with
        | Some x -> x
        | _ -> blk
      in
      c#add_children_r [child];
      let tpl = (c, nd, lv, blk, child_opt, l) in
      [%debug_log "%s -> %s" (tpl_to_string tpl0) (tpl_to_string tpl)];
      Stack.push tpl stack
    in

    let elaborated =
      List.fold_left
        (fun l nd ->
          [%debug_log "%s" nd#to_string];
          try
            let (cnt, _, lv, blk, _, lab) = Stack.top stack in

            if L.is_do_stmt nd#label then begin

              let lab' = get_do_label nd#label in
              let blk' = new Ast.node L.DoBlock in
              let cnt' =
                new Ast.node ~lloc:nd#lloc ~children:[nd; blk'] (L.DoConstruct nd#get_var_opt)
              in
              add_new_block cnt' blk';
              if lab' <> lab || (lab' = "" && lab = "") then begin
                push (cnt', nd, lv, blk', None, lab')
              end
              else begin (* shared do-construct *)
                cnt#add_children_r [cnt'];
                push (cnt', nd, lab::lv, blk', None, lab');
              end;
              l

            end
            else if L.is_if_then_stmt nd#label then begin
              let blk' = new Ast.node L.Block in
              let ifthen_blk = new Ast.node ~lloc:nd#lloc ~children:[nd;blk'] L.IfThenBlock in
              let cnt' = new Ast.node ~lloc:nd#lloc ~children:[ifthen_blk] L.IfConstruct in
              add_new_block ifthen_blk blk';
              push (cnt', nd, lv, blk', Some ifthen_blk, "");
              l
            end
            else if L.is_else_if_stmt nd#label then begin
              if L.is_if_construct cnt#label then begin
                let blk' = new Ast.node L.Block in
                let elseif_blk = new Ast.node ~lloc:nd#lloc ~children:[nd;blk'] L.ElseIfBlock in
                change_top_block ~child_opt:(Some elseif_blk) blk'
              end
              else begin
                if not_parsing_partially then
                  parse_warning_loc nd#loc "misplaced else-if-stmt";
                add_to_blk blk nd
              end;
              l
            end
            else if L.is_else_stmt nd#label then begin
              if L.is_if_construct cnt#label then begin
                let blk' = new Ast.node L.Block in
                let else_blk = new Ast.node ~lloc:nd#lloc ~children:[nd;blk'] L.ElseBlock in
                change_top_block ~child_opt:(Some else_blk) blk'
              end
              else begin
                if not_parsing_partially then
                  parse_warning_loc nd#loc "misplaced else-stmt";
                add_to_blk blk nd
              end;
              l
            end
            else begin
              if L.is_action_stmt nd#label then begin
                try
                  let lab' = L.get_stmt_label nd#label in
                  if lab' = lab && L.is_do_construct cnt#label then begin (* terminal action-stmt *)
                    [%debug_log "[action-stmt] adding %s to %s" nd#to_string cnt#to_string];
                    cnt#add_children_r [nd];

                    pop();
                    cnt#set_lloc (Layeredloc.merge cnt#lloc nd#lloc);

                    if Stack.is_empty stack then begin
                      add_elaborated l cnt
                    end
                    else begin
                      if lv_has_lab lv lab then begin
                        try
                          while true do
                            let (cnt', _, lv', _, _, _) = Stack.top stack in
                            cnt'#set_lloc (Layeredloc.merge cnt'#lloc nd#lloc);
                            pop();
                            if not (lv_has_lab lv' lab) then begin
                              if Stack.is_empty stack then begin
                                raise (Outermost (add_elaborated l cnt'))
                              end
                              else begin
                                let (_, _, _, blk'', _, _) = Stack.top stack in
                                add_to_blk blk'' cnt';
                                raise (Outermost l)
                              end
                            end
                          done;
                          []
                        with
                          Outermost l' -> l'
                      end
                      else begin
                        let (_, _, _, blk', _, _) = Stack.top stack in
                        add_to_blk blk' cnt;
                        l
                      end
                    end

                  end
                  else begin
                    add_to_blk blk nd;
                    l
                  end
                with
                  Not_found ->
                    add_to_blk blk nd;
                    l
              end
              else if L.is_end_do_stmt nd#label then begin
                [%debug_log "[end-do-stmt] adding %s to %s" nd#to_string cnt#to_string];
                cnt#add_children_r [nd];

                if L.is_do_construct cnt#label then begin
                  pop();
                  cnt#set_lloc (Layeredloc.merge cnt#lloc nd#lloc);
                  if Stack.is_empty stack then begin
                    add_elaborated l cnt
                  end
                  else begin
                    let (_, _, _, blk', _, _) = Stack.top stack in
                    add_to_blk blk' cnt;
                    l
                  end
                end
                else begin
                  if not_parsing_partially then
                    parse_warning_loc nd#loc "misplaced end-do-stmt";
                  l
                end
              end
              else if L.is_end_if_stmt nd#label then begin
                [%debug_log "[end-if-stmt] adding %s to %s" nd#to_string cnt#to_string];
                cnt#add_children_r [nd];

                if L.is_if_construct cnt#label then begin
                  pop();
                  cnt#set_lloc (Layeredloc.merge cnt#lloc nd#lloc);
                  if Stack.is_empty stack then begin
                    add_elaborated l cnt
                  end
                  else begin
                    let (_, _, _, blk', _, _) = Stack.top stack in
                    add_to_blk blk' cnt;
                    l
                  end
                end
                else begin
                  if not_parsing_partially then
                    parse_warning_loc nd#loc "misplaced end-if-stmt";
                  l
                end
              end
              else begin (* other stmt *)
                begin
                  try
                    if (L.get_stmt_label nd#label) = lab then
                      if not_parsing_partially then
                        parse_warning_loc nd#loc "do construct does not end with action-stmt"
                  with
                    Not_found -> ()
                end;
                add_to_blk blk nd;
                l
              end
            end
          with
            Stack.Empty ->
              if L.is_do_stmt nd#label then
                let lab = get_do_label nd#label in
                let blk = new Ast.node L.DoBlock in
                let cnt = new Ast.node ~lloc:ep_nd#lloc ~children:[nd; blk] (L.DoConstruct nd#get_var_opt) in
                cnt#set_lloc nd#lloc;
                add_new_block cnt blk;
                push (cnt, nd, [], blk, None, lab);
                l
              else if L.is_if_then_stmt nd#label then
                let blk = new Ast.node L.Block in
                let ifthen_blk = new Ast.node ~lloc:nd#lloc ~children:[nd;blk] L.IfThenBlock in
                let cnt = new Ast.node ~lloc:nd#lloc ~children:[ifthen_blk] L.IfConstruct in
                add_new_block ifthen_blk blk;
                push (cnt, nd, [], blk, Some ifthen_blk, "");
                l
              else
                add_elaborated l nd

        ) [] ep_nd#children
    in
    let partial = ref [] in
    begin
      Stack.iter
        (fun (cnt, nd, _, blk, _, _) ->
          if not_parsing_partially then
            parse_warning_loc cnt#loc "non-terminated construct: %s" cnt#to_string
          else
            partial := nd :: (blk#children @ !partial)
        ) stack
    end;
    List.iter (* remove empty Block *)
      (fun (p, b) ->
        match b#children with
        | [] -> p#set_children (List.filter (fun n -> n != b) p#children)
        | _ -> ()
      ) !new_blocks;
    ep_nd#set_children elaborated;
    if !partial <> [] && env#partial_parsing_flag then begin
      ep_nd#add_children_r !partial
    end
  (* end of func elaborate_execution_part *)

  let set_pp_context c nd =
    match nd#label with
    | L.PpDirective ppd -> PpDirective.set_context c ppd
    | _ -> ()


  let finalize_spec_exec ((* orig, *)spcs, dtvs, excs) =
    begin %debug_block
(*
      [%debug_log "original nodes:"];
      List.iter (fun n -> [%debug_log "  %s" n#to_string]) orig;
*)
      [%debug_log "specification part constructs:"];
      List.iter (fun n -> [%debug_log "  %s" n#to_string]) spcs;

      [%debug_log "directives:"];
      List.iter (fun n -> [%debug_log "  %s" n#to_string]) dtvs;

      [%debug_log "execution part constructs:"];
      List.iter (fun n -> [%debug_log "  %s" n#to_string]) excs;
    end;

(*
    begin
      List.iter2
        (fun x y ->
          if x != y then begin
            Xprint.message "%s != %s" x#to_string y#to_string;
            assert false
          end
        ) orig (excs@dtvs@spcs)
    end;
*)

    let spcs', excs' =
      if excs = [] then
        dtvs @ spcs, excs
      else
        spcs, excs @ dtvs
    in

    let specs =
      List.fold_left
        (fun l nd ->
          set_pp_context Context.Tspecification_part nd;
          nd :: l
        ) [] spcs'
    in
    let execs =
      List.fold_left
      (fun l nd ->
        set_pp_context Context.Texecution_part nd;
        if
          L.is_specification_part_construct nd#label &&
          not (L.is_execution_part_construct nd#label)
        then
          parse_warning_loc nd#loc "invalid construct order: %s" (L.to_simple_string nd#label);
        nd :: l
      ) [] excs'
    in
    specs, execs

  let finalize_fragment ctx nd =
    [%debug_log "finalizing: %s" nd#to_string];
    match nd#label with
    | L.Fragment -> begin
        match nd#children with
        | [] -> begin
            [%debug_log "result: []"];
            []
        end
        | children -> begin
            begin %debug_block
              List.iter (fun c -> [%debug_log "  %s" c#to_string]) children;
            end;
            let dvs_rev, fc_rev =
              List.fold_left
                (fun (dvs, fc) x ->
                  match x#label with
                  | L.PpDirective ppd -> begin
                      [%debug_log "%s" (L.to_string x#label)];
                      PpDirective.set_context ctx ppd;
                      if fc = [] then
                        x :: dvs, []
                      else
                        dvs, x::fc
                  end
                  | L.OclDirective _ | L.OmpDirective _ | L.XlfDirective _ -> begin
                      [%debug_log "%s" (L.to_string x#label)];
                      if fc = [] then
                        x :: dvs, []
                      else
                        dvs, x::fc
                  end
                  | _ -> dvs, x::fc
                ) ([], []) children
            in
            let l =
              if fc_rev = [] then
                List.rev dvs_rev
              else begin
                let c = List.rev fc_rev in
                nd#set_children c;
                nd#set_lloc (Ast.lloc_of_nodes c);
                List.rev (nd::dvs_rev)
              end
            in
            begin %debug_block
              [%debug_log "result:"];
              List.iter (fun n -> [%debug_log "  %s" n#to_string]) l;
            end;
            l
        end
    end
    | _ -> invalid_arg "Disambg.finalize_fragment"


  let finalize_format_items nds =
    let l, last_opt =
      List.fold_left
         (fun (finalized, r_opt) nd ->
           match nd#label with
           | L.FormatItem item -> begin
               if F_format_item.is_bare_vfe item && nd#nchildren = 1 then begin
                 let finalized' =
                   match r_opt with
                   | Some x -> x :: finalized
                   | _ -> finalized
                 in
                 (finalized', Some nd)
               end
               else begin
                 begin
                   match r_opt with
                   | Some x -> nd#add_children_l x#children
                   | None -> ()
                 end;
                 (nd :: finalized, None)
               end
           end
           | _ -> begin
               let finalized' =
                 match r_opt with
                 | Some x -> x::finalized
                 | _ -> finalized
               in
               (nd :: finalized', None)
           end
         ) ([], None) nds
    in
    List.rev (match last_opt with Some x -> x::l | None -> l)


  let handle_use mod_name ro_opt =
    [%debug_log "%s" mod_name];
    let name_tbl = Hashtbl.create 0 in
    let add_name x y =
      let x = String.lowercase_ascii x in
      let y = String.lowercase_ascii y in
      [%debug_log "%s -> %s" x y];
      let s =
        try
          Hashtbl.find name_tbl x
        with
          Not_found ->
            let s = Xset.create 0 in
            Hashtbl.add name_tbl x s;
            s
      in
      Xset.add s y;
    in
    let rec collect_name nd =
      match nd#label, nd#children with
      | L.Rename, [l; u] -> begin
          try
            add_name u#get_name l#get_name
          with
            Not_found -> ()
      end
      | L.Ambiguous (Ambiguous.GenericSpecOrUseName n), []
      | L.GenericSpec (GenericSpec.Name n), _ -> add_name n n

      | L.OnlyList, onlys -> List.iter collect_name onlys
      | _ -> ()
    in

    let only_nds =
      match ro_opt with
      | Some nds ->
          List.iter collect_name nds;
          nds
      | None ->
          env#register_used_module mod_name;
          []
    in

    let visible x =
      let b =
        if only_nds = [] then
          true
        else
          Hashtbl.mem name_tbl (String.lowercase_ascii x)
      in
      [%debug_log "%s --> %B" x b];
      b
    in
    begin
      match env#lookup_name ~allow_implicit:false ~afilt:N.Spec.is_module mod_name with
      | [] -> begin
          [%debug_log "not found: %s" mod_name];
          let frm = new N.frame (N.ScopingUnit.mkmodule mod_name) in
          frm#set_default_accessibility_public;
          Hashtbl.iter (fun n _ -> frm#add n N.Spec.module_entity) name_tbl;
          Aux.register_module mod_name frm;

          List.iter (Aux.register_external mod_name) only_nds
      end
      | spec::_ ->
          [%debug_log "found: %s --> %s" mod_name (N.Spec.to_string spec)];
          let dom = N.Spec.get_domain spec in
          [%debug_log "dom: {%s}" (Xlist.to_string (fun x -> x) "," (Xset.to_list dom))];
          let adder = N.Spec.get_adder spec in
          Hashtbl.iter
            (fun n _ ->
              if not (Xset.mem dom n) then
                adder n N.Spec.module_entity
            ) name_tbl;
          let finder = N.Spec.get_finder spec in
          Xset.iter
            (fun n ->
              try
                if visible n then begin
                  if only_nds = [] then
                    env#register_name n (finder n)
                  else
                    Xset.iter
                      (fun x -> env#register_name x (finder n))
                      (Hashtbl.find name_tbl n)
                end
              with
                Not_found -> assert false

            ) dom;
          Hashtbl.iter (fun n _ -> Xset.remove dom n) name_tbl;
          [%debug_log "dom: {%s}" (Xlist.to_string (fun x -> x) "," (Xset.to_list dom))];
          List.iter (Aux.register_external ~exclude:dom mod_name) only_nds
    end;
    let rec disambiguate nd =
      match nd#label, nd#children with
      | L.Ambiguous (Ambiguous.GenericSpecOrUseName _), []
      | L.GenericSpec (GenericSpec.Name _), _ -> disambiguate_generic_spec_OR_use_name nd
      | L.OnlyList, onlys -> List.iter disambiguate onlys
      | _ -> ()
    in
    List.iter disambiguate only_nds;
    only_nds


end (* of module Disambg.F *)
]
