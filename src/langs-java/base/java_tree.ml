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
(*
 * AST for the Java Language (for otreediff)
 *
 * java/java_tree.ml
 *
 *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xset = Diffast_misc.Xset
module Xhash = Diffast_misc.Xhash
module Xchannel = Diffast_misc.Xchannel
module Xprint = Diffast_misc.Xprint
module Binding = Diffast_misc.Binding
module Loc = Diffast_misc.Loc
module Spec_base = Diffast_core.Spec_base
module Spec = Diffast_core.Spec
module Fact_base = Diffast_core.Fact_base
module Lang_base = Diffast_core.Lang_base
module Sourcecode = Diffast_core.Sourcecode
module P   = Java_parsing.Printer
module L   = Java_label
module BID = Binding.ID
module FB  = Fact_base.F (L)
module UID = Diffast_misc.UID
module Triple = Diffast_core.Triple

module Ast = Java_parsing.Ast
module Astloc = Langs_common.Astloc

let sprintf = Printf.sprintf

let qualifier_of_name n =
  match n.Ast.n_desc with
  | Ast.Nsimple(_, _) -> None
  | Ast.Nqualified(_, name, _, _) -> Some name
  | Ast.Nerror _ -> None

let conv_loc = L.conv_loc

let loc_of_name n = conv_loc n.Ast.n_loc

let set_loc nd loc = nd#data#set_loc (conv_loc loc)

let rec set_ghost_rec nd =
  nd#data#set_loc Loc.ghost;
  Array.iter set_ghost_rec nd#children

let is_ghost = Triple.is_ghost_ast_node

let getlab = FB.getlab
let get_orig_lab_opt nd =
  match nd#data#orig_lab_opt with
  | Some o -> Some (Obj.obj o : L.t)
  | None -> None
let get_orig_lab nd =
  match nd#data#orig_lab_opt with
  | Some o -> (Obj.obj o : L.t)
  | None -> raise Not_found

let get_surrounding_classes_or_interfaces nd =
  FB.get_surrounding_xxxs (fun l -> L.is_class l || L.is_interface l || L.is_enum l) nd

let get_uqn name =
  Xlist.last (String.split_on_char '.' name)

let get_fqn ?(strip=false) package_name nd lab =
  let name = get_uqn (L.get_name ~strip lab) in
  let get_name n = L.get_name ~strip (getlab n) in
  let pkg_prefix =
    if package_name = "" then
      ""
    else
      package_name^"."
  in
  let sep =
    if L.is_class lab || L.is_interface lab || L.is_enum lab then
      "$"
    else
      "."
  in
  let surrounding =
    String.concat "$"
      (List.map get_name (get_surrounding_classes_or_interfaces nd))
  in
  let surrounding_prefix =
    if surrounding = "" then
      ""
    else
      surrounding^sep
  in
  let fqn =
    pkg_prefix^
    surrounding_prefix^
    (*if L.is_ctor lab then
      surrounding
    else*)
      name
  in
  fqn


module Tree = Sourcecode.Tree (L)

open Tree

let get_annotation = get_annotation

class c options root is_whole = object
  inherit Tree.c options root is_whole

  method! private create root is_whole = new c options root is_whole

  method! unparse_subtree_ch ?(no_boxing=false) ?(no_header=false) ?(fail_on_error=true) =
    make_unparser (Java_unparsing.unparse ~no_boxing ~no_header ~fail_on_error)

end

let of_xnode options =
  Tree.of_xnode ~tree_creator:(fun options nd -> new c options nd true) options



let of_opt of_x x_opt = match x_opt with None -> [] | Some x -> [of_x x]

let set_nodes_loc nd nodes =
  match nodes with
  | [] -> ()
  | [n] -> nd#data#set_loc n#data#src_loc
  | n::rest ->
      let loc = Loc._merge n#data#src_loc (List.hd(List.rev rest))#data#src_loc in
      nd#data#set_loc loc


let apply_child is_xxx f children =
  Array.iter
    (fun nd ->
      let lab = getlab nd in
      if is_xxx lab then
        f nd
    ) children


let vdid_to_id vdid =
  try
    String.sub vdid 0 (String.index vdid '[')
  with
    Not_found -> vdid

let strip_vdid (id, d) = vdid_to_id id, d


[%%capture_path
let set_control_flow body =

  let find_target env x = List.assoc x env in
  let find_break_target = function
    | (_, x) :: _ -> x
    | [] -> raise Not_found
  in
  let rec find_continue_target = function
    | (Some x, _) :: _ -> x
    | (None, _) :: rest -> find_continue_target rest
    | [] -> raise Not_found
  in
  let rec set_succ label_env loop_env nexts nd =
    let ndlab = getlab nd in

    let add_succ1 s =
      [%debug_log "%s[%s] -> %s[%s]"
        (L.to_string ndlab) (Loc.to_string nd#data#src_loc)
        (L.to_string (getlab s)) (Loc.to_string s#data#src_loc)];
      nd#data#add_successor s
    in
    let add_succ = List.iter add_succ1 in

    let children = nd#initial_children in
    let nchildren = nd#initial_nchildren in

    let handle_block children nchildren =
      [%debug_log "nchidlen=%d" nchildren];
      if nchildren = 0 then
        add_succ nexts
      else if nchildren > 0 then begin
        add_succ1 children.(0);
        let lasti = nchildren - 1 in
        for i = 0 to lasti - 1 do
          [%debug_log "i=%d" i];
          set_succ label_env loop_env [children.(i+1)] children.(i)
        done;
        set_succ label_env loop_env nexts children.(lasti)
      end
    in
    match ndlab with
    | L.Statement stmt -> begin
        match stmt with
        | L.Statement.If _ -> begin
            let c1 = children.(1) in
            add_succ1 c1;
            set_succ label_env loop_env nexts c1;
            for i = 2 to Array.length children - 1 do
              let ci = children.(i) in
              add_succ1 ci;
              set_succ label_env loop_env nexts ci
            done;
            add_succ nexts
        end
        | L.Statement.ElseIf _ -> begin
            let c1 = children.(1) in
            add_succ1 c1;
            set_succ label_env loop_env nexts c1;
            add_succ nexts
        end
        | L.Statement.Else -> begin
            let c = children.(0) in
            add_succ1 c;
            set_succ label_env loop_env nexts c;
            add_succ nexts
        end
        | L.Statement.Switch -> begin
            Array.iter
              (fun n ->
                add_succ1 n;
                set_succ label_env ((None, nexts)::loop_env) nexts n
              ) (children.(1))#initial_children
        end
        | L.Statement.For -> begin
            let c3 = (Sourcecode.get_logical_nth_child nd 1).(0) in
            add_succ1 c3;
            set_succ label_env ((Some c3, c3::nexts)::loop_env) nexts c3
        end
        | L.Statement.ForEnhanced -> begin
            let c2 = children.(2) in
            add_succ1 c2;
            set_succ label_env ((Some c2, c2::nexts)::loop_env) nexts c2
        end
        | L.Statement.While -> begin
            let c1 = children.(1) in
            add_succ1 c1;
            set_succ label_env ((Some c1, c1::nexts)::loop_env) nexts c1
        end
        | L.Statement.Do -> begin
            let c0 = children.(0) in
            add_succ1 c0;
            set_succ label_env ((Some c0, c0::nexts)::loop_env) nexts c0
        end
        | L.Statement.Break lab_opt -> begin
            try
              let ns =
                match lab_opt with
                | Some lab -> find_target label_env lab
                | None     -> find_break_target loop_env
              in
              add_succ ns
            with
              _ -> ()
        end
        | L.Statement.Continue lab_opt -> begin
            try
              let ns =
                match lab_opt with
                | Some lab -> find_target label_env lab
                | None     -> [find_continue_target loop_env]
              in
              add_succ ns
            with
              _ -> ()
        end
        | L.Statement.Labeled lab -> begin
            let c0 = children.(0) in
            add_succ1 c0;
            set_succ ((lab, nexts)::label_env) loop_env nexts c0
        end
        | L.Statement.Synchronized -> begin
            let c1 = children.(1) in
            add_succ1 c1;
            set_succ label_env loop_env nexts c1
        end
        | L.Statement.Try -> begin
            apply_child L.is_block
              (fun c ->
                add_succ1 c;
                set_succ label_env loop_env nexts c
              ) children
        end
        | L.Statement.Throw -> begin
        end

        | L.Statement.Return -> begin
        end

        | _ -> begin
            add_succ nexts
        end
    end
    | L.Block _ -> begin
        handle_block children nchildren
    end
    | L.SwitchBlockStatementGroup -> begin
        let children = Sourcecode.get_logical_nth_child nd 1 in
        let nchildren = Array.length children in
        handle_block children nchildren
    end
    | L.LocalVariableDeclaration _ -> begin
        add_succ nexts
    end
    | L.ThisInvocation
    | L.SuperInvocation
    | L.PrimaryInvocation
    | L.NameInvocation _ -> begin
        add_succ nexts
    end

    | _ -> ()
  in
  let children = body#initial_children in
  let nchildren = body#initial_nchildren in
  [%debug_log "* %s[%s]: nchildren=%d"
    (L.to_string (getlab body)) (Loc.to_string body#data#src_loc) nchildren];
  for i = 0 to nchildren - 2 do
    set_succ [] [] [children.(i+1)] children.(i)
  done;
  if nchildren > 0 then
    set_succ [] [] [] children.(nchildren - 1)
]

[%%capture_path
class visitor options bid_gen static_vdtors tree = object (self)
  inherit Sourcecode.visitor tree

  initializer
    begin %debug_block
      [%debug_log "%d static vdtors" (Xset.length static_vdtors)];
      Xset.iter (fun n -> [%debug_log "%s" n#data#to_string]) static_vdtors
    end

  val stack = new Sourcecode.stack

  val deferred_tbl = Hashtbl.create 0

  method reg_deferred nd f =
    Hashtbl.add deferred_tbl nd f

  method apply_deferred nd =
    try
      (Hashtbl.find deferred_tbl nd)()
    with Not_found -> ()

  method set_scope_node nd =
    try
      let n = stack#top.Sourcecode.f_scope_node in
      [%debug_log "n=%s" n#data#to_string];
      nd#data#set_scope_node n
    with
      Not_found -> ()

  method! scanner_body_before_subscan nd =
    let lab = getlab nd in
    if L.is_scope_creating lab then
      stack#push nd

  method! scanner_body_after_subscan nd =
    let lab = getlab nd in

    if L.is_scope_creating lab then
      stack#pop;

    if L.is_import_single lab then begin
      nd#data#set_scope_node tree#root
    end;

    if L.is_parameter lab then begin
      let name = L.get_name lab in
      let bid = bid_gen#gen in
      tree#add_to_bid_tbl bid name;
      let is_abst =
        let meth = nd#initial_parent#initial_parent in
        L.is_method (getlab meth) &&
        try
          match Sourcecode.get_logical_nth_child meth 6 with
          | [||] -> true
          | _ -> false
        with _ -> true
      in
      [%debug_log "is_abst=%B" is_abst];
      if is_abst then begin
        [%debug_log "USE(param): %s (bid=%a) %s" name BID.ps bid nd#to_string];
        nd#data#set_binding (Binding.make_use bid)
      end
      else begin
        [%debug_log "DEF(param): %s (bid=%a) %s" name BID.ps bid nd#to_string];
        nd#data#set_binding (Binding.make_unknown_def bid true);
        self#set_scope_node nd;
        stack#register name nd
      end
    end;

    if L.is_catch_parameter lab then begin
      let name = L.get_name lab in
      let bid = bid_gen#gen in
      tree#add_to_bid_tbl bid name;
      [%debug_log "DEF(catch param): %s (bid=%a) %s" name BID.ps bid nd#to_string];
      nd#data#set_binding (Binding.make_unknown_def bid true);
      self#set_scope_node nd;
      stack#register name nd
    end;

    if L.is_for lab then begin
      self#apply_deferred nd
    end;

    if L.is_variabledeclarator lab then begin
      if L.is_localvariabledecl (getlab nd#initial_parent) then begin
        let name = L.get_name lab in
        let bid, bid_is_generated =
          try
            Binding.get_bid nd#data#binding, false
          with _ -> bid_gen#gen, true
        in
        [%debug_log "DEF(decl): %s (bid=%a) %s" name BID.ps bid nd#to_string];
        if bid_is_generated then begin
          nd#data#set_binding (Binding.make_unknown_def bid true);
          tree#add_to_bid_tbl bid name;
          tree#add_to_def_bid_tbl bid nd
        end;
        self#set_scope_node nd;
        stack#register name nd;
        self#apply_deferred nd;

        let rec scan_expr expr_nd =
          begin
            try
              let expr_lab = getlab expr_nd in
              if L.is_primaryname expr_lab || L.is_fieldaccess expr_lab then begin
                let expr_name = expr_nd#data#get_name in
                let expr_bid = Binding.get_bid expr_nd#data#binding in
                [%debug_log "EXPR: %s %a<->%a %s" expr_name BID.ps expr_bid BID.ps bid name];
                if not options#no_binding_trace_flag then begin
                  tree#add_to_bid_map bid expr_bid;
                  tree#add_to_bid_map expr_bid bid;
                end;
                tree#add_to_bid_tbl expr_bid expr_name
              end
            with
              _ -> ()
          end;
          Array.iter scan_expr expr_nd#initial_children
        in
        if nd#initial_nchildren > 0 then
          scan_expr nd#initial_children.(0);

        (*begin
          try
            let expr_nd = nd#initial_children.(0) in
            let expr_lab = getlab expr_nd in
            if L.is_primaryname expr_lab || L.is_fieldaccess expr_lab then begin
              let expr_name = expr_nd#data#get_name in
              let expr_bid = Binding.get_bid expr_nd#data#binding in
              [%debug_log "EXPR: %s %a<->%a %s" expr_name BID.ps expr_bid BID.ps bid name];
              if not options#no_binding_trace_flag then begin
                tree#add_to_bid_map bid expr_bid;
                tree#add_to_bid_map expr_bid bid;
              end;
              tree#add_to_bid_tbl expr_bid expr_name
            end
          with
            _ -> ()
        end*)
      end
      else if Xset.mem static_vdtors nd then begin
        let name = L.get_name lab in
        let bid, bid_is_generated =
          try
            Binding.get_bid nd#data#binding, false
          with _ -> bid_gen#gen, true
        in
        [%debug_log "DEF(decl): %s (bid=%a) %s" name BID.ps bid nd#to_string];
        if bid_is_generated then begin
          nd#data#set_binding (Binding.make_unknown_def bid true);
          tree#add_to_bid_tbl bid name;
          tree#add_to_def_bid_tbl bid nd
        end;
        self#set_scope_node nd;
        stack#register name nd
      end
    end;

    let setup_binding binder_nd nd name =
      let bid = Binding.get_bid binder_nd#data#binding in
      tree#add_to_bid_tbl bid name;
      Binding.incr_use binder_nd#data#binding;
      [%debug_log "    USE: %s (bid=%a) %s" name BID.ps bid nd#to_string];
      let loc_opt = Some (binder_nd#uid, binder_nd#data#src_loc) in
      nd#data#set_binding (Binding.make_use ~loc_opt bid);
        (*begin
          try
            let vdtor =
              Misc.get_p_ancestor (fun x -> L.is_variabledeclarator (getlab x)) nd
            in
            [%debug_log "vdtor: %s" vdtor#data#to_string];
            let f () =
              try
                let vname = vdtor#data#get_name in
                let vbid = Binding.get_bid vdtor#data#binding in
                [%debug_log "VDTOR: %s %a<-%a %s" vname BID.ps vbid BID.ps bid name];
                if not options#no_binding_trace_flag then begin
                tree#add_to_bid_map bid vbid;
                (*tree#add_to_bid_map vbid bid;*)
                end;
                tree#add_to_bid_tbl bid name;
                tree#add_to_bid_tbl vbid vname
              with _ -> ()
            in
            self#reg_deferred vdtor f
          with
            _ -> ()
        end;*)
        begin
          try
            let pnd = nd#initial_parent in
            let assign =
              if nd#initial_pos = 1 && L.is_assignment (getlab pnd) then
                pnd
              else
                raise Not_found
                (*let a =
                  Misc.get_p_ancestor
                    (fun x ->
                      x#initial_pos = 1 && L.is_assignment (getlab x#initial_parent)
                    ) pnd
                in
                a#initial_parent*)
            in
            [%debug_log "assign: %s" assign#data#to_string];
            let lhs = assign#initial_children.(0) in
            let lhs_name = lhs#data#get_name in
            let lhs_bid = Binding.get_bid lhs#data#binding in
            [%debug_log "LHS: %s %a<->%a" lhs_name BID.ps lhs_bid BID.ps bid];
            if not options#no_binding_trace_flag then begin
              tree#add_to_bid_map bid lhs_bid;
              tree#add_to_bid_map lhs_bid bid;
            end;
            tree#add_to_bid_tbl lhs_bid lhs_name
          with
            _ -> ()
        end
    in

    if L.is_primaryname lab then begin
      let name = L.get_name lab in
      (*[%debug_log "nd=%s" nd#data#to_string];*)
      try
        let binder_nd = stack#lookup name in
        (*[%debug_log "binder_nd=%s" binder_nd#data#to_string];*)
        setup_binding binder_nd nd name
      with
        Not_found -> ()
    end;

    if L.is_fieldaccess lab && nd#initial_nchildren = 0 then begin
      let name = L.get_name lab in
      [%debug_log "nd=%s" nd#data#to_string];
      try
        let binder_nd = stack#lookup name in
        [%debug_log "binder_nd=%s" binder_nd#data#to_string];

        setup_binding binder_nd nd name;

        if Xset.mem static_vdtors binder_nd then begin
          let lab' = L.Primary (L.Primary.Name name) in
          let obj' = Obj.repr lab' in
          nd#data#relab ~orig:(Some obj') obj'
        end
      with
        Not_found -> ()
    end;

    begin
      match lab with
      | L.MethodBody _ | L.ConstructorBody _ -> set_control_flow nd
      | L.StaticInitializer | L.InstanceInitializer | L.Finally ->
            set_control_flow nd#initial_children.(0)
      | L.CatchClause _ -> set_control_flow nd#initial_children.(1)
      | _ -> ()
    end

  (* end of method scanner_body_after_subscan *)

end (* of class Tree.visitor *)
]

let compare_node_sig ?(reverse=false) nd1 nd2 =
  ignore reverse;
  let c = compare_node nd1 nd2 in
  if c = 0 then
    try
      let sig1 = L.get_signature (getlab nd1) in
      let sig2 = L.get_signature (getlab nd2) in
      compare sig1 sig2
    with _ -> c
  else
    c

[%%capture_path
class translator options =
  let bid_gen = options#bid_generator in
  object (self)
  inherit node_maker options

  val orphan_uids = Xset.create 0

  val static_vdtors = Xset.create 0

  val mutable huge_array_list = []

  method orphan_uids = orphan_uids

  method huge_array_list = huge_array_list
  method reg_huge_array orig nd = huge_array_list <- (orig, nd) :: huge_array_list

  method set_bindings (tree : Spec.tree_t) =

    (* for imports *)
    let importtbl = Hashtbl.create 0 (* FQN -> node *) in
    let reftytbl = Hashtbl.create 0 (* FQN -> node *) in

    (* for fields *)
    let fieldtbl = Hashtbl.create 0 (* FQN -> node *) in
    let facctbl = Hashtbl.create 0 (* FQN -> node *) in

    (* for methods *)
    (*let methodtbl = Hashtbl.create 0 (* FQN -> node *) in
    let ivktbl = Hashtbl.create 0 (* FQN -> node *) in*)

    let add tbl nm nd =
      try
        let nds = Hashtbl.find tbl nm in
        Hashtbl.replace tbl nm (nd :: nds)
      with
        Not_found -> Hashtbl.add tbl nm [nd]
    in
    let add_import = add importtbl in
    let add_refty = add reftytbl in
    let add_field = add fieldtbl in
    let add_facc = add facctbl in
    (*let add_method = add methodtbl in
    let add_ivk = add ivktbl in*)

    let is_self_facc nd =
      match nd#initial_children with
      | [||] -> true
      | [|n|] -> L.is_primarythis (getlab n)
      | _ -> false
    in

    (*let count_params msig =
      let count = ref 0 in
      let skip = ref true in
      begin
        try
          String.iter
            (fun c ->
              match c with
              | '(' -> skip := false
              | ')' -> raise Exit
              | 'L' -> skip := true
              | ';' -> incr count; skip := false
              | _ when !skip -> ()
              | _ -> incr count
            ) msig
        with
          Exit -> ()
      end;
      [%debug_log "%s -> %d" msig !count];
      !count
    in*)

    tree#fast_scan_whole_initial
      (fun nd ->
        let lab = getlab nd in
        if L.is_fieldaccess lab then begin
          if is_self_facc nd then begin
            let fqn = get_fqn ~strip:true "" nd lab in
            [%debug_log "FACC: fqn=%s %s" fqn nd#data#to_string];
            add_facc fqn nd
          end
        end
        (*else if L.is_field lab then begin
          let fqn = get_fqn ~strip:true "" nd lab in
          [%debug_log "FDECL: fqn=%s %s" fqn nd#data#to_string];
          add_field fqn nd
        end*)
        (*else if L.is_method lab then begin
          let fqn =
            sprintf "%s#%d" (get_fqn "" nd lab) (count_params (L.get_signature lab))
          in
          add_method fqn nd
        end
        else if L.is_simple_invocation lab then begin
          add_ivk (get_fqn "" nd lab) nd
        end*)
        else if L.is_variabledeclarator lab then begin
          if L.is_localvariabledecl (getlab nd#initial_parent) then
            ()
          else begin
            let fqn = get_fqn ~strip:true "" nd lab in
            [%debug_log "VDTOR: fqn=%s %s" fqn nd#data#to_string];
            add_field fqn nd
          end
        end
        else if L.is_import_single lab then begin
          add_import (L.get_name lab) nd
        end
        else if L.is_type lab then begin
          let rec getn = function
            | L.Type.ClassOrInterface n | L.Type.Class n | L.Type.Interface n -> n
            | L.Type.Array(t, _) -> getn t
            | _ -> raise Not_found
          in
          try
            match lab with
            | L.Type ty -> add_refty (getn ty) nd
            | _ -> ()
          with _ -> ()
        end
      );

    Hashtbl.iter
      (fun nm nds ->
        let bid = bid_gen#gen in
        tree#add_to_bid_tbl bid nm;
        let ref_bnd = Binding.make_use bid in
        [%debug_log "FQN: %s (bid=%a)" nm BID.ps bid];
        let referred = ref 0 in
        begin
          try
            let nds' = Hashtbl.find reftytbl nm in
            List.iter
              (fun n ->
                [%debug_log "    refty: %s" n#to_string];
                n#data#set_binding ref_bnd;
                incr referred
              ) nds'
          with
            Not_found ->
              [%debug_log "    refty: not found"]
        end;
        let def_bnd = Binding.make_used_def bid !referred false in
        List.iter
          (fun n ->
            [%debug_log "    import: %s" n#to_string];
            n#data#set_binding def_bnd;
            tree#add_to_def_bid_tbl bid n
          ) nds;
      ) importtbl;

    Hashtbl.iter
      (fun nm nds ->
        match nds with
        | def_nd::_ -> begin
            let bid = bid_gen#gen in
            tree#add_to_bid_tbl bid nm;
            tree#add_to_def_bid_tbl bid def_nd;
            let loc_opt = Some (def_nd#uid, def_nd#data#src_loc) in
            let ref_bnd = Binding.make_use ~loc_opt bid in
            [%debug_log "FQN: %s (bid=%a)" nm BID.ps bid];
            let referred = ref 0 in
            begin
              try
                let use_nds' = Hashtbl.find facctbl nm in
                List.iter
                  (fun n' ->
                    [%debug_log "    facc: %s" n'#to_string];
                    n'#data#set_binding ref_bnd;
                    incr referred
                  ) use_nds'
              with
                Not_found -> begin
                  [%debug_log "    facc: not found]"]
                end
            end;
            let def_bid = Binding.make_used_def bid !referred false in
            [%debug_log "    field: %s" def_nd#to_string];
            def_nd#data#set_binding def_bid
        end
        | _ -> assert false
      ) fieldtbl;

    (*Hashtbl.iter
      (fun nm nds ->
        match nds with
        | [_] -> begin
            let bid = bid_gen#gen in
            let ref_bnd = Binding.make_use bid in
            [%debug_log "FQN: %s (bid=%a)" nm BID.ps bid];
            let referred = ref 0 in
            begin
              try
                let nds' = Hashtbl.find ivktbl nm in
                List.iter
                  (fun n ->
                    [%debug_log "    ivk: %s" n#to_string];
                    n#data#set_binding ref_bnd;
                    incr referred
                  ) nds'
              with
                Not_found ->
                  [%debug_log "    ivk: not found"]
            end;
            let def_bnd = Binding.make_used_def bid !referred false in
            List.iter
              (fun n ->
                [%debug_log "    method: %s" n#to_string];
                n#data#set_binding def_bnd
              ) nds;
        end
        | _ -> ()
      ) methodtbl;*)

    (* for local variables *)
    let visitor = new visitor options bid_gen static_vdtors tree in
    visitor#visit_all

    (* end of method set_bindings *)



  method mkatid nd =
    Lang_base.mktid
      (if options#incomplete_info_flag then
        ""
      else
        let tree = new c options nd true in
        let atree = tree#make_anonymized_subtree_copy nd in
        Xhash.to_hex atree#digest)
      (if options#incomplete_info_flag then
        ""
      else
        nd#data#anonymized_label)

  method mktid nd =
    Lang_base.mktid
      (if options#incomplete_info_flag then
        ""
      else
        Xhash.to_hex (new c options nd false)#digest)
      (if options#incomplete_info_flag then
        ""
      else
        nd#data#anonymized_label)

  method _mktid nd =
    Lang_base.mktid
      (if options#incomplete_info_flag then
        ""
      else
        let t = new c options nd false in
        let _ = t#setup_initial_children in
        Xhash.to_hex t#digest)
      ""

  method __mktid (lab : string) =
    Lang_base.mktid ""
      (if options#incomplete_info_flag then
        ""
      else
        lab)


  val true_parent_tbl = Hashtbl.create 0
  method true_parent_tbl = true_parent_tbl
  method add_true_parent (uid : UID.t) (nd : Spec.node_t) =
    Hashtbl.add true_parent_tbl uid nd

  val true_children_tbl = Hashtbl.create 0
  method true_children_tbl = true_children_tbl
  method add_true_children nd children =
    [%debug_log "%s -> [\n%s\n]"
      nd#to_string (String.concat ";\n" (List.map (fun c -> c#to_string) (Array.to_list children)))];
    Hashtbl.add true_children_tbl nd children

  method of_javatype dims ty =
    let ty =
      if dims <> [] then begin
        let mkty d =
          { Ast.ty_desc=d; ty_loc=Astloc.merge ty.Ast.ty_loc (Xlist.last dims).Ast.ad_loc }
        in
        match ty.Ast.ty_desc with
        | Ast.Tarray(ty', dims') -> mkty (Ast.Tarray(ty', dims' @ dims))
        | _                      -> mkty (Ast.Tarray(ty, dims))
      end
      else
        ty
    in
    let rec get_children ?(dims=[]) desc =
      let mkotbl, mkc =
        if dims = [] then
          (fun specs -> Some (new ordinal_tbl specs)), fun l -> l
        else
          (fun specs -> Some (new ordinal_tbl (specs @ [List.length dims]))), fun l -> l @ dims
      in
      match desc with
      | Ast.Tprimitive(al, _) ->
          let ordinal_tbl_opt = mkotbl [0; List.length al; 0] in
          mkc (List.map self#of_annotation al), None, ordinal_tbl_opt

      | Ast.TclassOrInterface tss
      | Ast.Tclass tss
      | Ast.Tinterface tss -> begin
          let take_children, nds, ordinal_tbl_opt =
            match tss with
            | [] -> false, [], None
            | [Ast.TSname(al, _)] ->
                let ordinal_tbl_opt = mkotbl [0; List.length al; 0] in
                false, mkc (List.map self#of_annotation al), ordinal_tbl_opt
            | _ -> begin
                List.fold_left
                  (fun (_, l, _) spec ->
                    let al, n, tas_opt =
                      match spec with
                      | Ast.TSname(al, n)       -> al, n, None
                      | Ast.TSapply(al, n, tas) -> al, n, Some tas
                    in
                    let id = L.conv_name n in
                    let orig_id = L.conv_name ~resolve:false n in
                    let loc0 =
                      match al with
                      | []   -> n.Ast.n_loc
                      | a::_ -> a.Ast.a_loc
                    in
                    let loc1 =
                      match tas_opt with
                      | Some tas -> tas.Ast.tas_loc
                      | None     -> n.Ast.n_loc
                    in
                    let loc =
                      if loc0 == loc1 then
                        loc0
                      else
                        Ast.Loc.merge loc0 loc1
                    in
                    let tal =
                      match tas_opt with
                      | Some tas -> [self#of_type_arguments id tas]
                      | None -> []
                    in
                    let c = mkc (l @ (List.map self#of_annotation al) @ tal) in
                    let ordinal_tbl_opt = mkotbl [List.length l; List.length al; List.length tal] in
                    let orig_lab_opt = Some (L.Type (L.Type.ClassOrInterface orig_id)) in
                    let lab = L.Type (L.Type.ClassOrInterface id) in
                    let nd = self#mknode ~orig_lab_opt ~ordinal_tbl_opt lab c in
                    set_loc nd loc;
                    true, [nd], ordinal_tbl_opt
                  ) (false, [], None) tss
            end
          in
          match take_children, nds with
          | _, [] -> [], None, None
          | true, (nd :: _) -> Array.to_list nd#children, get_orig_lab_opt nd, ordinal_tbl_opt
          | false, nds -> nds, None, ordinal_tbl_opt
      end
      | Ast.Tarray(t, dims) -> begin
          let dims_ =
            if Ast.annot_exists dims then
              List.map self#of_annot_dim dims
            else
              []
          in
          let ndims =
            let count = ref 0 in
            List.iter (fun d -> if not d.Ast.ad_ellipsis then incr count) dims;
            !count
          in
          let children, _lab_opt, ordinal_tbl_opt = get_children ~dims:dims_ t.Ast.ty_desc in
          let lab_opt =
            match _lab_opt with
            | Some (L.Type lab) -> Some (L.Type (L.Type.Array(lab, ndims)))
            | Some _ -> assert false
            | None -> None
          in
          children, lab_opt, ordinal_tbl_opt
      end
      | Ast.Tvoid -> [], None, None
    in
    let children, lab_opt, ordinal_tbl_opt =
      get_children ty.Ast.ty_desc
    in
    let orig_lab_opt =
      match lab_opt with
      | None -> Some (L.of_javatype ~resolve:false ty)
      | Some _ -> lab_opt
    in
    let nd = self#mknode ~orig_lab_opt ~ordinal_tbl_opt (L.of_javatype ty) children in
    set_loc nd ty.Ast.ty_loc;
    [%debug_log "!!! %s" nd#to_string];
    nd


  method param_to_tystr ?(resolve=true) param =
    (*(if param.Ast.fp_variable_arity then "[" else "")^*)
    (P.type_to_short_string ~resolve
       (snd param.Ast.fp_variable_declarator_id) param.Ast.fp_type)

  method signature_of_method_header ?(resolve=true) mh =
    let params = mh.Ast.mh_parameters in
    (*sprintf "%s(%s)%s"
      mh.Ast.mh_name
      (Xlist.to_string self#param_to_tystr "" params)
      (P.type_to_short_string 0 mh.Ast.mh_return_type)*)
    sprintf "(%s)%s"
      (Xlist.to_string (self#param_to_tystr ~resolve) "" params)
      (P.type_to_short_string ~resolve [] mh.Ast.mh_return_type)

  method of_parameter param =
    match param.Ast.fp_receiver with
    | Some id ->
        let mods = param.Ast.fp_modifiers in
        let mod_nodes = self#of_modifiers_opt (L.Kparameter "") mods in
        let ordinal_tbl_opt = Some (new ordinal_tbl [List.length mod_nodes; 1]) in
        let nd =
          self#mknode ~ordinal_tbl_opt
            (L.ReceiverParameter (if id = "" then None else Some id))
            (mod_nodes @ [self#of_javatype [] param.Ast.fp_type])
        in
        set_loc nd param.Ast.fp_loc;
        nd
    | _ -> begin
        let (iloc, name), dims = param.Ast.fp_variable_declarator_id in
        let mods = param.Ast.fp_modifiers in
        let mod_nodes = self#of_modifiers_opt (L.Kparameter name) mods in
        let dims_have_annot = Ast.annot_exists dims in
        let otbl_spec =
          if dims_have_annot then
            [List.length mod_nodes; 1; List.length dims]
          else
            [List.length mod_nodes; 1]
        in
        let ordinal_tbl_opt = Some (new ordinal_tbl otbl_spec) in
        let id_loc =
          if iloc == Ast.Loc.dummy then
            Loc.dummy
          else
            conv_loc iloc
        in
        let dim_nds =
          if dims_have_annot then
            List.map self#of_annot_dim dims
          else
            []
        in
        let nd =
          self#mknode ~ordinal_tbl_opt ~id_loc
            (L.Parameter(name, List.length dims, param.Ast.fp_variable_arity))
            (mod_nodes @ [self#of_javatype [] param.Ast.fp_type] @ dim_nds)
        in
        set_loc nd param.Ast.fp_loc;
        nd
    end

  method of_for_header param =
    let (iloc, name), dims = param.Ast.fp_variable_declarator_id in
    let ndims = List.length dims in
    let vdtor_loc = conv_loc iloc in
    let vdtor_nd =
      self#mknode
        ~ordinal_tbl_opt:(Some (new ordinal_tbl [0])) ~id_loc:vdtor_loc
        (L.VariableDeclarator(name, ndims)) []
    in
    vdtor_nd#data#set_loc vdtor_loc;

    let mods = param.Ast.fp_modifiers in
    let mod_nodes = self#of_modifiers_opt (L.Kparameter name) mods in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length mod_nodes; 1; 1])
    in
    let id_loc =
      if iloc == Ast.Loc.dummy then
        Loc.dummy
      else
        conv_loc iloc
    in
    let lab = L.LocalVariableDeclaration(false, [name, ndims]) in
    let nd =
      self#mknode ~ordinal_tbl_opt ~id_loc lab
        (mod_nodes @ [self#of_javatype [] param.Ast.fp_type; vdtor_nd])
    in
    set_loc nd param.Ast.fp_loc;
    nd

  method of_parameters mname aloc params =
    match params with
    | [] -> []
    | _ ->
        (*let ordinal_tbl_opt = Some (new ordinal_tbl [List.length params]) in*)
        let nd =
          self#mknode (*~ordinal_tbl_opt*)
            (L.Parameters mname) (List.map self#of_parameter params)
        in
        set_loc nd aloc;
        [nd]


  method of_type_parameters name tps =
    let tparams = tps.Ast.tps_type_parameters in
    (*let ordinal_tbl_opt = Some (new ordinal_tbl [List.length tparams]) in*)
    let nd =
      self#mknode (*~ordinal_tbl_opt*) (L.TypeParameters name)
        (List.map self#of_type_parameter tparams)
    in
    set_loc nd tps.Ast.tps_loc;
    nd

  method of_type_parameters_opt name tparams_opt =
    of_opt (self#of_type_parameters name) tparams_opt

  method of_type_parameter tp =
    let annots = tp.Ast.tp_annotations in
    let tbound = tp.Ast.tp_type_bound in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length annots; if tbound = None then 0 else 1])
    in
    let children =
      (List.map self#of_annotation annots) @
      match tbound with
      | None -> []
      | Some tb when options#ast_reduction_flag -> begin
          let t = P.type_to_string ~show_attr:false tb.Ast.tb_reference_type in
          if t = "java.lang.Object" then
            []
          else
            [self#of_type_bound tb]
      end
      | Some tb -> [self#of_type_bound tb]
    in
    let nd =
      self#mknode ~ordinal_tbl_opt (L.TypeParameter tp.Ast.tp_type_variable) children
    in
    set_loc nd tp.Ast.tp_loc;
    nd

  method of_type_bound tb =
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [1; List.length tb.Ast.tb_additional_bounds])
    in
    let children =
      (self#of_javatype [] tb.Ast.tb_reference_type) ::
      (List.map self#of_additional_bound tb.Ast.tb_additional_bounds)
    in
    let nd = self#mknode ~ordinal_tbl_opt L.TypeBound children in
    set_loc nd tb.Ast.tb_loc;
    nd

  method of_additional_bound ab =
    let nd = self#of_javatype [] ab.Ast.ab_interface in
    set_loc nd ab.Ast.ab_loc;
    nd

  method of_modifier m =
    match m.Ast.m_desc with
    | Ast.Mannotation a -> self#of_annotation a
    | _ ->
    let lab =
      match m.Ast.m_desc with
      | Ast.Mpublic       -> L.Modifier.Public
      | Ast.Mprotected    -> L.Modifier.Protected
      | Ast.Mprivate      -> L.Modifier.Private
      | Ast.Mstatic       -> L.Modifier.Static
      | Ast.Mabstract     -> L.Modifier.Abstract
      | Ast.Mfinal        -> L.Modifier.Final
      | Ast.Mnative       -> L.Modifier.Native
      | Ast.Msynchronized -> L.Modifier.Synchronized
      | Ast.Mtransient    -> L.Modifier.Transient
      | Ast.Mvolatile     -> L.Modifier.Volatile
      | Ast.Mstrictfp     -> L.Modifier.Strictfp
      | Ast.Mdefault      -> L.Modifier.Default
      | Ast.Mtransitive   -> L.Modifier.Transitive
      | Ast.Msealed       -> L.Modifier.Sealed
      | Ast.Mnon_sealed   -> L.Modifier.NonSealed
      | Ast.Merror s      -> L.Modifier.Error s
      | Ast.Mannotation _ -> assert false
    in
    let nd = self#mkleaf (L.Modifier lab) in
    set_loc nd m.Ast.m_loc;
    nd

  method of_modifiers kind (*name*) ms =
    let children = List.map self#of_modifier ms.Ast.ms_modifiers in
    let children' =
      if options#sort_unordered_flag then
        List.fast_sort compare_node children
      else
        children
    in
    (*let namek = name^(L.kind_to_suffix kind) in*)
    let nd = self#mklnode (L.Modifiers kind) children' in
    if options#sort_unordered_flag then
      self#add_true_children nd (Array.of_list children);
    set_loc nd ms.Ast.ms_loc;
    nd

  method of_modifiers_opt
      ?(remove_final=false)
      ?(interface=false)
      ?(interface_field=false)
      ?(interface_method=false)
      ?(enum=false)
      ?(nested_enum=false)
      kind (*name*)
      = function
    | None -> []
        (*let namek = name^(L.kind_to_suffix kind) in
        let nd = self#mklnode (L.Modifiers namek) [] in
        [nd]*)
    | Some ms when remove_final -> begin
        let l = List.filter (fun m -> m.Ast.m_desc <> Ast.Mfinal) ms.Ast.ms_modifiers in
        match l with
        | [] -> []
        | _ ->
            let ms_ = {Ast.ms_modifiers=l; Ast.ms_loc=ms.Ast.ms_loc} in
            [self#of_modifiers kind ms_]
    end
    | Some ms when options#ast_reduction_flag -> begin
        let filter m =
          (not interface ||
          m.Ast.m_desc <> Ast.Mpublic &&
          m.Ast.m_desc <> Ast.Mabstract)
            &&
          (not interface_field ||
          m.Ast.m_desc <> Ast.Mpublic &&
          m.Ast.m_desc <> Ast.Mstatic &&
          m.Ast.m_desc <> Ast.Mfinal)
            &&
          (not interface_method ||
          let mods = List.map (fun m -> m.Ast.m_desc) ms.Ast.ms_modifiers in
          m.Ast.m_desc <> Ast.Mpublic &&
          not (m.Ast.m_desc = Ast.Mabstract &&
               List.for_all
                 (fun m ->
                   not (List.mem m mods)
                 ) [Ast.Mprivate; Ast.Mstatic; Ast.Mdefault]
              ))
            &&
          (not enum || m.Ast.m_desc <> Ast.Mfinal)
            &&
          (not nested_enum || m.Ast.m_desc <> Ast.Mstatic)
        in
        let l = List.filter filter ms.Ast.ms_modifiers in
        match l with
        | [] -> []
        | _ ->
            let ms_ = {Ast.ms_modifiers=l; Ast.ms_loc=ms.Ast.ms_loc} in
            [self#of_modifiers kind ms_]
    end
    | Some ms -> [self#of_modifiers kind (*name*) ms]

  method of_throws mname th =
    let leaves = List.map (self#of_javatype []) th.Ast.th_exceptions in
    let nd = self#mklnode (L.Throws mname) leaves in
    set_loc nd th.Ast.th_loc;
    nd

  method of_throws_opt mname = function
    | None -> []
    | Some throws -> [self#of_throws mname throws]

  method name_of_method_header header = header.Ast.mh_name

  method name_sig_of_method_header header =
    (header.Ast.mh_name,
     (self#signature_of_method_header ~resolve:false header),
     (self#signature_of_method_header header))

  method of_method_header ?(interface_method=false) ?(loc_opt=None) header =
    let ident = header.Ast.mh_name in
    let mods = header.Ast.mh_modifiers in
    let tparams = header.Ast.mh_type_parameters in
    let params = header.Ast.mh_parameters in
    let dims = header.Ast.mh_dims in
    let throws = header.Ast.mh_throws in

    let mod_nodes = self#of_modifiers_opt ~interface_method (L.Kmethod ident) mods in
    let tp_nodes = self#of_type_parameters_opt ident tparams in
    let rty = self#of_javatype [] header.Ast.mh_return_type in
    let p_nodes = self#of_parameters ident header.Ast.mh_parameters_loc params in
    let dim_nodes = List.map self#of_annot_dim dims in
    let th_nodes = self#of_throws_opt ident throws in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length mod_nodes;
                             List.length tp_nodes;
                             1;
                             List.length p_nodes;
                             List.length dim_nodes;
                             List.length th_nodes;
                           ])
    in
    let children = mod_nodes @ tp_nodes @ [rty] @ p_nodes @ dim_nodes @ th_nodes in
    let msig = self#signature_of_method_header header in
    let orig_msig = self#signature_of_method_header ~resolve:false header in
    let orig_lab_opt =
      (*Some (L.Method(ident, ""))*)
      Some (L.Method(ident, orig_msig))
      (*if msig <> orig_msig then
        Some (L.Method(ident, orig_msig))
      else
        None*)
    in
    let id_loc = conv_loc header.Ast.mh_name_loc in
    let nd =
      self#mknode
        ~annot:(L.make_annotation msig)
        ~orig_lab_opt
        ~ordinal_tbl_opt
        ~id_loc
        (L.Method(ident, msig)) children
    in
    let loc =
      match loc_opt with
      | Some l -> l
      | None -> header.Ast.mh_loc
    in
    set_loc nd loc;
    nd

  method of_variable_initializer vi =
    match vi.Ast.vi_desc with
    | Ast.VIexpression e -> self#of_expression e
    | Ast.VIarray ai -> begin
        let ordinal_tbl_opt = Some (new ordinal_tbl [List.length ai]) in
        let nd =
          self#mknode ~ordinal_tbl_opt
            L.ArrayInitializer (List.map self#of_variable_initializer ai)
        in
        let nd =
          if options#ignore_huge_arrays_flag then begin
            let n = new c options nd false in
            let _ = n#setup_initial_children in
            (*let _ = n#setup_initial_size in
            let sz = n#initial_size in*)
            let sz =
              let c = ref 0 in
              n#scan_whole_initial
                (fun n ->
                  if L.is_literal (getlab n) then
                    incr c
                );
              !c
            in
            if sz >= options#huge_array_threshold then begin
              Xprint.verbose options#verbose_flag "huge array found at %s (size=%d)"
                (Ast.Loc.to_string vi.Ast.vi_loc) sz;
              let buf = Buffer.create 0 in
              let _oc = new Xchannel.out_channel (Xchannel.Destination.of_buffer buf) in
              let oc = Spec_base.OutChannel.of_xchannel _oc in
              let _ = n#unparse_ch oc in
              let u = Buffer.contents buf in
              let _ = Spec_base.OutChannel.close oc in
              let nd_ = self#mkleaf (L.HugeArray(sz, u)) in
              self#reg_huge_array nd nd_;
              nd_
            end
            else
              nd
          end
          else
            nd
        in
        set_loc nd vi.Ast.vi_loc;
        nd
    end
    | Ast.VIerror s -> begin
        let nd = self#mkleaf (L.Error s) in
        set_loc nd vi.Ast.vi_loc;
        nd
    end

  method of_variable_declarator ?(is_static=false) vd =
    let loc = conv_loc vd.Ast.vd_loc in
    let (iloc, name), dims = vd.Ast.vd_variable_declarator_id in
    let children =
      match vd.Ast.vd_variable_initializer with
      | None -> []
      | Some init -> [self#of_variable_initializer init]
    in
    let ordinal_tbl_opt = Some (new ordinal_tbl [List.length children]) in
    let id_loc =
      if iloc == Ast.Loc.dummy then
        Loc.dummy
      else
        conv_loc iloc
    in
    let nd =
      self#mknode ~ordinal_tbl_opt ~id_loc (L.VariableDeclarator(name, List.length dims)) children
    in
    nd#data#set_loc loc;
    if is_static then
      Xset.add static_vdtors nd;
    nd

  method vdids_to_str vdids = String.concat ";" (List.map (fun ((_, id), _) -> id) vdids)

  method of_local_variable_declaration ?(remove_final=false) ~is_stmt lvd =
    let mods = lvd.Ast.lvd_modifiers in
    let vdtors = lvd.Ast.lvd_variable_declarators in

    if options#normalize_ast_flag then begin
      let _mklvdecl ghost vd vdnd =
        let ty_leaf = self#of_javatype [] lvd.Ast.lvd_type in
        let vdid = vd.Ast.vd_variable_declarator_id in
        let (_, vdid_id), vdid_dims = vdid in
        let vdid_ = vdid_id, List.length vdid_dims in
        let orig_lab_opt = Some (L.LocalVariableDeclaration(is_stmt, [strip_vdid vdid_])) in
        let mod_nodes = self#of_modifiers_opt ~remove_final (L.Klocal vdid_id) mods in
        let ordinal_tbl_opt = Some (new ordinal_tbl [List.length mod_nodes; 1; 1]) in
        let children = mod_nodes @ [ty_leaf; vdnd] in
        let nd =
          self#mknode ~orig_lab_opt ~ordinal_tbl_opt
            (L.LocalVariableDeclaration(is_stmt, [vdid_])) children
        in
        if ghost then begin
          nd#data#set_loc Loc.ghost;
          List.iter set_ghost_rec mod_nodes;
          set_ghost_rec ty_leaf
        end
        else
          set_loc nd lvd.Ast.lvd_loc;
        nd
      in
      let mklvdecl ghost vd =
        _mklvdecl ghost vd (self#of_variable_declarator vd)
      in
      match vdtors with
      | []       -> []
      | [vd]     -> [mklvdecl false vd]
      | vd::rest ->
          let lvdecl_nd = mklvdecl false vd in
          let rest_vdnds = List.map self#of_variable_declarator rest in
          List.iter (fun vn -> self#add_true_parent vn#uid lvdecl_nd) rest_vdnds;
          lvdecl_nd :: (List.map2 (fun v vn -> _mklvdecl true v vn) rest rest_vdnds)
    end
    else begin
      let vdids = List.map (fun vd -> vd.Ast.vd_variable_declarator_id) vdtors in
      let vdids_ =
        List.map
          (fun vd ->
            let (_, vdid_id), vdid_dims = vd.Ast.vd_variable_declarator_id in
            vdid_id, List.length vdid_dims
          ) vdtors
      in
      let vdids_str = self#vdids_to_str vdids in
      let orig_lab_opt = Some (L.LocalVariableDeclaration (is_stmt, List.map strip_vdid vdids_)) in
      let mod_nodes = self#of_modifiers_opt ~remove_final (L.Klocal vdids_str) mods in
      let ordinal_tbl_opt = Some (new ordinal_tbl [List.length mod_nodes; 1; List.length vdtors]) in
      let ty_leaf = self#of_javatype [] lvd.Ast.lvd_type in
      let nd =
        self#mknode ~orig_lab_opt ~ordinal_tbl_opt (L.LocalVariableDeclaration(is_stmt, vdids_))
          (mod_nodes @
           [ty_leaf] @
           (List.map self#of_variable_declarator vdtors))
      in
      set_loc nd lvd.Ast.lvd_loc;
      [nd]
    end

  method of_literal lit =
    let anonymize_int = options#anonymize_int_flag in
    let anonymize_float = options#anonymize_float_flag in
    let anonymize_string = options#anonymize_string_flag in
    let orig_lab_opt, lab =
      if anonymize_int || anonymize_float || anonymize_string then
        (Some (L.of_literal ~reduce:options#ast_reduction_flag lit)),
        L.of_literal
          ~anonymize_int ~anonymize_float ~anonymize_string ~reduce:options#ast_reduction_flag
          lit
      else
        None, L.of_literal ~reduce:options#ast_reduction_flag lit
    in
    self#mkleaf ~orig_lab_opt lab

  method is_empty_arguments args = args.Ast.as_arguments = []

  method digest_of_arguments args =
    let t = new c options (self#of_arguments args) false in
    t#digest

  method addhash s h = sprintf "%s:%s" s h


  method of_type_arguments ?(nth=1) name tas =
    let children = List.map self#of_type_argument tas.Ast.tas_type_arguments in
    (*let ordinal_tbl_opt = Some (new ordinal_tbl [List.length children]) in*)
    let nd = self#mknode (*~ordinal_tbl_opt*) (L.TypeArguments(nth, name)) children in
    set_loc nd tas.Ast.tas_loc;
    nd

  method of_type_arguments_opt ?(nth=1) name targs_opt =
    of_opt (self#of_type_arguments ~nth name) targs_opt

  method of_type_argument ta =
    let nd =
      match ta.Ast.ta_desc with
      | Ast.TAreferenceType ty -> self#of_javatype [] ty
      | Ast.TAwildcard wc      -> self#of_wildcard wc
    in
    set_loc nd ta.Ast.ta_loc;
    nd

  method of_wildcard (al, wb_opt) =
    let a_nodes = self#of_annotations al in
    let wb_nodes =
      match wb_opt with
      | None -> []
      | Some wb -> [self#of_wildcard_bounds wb]
    in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length a_nodes;
                             List.length wb_nodes;
                           ])
    in
    let children = a_nodes @ wb_nodes in
    let nd = self#mknode ~ordinal_tbl_opt L.Wildcard children in
    set_nodes_loc nd children;
    nd

  method of_wildcard_bounds wb =
    let nd =
      match wb.Ast.wb_desc with
      | Ast.WBextends ty -> self#mknode L.WildcardBoundsExtends [self#of_javatype [] ty]
      | Ast.WBsuper ty   -> self#mknode L.WildcardBoundsSuper [self#of_javatype [] ty]
    in
    set_loc nd wb.Ast.wb_loc;
    nd

  method _of_arguments ?(orig_lab_opt=None) lab args =
    let children = List.map self#of_expression args.Ast.as_arguments in
    (*let ordinal_tbl_opt = Some (new ordinal_tbl [List.length children]) in*)
    let nd = self#mknode ~orig_lab_opt (*~ordinal_tbl_opt*) lab children in
    set_loc nd args.Ast.as_loc;
    nd

  method of_arguments args = self#_of_arguments L.Arguments args

  method of_named_arguments ?(orig_lab_opt=None) name args =
    self#_of_arguments ~orig_lab_opt (L.NamedArguments name) args

  method of_named_arguments_opt ?(orig_lab_opt=None) name args_opt =
    of_opt (self#of_named_arguments ~orig_lab_opt name) args_opt

  method of_class_instance_creation ?(is_stmt=false) cic =

    let deco id args =
      id^".<init>#"^(string_of_int (List.length args.Ast.as_arguments))
    in

    let create ?(orig_lab_opt=None) plab children otbl =
      let lab = L.mkplab is_stmt plab in
      let orig_lab_opt =
        match orig_lab_opt with
        | Some l -> Some (L.mkplab is_stmt l)
        | None -> None
      in
      let ordinal_tbl_opt = Some (new ordinal_tbl otbl) in
(*
      let children =
        if is_stmt then
          let n = self#mknode (L.mkplab false plab) children in
          set_loc n cic.Ast.cic_loc;
          [n]
        else
          children
      in
*)
      self#mknode ~orig_lab_opt ~ordinal_tbl_opt lab children
    in
    match cic.Ast.cic_desc with
    | Ast.CICunqualified(targs_opt, ty, args, body_opt) ->
        let orig_name = P.type_to_string ~show_attr:false ty in
        let name = P.type_to_string ~resolve:true ~show_attr:false ty in
        let args_nd =
          let orig_lab_opt = Some (L.NamedArguments orig_name) in
          [self#of_named_arguments ~orig_lab_opt (deco name args) args]
        in
        let ta_nodes = self#of_type_arguments_opt name targs_opt in
        let cb_nodes = self#of_class_body_opt ~in_method:true name body_opt in
        let otbl =
          [List.length ta_nodes;
           1;
           1;
           List.length cb_nodes;
         ]
        in
        let children =
          ta_nodes @ [self#of_javatype [] ty] @ args_nd @ cb_nodes
        in
        let orig_lab_opt =
          Some (L.Primary.InstanceCreation orig_name)
        in
        let plab = L.Primary.InstanceCreation (deco name args) in
        create ~orig_lab_opt plab children otbl

    | Ast.CICqualified(prim, targs_opt1, ident, targs_opt2, args, body_opt) ->
        let args_nd = [self#of_named_arguments ident args] in
        let ta_nodes1 = self#of_type_arguments_opt ident targs_opt1 in
        let ta_nodes2 = self#of_type_arguments_opt ~nth:2 ident targs_opt2 in
        let cb_nodes = self#of_class_body_opt ~in_method:true ident body_opt in
        let otbl =
          [1;
           List.length ta_nodes1;
           List.length ta_nodes2;
           1;
           List.length cb_nodes;
         ]
        in
        let children =
          (self#of_primary prim) ::
          (ta_nodes1 @ (* ! *)
           ta_nodes2 @
           args_nd @
           cb_nodes) (* ! *)
        in
        let orig_lab_opt =
          Some (L.Primary.QualifiedInstanceCreation ident)
        in
        let plab = L.Primary.QualifiedInstanceCreation (deco ident args) in
        create ~orig_lab_opt plab children otbl

    | Ast.CICnameQualified(name, targs_opt1, ident, targs_opt2, args, body_opt) ->
        let n = L.conv_name name in
        let args_nd = [self#of_named_arguments ident args] in
        let ta_nodes1 = self#of_type_arguments_opt n targs_opt1 in
        let ta_nodes2 = self#of_type_arguments_opt ~nth:2 ident targs_opt2 in
        let cb_nodes = self#of_class_body_opt ~in_method:true n body_opt in
        let otbl =
          [List.length ta_nodes1;
           List.length ta_nodes2;
           1;
           List.length cb_nodes;
         ]
        in
        let children = ta_nodes1 @ ta_nodes2 @ args_nd @ cb_nodes in
        let orig_lab_opt =
          Some (L.Primary.NameQualifiedInstanceCreation(L.conv_name ~resolve:false name, ident))
        in
        let plab = L.Primary.NameQualifiedInstanceCreation(n, deco ident args) in
        create ~orig_lab_opt plab children otbl


  method of_field_access = function
    | Ast.FAprimary(prim, name) ->
        self#mknode (L.Primary (L.Primary.FieldAccess name)) [self#of_primary prim]
    | Ast.FAsuper name ->
        self#mkleaf (L.Primary (L.Primary.SuperFieldAccess name))
    | Ast.FAclassSuper(classname, name) ->
        self#mknode (L.Primary (L.Primary.ClassSuperFieldAccess name))
          [self#mkleaf (L.of_classname classname)]
    | Ast.FAimplicit name -> self#mkleaf (L.Primary (L.Primary.FieldAccess (Ast.rightmost_identifier name)))


  method of_method_invocation ?(is_stmt=false) mi =

    let deco id args =
      id^"#"^(string_of_int (List.length args.Ast.as_arguments))
    in

    let create ?(orig_lab_opt=None) plab children otbl =
      let ordinal_tbl_opt = Some (new ordinal_tbl otbl) in
      let tid = ref L.null_tid in
(*
      let children =
        if is_stmt then
          let n = self#mknode (L.mkplab false plab) children in
          tid := self#_mktid n;
          set_loc n mi.Ast.mi_loc;
          [n]
        else
          children
      in
*)
      let orig_lab_opt =
        match orig_lab_opt with
        | Some l -> Some (L.mkplab is_stmt l)
        | None -> None
      in
      let lab = L.mkplab ~tid:!tid is_stmt plab in
      self#mknode ~orig_lab_opt ~ordinal_tbl_opt lab children
    in
    let nd =
      match mi.Ast.mi_desc with
      | Ast.MImethodName(name, args) ->

          let rightmost = Ast.rightmost_identifier name in
(*
  let mname = L.conv_name name in
 *)
          let q = qualifier_of_name name in
          let a_node = self#of_named_arguments rightmost args in
          let otbl = [if q <> None then 1 else 0; 1] in
          let children =
            match q with
            | None -> [a_node]
            | Some n -> (* !!! *)
                let orig_lab_opt = Some (L.Qualifier (L.conv_name ~resolve:false n)) in
                let qnd = self#mkleaf ~orig_lab_opt (L.Qualifier (L.conv_name n)) in
                qnd#data#set_loc (loc_of_name n);
                [qnd; a_node]
          in
(*
  let hash = self#digest_of_arguments args in
  let rightmost = self#addhash rightmost hash in
 *)
          let orig_lab_opt = Some (L.Primary.SimpleMethodInvocation rightmost) in
          let plab = L.Primary.SimpleMethodInvocation (deco rightmost args) in
          create ~orig_lab_opt plab children otbl

      | Ast.MIprimary(prim, targs_opt, ident, args) ->
(*
  let hash = self#digest_of_arguments args in
  let ident = self#addhash ident hash in
 *)
          let prim_nd = self#of_primary prim in
          let orig_lab_opt = Some (L.Primary.PrimaryMethodInvocation ident) in
          let plab =
            (*if L.is_ambiguous_name (getlab prim_nd) then
              L.Primary.AmbiguousMethodInvocation (deco ident args)
            else*)
              L.Primary.PrimaryMethodInvocation (deco ident args)
          in
          let ta_nodes = self#of_type_arguments_opt ident targs_opt in
          let otbl = [1; List.length ta_nodes; 1] in
          let children =
            prim_nd :: (ta_nodes @ [self#of_named_arguments ident args])
          in
          create ~orig_lab_opt plab children otbl

      | Ast.MItypeName(name, targs_opt, ident, args) ->
          let n = L.conv_name name in
(*
  let hash = self#digest_of_arguments args in
  let ident = self#addhash ident hash in
 *)
          let orig_lab_opt, orig_ty_name =
            let n = L.conv_name ~resolve:false name in
            Some (L.Primary.TypeMethodInvocation(n, ident(*deco ident args*))), n
          in
          let plab = L.Primary.TypeMethodInvocation(n, deco ident args) in
          let ty_node =
            let orig_lab_opt = Some (L.Type (L.Type.Class orig_ty_name)) in
            let nd = self#mkleaf ~orig_lab_opt (L.Type (L.Type.Class n)) in
            let loc = Astloc.collapse_forward ~len:(String.length orig_ty_name) mi.Ast.mi_loc in
            set_loc nd loc;
            nd
          in
          let ta_nodes = self#of_type_arguments_opt ident targs_opt in
          let otbl = [1; List.length ta_nodes; 1] in
          let children = ty_node :: ta_nodes @ [self#of_named_arguments ident args] in
          create ~orig_lab_opt plab children otbl

      | Ast.MIsuper(loc_super, targs_opt, ident, args) ->
          let snd = self#mkleaf L.Super in
          set_loc snd loc_super;
(*
  let hash = self#digest_of_arguments args in
  let ident = self#addhash ident hash in
 *)
          let orig_lab_opt = Some (L.Primary.SuperMethodInvocation ident) in
          let plab = L.Primary.SuperMethodInvocation (deco ident args) in
          let ta_nodes = self#of_type_arguments_opt ident targs_opt in
          let otbl = [1; List.length ta_nodes; 1] in
          let children =
            snd::(ta_nodes @ [self#of_named_arguments ident args])
          in
          create ~orig_lab_opt plab children otbl

      | Ast.MIclassSuper(loc_cl, loc_super, classname, targs_opt, ident, args) ->
          let cnd =
            self#mkleaf
              ~orig_lab_opt:(Some (L.of_classname ~resolve:false classname))
              (L.of_classname classname)
          in
          set_loc cnd loc_cl;
          let snd = self#mkleaf L.Super in
          set_loc snd loc_super;
(*
  let hash = self#digest_of_arguments args in
  let ident = self#addhash ident hash in
 *)
          let orig_lab_opt = Some (L.Primary.ClassSuperMethodInvocation ident) in
          let plab = L.Primary.ClassSuperMethodInvocation (deco ident args) in
          let ta_nodes = self#of_type_arguments_opt ident targs_opt in
          let otbl = [1; 1; List.length ta_nodes; 1] in
          let children =
            cnd::snd::(ta_nodes @ [self#of_named_arguments ident args])
          in
          create ~orig_lab_opt plab children otbl

    in
    set_loc nd mi.Ast.mi_loc;
    nd


  method of_array_access aa =
    let children =
      match aa.Ast.aa_desc with
      | Ast.AAname(name, expr) ->
          let pnd =
            let orig_lab_opt =
              Some (L.Primary (L.Primary.Name (L.conv_name ~resolve:false name)))
            in
            self#mkleaf ~orig_lab_opt (L.Primary (L.Primary.Name (L.conv_name name)))
          in
          set_loc pnd name.Ast.n_loc;
          [pnd; self#of_expression expr]
      | Ast.AAprimary(prim, expr) -> [self#of_primary prim; self#of_expression expr]
    in
    let nd = self#mknode (L.Primary L.Primary.ArrayAccess) children in
    set_loc nd aa.Ast.aa_loc;
    nd

  method of_dim_expr de =
    let en = self#of_expression de.Ast.de_desc in
    let nd = self#mknode L.DimExpr [en] in
    set_loc nd de.Ast.de_loc;
    nd

  method of_array_creation_expression = function
    | Ast.ACEtype(ty, exprs, dims) ->
        let ordinal_tbl_opt = Some (new ordinal_tbl [1; List.length exprs]) in
        self#mknode ~ordinal_tbl_opt (L.Primary (L.Primary.ArrayCreationDims (List.length dims)))
          ((self#of_javatype [] ty) :: (List.map self#of_dim_expr exprs))

    | Ast.ACEtypeInit(_, _, [array_initializer]) when options#ast_reduction_flag ->
        self#of_variable_initializer array_initializer

    | Ast.ACEtypeInit(ty, dims, array_initializer) ->
        let ordinal_tbl_opt = Some (new ordinal_tbl [1; List.length array_initializer]) in
        let ty_nd = self#of_javatype dims ty in
        self#mknode ~ordinal_tbl_opt (L.Primary L.Primary.ArrayCreationInit)
          (ty_nd :: (List.map self#of_variable_initializer array_initializer))

  method of_name loc0 name =
    let name_to_node ?(children=[]) mkplab n =
      let unresolved = L.conv_name ~resolve:false n in
      let resolved =
        if options#partial_name_resolution_flag then
          unresolved
        else
          L.conv_name n
      in
      let orig_lab_opt = Some (L.Primary (mkplab unresolved)) in
      let nd = self#mknode ~orig_lab_opt (L.Primary (mkplab resolved)) children in
      let loc = Ast.Loc.widen loc0 (String.length unresolved) in
      set_loc nd loc;
      nd
    in
    match qualifier_of_name name with
    | None -> begin
        let mklab =
          if Ast.is_ambiguous_name name then
            (fun x -> L.Primary.AmbiguousName x)
          else
            (fun x -> L.Primary.Name x)
        in
        name_to_node mklab name
    end
    (*| Some _ when options#partial_name_resolution_flag -> begin
        let mklab =
          if Ast.is_ambiguous_name name then
            (fun x -> L.Primary.AmbiguousName x)
          else
            (fun x -> L.Primary.Name x)
        in
        name_to_node mklab name
    end*)
    | Some q -> begin
        let mkplab =
          if Ast.is_ambiguous_name q then
            fun x -> L.Primary.AmbiguousName x
          else
            fun x -> L.Primary.Name x
        in
        let mknd ?(children=[]) =
          name_to_node ~children mkplab
        in
        let rec doit n =
          try
            let n0, _ = Ast.decompose_name n in
            mknd ~children:[doit n0] n
          with
            _ -> mknd n
        in
        doit name
(*
        if Ast.is_ambiguous_name q then begin
          if
            options#rely_on_naming_convention_flag &&
            (*Ast.is_simple q &&*)
            Ast.is_rightmost_id_capitalized q
          then begin
            (* assumes a type name starts with a capital letter *)
            name_to_node (fun x -> L.Primary.AmbiguousName x) name
          end
          else(* if options#fact_flag then*) begin
            let mknd ?(children=[]) =
              name_to_node ~children (fun x -> L.Primary.AmbiguousName x)
            in
            let rec doit n =
              try
                let n0, _ = Ast.decompose_name n in
                mknd ~children:[doit n0] n
              with
                _ -> mknd n
            in
            doit name
          end
          (*else begin
            name_to_node (fun x -> L.Primary.AmbiguousName x) name
          end*)
        end
        else
          name_to_node (fun x -> L.Primary.Name x) name
*)
    end

  method of_primary p =
    let nd =
      match p.Ast.p_desc with
      | Ast.Pname name -> let loc0 = Ast.Loc.collapse_forward p.Ast.p_loc in self#of_name loc0 name
      | Ast.Pliteral lit -> self#of_literal lit
      | Ast.PclassLiteral ty -> self#mknode (L.Primary L.Primary.ClassLiteral) [self#of_javatype [] ty]
      | Ast.PclassLiteralVoid -> self#mkleaf (L.Primary (L.Primary.ClassLiteralVoid))
      | Ast.Pthis -> self#mkleaf (L.Primary L.Primary.This)
      | Ast.PqualifiedThis name ->
          let orig_lab_opt =
            Some (L.Primary (L.Primary.QualifiedThis (L.conv_name ~resolve:false name)))
          in
          self#mkleaf ~orig_lab_opt (L.Primary (L.Primary.QualifiedThis (L.conv_name name)))

      | Ast.Pparen expr when options#ast_reduction_flag -> self#of_expression expr

      | Ast.Pparen expr ->
          let e_nd = self#of_expression expr in
          let tid = self#mktid e_nd in
          self#mknode (L.Primary (L.Primary.Paren tid)) [e_nd]

      | Ast.PclassInstanceCreation class_instance_creation ->
          self#of_class_instance_creation class_instance_creation

      | Ast.PfieldAccess field_acc -> self#of_field_access field_acc
      | Ast.PmethodInvocation meth_inv -> self#of_method_invocation meth_inv
      | Ast.ParrayAccess arr_acc -> self#of_array_access arr_acc
      | Ast.ParrayCreationExpression array_creation ->
          self#of_array_creation_expression array_creation

      | Ast.PmethodReference method_reference ->
          self#of_method_reference method_reference

      | Ast.Perror s -> self#mkleaf (L.Error s)
    in
    set_loc nd p.Ast.p_loc;
    nd

  method of_method_reference mr =
    let mkprim ?(orig_lab_opt=None) ordinal_tbl_opt l c =
      let orig_lab_opt =
        match orig_lab_opt with
        | Some l -> Some (L.Primary l)
        | None -> None
      in
      self#mknode ~orig_lab_opt ~ordinal_tbl_opt (L.Primary l) c
    in
    match mr.Ast.mr_desc with
  | Ast.MRname(n, tas_opt, id) ->
      let ta_nodes = self#of_type_arguments_opt id tas_opt in
      let ordinal_tbl_opt = Some (new ordinal_tbl [List.length ta_nodes]) in
      let orig_lab_opt =
        Some (L.Primary.NameMethodReference(L.conv_name ~resolve:false n, id))
      in
      mkprim ~orig_lab_opt ordinal_tbl_opt
        (L.Primary.NameMethodReference(L.conv_name n, id)) ta_nodes

  | Ast.MRprimary(p, tas_opt, id) ->
      let ta_nodes = self#of_type_arguments_opt id tas_opt in
      let ordinal_tbl_opt = Some (new ordinal_tbl [1; List.length ta_nodes]) in
      mkprim ordinal_tbl_opt
        (L.Primary.PrimaryMethodReference id) ((self#of_primary p) :: ta_nodes)

  | Ast.MRsuper(tas_opt, id) ->
      let ta_nodes = self#of_type_arguments_opt id tas_opt in
      let ordinal_tbl_opt = Some (new ordinal_tbl [List.length ta_nodes]) in
      mkprim ordinal_tbl_opt
        (L.Primary.SuperMethodReference id) ta_nodes

  | Ast.MRtypeSuper(n, tas_opt, id) ->
      let ta_nodes = self#of_type_arguments_opt id tas_opt in
      let ordinal_tbl_opt = Some (new ordinal_tbl [List.length ta_nodes]) in
      let orig_lab_opt =
        Some (L.Primary.TypeSuperMethodReference(L.conv_name ~resolve:false n, id))
      in
      mkprim ~orig_lab_opt ordinal_tbl_opt
        (L.Primary.TypeSuperMethodReference(L.conv_name n, id)) ta_nodes

  | Ast.MRtypeNew(ty, tas_opt) ->
      let ta_nodes = self#of_type_arguments_opt "" tas_opt in
      let ordinal_tbl_opt = Some (new ordinal_tbl [1; List.length ta_nodes]) in
      let ty_node = self#of_javatype [] ty in
      let n = L.get_name (getlab ty_node) in
      let orig_lab_opt =
        match get_orig_lab_opt ty_node with
        | Some lab -> Some (L.Primary.TypeNewMethodReference(L.get_name lab))
        | None -> None
      in
      mkprim ~orig_lab_opt ordinal_tbl_opt
        (L.Primary.TypeNewMethodReference(n)) (ty_node::ta_nodes)

  method of_assignment ?(is_stmt=false) (lhs, ao, expr) =
    let lhs_ = self#of_expression lhs in
    let lab = L.of_assignment_operator ~is_stmt ao L.null_tid(*(self#mktid lhs_)*) in
    let children = [lhs_; self#of_expression expr] in
(*
   let children =
     if is_stmt then
       let n = self#mknode (L.of_assignment_operator ~is_stmt:false ao) children in
       set_loc n ao.Ast.ao_loc;
       [n]
     else
       children
   in
*)
   let nd = self#mknode lab children in
   set_loc nd ao.Ast.ao_loc;
   nd

  method of_expression ?(sub=false) ?(is_stmt=false) e =
    [%debug_log "sub=%B is_stmt=%B" sub is_stmt];
    let nd =
      match e.Ast.e_desc with
      | Ast.Eprimary prim -> self#of_primary prim

      | Ast.Eunary(unary_op, expr) ->
          self#mknode (L.of_unary_operator ~is_stmt unary_op) [self#of_expression expr]

      | Ast.Ebinary(bin_op, expr1, expr2) -> begin
          [%debug_log "bin_op=(%s)" (P.binary_operator_to_string bin_op)];
          let nd =
            self#mknode (L.of_binary_operator bin_op)
              [self#of_expression ~sub:true expr1; self#of_expression ~sub:true expr2]
          in
          [%debug_log "nd=%s" nd#to_string];
          let is_add n = L.is_binary_add (getlab n) in
          if not sub && options#ignore_huge_exprs_flag then begin
            [%debug_log "@"];
            let t = new c options nd false in
            let _ = t#setup_initial_children in
            (*let _ = t#setup_initial_size in
              let sz = t#initial_size in*)
            let sz =
              let c = ref 0 in
              t#scan_whole_initial
                (fun n ->
                  if L.is_literal (getlab n) then
                    incr c
                );
              !c
            in
            if sz >= options#huge_expr_threshold then begin
              Xprint.verbose options#verbose_flag "huge expression found at %s (size=%d)"
                (Ast.Loc.to_string e.Ast.e_loc) sz;
              let buf = Buffer.create 0 in
              let _oc = new Xchannel.out_channel (Xchannel.Destination.of_buffer buf) in
              let oc = Spec_base.OutChannel.of_xchannel _oc in
              let _ = t#unparse_ch oc in
              let u = Buffer.contents buf in
              let _ = Spec_base.OutChannel.close oc in
              self#mkleaf (L.HugeExpr(sz, u))
            end
            else if is_add nd then begin
              [%debug_log "@"];
              let t = new c options nd false in
              let _ = t#setup_initial_children in
              [%debug_log "t:\n%s" t#to_string];
              let children = ref [] in
              try
                let rec scan n =
                  [%debug_log "n=%s" n#to_string];
                  if is_add n then begin
                    children := n#children.(1) :: !children;
                    scan n#children.(0)
                  end
                  else
                    children := n :: !children
                in
                scan t#root;
                let nc = List.length !children in
                [%debug_log "nc=%d" nc];
                if nc > 3 then
                  self#mknode (L.Expression L.Expression.NaryAdd) !children
                else
                  nd
              with
                _ -> nd
            end
            else
              nd
          end
          else
            nd
      end
      | Ast.Ecast(ty, expr) ->
          self#mknode (L.Expression L.Expression.Cast)
            [self#of_javatype [] ty; self#of_expression expr]

      | Ast.Einstanceof(expr, ty) ->
          self#mknode (L.Expression L.Expression.Instanceof)
            [self#of_expression expr; self#of_javatype [] ty]

      | Ast.EinstanceofP(expr, lvd) ->
          self#mknode (L.Expression L.Expression.Instanceof)
            ((self#of_expression expr)::(self#of_local_variable_declaration ~is_stmt:false lvd))

      | Ast.Econd(expr1, expr2, expr3) ->
          self#mknode (L.Expression L.Expression.Cond)
            [self#of_expression expr1; self#of_expression expr2; self#of_expression expr3]

      | Ast.Eassignment assignment -> self#of_assignment ~is_stmt assignment

      | Ast.Eswitch(e, switch_block) ->
          self#mknode (L.Expression L.Expression.Switch)
            [self#of_expression e; self#of_switch_block switch_block]

      | Ast.Elambda(params, body) ->
          self#mknode (L.Expression L.Expression.Lambda)
            [self#of_lambda_params params; self#of_lambda_body body]

      | Ast.Eerror s -> self#mkleaf (L.Error s)
    in
    set_loc nd e.Ast.e_loc;
    nd

  method of_lambda_params params =
    match params.Ast.lp_desc with
    | Ast.LPident id     ->
        let nd = self#mkleaf (L.InferredFormalParameter id) in
        set_loc nd params.Ast.lp_loc;
        nd

    | Ast.LPformal fps ->
        let nd = self#mknode (L.Parameters "") (List.map self#of_parameter fps) in
        set_loc nd params.Ast.lp_loc;
        nd

    | Ast.LPinferred [(loc, id)] when options#ast_reduction_flag ->
        let nd = self#mkleaf (L.InferredFormalParameter id) in
        set_loc nd loc;
        nd

    | Ast.LPinferred ids ->
        let mkp (loc, id) =
          let n = self#mkleaf (L.InferredFormalParameter id) in
          set_loc n loc;
          n
        in
        let nd = self#mknode (L.InferredFormalParameters) (List.map mkp ids) in
        set_loc nd params.Ast.lp_loc;
        nd

  method of_lambda_body = function
    | Ast.LBexpr expr   -> self#of_expression expr
    | Ast.LBblock block -> self#of_block ~tid:(self#__mktid "lambda") block


  method of_statement_expression ?(is_stmt=false) se =
    let nd =
      match se.Ast.se_desc with
      | Ast.SEassignment assign  -> self#of_assignment ~is_stmt assign
      | Ast.SEpreIncrement expr  -> self#of_expression ~is_stmt expr
      | Ast.SEpreDecrement expr  -> self#of_expression ~is_stmt expr
      | Ast.SEpostIncrement expr -> self#of_expression ~is_stmt expr
      | Ast.SEpostDecrement expr -> self#of_expression ~is_stmt expr

      | Ast.SEmethodInvocation method_invocation ->
          self#of_method_invocation ~is_stmt method_invocation

      | Ast.SEclassInstanceCreation class_instance_creation ->
          self#of_class_instance_creation ~is_stmt class_instance_creation

      | Ast.SEerror s -> self#mkleaf (L.Error s)
    in
    set_loc nd se.Ast.se_loc;
    nd

  method of_switch_label sl =
    let nd =
      match sl.Ast.sl_desc with
      | Ast.SLconstant el -> begin
          let _nd = self#mknode (L.SLconstant L.null_tid) (List.map self#of_expression el) in
          let tid = self#mktid _nd in
          self#mknode (L.SLconstant tid) (List.map self#of_expression el)
      end
      | Ast.SLdefault -> self#mkleaf L.SLdefault
    in
    set_loc nd sl.Ast.sl_loc;
    nd

  method of_switch_block_statement_group (sls, bss) =
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length sls; List.length bss])
    in
    let children =
      (List.map self#of_switch_label sls) @
      (List.concat_map self#of_block_statement bss)
    in
    let nd = self#mknode ~ordinal_tbl_opt L.SwitchBlockStatementGroup children in
    set_nodes_loc nd children;
    nd

  method of_switch_rule_label srl =
    let nd =
      match srl.Ast.srl_desc with
      | Ast.SLconstant el -> self#mknode L.SRLconstant (List.map self#of_expression el)
      | Ast.SLdefault -> self#mkleaf L.SRLdefault
    in
    set_loc nd srl.Ast.srl_loc;
    nd

  method of_switch_rule_body srb =
    let nd =
      match srb.Ast.srb_desc with
      | Ast.SRBexpr e -> self#of_expression e
      | Ast.SRBblock b -> self#of_block ~tid:(self#__mktid "switch-rule") b
      | Ast.SRBthrow t -> self#of_statement t
    in
    set_loc nd srb.Ast.srb_loc;
    nd

  method of_switch_rule (srl, srb) =
    let children = [self#of_switch_rule_label srl; self#of_switch_rule_body srb] in
    let nd = self#mknode L.SwitchRule children in
    set_nodes_loc nd children;
    nd

  method of_resource r =
    match r.Ast.r_desc with
    | Ast.RlocalVarDecl lvd -> begin
        let remove_final = options#ast_reduction_flag in
        match self#of_local_variable_declaration ~remove_final ~is_stmt:false lvd with
        | [nd] -> nd
        | _ -> assert false
    end
    | Ast.RfieldAccess fa -> self#of_field_access fa
    | Ast.Rname name -> begin
        let loc0 = Ast.Loc.collapse_forward r.Ast.r_loc in
        let nd = self#of_name loc0 name in
        set_loc nd r.Ast.r_loc;
        nd
    end

  method of_resource_spec rs =
    let rl = List.map self#of_resource rs.Ast.rs_resources in
    let nd = self#mknode L.ResourceSpec rl in
    set_loc nd rs.Ast.rs_loc;
    nd

  method of_catch_parameter param =
    let (iloc, name), dims = param.Ast.cfp_variable_declarator_id in
    let mods = param.Ast.cfp_modifiers in
    let mod_nodes = self#of_modifiers_opt (L.Kparameter name) mods in
    let type_nodes = List.map (self#of_javatype []) param.Ast.cfp_type_list in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length mod_nodes; List.length type_nodes])
    in
    let id_loc =
      if iloc == Ast.Loc.dummy then
        Loc.dummy
      else
        conv_loc iloc
    in
    let nd =
      self#mknode ~ordinal_tbl_opt ~id_loc
        (L.CatchParameter(name, List.length dims)) (mod_nodes @ type_nodes)
    in
    set_loc nd param.Ast.cfp_loc;
    nd

  method of_catch c =
    let p_ = self#of_catch_parameter c.Ast.c_formal_parameter in
    let tid = self#mktid p_ in
    let nd =
      self#mknode (L.CatchClause tid)
        [p_; self#of_block ~tid:(self#__mktid "catch-clause") c.Ast.c_block]
    in
    set_loc nd c.Ast.c_loc;
    nd

  method of_finally f =
    let nd =
      self#mknode L.Finally [self#of_block ~tid:(self#__mktid "finally") f.Ast.f_block]
    in
    set_loc nd f.Ast.f_loc;
    nd

  method of_for_init fi =
    let nd =
      match fi.Ast.fi_desc with
      | Ast.FIstatement se_list ->
          let children = List.map self#of_statement_expression se_list in
          let tid =
            match children with
            | [] -> L.null_tid
            | n::_ -> self#mktid n
          in
          self#mklnode (L.ForInit tid) children

      | Ast.FIlocal lvd ->
          let lvd_ndl = self#of_local_variable_declaration ~is_stmt:false lvd in
          let tid =
            match lvd_ndl with
            | lvd_nd::_ -> self#mktid lvd_nd
            | _ -> assert false
          in
          self#mknode (L.ForInit tid) lvd_ndl
    in
    set_loc nd fi.Ast.fi_loc;
    nd

  method of_switch_block sb =
    let nd =
      self#mknode (L.SwitchBlock)
        ((List.map self#of_switch_block_statement_group sb.Ast.sb_switch_block_stmt_grps) @
         (List.map self#of_switch_rule sb.Ast.sb_switch_rules))
    in
    set_loc nd sb.Ast.sb_loc;
    nd

  method private gen_block s_ =
    let tid = self#__mktid "block" in
    let nd = self#mklnode (L.Block tid) [s_] in
    nd#data#set_loc s_#data#src_loc;
    nd

  method private normalize_block_stmt s_ =
    if options#normalize_ast_flag && not (L.is_block (getlab s_)) then
      self#gen_block s_
    else
      s_

  method of_statement ?(extra_locs=None) ?(block_context="block") s =
    (*[%debug_log "block_context=\"%s\" s.s_loc=%s" block_context (Astloc.to_string s.Ast.s_loc)];*)
    let nd =
      match s.Ast.s_desc with
      | Ast.Sblock block   -> self#of_block ~tid:(self#__mktid "block"(*block_context*)) block
      | Ast.Sempty         -> self#mkleaf (L.Statement L.Statement.Empty)
      | Ast.Sexpression se -> self#of_statement_expression ~is_stmt:true se

      | Ast.Sswitch(e, switch_block) ->
          self#mknode (L.Statement L.Statement.Switch)
            [self#of_expression e; self#of_switch_block switch_block]

      | Ast.Sdo(s, e) ->
          let s_ = self#of_statement ~block_context:"do" s in
          let s_ = self#normalize_block_stmt s_ in
          (self#mknode (L.Statement L.Statement.Do) [s_; self#of_expression e])

      | Ast.Sbreak ident_opt    -> self#mkleaf (L.Statement (L.Statement.Break ident_opt))

      | Ast.Scontinue ident_opt ->
          self#mkleaf (L.Statement (L.Statement.Continue ident_opt))

      | Ast.Sreturn e_opt ->
          self#mknode (L.Statement L.Statement.Return) (of_opt self#of_expression e_opt)

      | Ast.Ssynchronized(e, block) ->
          self#mknode (L.Statement L.Statement.Synchronized)
            [self#of_expression e; self#of_block ~tid:(self#__mktid "synchronized") block]

      | Ast.Sthrow e -> self#mknode (L.Statement L.Statement.Throw) [self#of_expression e]

      | Ast.Stry(rspec_opt, block, catches_opt, finally_opt) ->
          let catches =
            match catches_opt with
            | Some cl -> cl
            | None -> []
          in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [if rspec_opt = None then 0 else 1;
                                   1;
                                   List.length catches;
                                   if finally_opt = None then 0 else 1;
                                 ])
          in
          self#mknode ~ordinal_tbl_opt (L.Statement L.Statement.Try)
            ((of_opt self#of_resource_spec rspec_opt) @
             ((self#of_block ~tid:(self#__mktid "try") block) ::
              ((List.map self#of_catch catches) @ (of_opt self#of_finally finally_opt))))

      | Ast.Syield e -> self#mknode (L.Statement L.Statement.Yield) [self#of_expression e]

      | Ast.Slabeled(name, s) ->
          self#mknode (L.Statement (L.Statement.Labeled name)) [self#of_statement s]

      | Ast.SifThen(e, s) ->
          let e_ = self#of_expression e in
          let tid = self#mktid e_ in
          (*let tid = L.null_tid in*)
          let lab = L.Statement (L.Statement.If tid) in
          let s_ = self#of_statement ~block_context:"if" s in
          let s_ = self#normalize_block_stmt s_ in
          self#mknode lab [e_; s_] (* order sensitive s -> e *)

      | Ast.SifThenElse(e, s1, s2) -> begin

          if block_context = "if" then begin
            match extra_locs with
            | Some q -> Queue.add s.Ast.s_extra_loc q
            | None -> ()
          end;

          let rec get_depth x =
            match x.Ast.s_desc with
            | Ast.SifThenElse(_, _, s) -> 1 + get_depth s
            | Ast.SifThen _ -> 1
            | _ -> 0
          in
          let flatten_if =
            if options#flatten_if_flag && block_context <> "if" then begin
              let d = get_depth s2 in
              let b = d >= 0 in
              (*let b = d > options#deep_if_threshold in*)
              [%debug_log "flatten_if=%B (depth=%d)" b d];
              b
            end
            else
              false
          in

          let e_ = self#of_expression e in
          let tid = self#mktid e_ in
          (*let tid = L.null_tid in*)
          let lab = L.Statement (L.Statement.If tid) in
          let s1_ = self#of_statement ~block_context:"if" s1 in
          let extra_locs =
            if flatten_if then
              let q = Queue.create() in
              Queue.add s.Ast.s_extra_loc q;
              Some q
            else
              extra_locs
          in
          let s2_ = self#of_statement ~extra_locs ~block_context:"if" s2 in
          let s1_ = self#normalize_block_stmt s1_ in
          let s2_ = self#normalize_block_stmt s2_ in
          let nd = self#mknode lab [e_; s1_; s2_] in (* order sensitive s2 -> s1 -> e *)

          begin %debug_block
            if flatten_if then
              match extra_locs with
              | Some q -> begin
                  Queue.iter
                    (fun extra_loc ->
                      [%debug_log "extra_loc: %s"
                        (match extra_loc with
                        | Some loc -> Astloc.to_string ~short:true loc
                        | None -> "None"
                        )]
                    ) q
              end
              | None -> ()
          end;

          if flatten_if then begin
            let elseif_count = ref 0 in
            let else_count = ref 0 in
            let take_loc =
              match extra_locs with
              | Some q -> begin
                  fun () ->
                    match Queue.take q with
                    | Some loc -> conv_loc loc
                    | None -> raise Not_found
              end
              | None -> fun () -> assert false
            in
            let rec flatten ?(is_top=true) nd0 =
              let lab0 = getlab nd0 in
              let nchildren0 = nd0#nchildren in
              if is_top then
                if L.is_if lab0 then
                  if nchildren0 = 3 then
                    let next = nd0#children.(2) in
                    if L.is_if (getlab next) then begin
                      (*nd0#del_rightmost_child();
                      let loc_ = Loc._merge nd0#data#src_loc nd0#children.(1)#data#src_loc in
                      nd0#data#set_loc loc_;*)
                      nd0 :: (flatten ~is_top:false next)
                    end
                    else begin
                      let nd_ = self#mknode (L.Statement (L.Statement.Else)) [next] in
                      let loc_ =
                        match s.Ast.s_extra_loc with
                        | Some loc -> Loc._merge (conv_loc loc) next#data#src_loc
                        | None -> next#data#src_loc
                      in
                      nd_#data#set_loc loc_;
                      incr else_count;
                      [nd0; nd_]
                    end
                  else
                    assert false
                else
                  assert false
              else (* not is_top *)
                if L.is_if lab0 then
                  let lab_ =
                    match lab0 with
                    | L.Statement (L.Statement.If tid0) -> L.Statement (L.Statement.ElseIf tid0)
                    | _ -> assert false
                  in
                  if nchildren0 = 3 then begin
                    let next = nd0#children.(2) in
                    let loc_ =
                      try
                        Loc._merge (take_loc()) nd0#children.(1)#data#src_loc
                      with
                        _ -> Loc._merge nd0#data#src_loc nd0#children.(1)#data#src_loc
                    in
                    [%debug_log "loc_=%s" (Loc.to_string loc_)];
                    let nd_ = self#_mknode lab_ (Array.sub nd0#children 0 2) in
                    nd_#data#set_loc loc_;
                    incr elseif_count;
                    if L.is_if (getlab next) then
                      nd_ :: (flatten ~is_top:false next)
                    else begin
                      let nd__ = self#mknode (L.Statement (L.Statement.Else)) [next] in
                      let loc__ =
                        try
                          Loc._merge (take_loc()) next#data#src_loc
                        with
                          _ -> next#data#src_loc
                      in
                      nd__#data#set_loc loc__;
                      incr else_count;
                      [nd_; nd__]
                    end
                  end
                  else begin
                    let nd_ = self#_mknode lab_ nd0#children in
                    let loc_ =
                      try
                        Loc._merge (take_loc()) nd0#data#src_loc
                      with
                        _ -> nd0#data#src_loc;
                    in
                    nd_#data#set_loc loc_;
                    incr elseif_count;
                    [nd_]
                  end
                else
                  assert false
            in
            let children = flatten nd in
            match children with
            | nd0::rest -> begin
                [%debug_log "%s" nd0#to_string];
                let ca0 = nd0#children in
                (*[%debug_log "%d children found" (Array.length ca0)];*)
                let children' = ca0.(0)::ca0.(1)::rest in
                let ordinal_tbl_opt = Some (new ordinal_tbl [1; 1; !elseif_count; !else_count]) in
                self#mknode ~ordinal_tbl_opt (L.Statement (L.Statement.If tid)) children'
            end
            | _ -> assert false
            (*let ordinal_tbl_opt = Some (new ordinal_tbl [1; !elseif_count; !else_count]) in
            self#mknode ~ordinal_tbl_opt (L.Statement (L.Statement.FlattenedIf tid)) children*)
          end
          else
            nd
      end
      | Ast.Swhile(e, s) ->
          let s_ = self#of_statement ~block_context:"while" s in
          let s_ = self#normalize_block_stmt s_ in
          self#mknode (L.Statement L.Statement.While) [self#of_expression e; s_]

      | Ast.Sfor(init_opt, e_opt, se_list, s) ->
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [if init_opt = None then 0 else 1;
                                   if e_opt = None then 0 else 1;
                                   if se_list = [] then 0 else 1;
                                 ])
          in
          let children =
            (match init_opt with None -> [] | Some init -> [self#of_for_init init]) @
            (match e_opt with
            | None -> []
            | Some e ->
                let e_nd = self#of_expression e in
                let tid = self#mktid e_nd in
                let n = self#mknode (L.ForCond tid) [e_nd] in
                set_loc n e.Ast.e_loc;
                [n]
            ) @
            (if se_list <> []
            then begin
              let se_nodes = List.map self#of_statement_expression se_list in
              let tid =
                match se_nodes with
                | [] -> L.null_tid
                | n::_ -> self#mktid n
              in
              let n = self#mknode (L.ForUpdate tid) se_nodes in
              set_nodes_loc n se_nodes;
              [n]
            end
            else [])
          in
          let s_ = self#of_statement ~block_context:"for" s in
          let s_ = self#normalize_block_stmt s_ in
          let children, ordinal_tbl_opt =
            match children with
            | [] -> [s_], Some (new ordinal_tbl [0; 1])
            | cl -> begin
                let _head_nd = self#mknode ~ordinal_tbl_opt (L.ForHead L.null_tid) children in
                let tid = self#mktid _head_nd in
                let head_nd = self#mknode ~ordinal_tbl_opt (L.ForHead tid) children in
                let head_loc = Loc.merge (List.hd cl)#data#src_loc (Xlist.last cl)#data#src_loc in
                head_nd#data#set_loc head_loc;
                [head_nd; s_], Some (new ordinal_tbl [1; 1])
            end
          in
          self#mknode ~ordinal_tbl_opt (L.Statement L.Statement.For) children

      | Ast.SforEnhanced(param, e, s) ->
          let s_ = self#of_statement ~block_context:"for" s in
          let s_ = self#normalize_block_stmt s_ in
          self#mknode (L.Statement L.Statement.ForEnhanced)
            [self#of_for_header param;
             self#of_expression e;
             s_]

      | Ast.Sassert1 e ->
          self#mknode (L.Statement L.Statement.Assert) [self#of_expression e]

      | Ast.Sassert2(e1, e2) ->
          self#mknode (L.Statement L.Statement.Assert)
            [self#of_expression e1; self#of_expression e2]

      | Ast.Serror s -> self#mkleaf (L.Error s)
    in
    set_loc nd s.Ast.s_loc;
    nd

  method _of_block ?(orig_lab_opt=None) lab b =
    let stmt_ndl = List.concat_map self#of_block_statement b.Ast.b_block_statements in
    if
      options#ast_reduction_flag && not options#normalize_ast_flag &&
      List.length stmt_ndl = 1
    then
      match stmt_ndl with
      | [stmt_nd] -> stmt_nd
      | _ -> assert false
    else
      let nd = self#mklnode ~orig_lab_opt lab stmt_ndl in
      set_loc nd b.Ast.b_loc;
      nd

  method of_block ?(tid=L.null_tid) b = self#_of_block (L.Block tid) b

  method of_method_body (mname, (*orig_msig*)_, msig) body =
    let orig_lab_opt =
      Some (L.MethodBody(mname, ""))
      (*if orig_msig <> msig then
        Some (L.MethodBody(mname, orig_msig))
      else
        None*)
    in
    self#_of_block ~orig_lab_opt (L.MethodBody(mname, msig)) body

  method of_block_statement bs =
    match bs.Ast.bs_desc with
    | Ast.BSlocal lvd -> begin
        let ndl = self#of_local_variable_declaration ~is_stmt:true lvd in
        List.iter (fun nd -> set_loc nd bs.Ast.bs_loc) ndl;
        ndl
    end
    | Ast.BSclass cd -> begin
        let nd = self#of_class_declaration false cd in
        set_loc nd bs.Ast.bs_loc;
        [nd]
    end
    | Ast.BSstatement s -> begin
        let nd = self#of_statement s in
        set_loc nd bs.Ast.bs_loc;
        [nd]
    end
    | Ast.BSerror s -> begin
        let nd = self#mkleaf (L.Error s) in
        set_loc nd bs.Ast.bs_loc;
        [nd]
    end

  method of_field_declaration ?(interface_field=false) fd =
    let mods = fd.Ast.fd_modifiers in
    let is_static =
      match mods with
      | None -> false
      | Some ms ->
          List.exists
            (fun m ->
              match m.Ast.m_desc with
              | Ast.Mstatic -> true
              | _ -> false
            ) ms.Ast.ms_modifiers
    in
    let vdtors = fd.Ast.fd_variable_declarators in

    if options#normalize_ast_flag then begin
      let _mkfdecl ghost vd vdnd =
        let ty_leaf = self#of_javatype [] fd.Ast.fd_type in
        let vdid = vd.Ast.vd_variable_declarator_id in
        let (_, vdid_id), vdid_dims = vdid in
        let vdid_ = vdid_id, List.length vdid_dims in
        let orig_lab_opt = Some (L.FieldDeclaration [strip_vdid vdid_]) in
        let mod_nodes = self#of_modifiers_opt ~interface_field (L.Kfield vdid_id) mods in
        let ordinal_tbl_opt = Some (new ordinal_tbl [List.length mod_nodes; 1; 1]) in
        let children = mod_nodes @ [ty_leaf; vdnd] in
        let id_loc = Loc.ghost in
        let nd =
          self#mknode ~orig_lab_opt ~ordinal_tbl_opt ~id_loc (L.FieldDeclaration [vdid_]) children
        in
        if ghost then begin
          nd#data#set_loc Loc.ghost;
          List.iter set_ghost_rec mod_nodes;
          set_ghost_rec ty_leaf
        end
        else
          set_loc nd fd.Ast.fd_loc;
        nd
      in
      let mkfdecl ghost vd =
        _mkfdecl ghost vd (self#of_variable_declarator ~is_static vd)
      in
      match vdtors with
      | []       -> []
      | [vd]     -> [mkfdecl false vd]
      | vd::rest ->
          let fdecl_nd = mkfdecl false vd in
          let rest_vdnds = List.map (self#of_variable_declarator ~is_static) rest in
          List.iter (fun vn -> self#add_true_parent vn#uid fdecl_nd) rest_vdnds;
          fdecl_nd :: (List.map2 (fun v vn -> _mkfdecl true v vn) rest rest_vdnds)
    end
    else begin
      let vdids = List.map (fun vd -> vd.Ast.vd_variable_declarator_id) vdtors in
      let vdids_ =
        List.map
          (fun vd ->
            let (_, vdid_id), vdid_dims = vd.Ast.vd_variable_declarator_id in
            vdid_id, List.length vdid_dims
          ) vdtors
      in
      let vdid_str = self#vdids_to_str vdids in
      let orig_lab_opt = Some (L.FieldDeclaration (List.map strip_vdid vdids_)) in
      let mod_nodes = self#of_modifiers_opt ~interface_field (L.Kfield vdid_str) mods in
      let ordinal_tbl_opt = Some (new ordinal_tbl [List.length mod_nodes; 1; List.length vdtors]) in
      let ty_leaf = self#of_javatype [] fd.Ast.fd_type in
      let id_loc = Loc.ghost in
      let nd =
        self#mknode ~orig_lab_opt ~ordinal_tbl_opt ~id_loc (L.FieldDeclaration vdids_)
          (mod_nodes @
           [ty_leaf] @
           (List.map (self#of_variable_declarator ~is_static) vdtors))
      in
      set_loc nd fd.Ast.fd_loc;
      [nd]
    end

  method of_explicit_constructor_invocation eci =
    let nd =
      match eci.Ast.eci_desc with
      | Ast.ECIthis(targs_opt, args) ->
          let ta_nodes = self#of_type_arguments_opt "" targs_opt in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [List.length ta_nodes; 1])
          in
          self#mknode ~ordinal_tbl_opt L.ThisInvocation
            (ta_nodes @ [self#of_named_arguments "this" args])

      | Ast.ECIsuper(targs_opt, args) ->
          let ta_nodes = self#of_type_arguments_opt "" targs_opt in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [List.length ta_nodes; 1])
          in
          self#mknode ~ordinal_tbl_opt L.SuperInvocation
            (ta_nodes @ [self#of_named_arguments "super" args])

      | Ast.ECIprimary(prim, targs_opt, args) ->
          let ta_nodes = self#of_type_arguments_opt "" targs_opt in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [1; List.length ta_nodes; 1])
          in
          self#mknode ~ordinal_tbl_opt L.PrimaryInvocation
            ((self#of_primary prim) :: (ta_nodes @ [self#of_arguments args]))

      | Ast.ECIname(name, targs_opt, args) ->
          let ta_nodes = self#of_type_arguments_opt "" targs_opt in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [List.length ta_nodes; 1])
          in
          let orig_lab_opt =
            Some (L.NameInvocation (L.conv_name ~resolve:false name))
          in
          self#mknode ~orig_lab_opt ~ordinal_tbl_opt
            (L.NameInvocation (L.conv_name name)) (ta_nodes @ [self#of_arguments args])

      | Ast.ECIerror s -> self#mkleaf (L.Error s)
    in
    set_loc nd eci.Ast.eci_loc;
    nd

  method of_class_body_declaration cbd =
    let loc = cbd.Ast.cbd_loc in
    let nds =
      match cbd.Ast.cbd_desc with
      | Ast.CBDfield fd -> self#of_field_declaration fd
      | Ast.CBDmethod(method_header, block_opt) ->
          let nd = self#of_method_header method_header in
          begin
            match block_opt with
            | None -> ()
            | Some block -> begin
                nd#add_child_rightmost
                  (self#of_method_body
                     (self#name_sig_of_method_header method_header) block);
                nd#data#add_to_ordinal_list [1]
            end
          end;
          [nd]

      | Ast.CBDclass cd      -> [self#of_class_declaration false cd]
      | Ast.CBDinterface ifd -> [self#of_interface_declaration false ifd]

      | Ast.CBDstaticInitializer block ->
          [self#mknode L.StaticInitializer [self#of_block ~tid:(self#__mktid "static-initializer") block]]

      | Ast.CBDinstanceInitializer block ->
          [self#mknode L.InstanceInitializer [self#of_block ~tid:(self#__mktid "instance-initializer") block]]

      | Ast.CBDconstructor cd ->
          let mods = cd.Ast.cnd_modifiers in
          let tparams = cd.Ast.cnd_type_parameters in
          let params = cd.Ast.cnd_parameters in
          let throws = cd.Ast.cnd_throws in
          let orig_name = cd.Ast.cnd_name in
          let name = orig_name^".<init>" in
          let signature =
            Xlist.to_string self#param_to_tystr "" params
          in
          let mod_nodes = self#of_modifiers_opt (L.Kconstructor signature) mods in
          let ta_nodes = self#of_type_parameters_opt signature tparams in
          let p_nodes = self#of_parameters signature cd.Ast.cnd_parameters_loc params in
          let th_nodes = self#of_throws_opt name throws in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [List.length mod_nodes;
                                   List.length ta_nodes;
                                   List.length p_nodes;
                                   List.length th_nodes;
                                   1;
                                 ])
          in
          let children =
            mod_nodes @ ta_nodes @ p_nodes @ th_nodes @
            [self#of_constructor_body name signature cd.Ast.cnd_body]
          in
          let msig = sprintf "(%s)V" signature in
          let annot = L.make_annotation msig in
          let orig_lab_opt = Some (L.Constructor(orig_name, ""(*msig*))) in
          let nd =
            self#mknode ~orig_lab_opt ~annot ~ordinal_tbl_opt
              (L.Constructor(name, msig)) children
          in
          [nd]
      | Ast.CBDempty -> [self#mkleaf L.EmptyDeclaration]
      | Ast.CBDerror s -> [self#mkleaf (L.Error s)]
      | Ast.CBDpointcut p ->
          let ident = p.Ast.pcd_name in
          let mods = p.Ast.pcd_modifiers in
          let params = p.Ast.pcd_parameters in
          let mod_nodes = self#of_modifiers_opt (L.Kpointcut ident) mods in
          let p_nodes = self#of_parameters ident p.Ast.pcd_parameters_loc params in
          let e_nodes = of_opt self#of_pointcut_expr p.Ast.pcd_pointcut_expr in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [List.length mod_nodes;
                                   List.length p_nodes;
                                   List.length e_nodes;
                                 ])
          in
          let children = mod_nodes @ p_nodes @ e_nodes in
          let nd = self#mknode ~ordinal_tbl_opt (L.Pointcut ident) children in
          set_loc nd p.Ast.pcd_loc;
          [nd]
      | Ast.CBDdeclare d ->
          let lab, children, ordinal_tbl_opt =
            match d.dd_desc with
            | Ast.DDparents(_, c, x_opt, i_opt) ->
                let x_nodes = self#of_extends_class_opt x_opt in
                let i_nodes = self#of_implements_opt i_opt in
                let ordinal_tbl_opt =
                  Some (new ordinal_tbl [1;
                                         List.length x_nodes;
                                         List.length i_nodes;
                                       ])
                in
                L.DeclareParents, (self#of_classname_pattern_expr c)::(x_nodes@i_nodes), ordinal_tbl_opt
            | Ast.DDmessage(k, p, s) -> L.DeclareMessage k, [self#of_pointcut_expr p; self#of_primary s], None
            | Ast.DDsoft(_, p) -> L.DeclareSoft, [self#of_pointcut_expr p], None
            | Ast.DDprecedence(_, cl) -> L.DeclarePrecedence, List.map self#of_classname_pattern_expr cl, None
          in
          let nd = self#mknode ~ordinal_tbl_opt lab children in
          set_loc nd d.Ast.dd_loc;
          [nd]
    in
    List.iter
      (fun nd ->
        if not (is_ghost nd) then
          set_loc nd loc
      ) nds;
    nds

  method of_record_body_declaration rbd =
    match rbd.Ast.rbd_desc with
    | RBDclass_body_decl cbd -> self#of_class_body_declaration cbd
    | RBDcompact_ctor_decl ccd -> self#of_compact_ctor_decl ccd

  method of_compact_ctor_decl ccd =
    let mods = ccd.Ast.ccnd_modifiers in
    let orig_name = ccd.Ast.ccnd_name in
    let name = orig_name^".<init>" in
    let signature = "" in
    let mod_nodes = self#of_modifiers_opt (L.Kconstructor signature) mods in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length mod_nodes;
                             1;
                           ])
    in
    let children =
      mod_nodes @ [self#of_constructor_body name signature ccd.Ast.ccnd_body]
    in
    let msig = sprintf "(%s)V" signature in
    let annot = L.make_annotation msig in
    let orig_lab_opt = Some (L.Constructor(orig_name, ""(*msig*))) in
    let nd =
      self#mknode ~orig_lab_opt ~annot ~ordinal_tbl_opt
        (L.Constructor(name, msig)) children
    in
    set_loc nd ccd.Ast.ccnd_loc;
    [nd]

  method of_pointcut_expr pe =
    let lab, children =
      match pe.pe_desc with
      | Ast.PEand(pe0, pe1) -> L.PointcutAnd, [self#of_pointcut_expr pe0; self#of_pointcut_expr pe1]
      | Ast.PEor(pe0, pe1) -> L.PointcutOr, [self#of_pointcut_expr pe0; self#of_pointcut_expr pe1]
      | Ast.PEnot pe0 -> L.PointcutNot, [self#of_pointcut_expr pe0]
      | Ast.PEparen pe0 -> L.PointcutParen, [self#of_pointcut_expr pe0]
      | Ast.PEwithin cpe -> L.PointcutWithin, [self#of_classname_pattern_expr cpe]
    in
    let nd = self#mknode lab children in
    set_loc nd pe.Ast.pe_loc;
    nd

  method of_classname_pattern_expr cpe =
    let lab, children =
      match cpe.cpe_desc with
      | CPEand(cpe0, cpe1) ->
          L.ClassnamePatternAnd, [self#of_classname_pattern_expr cpe0; self#of_classname_pattern_expr cpe1]
      | CPEor(cpe0, cpe1) ->
          L.ClassnamePatternOr, [self#of_classname_pattern_expr cpe0; self#of_classname_pattern_expr cpe1]
      | CPEnot cpe0 -> L.ClassnamePatternNot, [self#of_classname_pattern_expr cpe0]
      | CPEparen cpe0 -> L.ClassnamePatternParen, [self#of_classname_pattern_expr cpe0]
      | CPEname n -> L.ClassnamePatternName n, []
      | CPEnamePlus n -> L.ClassnamePatternNamePlus n, []
    in
    let nd = self#mknode lab children in
    set_loc nd cpe.Ast.cpe_loc;
    nd

  method of_constructor_body name signature cnb =
    let ctor_invk = cnb.Ast.cnb_explicit_constructor_invocation in
    let bss = cnb.Ast.cnb_block in
    let ctor_nodes = of_opt self#of_explicit_constructor_invocation ctor_invk in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length ctor_nodes; List.length bss])
    in
    let stmts = List.concat_map self#of_block_statement bss in
    let children = ctor_nodes @ stmts in
    let msig =
      if options#java_anon_ctor_body_flag then
        ""
      else
        sprintf "(%s)V" signature
    in
    let orig_lab_opt = Some (L.ConstructorBody(name, "")) in
    let nd =
      self#mknode ~ordinal_tbl_opt ~orig_lab_opt (L.ConstructorBody(name, msig)) children
    in
    set_loc nd cnb.Ast.cnb_loc;
    nd

  method of_record_body ?(in_method=false) rname rb =
    let body = rb.Ast.rb_record_body_declarations in
    let children = List.concat_map self#of_record_body_declaration body in
    self#_of_class_body ~in_method rname children rb.Ast.rb_loc

  method of_class_body_opt ?(in_method=false) name cb = of_opt (self#of_class_body ~in_method name) cb

  method of_class_body ?(in_method=false) cname cb =
    let body = cb.Ast.cb_class_body_declarations in
    let children = List.concat_map self#of_class_body_declaration body in
    self#_of_class_body ~in_method cname children cb.Ast.cb_loc

  method sort_class_body_members cname children =
    let fields, methods, ctors, classes, enums, ifaces, static_inits, inst_inits, others
        = ref [], ref [], ref [], ref [], ref [], ref [], ref [], ref [], ref []
    in
    let classify nd =
      match getlab nd with
      | L.FieldDeclaration _  -> fields := nd :: !fields
      | L.Method _            -> methods := nd :: !methods
      | L.Constructor _       -> ctors := nd :: !ctors
      | L.Class _             -> classes := nd :: !classes
      | L.Enum _              -> enums := nd :: !enums
      | L.Interface _         -> ifaces := nd :: !ifaces
      | L.AnnotationType _    -> ifaces := nd :: !ifaces
      | L.StaticInitializer   -> static_inits := nd :: !static_inits
      | L.InstanceInitializer -> inst_inits := nd :: !inst_inits
      | L.EmptyDeclaration when
          options#strip_empty_flag &&
          not options#recover_orig_ast_flag &&
          options#sort_unordered_flag
        -> ()
      | _ -> others := nd :: !others
    in
    let _ = List.iter classify children in
    let _ =
      enums        := List.rev !enums;
      ifaces       := List.rev !ifaces;
      classes      := List.rev !classes;
      fields       := List.rev !fields;
      ctors        := List.rev !ctors;
      static_inits := List.rev !static_inits;
      inst_inits   := List.rev !inst_inits;
      methods      := List.rev !methods;
      others       := List.rev !others;
    in
    if options#sort_unordered_flag then begin
      enums   := List.fast_sort compare_node !enums;
      ifaces  := List.fast_sort compare_node !ifaces;
      classes := List.fast_sort compare_node !classes;
      fields  := List.fast_sort compare_node !fields;(*do not remove!!!NG!!!*)
      ctors   := List.fast_sort compare_node_sig !ctors;
      methods := List.fast_sort compare_node_sig !methods;
    end;
    let fields_l =
      if !fields = [] then
        []
      else
        let fields_ = self#mklnode (L.FieldDeclarations cname) !fields in
        fields_#data#set_loc Loc.ghost;
        [fields_]
    in
    let children' =
      List.flatten
        [ !enums;
          !ifaces;
          !classes;
          fields_l;
          !static_inits;
          !inst_inits;
          !ctors;
          !methods;
          !others
        ]
    in
    begin %debug_block
        [%debug_log "ClassBody(%s):" cname];
      List.iteri
        (fun i n ->
          [%debug_log "%d: (%a)%s" i UID.ps n#uid (L.to_string (getlab n))]
        ) children'
    end;
    children'

  method _of_class_body ?(in_method=false) cname children loc =
    let children' =
      if in_method then
        children
      else
        self#sort_class_body_members cname children
    in
    let nd = self#mklnode (L.ClassBody cname) children' in
    self#add_true_children nd (Array.of_list children);
    set_loc nd loc;
    nd

  method of_enum_body name eb =
    let econsts = eb.Ast.eb_enum_constants in
    let cbdecls = eb.Ast.eb_class_body_declarations in
    let dnds = List.concat_map self#of_class_body_declaration cbdecls in
    let dnds =
      if
        options#ast_reduction_flag &&
        match dnds with
        | [dnd] when getlab dnd = L.EmptyDeclaration -> true
        | _ -> false
      then
        []
      else
        dnds
    in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length econsts; List.length dnds])
    in
    let nd =
      self#mknode ~ordinal_tbl_opt (L.EnumBody name)
        ((List.map self#of_enum_constant econsts) @ dnds)
    in
    set_loc nd eb.Ast.eb_loc;
    nd

  method of_enum_constant ec =
    let al = ec.Ast.ec_annotations in
    let args = ec.Ast.ec_arguments in
    let ident = ec.Ast.ec_identifier in
    let a_nodes = self#of_annotations al in
    let na_nodes =
      match args with
      | None -> []
      | Some a when options#ast_reduction_flag && a.Ast.as_arguments = [] -> []
      | Some a -> [self#of_named_arguments ident a]
    in
    let cb_nodes = self#of_class_body_opt ident ec.Ast.ec_class_body in
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length a_nodes;
                             List.length na_nodes;
                             List.length cb_nodes;
                           ])
    in
    let nd =
      self#mknode ~ordinal_tbl_opt (L.EnumConstant ident)
        (a_nodes @ na_nodes @ cb_nodes)
    in
    set_loc nd ec.Ast.ec_loc;
    nd

  method of_annotations ans =
    let children = List.map self#of_annotation ans in
    if children = [] then
      []
    else
      let nd = self#mklnode L.Annotations children in
      set_nodes_loc nd children;
      [nd]

  method of_annotation a =
    let nd =
      match a.Ast.a_desc with
      | Ast.Anormal(name, [{ Ast.evp_desc=("value", ev); Ast.evp_loc=_ }])
        when options#ast_reduction_flag ->
          let orig_lab_opt =
            Some (L.Annotation (L.Annotation.SingleElement (L.conv_name ~resolve:false name)))
          in
          self#mknode ~orig_lab_opt
            (L.Annotation (L.Annotation.SingleElement (L.conv_name name)))
            [self#of_element_value ev]

      | Ast.Anormal(name, evps) ->
          let orig_lab_opt =
            Some (L.Annotation (L.Annotation.Normal (L.conv_name ~resolve:false name)))
          in
          self#mknode ~orig_lab_opt
            (L.Annotation (L.Annotation.Normal (L.conv_name name)))
            (List.map self#of_element_value_pair evps)

      | Ast.Amarker name ->
          let orig_lab_opt =
            Some (L.Annotation (L.Annotation.Marker (L.conv_name ~resolve:false name)))
          in
          self#mkleaf ~orig_lab_opt (L.Annotation (L.Annotation.Marker (L.conv_name name)))

      | Ast.AsingleElement(name, ev) ->
          let orig_lab_opt =
            Some (L.Annotation (L.Annotation.SingleElement (L.conv_name ~resolve:false name)))
          in
          self#mknode ~orig_lab_opt
            (L.Annotation (L.Annotation.SingleElement (L.conv_name name)))
            [self#of_element_value ev]
    in
    set_loc nd a.Ast.a_loc;
    nd

  method of_element_value_pair { Ast.evp_desc=(ident, ev); Ast.evp_loc=loc } =
    let nd = self#mknode (L.ElementValuePair ident) [self#of_element_value ev] in
    set_loc nd loc;
    nd

  method of_element_value ev =
    let nd =
      match ev.Ast.ev_desc with
      | Ast.EVconditional e -> self#mknode L.EVconditional [self#of_expression e]
      | Ast.EVannotation a -> self#mknode L.EVannotation [self#of_annotation a]
      | Ast.EVarrayInit [ev] when options#ast_reduction_flag -> self#of_element_value ev
      | Ast.EVarrayInit evs ->
          self#mknode L.EVarrayInit (List.map self#of_element_value evs)
    in
    set_loc nd ev.Ast.ev_loc;
    nd

  method of_extends_class exc =
    let nd = self#mknode L.Extends [self#of_javatype [] exc.Ast.exc_class] in
    set_loc nd exc.Ast.exc_loc;
    nd

  method of_extends_class_opt exc = of_opt self#of_extends_class exc

  method of_extends_interfaces exi =
    let nd =
      self#mklnode L.ExtendsInterfaces
        (List.map (self#of_javatype []) exi.Ast.exi_interfaces)
    in
    set_loc nd exi.Ast.exi_loc;
    nd

  method of_extends_interfaces_opt exi = of_opt self#of_extends_interfaces exi

  method of_implements im =
    let nd =
      self#mklnode L.Implements (List.map (self#of_javatype []) im.Ast.im_interfaces)
    in
    set_loc nd im.Ast.im_loc;
    nd

  method of_implements_opt im = of_opt self#of_implements im

  method of_type_name n =
    let nd = self#mkleaf (L.TypeName (L.conv_name ~resolve:false n)) in
    set_loc nd n.Ast.n_loc;
    nd

  method of_permits pm =
    let nd =
      self#mklnode L.Permits (List.map self#of_type_name pm.Ast.pm_type_names)
    in
    set_loc nd pm.Ast.pm_loc;
    nd

  method of_permits_opt pm = of_opt self#of_permits pm

  method make_specifier_node kind children otbl loc =
    if children = [] then
      []
    else
      let ordinal_tbl_opt = Some (new ordinal_tbl otbl) in
      let nd = self#mknode ~ordinal_tbl_opt (L.Specifier kind) children in
      set_loc nd loc;
      [nd]

  method of_class_declaration_head ?(interface=false) ?(enum=false) ?(nested_enum=false) kind otbl h =
    let ident = h.Ast.ch_identifier in
    let mod_nodes =
      self#of_modifiers_opt ~interface ~enum ~nested_enum kind (*ident*) h.Ast.ch_modifiers
    in
    let ta_nodes = self#of_type_parameters_opt ident h.Ast.ch_type_parameters in
    let ex_nodes = self#of_extends_class_opt h.Ast.ch_extends_class in
    let im_nodes = self#of_implements_opt h.Ast.ch_implements in
    let pm_nodes = self#of_permits_opt h.Ast.ch_permits in
    let children = mod_nodes @ ta_nodes @ ex_nodes @ im_nodes @ pm_nodes in
    self#make_specifier_node kind children otbl h.Ast.ch_loc

  method of_record_declaration_head ?(interface=false) kind otbl h =
    let ident = h.Ast.rh_identifier in
    let mod_nodes = self#of_modifiers_opt ~interface kind (*ident*) h.Ast.rh_modifiers in
    let ta_nodes = self#of_type_parameters_opt ident h.Ast.rh_type_parameters in
    let h_nodes = List.map self#of_parameter h.Ast.rh_record_header in
    let im_nodes = self#of_implements_opt h.Ast.rh_implements in
    let children = mod_nodes @ ta_nodes @ h_nodes @ im_nodes in
    self#make_specifier_node kind children otbl h.Ast.rh_loc

  method of_module_name mn =
    let nd = self#mkleaf (L.ModuleName (L.conv_name mn.Ast.mn_name)) in
    set_loc nd mn.Ast.mn_loc;
    nd

  method of_module_directive md =
    let of_modifiers = List.map self#of_modifier in
    let of_module_names = List.map self#of_module_name in
    let nd =
      match md.Ast.md_desc with
      | MDrequires(ms, n) -> self#mknode (L.Requires (L.conv_name n)) (of_modifiers ms)
      | MDexports(n, ns) -> self#mknode (L.Exports (L.conv_name n)) (of_module_names ns)
      | MDopens(n, ns) -> self#mknode (L.Opens (L.conv_name n)) (of_module_names ns)
      | MDuses n -> self#mkleaf (L.Uses (L.conv_name n))
      | MDprovides(n, ns) -> self#mknode (L.Provides (L.conv_name n)) (of_module_names ns)
    in
    set_loc nd md.Ast.md_loc;
    nd

  method of_module_body name mb =
    let children = List.map self#of_module_directive mb.Ast.mb_module_directives in
    let nd = self#mknode (L.ModuleBody name) children in
    set_loc nd mb.Ast.mb_loc;
    nd

  method of_module_declaration m =
    let mdh = m.Ast.mod_head in
    let a_nodes = List.map self#of_annotation mdh.Ast.mdh_annotations in
    let o_nodes =
      match mdh.Ast.mdh_open with
      | Some loc -> let nd = self#mkleaf L.Open in set_loc nd loc; [nd]
      | _ -> []
    in
    let name_str = L.conv_name mdh.Ast.mdh_name in
    let mb = m.Ast.mod_body in
    let body_node = self#of_module_body name_str mb in
    let ordinal_tbl_opt = Some (new ordinal_tbl [List.length a_nodes; List.length o_nodes; 1]) in
    let children = a_nodes @ o_nodes @ [body_node] in
    let nd = self#mknode ~ordinal_tbl_opt (L.Module name_str) children in
    set_loc nd m.Ast.mod_loc;
    nd

  method of_class_declaration ?(interface=false) is_top cd =
    let nd =
      match cd.Ast.cd_desc with
      | Ast.CDclass(h, body) ->
          let otbl =
            [if h.Ast.ch_modifiers <> None then 1 else 0;
             if h.Ast.ch_type_parameters <> None then 1 else 0;
             if h.Ast.ch_extends_class <> None then 1 else 0;
             if h.Ast.ch_implements <> None then 1 else 0;
           ]
          in
          let ident = h.Ast.ch_identifier in
          let id_loc = conv_loc h.Ast.ch_identifier_loc in
          let specifier_node = self#of_class_declaration_head ~interface (L.Kclass ident) otbl h in
          let children = specifier_node @ [self#of_class_body ident body] in
          self#mknode ~id_loc (L.Class ident) children

      | Ast.CDenum(h, body) ->
          let otbl =
            [
             if h.Ast.ch_modifiers <> None then 1 else 0;
             if h.Ast.ch_implements <> None then 1 else 0;
           ]
          in
          let ident = h.Ast.ch_identifier in
          let id_loc = conv_loc h.Ast.ch_identifier_loc in
          let body_node = self#of_enum_body ident body in
          let enum =
            Array.for_all
              (fun c ->
                match getlab c with
                | L.EnumConstant _ -> begin
                    Array.for_all
                      (fun cc ->
                        match getlab cc with
                        | L.ClassBody _ -> false
                        | _ -> true
                      ) c#children
                end
                | _ -> true
              ) body_node#children
          in
          let nested_enum = not is_top in
          let specifier_node =
            self#of_class_declaration_head ~interface ~enum ~nested_enum (L.Kenum ident) otbl h
          in
          let children = specifier_node @ [body_node] in
          self#mknode ~id_loc (L.Enum ident) children

      | Ast.CDrecord(h, body) ->
          let otbl =
            [if h.Ast.rh_modifiers <> None then 1 else 0;
             if h.Ast.rh_type_parameters <> None then 1 else 0;
             List.length h.Ast.rh_record_header;
             if h.Ast.rh_implements <> None then 1 else 0;
           ]
          in
          let ident = h.Ast.rh_identifier in
          let id_loc = conv_loc h.Ast.rh_identifier_loc in
          let specifier_node = self#of_record_declaration_head ~interface (L.Krecord ident) otbl h in
          let children = specifier_node @ [self#of_record_body ident body] in
          self#mknode ~id_loc (L.Record ident) children

      | Ast.CDaspect(h, body) ->
          let otbl =
            [if h.Ast.ch_modifiers <> None then 1 else 0;
             if h.Ast.ch_extends_class <> None then 1 else 0;
             if h.Ast.ch_implements <> None then 1 else 0;
           ]
          in
          let ident = h.Ast.ch_identifier in
          let id_loc = conv_loc h.Ast.ch_identifier_loc in
          let specifier_node = self#of_class_declaration_head ~interface (L.Kaspect ident) otbl h in
          let children = specifier_node @ [self#of_aspect_body ident body] in
          self#mknode ~id_loc (L.Aspect ident) children
    in
    set_loc nd cd.Ast.cd_loc;
    nd

  method of_aspect_body aname abd =
    let body = abd.Ast.abd_aspect_body_declarations in
    let children = List.concat_map self#of_class_body_declaration body in
    self#_of_class_body aname children abd.Ast.abd_loc

  method of_abstract_method_declaration amd =
    self#of_method_header
      ~interface_method:true ~loc_opt:(Some amd.Ast.amd_loc)
      amd.Ast.amd_method_header

  method of_interface_member_declaration imd =
    match imd.Ast.imd_desc with
    | Ast.IMDconstant field_decl      -> self#of_field_declaration ~interface_field:true field_decl
    | Ast.IMDinterfaceMethod abs_meth -> [self#of_abstract_method_declaration abs_meth]
    | Ast.IMDclass class_decl         -> [self#of_class_declaration ~interface:true false class_decl]
    | Ast.IMDinterface iface_decl     -> [self#of_interface_declaration false iface_decl]
    | Ast.IMDempty -> [let nd = self#mkleaf L.EmptyDeclaration in set_loc nd imd.imd_loc; nd]

  method of_interface_body iname ib =
    let mems = ib.Ast.ib_member_declarations in
    let children = List.concat_map self#of_interface_member_declaration mems in
    let fields, methods, classes, enums, ifaces, others =
      ref [], ref [], ref [], ref [], ref [], ref []
    in
    let classify nd =
      match (Obj.obj nd#data#_label : L.t) with
      | L.FieldDeclaration _ -> fields := nd::!fields
      | L.Method _ -> methods := nd::!methods
      | L.Class _ -> classes := nd::!classes
      | L.Enum _ -> enums := nd::!enums
      | L.Interface _
      | L.AnnotationType _ -> ifaces := nd::!ifaces
      | L.EmptyDeclaration when
          options#strip_empty_flag &&
          not options#recover_orig_ast_flag &&
          options#sort_unordered_flag
        -> ()
      | _ -> others := nd::!others
    in
    List.iter classify children;
    let mapper =
      if options#sort_unordered_flag then
        List.fast_sort compare_node
      else
        fun x -> x
    in
    let mapper_meth =
      if options#sort_unordered_flag then
        List.fast_sort compare_node_sig
      else
        fun x -> x
    in
    let children' =
      List.flatten ([ mapper !enums;
                      mapper !ifaces;
                      mapper !classes;
                      mapper !fields;
                      mapper_meth !methods;
                      mapper !others;
                    ])
    in
    begin %debug_block
      [%debug_log "InterfaceBody(%s):" iname];
      List.iteri
        (fun i n ->
          [%debug_log "%d: (%a)%s" i UID.ps n#uid (L.to_string (getlab n))]
        ) children'
    end;
    let nd = self#mklnode (L.InterfaceBody iname) children' in
    self#add_true_children nd (Array.of_list children);
    set_loc nd ib.Ast.ib_loc;
    nd

  method of_annotation_type_body name atb =
    let nd =
      self#mklnode (L.AnnotationTypeBody name)
        (List.concat_map
           self#of_annotation_type_member_declaration
           atb.Ast.atb_member_declarations)
    in
    set_loc nd atb.Ast.atb_loc;
    nd

  method of_constant_declaration cd = self#of_field_declaration cd

  method of_default_value dv = self#of_element_value dv

  method of_annot_dim adim =
    let lab = L.AnnotDim adim.Ast.ad_ellipsis in
    let nd = self#mknode lab (self#of_annotations adim.Ast.ad_annotations) in
    set_loc nd adim.Ast.ad_loc;
    nd

  method of_annotation_type_member_declaration atmd =
    let nds =
      match atmd.Ast.atmd_desc with
      | Ast.ATMDconstant cd -> self#of_constant_declaration cd
      | Ast.ATMDelement(modifiers_opt, ty, ident, dl, dval_opt) ->
          let mod_nodes = self#of_modifiers_opt (L.Kannotation ident) modifiers_opt in
          let dval_nodes = of_opt self#of_default_value dval_opt in
          let ordinal_tbl_opt =
            Some (new ordinal_tbl [List.length mod_nodes;
                                   1;
                                   List.length dl;
                                   List.length dval_nodes])
          in
          [self#mknode ~ordinal_tbl_opt (L.ElementDeclaration ident)
             (mod_nodes @ [self#of_javatype [] ty] @
              (List.map self#of_annot_dim dl) @ dval_nodes)]

      | Ast.ATMDclass cd -> [self#of_class_declaration false cd]
      | Ast.ATMDinterface ifd -> [self#of_interface_declaration false ifd]
      | Ast.ATMDempty -> [self#mkleaf L.EmptyDeclaration]
    in
    let loc = atmd.Ast.atmd_loc in
    List.iter (fun nd -> set_loc nd loc) nds;
    nds

  method of_interface_declaration_head kind otbl h =
    let ident = h.Ast.ifh_identifier in
    let children =
      (self#of_modifiers_opt ~interface:true kind (*ident*) h.Ast.ifh_modifiers) @
      (self#of_type_parameters_opt ident h.Ast.ifh_type_parameters) @
      (self#of_extends_interfaces_opt h.Ast.ifh_extends_interfaces) @
      (self#of_permits_opt h.Ast.ifh_permits)
    in
    self#make_specifier_node kind children otbl h.Ast.ifh_loc

  method of_interface_declaration (*is_top*)_ ifd =
    let nd =
      match ifd.Ast.ifd_desc with
      | Ast.IFDnormal(h, body) ->
          let otbl =
            [if h.Ast.ifh_modifiers <> None then 1 else 0;
             if h.Ast.ifh_type_parameters <> None then 1 else 0;
             if h.Ast.ifh_extends_interfaces <> None then 1 else 0;
           ]
          in
          let ident = h.Ast.ifh_identifier in
          let specifier_node = self#of_interface_declaration_head (L.Kinterface ident) otbl h in
          let children = specifier_node @ [self#of_interface_body ident body] in
          self#mknode (L.Interface ident) children

      | Ast.IFDannotation(h, body) ->
          let otbl =
            [if h.Ast.ifh_modifiers <> None then 1 else 0; 1]
          in
          let ident = h.Ast.ifh_identifier in
          let specifier_node = self#of_interface_declaration_head (L.Kannotation ident) otbl h in
          let children = specifier_node @ [self#of_annotation_type_body ident body] in
          self#mknode (L.AnnotationType ident) children
    in
    set_loc nd ifd.Ast.ifd_loc;
    nd

  method of_type_declaration td =
    let loc = td.Ast.td_loc in
    let nds =
      match td.Ast.td_desc with
      | Ast.TDclass class_decl -> begin
          let nd = self#of_class_declaration true class_decl in
          set_loc nd loc;
          [nd]
      end
      | Ast.TDinterface iface_decl -> begin
          let nd = self#of_interface_declaration true iface_decl in
          set_loc nd loc;
          [nd]
      end
      | Ast.TDempty -> begin
          let nd = self#mkleaf L.EmptyDeclaration in
          set_loc nd loc;
          [nd]
      end
      | Ast.TDerror s -> begin
          let nd = self#mkleaf (L.Error s) in
          set_loc nd loc;
          [nd]
      end
      | Ast.TDorphan(err_opt, cbd) -> begin
          let cbdl = self#of_class_body_declaration cbd in
          List.iter
            (fun n ->
              Xset.add orphan_uids n#uid;
              set_loc n loc
            ) cbdl;
          (match err_opt with
          | Some err -> self#of_type_declaration err
          | None -> []
          ) @ cbdl
      end
    in
    nds

  method of_package_decl pd =
    let nd =
      self#mknode (L.PackageDeclaration (L.conv_name pd.Ast.pd_name))
        (List.map self#of_annotation pd.Ast.pd_annotations)
    in
    set_loc nd pd.Ast.pd_loc;
    nd

  method of_import_decls idecls =
    match idecls with
    | [] ->(* []*)
        let nd = self#mklnode L.ImportDeclarations [] in
        nd#data#set_loc Loc.ghost;
        [nd]
    | _ ->
        let of_import_decl id =
          let nd =
            match id.Ast.id_desc with
            | Ast.IDsingle name -> self#mkleaf (L.IDsingle (L.conv_name ~resolve:false name))
            | Ast.IDtypeOnDemand name -> self#mkleaf (L.IDtypeOnDemand (L.conv_name name))
            | Ast.IDsingleStatic(name, ident) ->
                self#mkleaf (L.IDsingleStatic(L.conv_name ~resolve:false name, ident))

            | Ast.IDstaticOnDemand name -> self#mkleaf (L.IDstaticOnDemand (L.conv_name name))
            | Ast.IDerror s -> self#mkleaf (L.Error s)
          in
          set_loc nd id.Ast.id_loc;
          nd
        in
        let inodes = List.map of_import_decl idecls in
        let inodes' =
          if options#sort_unordered_flag then
            List.fast_sort compare_node inodes
          else
            inodes
        in
        let nd = self#mklnode L.ImportDeclarations inodes' in
        if options#sort_unordered_flag then
          self#add_true_children nd (Array.of_list inodes);
        set_nodes_loc nd inodes;
        [nd]

end (* of class Tree.translator *)
]

[%%capture_path
let of_compilation_unit options cu =
  let trans = new translator options in
  let package_decl = cu.Ast.cu_package in
  let import_decls = cu.Ast.cu_imports in
  let type_decls = cu.Ast.cu_tydecls in
  let modecl = cu.Ast.cu_modecl in
  let pdecl_nodes = of_opt trans#of_package_decl package_decl in
  let idecl_nodes = trans#of_import_decls import_decls in
  let tdecl_nodes =
    match type_decls with
    | [] -> []
    | _ -> begin
        let td_nodes = List.concat_map trans#of_type_declaration type_decls in

        let td_nodes =
          let orphan_uids = trans#orphan_uids in
          let is_orphan n =
            let b = Xset.mem orphan_uids n#uid in
            [%debug_log "%a --> %B" UID.ps n#uid b];
            b
          in
          let n_orphan_uids = Xset.length orphan_uids in
          if
            n_orphan_uids > 0 &&
            List.exists is_orphan td_nodes
          then begin
            [%debug_log "%d orphan nodes found" n_orphan_uids];
            let nl = ref [] in
            let flag = ref false in
            let last_td_opt = ref None in
            let is_td n =
              let b = L.is_typedeclaration (getlab n) in
              [%debug_log "%a --> %B" UID.ps n#uid b];
              b
            in
            let is_err n =
              let b =
                match getlab n with
                | L.Error "}" -> true
                | _ -> false
              in
              [%debug_log "%a --> %B" UID.ps n#uid b];
              b
            in
            let get_body td =
              try
                let last_idx = (Array.length td#children) - 1 in
                [%debug_log "last_idx=%d" last_idx];
                let body = td#children.(last_idx) in
                body
              with
                _ -> invalid_arg "get_body"
            in
            let get_name td = L.get_name (getlab td) in
            let extend_loc n x =
              let loc = Loc.merge n#data#src_loc x#data#src_loc in
              [%debug_log "%s -> %s"
                 (Loc.to_string ~long:false n#data#src_loc)
                 (Loc.to_string ~long:false loc)];
              n#data#set_loc loc
            in
            let add_orphan n =
              match !last_td_opt with
              | Some td -> begin
                  [%debug_log "td=%s" td#to_string];
                  try
                    let body = get_body td in
                    [%debug_log "body=%s" body#to_string];
                    let tbl = trans#true_children_tbl in
                    begin
                      try
                        let true_children = Hashtbl.find tbl body in
                        Hashtbl.replace tbl body (Array.append true_children [|n|])
                      with
                        Not_found -> body#add_child_rightmost n
                    end;
                    [%debug_log "added %a to %a" UID.ps n#uid UID.ps body#uid]
                  with
                    _ -> failwith "add_orphan"
              end
              | None -> failwith "add_orphan"
            in
            let add_node n =
              [%debug_log "%a" UID.ps n#uid];
              nl := n :: !nl
            in
            List.iter
              (fun n ->
                [%debug_log "%s" n#to_string];
                [%debug_log "flag=%B" !flag];
                if !flag then begin
                  if is_orphan n then begin
                    try
                      add_orphan n
                    with
                      _ -> add_node n
                  end
                  else if is_err n then begin
                    flag := false;
                    match !last_td_opt with
                    | Some td -> begin
                        try
                          let body = get_body td in
                          let true_children =
                            Hashtbl.find trans#true_children_tbl body
                          in
                          let cl =
                            trans#sort_class_body_members
                              (get_name td) (Array.to_list true_children)
                          in
                          let ca = Array.of_list cl in
                          body#set_children ca;
                          extend_loc body n;
                          extend_loc td n
                        with
                          _ -> ()
                    end
                    | None -> ()
                  end
                  else begin
                    flag := false;
                    add_node n
                  end
                end
                else begin
                  if is_err n then begin
                    flag := true;
                    add_orphan n
                  end
                  else begin
                    if is_td n then
                      last_td_opt := Some n;
                    add_node n
                  end
                end
              ) td_nodes;
            List.rev !nl
          end
          else
            td_nodes
        in

        let nd = mklnode options L.TypeDeclarations td_nodes in
        set_nodes_loc nd td_nodes;
        [nd]
    end
  in
  let modecl_nodes =
    match modecl with
    | Some m -> [trans#of_module_declaration m]
    | _ -> []
  in
  let compilation_unit_node =
    let ordinal_tbl_opt =
      Some (new ordinal_tbl [List.length pdecl_nodes;
                             List.length idecl_nodes;
                             List.length tdecl_nodes;
                             List.length modecl_nodes;
                           ])
    in
    let children = pdecl_nodes @ idecl_nodes @ tdecl_nodes @ modecl_nodes in
    let nd = mknode options ~ordinal_tbl_opt L.CompilationUnit children in
    set_nodes_loc nd children;
    nd
  in
  let tree =
    new c options compilation_unit_node true
  in
  let n_huge_arrays = List.length trans#huge_array_list in
  [%debug_log "T:\n%s" tree#to_string];
  [%debug_log "%d huge array(s) found" n_huge_arrays];
  tree#set_true_parent_tbl trans#true_parent_tbl;
  tree#set_true_children_tbl trans#true_children_tbl;
  if options#use_binding_info_flag then
    trans#set_bindings tree;
  tree#collapse;
  if n_huge_arrays > 0 then begin
    Xprint.verbose options#verbose_flag "%d huge array(s) found" n_huge_arrays;
  end;
  tree
]

[%%capture_path
let of_ast options ast =
  [%debug_log "nintegers=%d nfloats=%d nstrings=%d" ast#nintegers ast#nfloats ast#nstrings];
  (*if ast#nintegers > 32 then
    options#set_anonymize_int_flag;
  if ast#nintegers > 32 then
    options#set_anonymize_float_flag;
  if ast#nstrings > 32 then
    options#set_anonymize_string_flag;*)

  let tree = of_compilation_unit options ast#compilation_unit in
  tree#set_misparsed_regions ast#missed_regions;
  tree#set_misparsed_LOC ast#missed_LOC;
  tree#set_total_LOC ast#lines_read;
  tree#set_ignored_regions (ast#comment_regions @ ast#ignored_regions);
  tree
]
