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
(* java/change.ml *)

module Xlist = Diffast_misc.Xlist
module UID = Diffast_misc.UID
module Otree = Diffast_misc.Otree
module Edit = Diffast_core.Edit
module Misc = Diffast_core.Misc
module Triple = Diffast_core.Triple
module Info = Diffast_core.Info
module Java_label = Java_base.Java_label

let nups = Misc.nups

module F (L : Java_label.T) = struct

  module I = Info
  module E = Edit

  (*let sprintf = Printf.sprintf*)

  include Diffast_core.Change_base

  module CB = F(L)

  let mkjres = Triple.mkjres

  let p_accessibility_increased = mkjres "accessibilityIncreased"
  let p_accessibility_decreased = mkjres "accessibilityDecreased"


(* predicates *)

  let getlab = L.getlab

  let is_meth nd         = L.is_method (getlab nd)
  let is_ctor nd         = L.is_ctor (getlab nd)
  let is_param nd        = L.is_parameter (getlab nd)
  let is_tparam nd       = L.is_typeparameter (getlab nd)
  let is_type nd         = L.is_type (getlab nd)
  let is_stmt nd         = L.is_statement (getlab nd)
  let is_field nd        = L.is_field (getlab nd)
  let is_class nd        = L.is_class (getlab nd)
  let is_interface nd    = L.is_interface (getlab nd)
  let is_enum nd         = L.is_enum (getlab nd)
  let is_final nd        = L.is_final (getlab nd)
  let is_public nd       = L.is_public (getlab nd)
  let is_protected nd    = L.is_protected (getlab nd)
  let is_private nd      = L.is_private (getlab nd)
  let is_methodbody nd   = L.is_methodbody (getlab nd)
  let is_methinvok nd    = L.is_methodinvocation (getlab nd)
  let is_extends nd      = L.is_extends (getlab nd)
  let is_extendsifs nd   = L.is_extendsinterfaces (getlab nd)
  let is_modifiers nd    = L.is_modifiers (getlab nd)
  let is_modifier nd     = L.is_modifier (getlab nd)
  let is_vdeclaration nd = L.is_localvariabledecl (getlab nd)
  let is_vdeclarator nd  = L.is_variabledeclarator (getlab nd)
  let is_literal nd      = L.is_literal (getlab nd)
  let is_name nd         = L.is_name (getlab nd)
  let is_named nd        = L.is_named (getlab nd)
  let is_instcreat nd    = L.is_instancecreation (getlab nd)
  let is_acreat nd       = L.is_arraycreation (getlab nd)
  let is_ctorinvok nd    = L.is_ctorinvocation (getlab nd)
  let is_assign nd       = L.is_assignment (getlab nd)
  let is_qual nd         = L.is_qualifier (getlab nd)
  let is_throws nd       = L.is_throws (getlab nd)
(*
  let is_namedxxx nd = L.is_namedxxx (getlab nd)
  let is_namedxxxpair(nd1, nd2) = L.is_namedxxxpair(getlab nd1, getlab nd2)
*)
  let is_expression nd = L.is_expression (getlab nd)
  let is_primary nd    = L.is_primary (getlab nd)
  let is_unaryop nd    = L.is_unaryop (getlab nd)
  let is_binaryop nd   = L.is_binaryop (getlab nd)
  let is_pdecl nd      = L.is_packagedeclaration (getlab nd)
  let is_field_acc nd  = L.is_fieldaccess (getlab nd)

  let is_arg nd =
    try
      L.is_arguments (getlab nd#initial_parent)
    with _ -> false



  let is_else nd =
    try
      let pnd = nd#initial_parent in
      L.is_if (getlab pnd) && nd#pos = 2
    with _ -> false

  let is_cond nd =
    try
      let pnd = nd#initial_parent in
      let lab = getlab pnd in
      L.is_if lab && nd#pos = 0 ||
      L.is_while lab && nd#pos = 0 ||
      L.is_do lab && nd#pos = 1
    with _ -> false


  let is_paramty nd =
    try
      let pnd = nd#initial_parent in
      is_param pnd && nd#pos = pnd#nchildren - 1
    with _ -> false

  let is_retty nd =
    try
      is_type nd && L.is_method (getlab nd#initial_parent)
    with _ -> false

  let is_retval nd =
    try
      is_expression nd && L.is_return (getlab nd#initial_parent)
    with _ -> false

  let is_fieldty nd =
    try
      let pnd = nd#initial_parent in
      is_type nd && is_field pnd
    with _ -> false

  let is_varty nd =
    try
      is_type nd && is_vdeclaration nd#initial_parent
    with _ -> false

  let is_extended nd =
    try
      is_type nd && is_extends nd#initial_parent
    with _ -> false

  let is_extendedifs nd =
    try
      is_type nd && is_extendsifs nd#initial_parent
    with _ -> false

  let is_assert nd = L.is_assert (getlab nd)
  let is_assertcond nd =
    try
      is_assert nd#initial_parent && nd#pos = 0
    with _ -> false
  let is_assertmes nd =
    try
      is_assert nd#initial_parent && nd#pos = 1
    with _ -> false

  let is_forinit nd =
    try
      L.is_forinit (getlab nd#initial_parent)
    with _ -> false
  let is_forcond nd =
    try
      L.is_forcond (getlab nd#initial_parent)
    with _ -> false
  let is_forupdate nd =
    try
      L.is_forupdate (getlab nd#initial_parent)
    with _ -> false

  let is_lhs nd =
    try
      is_assign nd#initial_parent && nd#pos = 0
    with _ -> false
  let is_rhs nd =
    try
      is_assign nd#initial_parent && nd#pos = 1
    with _ -> false

  let is_idecl nd =
    try
      L.is_importdeclarations (getlab nd#initial_parent)
    with _ -> false

  let is_thty nd =
    try
      is_type nd && is_throws nd#initial_parent
    with _ -> false

  let is_primary_or_expression nd = is_primary nd || is_expression nd

  let is_block nd = L.is_block (getlab nd)

  let _nesting_depth_of_methodbody methodbody_nd =
    let tbl = Hashtbl.create 0 in
    let add d nd =
      try
        Hashtbl.replace tbl d (nd::(Hashtbl.find tbl d))
      with
          Not_found -> Hashtbl.add tbl d [nd]
    in
    let rec doit depth nd =
      if is_stmt nd then begin
        let new_depth = depth + 1 in
        add new_depth nd;
        Array.iter (doit new_depth) nd#children
      end
      else
        Array.iter (doit depth) nd#children
    in
    Array.iter (doit 0) methodbody_nd#children;

    let maxd = ref 0 in

    Hashtbl.iter
      (fun d _ ->
        if d > !maxd then
          maxd := d
      ) tbl;

    let nodes = Hashtbl.find tbl !maxd in

    [%debug_log "body=%s maxd=%d nd=%s"
      methodbody_nd#data#to_string
      !maxd
      (Xlist.to_string (fun n -> n#data#to_string) ";" nodes)];

    !maxd, nodes
  (* end of func _nesting_depth_of_methodbody *)

  let nesting_depth_of_methodbody mb =
    let d, _ = _nesting_depth_of_methodbody mb in
    d

  let enclosing_methodbody nd =
    let rec doit n =
      try
        let pnd = n#initial_parent in
        if is_methodbody pnd then pnd
        else doit pnd
      with
        Otree.Parent_not_found _ ->
          raise Not_found
    in
    let res = doit nd in

    [%debug_log "%s -> %s" nd#data#to_string res#data#to_string];

    res
  (* end of func enclosing_methodbody *)

  let stmt_ancestors stmt_nd =
    let res = ref [] in
    let rec doit n =
      try
        let p = n#initial_parent in
        if is_stmt p then
          res := p :: !res
        else
          doit p#initial_parent
      with
          Otree.Parent_not_found _ -> ()
    in
    doit stmt_nd;
    !res

  let is_depth_defining nd =
    try
      let mbnd = enclosing_methodbody nd in
      let ndepth, nodes = _nesting_depth_of_methodbody mbnd in
      let _ = ndepth in

      [%debug_log "nd=%s mbnd=%s depth=%d" nd#data#to_string mbnd#data#to_string ndepth];

      match nodes with
        | [] -> false
        | [n] -> n == nd
        | _ ->
          let tbl = Hashtbl.create 0 in
          List.iter
            (fun n ->
              List.iter (fun a -> Hashtbl.add tbl a true) (stmt_ancestors n);
            ) nodes;

          Hashtbl.mem tbl nd

    with Not_found -> false



(* *)

  let _get_unit tree nd =
    try
      let u = tree#get_nearest_containing_unit nd in
      u#data#label
    with Not_found -> ""

  let get_unit tree nd =
    let _unit = _get_unit tree nd in
    try
      if is_arg nd then
        _unit ^ "." ^ nd#initial_parent#initial_parent#data#label
      else
        _unit
    with _ -> _unit


  let ids_to_str ids =
    if ids = [] then "" else sprintf "{%s}" (String.concat "," ids)

  let subtree_to_str tree nd =
    sprintf "[%s]" (tree#subtree_to_simple_string nd#gindex)

  let get_desc1 is_whole tree nd =
    let ids = tree#get_ident_use_list nd#gindex in
    let extra =
      if is_whole then
        if is_param nd || is_vdeclaration nd then
          let ty = nd#initial_children.(0) in
          if is_type ty then
            ":"^ty#data#label
          else
            ""
        else
          ""
      else
        ""
    in
    let extra2 =
      if (* is_whole *) true then
        subtree_to_str tree nd
      else
        ""
    in
    nd#data#label^extra^(ids_to_str ids)^extra2

  let get_desc2 tree1 tree2 nd1 nd2 =
    let ids1 = tree1#get_ident_use_list nd1#gindex in
    let ids2 = tree2#get_ident_use_list nd2#gindex in
    sprintf "%s%s%s -> %s%s%s"
      nd1#data#label (ids_to_str ids1) (subtree_to_str tree1 nd1)
      nd2#data#label (ids_to_str ids2) (subtree_to_str tree2 nd2)






  let cat_argument = Triple.make_qname L.lang_prefix "Argument"


(* class Change.F.c *)

  class c options tree1 tree2 nmapping edits get_unit get_desc1 get_desc2 = object (self)
    inherit CB.c options tree1 tree2 nmapping edits get_unit get_desc1 get_desc2

    method mkt_accessibility_increased ?(category=Triple.ghost) = function
      | Cmodified(nd1, nd2) -> begin
          ignore category;
          [(self#mkent1 nd1, p_accessibility_increased, self#mkent2 nd2)]
      end
      | _ -> []

    method mkt_accessibility_decreased ?(category=Triple.ghost) = function
      | Cmodified(nd1, nd2) -> begin
          ignore category;
          [(self#mkent1 nd1, p_accessibility_decreased, self#mkent2 nd2)]
      end
      | _ -> []

    method mkt_nesting_depth =
      self#_mkt_nesting_depth enclosing_methodbody nesting_depth_of_methodbody


    method make_implementation_change () =
      let changes = new change_set in
      edits#iter
        (fun ed ->
          match ed with
          | E.Move(_, _, (info1, _), (info2, _)) ->
              let nd1 = I.get_node info1 in
              let nd2 = I.get_node info2 in
              if is_methodbody nd1 && is_methodbody nd2 then begin
                try
                  let meth_nd1 = nd1#initial_parent in
                  let meth_nd2 = nd2#initial_parent in
                  changes#add (Cmodified(meth_nd1, meth_nd2))
                with
                  Otree.Parent_not_found _ -> assert false
              end
          | _ -> ()
        );
      changes#get_list

(* low <- private - protected - <none> - public -> high *)
    method make_accessibility_change ~rel_cond ~del_cond ~ins_cond () =
      let changes = new change_set in

      if not options#fact_for_changes_basic_flag then begin

        let d_tbl = Hashtbl.create 0 in
        let i_tbl = Hashtbl.create 0 in
        let use_cand_tbl = Hashtbl.create 0 in
        let add1 tbl k v =
          try
            Hashtbl.replace tbl k (v::(Hashtbl.find tbl k))
          with Not_found ->
            Hashtbl.add tbl k [v]
        in
        edits#iter
          (fun ed ->
            match ed with
            | E.Relabel(_, (info1, _), (info2, _)) ->
                let nd1 = I.get_node info1 in
                let nd2 = I.get_node info2 in
                let c = not (edits#mem_mov12 nd1 nd2) in
                if (rel_cond nd1 nd2) && c then begin
                  try
                    let ppnd1 = nd1#initial_parent#initial_parent in
                    let ppnd2 = nd2#initial_parent#initial_parent in
                    changes#add (Cmodified(ppnd1, ppnd2));
                    self#set_used ed;
                  with
                    Otree.Parent_not_found _ -> assert false
                end

            | E.Delete(_, info, _) -> begin
                let nd = I.get_node info in
                try
                  if del_cond nd then begin
                    let ppnd = nd#initial_parent#initial_parent in
                    add1 d_tbl ppnd nd;
                    add1 use_cand_tbl ppnd ed
                  end;
                with
                  Otree.Parent_not_found _ -> assert false
            end

            | E.Insert(_, info, _) -> begin
                let nd = I.get_node info in
                try
                  if ins_cond nd then begin
                    let ppnd = nd#initial_parent#initial_parent in
                    add1 i_tbl ppnd nd;
                    add1 use_cand_tbl ppnd ed
                  end;
                with
                  Otree.Parent_not_found _ -> assert false
            end

            | E.Move(_, sub, (info1, _), (info2, _)) ->
                if !sub <> E.Mpermutation then begin
                  let nd1 = I.get_node info1 in
                  let nd2 = I.get_node info2 in
                  try
                    if del_cond nd1 then begin
                      let ppnd1 = nd1#initial_parent#initial_parent in
                      add1 d_tbl ppnd1 nd1;
                      add1 use_cand_tbl ppnd1 ed
                    end;
                    if ins_cond nd2 then begin
                      let ppnd2 = nd2#initial_parent#initial_parent in
                      add1 i_tbl ppnd2 nd2;
                      add1 use_cand_tbl ppnd2 ed;
                    end;
                  with
                    Otree.Parent_not_found _ -> assert false
                end
          );

        Hashtbl.iter
          (fun nd nds ->
            [%debug_log "checking %a" nups nd];
            try
              let nd' = nmapping#find nd in

              [%debug_log " -> %a" nups nd'];

              let nds' =
                try
                  Hashtbl.find i_tbl nd'
                with Not_found -> []
              in
              if not
                  ((List.exists is_protected nds) &&
                   (List.exists is_protected nds'))
              then begin
                try
                  [%debug_log "added %s - %s"
                    nd#data#to_string nd'#data#to_string];

                  changes#add (Cmodified(nd, nd'));
                  List.iter self#set_used (Hashtbl.find use_cand_tbl nd)

                with _ -> assert false
              end
            with Not_found -> ()
          ) d_tbl;

        Hashtbl.iter
          (fun nd' nds' ->
            try
              let nd = nmapping#inv_find nd' in
              if not (Hashtbl.mem d_tbl nd) then
                if not (List.exists is_protected nds') then begin
                  try
                    [%debug_log "added %s - %s"
                      nd#data#to_string nd'#data#to_string];

                    changes#add (Cmodified(nd, nd'));
                    List.iter self#set_used (Hashtbl.find use_cand_tbl nd')

                  with _ -> assert false
                end
            with Not_found -> ()
          ) i_tbl;

      end; (* of if not options#fact_for_changes_basic_flag *)

      changes#get_list
    (* end of method make_accessibility_change *)


    method! make_changes_list () =
      let mkt_del = self#mkt_deleted ~category:Triple.ghost in
      let mkt_del_c cat = self#mkt_deleted ~category:cat in
      let mkt_ins = self#mkt_inserted ~category:Triple.ghost in
      let mkt_ins_c cat = self#mkt_inserted ~category:cat in
      let mkt_mod = self#mkt_modified ~category:Triple.ghost in
      let mkt_mod_c cat = self#mkt_modified ~category:cat in
      let mkt_chgto = self#mkt_changed_to ~category:Triple.ghost in
      let mkt_chgto_c cat = self#mkt_changed_to ~category:cat in
      let mkt_ren = self#mkt_renamed ~category:Triple.ghost in
      let mkt_ren_c cat = self#mkt_renamed ~category:cat in
      let mkt_mov = self#mkt_moved_to ~category:Triple.ghost in
      let mkt_odrchg = self#mkt_order_changed ~category:Triple.ghost in
      let mkt_odrchg_c cat = self#mkt_order_changed ~category:cat in
      [
        "primary name renamed", Slow, (self#make_renaming is_name), mkt_ren;

        "field access renamed", Slow, (self#make_renaming is_field_acc), mkt_ren;

        "condition expression changed",  Smedium, (self#make_changed_to is_cond), mkt_chgto;
        "condition expression modified", Smedium, (self#aggregate_changes is_cond), mkt_mod;

        "else-part removed",  Smedium, (self#make_delete_st is_else), mkt_del;
        "else-part added",    Smedium, (self#make_insert_st is_else), mkt_ins;
        "else-part deleted",  Smedium, (self#make_delete is_else), mkt_del;
        "else-part inserted", Smedium, (self#make_insert is_else), mkt_ins;

        "method renamed or signature changed", Shigh, (self#make_renaming is_meth), mkt_ren;

        "method removed", Scrucial, (self#make_delete_st is_meth), mkt_del;
        "method added",   Slow,     (self#make_insert_st is_meth), mkt_ins;
        "method modified", Slow,    (self#aggregate_changes is_meth), mkt_mod;

        "class renamed", Shigh,   (self#make_renaming is_class), mkt_ren;
        "class removed", Smedium, (self#make_delete_st is_class), mkt_del;
        "class added",   Slow,    (self#make_insert_st is_class), mkt_ins;

        "interface renamed", Shigh,   (self#make_renaming is_interface), mkt_ren;
        "interface removed", Smedium, (self#make_delete_st is_interface), mkt_del;
        "interface added",   Slow,    (self#make_insert_st is_interface), mkt_ins;

        "enum renamed", Shigh,   (self#make_renaming is_enum), mkt_ren;
        "enum removed", Smedium, (self#make_delete_st is_enum), mkt_del;
        "enum added",   Slow,    (self#make_insert_st is_enum), mkt_ins;

        "parameter removed",       Scrucial, (self#make_delete_st is_param), mkt_del;
        "parameter added",         Scrucial, (self#make_insert_st is_param), mkt_ins;
        "parameter order changed", Scrucial, (self#make_order_change is_param), mkt_odrchg;
        "parameter renamed",       Smedium,  (self#make_renaming is_param), mkt_ren;
        "parameter type changed",  Scrucial, (self#make_changed_to is_paramty), mkt_chgto;

        "type parameter removed",       Scrucial, (self#make_delete_st is_tparam), mkt_del;
        "type parameter added",         Scrucial, (self#make_insert_st is_tparam), mkt_ins;
        "type parameter order changed", Scrucial, (self#make_order_change is_tparam), mkt_odrchg;
        "type parameter renamed",       Smedium,  (self#make_renaming is_tparam), mkt_ren;

        "return type changed", Scrucial, (self#make_changed_to is_retty), mkt_chgto;

        "return value changed",  Scrucial, (self#make_changed_to is_retval), mkt_chgto;
        "return value modified", Scrucial, (self#aggregate_changes is_retval), mkt_mod;

        "constructor removed", Scrucial, (self#make_delete_st is_ctor), mkt_del;
        "constructor added",   Slow,     (self#make_insert_st is_ctor), mkt_ins;
        "constructor deleted", Scrucial, (self#make_delete is_ctor), mkt_del;
        "constructor inserted",   Slow,  (self#make_insert is_ctor), mkt_ins;

        "field removed",          Scrucial, (self#make_delete_st is_field), mkt_del;
        "field added",            Slow,     (self#make_insert_st is_field), mkt_ins;
        "field type changed",     Scrucial, (self#make_changed_to is_fieldty), mkt_chgto;
        "field renamed",          Shigh,    (self#make_renaming is_field), mkt_ren;
        "final modifier added",   Scrucial, (self#make_insert_st is_final), mkt_ins;
        "final modifier removed", Slow,     (self#make_delete_st is_final), mkt_del;

        "accessibility increased", Smedium,
        (self#make_accessibility_change
           ~rel_cond:(fun nd1 nd2 ->
             (is_private nd1 && (is_protected nd2 || is_public nd2)) ||
             (is_protected nd1 && is_public nd2))
           ~del_cond:(fun nd -> is_private nd || is_protected nd)
           ~ins_cond:is_public
        ),
        self#mkt_accessibility_increased ~category:Triple.ghost;

        "accessibility decreased", Scrucial,
        (self#make_accessibility_change
           ~rel_cond:(fun nd1 nd2 ->
             (is_public nd1 && (is_protected nd2 || is_private nd2)) ||
             (is_protected nd1 && is_private nd2))
           ~del_cond:is_public
           ~ins_cond:(fun nd -> is_protected nd || is_private nd)
        ),
        self#mkt_accessibility_decreased ~category:Triple.ghost;

        "statement deleted to decrease nesting-depth", Shigh,
        (self#make_delete (fun n -> is_depth_defining n && is_stmt n)),
        self#mkt_nesting_depth ~category:Triple.ghost;

        "statement removed to decrease nesting-depth", Shigh,
        (self#make_delete_st (fun n -> is_depth_defining n && is_stmt n)),
        self#mkt_nesting_depth ~category:Triple.ghost;

        "statement inserted to increase nesting-depth", Shigh,
        (self#make_insert (fun n -> is_depth_defining n && is_stmt n)),
        self#mkt_nesting_depth ~category:Triple.ghost;

        "statement added to increase nesting-depth",   Shigh,
        (self#make_insert_st (fun n -> is_depth_defining n && is_stmt n)),
        self#mkt_nesting_depth ~category:Triple.ghost;

        "statement moved to increase nesting-depth", Shigh,
        (self#_make_move
           (fun n1 n2 ->
             not (is_depth_defining n1) && is_depth_defining n2)
           is_stmt
        ),
        self#mkt_nesting_depth ~category:Triple.ghost;

        "statement moved to decrease nesting-depth", Shigh,
        (self#_make_move
           (fun n1 n2 ->
             is_depth_defining n1 && not (is_depth_defining n2))
           is_stmt
        ),
        self#mkt_nesting_depth ~category:Triple.ghost;

        "parent class removed", Scrucial, (self#make_delete_st is_extends), mkt_del;
        "parent class added",   Scrucial, (self#make_insert_st is_extends), mkt_ins;
        "parent class renamed", Scrucial, (self#make_renaming is_extended), mkt_ren;

        "parent interface removed", Scrucial,
        (self#make_delete_st (fun nd -> is_extendedifs nd || is_extendsifs nd)), mkt_del;
        "parent interface added", Scrucial,
        (self#make_insert_st (fun nd -> is_extendedifs nd || is_extendsifs nd)), mkt_ins;
        "parent interface renamed", Scrucial, (self#make_renaming is_extendedifs), mkt_ren;



        (* finer-grained changes *)

        "modifier removed", Smedium, (self#make_delete_st is_modifier), mkt_del;
        "modifier added",   Smedium, (self#make_insert_st is_modifier), mkt_ins;
        "modifier changed", Smedium, (self#make_changed_to is_modifier), mkt_chgto;

        "method invocation modified",             Slow, (self#aggregate_changes is_methinvok), mkt_mod;
        "method invocation renamed",              Slow, (self#make_renaming is_methinvok), mkt_ren;
        "method invocation changed",              Slow, (self#make_changed_to is_methinvok), mkt_chgto;
        "method invocation removed",              Slow, (self#make_delete_st is_methinvok), mkt_del;
        "method invocation added",                Slow, (self#make_insert_st is_methinvok), mkt_ins;
        "method invocation deleted",              Slow, (self#make_delete is_methinvok), mkt_del;
        "method invocation inserted",             Slow, (self#make_insert is_methinvok), mkt_ins;
        "qualifier of method invocation renamed", Slow, (self#make_renaming is_qual), mkt_ren;
        "qualifier of method invocation removed", Slow, (self#make_delete is_qual), mkt_del;
        "qualifier of method invocation added",   Slow, (self#make_insert is_qual), mkt_ins;

        "block removed",  Smedium, (self#make_delete_st is_block), mkt_del;
        "block added",    Smedium, (self#make_insert_st is_block), mkt_ins;
        "block deleted",  Smedium, (self#make_delete is_block), mkt_del;
        "block inserted", Smedium, (self#make_insert is_block), mkt_ins;
        "block moved",    Smedium, (self#make_move is_block), mkt_mov;

        "throws-clause removed",                   Smedium, (self#make_delete_st is_throws), mkt_del;
        "throws-clause added",                     Smedium, (self#make_insert_st is_throws), mkt_ins;
        "exception type removed in throws-clause", Smedium, (self#make_delete_st is_thty), mkt_del;
        "exception type added in throws-clause",   Smedium, (self#make_insert_st is_thty), mkt_ins;
        "exception type renamed in throws-clause", Smedium, (self#make_renaming is_thty), mkt_ren;

        "variable declaration renamed", Slow,    (self#make_renaming is_vdeclarator), mkt_ren;
        "variable declaration removed", Smedium,
        (self#make_delete_st (fun nd -> is_vdeclaration nd || is_vdeclarator nd)), mkt_del;
        "variable declaration added",   Smedium,
        (self#make_insert_st (fun nd -> is_vdeclaration nd || is_vdeclarator nd)), mkt_ins;
        "variable type changed",        Slow,    (self#make_changed_to is_varty), mkt_chgto;

        "instance creation changed",  Slow,    (self#make_changed_to is_instcreat), mkt_chgto;
        "instance creation modified", Slow,    (self#aggregate_changes is_instcreat), mkt_mod;
        "instance creation removed",  Smedium, (self#make_delete_st is_instcreat), mkt_del;
        "instance creation added",    Smedium, (self#make_insert_st is_instcreat), mkt_ins;

        "array creation changed",  Slow,    (self#make_changed_to is_acreat), mkt_chgto;
        "array creation modified", Slow,    (self#aggregate_changes is_acreat), mkt_mod;
        "array creation removed",  Smedium, (self#make_delete_st is_acreat), mkt_del;
        "array creation added",    Smedium, (self#make_insert_st is_acreat), mkt_ins;

        "constructor invocation changed",  Slow,    (self#make_changed_to is_ctorinvok), mkt_chgto;
        "constructor invocation modified", Slow,    (self#aggregate_changes is_ctorinvok), mkt_mod;
        "constructor invocation removed",  Smedium, (self#make_delete_st is_ctorinvok), mkt_del;
        "constructor invocation added",    Smedium, (self#make_insert_st is_ctorinvok), mkt_ins;

        "assertion condition changed",  Slow,    (self#make_changed_to is_assertcond), mkt_chgto;
        "assertion condition modified", Slow,    (self#aggregate_changes is_assertcond), mkt_mod;
        "assertion removed",            Smedium, (self#make_delete_st is_assert), mkt_del;
        "assertion added",              Smedium, (self#make_insert_st is_assert), mkt_ins;
        "assertion message removed",    Slow,    (self#make_delete_st is_assertmes), mkt_del;
        "assertion message added",      Slow,    (self#make_insert_st is_assertmes), mkt_ins;

        "initialization-part of for-statement changed",  Slow, (self#make_changed_to is_forinit), mkt_chgto;
        "initialization-part of for-statement modified", Slow, (self#aggregate_changes is_forinit), mkt_mod;
        "condition-part of for-statement changed",       Slow, (self#make_changed_to is_forcond), mkt_chgto;
        "condition-part of for-statement modified",      Slow, (self#aggregate_changes is_forcond), mkt_mod;
        "update-part of for-statement changed",          Slow, (self#make_changed_to is_forupdate), mkt_chgto;
        "update-part of for-statement modified",         Slow, (self#aggregate_changes is_forupdate), mkt_mod;

        "assignment removed",         Smedium, (self#make_delete_st is_assign), mkt_del;
        "assignment added",           Smedium, (self#make_insert_st is_assign), mkt_ins;
        "LHS of assignment changed",  Slow,    (self#make_changed_to is_lhs), mkt_chgto;
        "LHS of assignment modified", Slow,    (self#aggregate_changes is_lhs), mkt_mod;
        "RHS of assignment changed",  Slow,    (self#make_changed_to is_rhs), mkt_chgto;
        "RHS of assignment modified", Slow,    (self#aggregate_changes is_rhs), mkt_mod;


        "argument removed",       Scrucial, (self#make_delete_st is_arg), mkt_del_c cat_argument;
        "argument added",         Scrucial, (self#make_insert_st is_arg), mkt_ins_c cat_argument;
        "argument order changed", Scrucial, (self#make_order_change is_arg), mkt_odrchg_c cat_argument;
        "argument renamed",       Slow,     (self#make_renaming is_arg), mkt_ren_c cat_argument;
        "argument changed",       Slow,     (self#make_changed_to is_arg), mkt_chgto_c cat_argument;
        "argument modified",      Slow,     (self#aggregate_changes is_arg), mkt_mod_c cat_argument;

        "import declaration removed",       Smedium, (self#make_delete_st is_idecl), mkt_del;
        "import declaration added",         Smedium, (self#make_insert_st is_idecl), mkt_ins;
        "import declaration renamed",       Smedium, (self#make_renaming is_idecl), mkt_ren;
        "import declaration order changed", Slow,    (self#make_order_change is_idecl), mkt_odrchg;

        "package declaration removed",       Smedium, (self#make_delete_st is_pdecl), mkt_del;
        "package declaration added",         Smedium, (self#make_insert_st is_pdecl), mkt_ins;
        "package declaration renamed",       Smedium, (self#make_renaming is_pdecl), mkt_ren;

        "constant changed", Smedium, (self#make_changed_to is_literal), mkt_chgto;

        "expression removed",  Slow, (self#make_delete_st is_primary_or_expression), mkt_del;
        "expression added",    Slow, (self#make_insert_st is_primary_or_expression), mkt_ins;
        "expression moved",    Slow, (self#make_move is_primary_or_expression), mkt_mov;
        "expression changed",  Slow, (self#make_changed_to is_primary_or_expression), mkt_chgto;
        "expression modified", Slow, (self#aggregate_changes is_primary_or_expression), mkt_mod;

        "unary operator removed", Slow, (self#make_delete is_unaryop), mkt_del;
        "unary operator added",   Slow, (self#make_insert is_unaryop), mkt_ins;
        "unary operator changed", Slow, (self#make_changed_to is_unaryop), mkt_chgto;

        "binary operator removed", Slow, (self#make_delete is_binaryop), mkt_del;
        "binary operator added",   Slow, (self#make_insert is_binaryop), mkt_ins;
        "binary operator changed", Slow, (self#make_changed_to is_binaryop), mkt_chgto;

        "statement removed",       Smedium, (self#make_delete_st is_stmt), mkt_del;
        "statement added",         Smedium, (self#make_insert_st is_stmt), mkt_ins;
        "statement deleted",       Smedium, (self#make_delete is_stmt), mkt_del;
        "statement inserted",      Smedium, (self#make_insert is_stmt), mkt_ins;
        "statement order changed", Slow,    (self#make_order_change is_stmt), mkt_odrchg;
        "statement moved",         Smedium, (self#make_move is_stmt), mkt_mov;
        "statement changed",       Slow,    (self#make_changed_to is_stmt), mkt_chgto;
        "statement modified",      Slow,    (self#aggregate_changes is_stmt), mkt_mod;

        "method implementation changed", Slow, (self#make_implementation_change), mkt_mod;

        "(removed)",       Slow, (self#make_delete_st (fun _ -> true)), mkt_del;
        "(added)",         Slow, (self#make_insert_st (fun _ -> true)), mkt_ins;
        "(deleted)",       Slow, (self#make_delete (fun _ -> true)), mkt_del;
        "(inserted)",      Slow, (self#make_insert (fun _ -> true)), mkt_ins;
        "(moved)",         Slow, (self#make_move (fun _ -> true)), mkt_mov;
        "(changed)",       Slow, (self#make_changed_to (fun _ -> true)), mkt_chgto;
        "(renamed)",       Slow, (self#make_renaming is_named), mkt_ren;
        "(order changed)", Slow, (self#make_order_change (fun _ -> true)), mkt_odrchg;

      ]
    (* end of method make_changes_list *)



 end (* of class Change.F.c *)

  let extract options tree1 tree2 nmapping edits =
    let chg = new c options tree1 tree2 nmapping edits get_unit get_desc1 get_desc2 in
    let res = chg#extract in
    chg#recover_edits;
    res

end (* of functor Change.F *)
