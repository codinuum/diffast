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
(* change_base.ml *)

[%%prepare_logger]

module Xset = Diffast_misc.Xset
module Otree = Diffast_misc.Otree
module Loc = Diffast_misc.Loc

module EO = Editop


let sprintf = Printf.sprintf

type node_t = Spec.node_t

type change =
  | Cdeleted  of bool (* is whole subtree *) * node_t * node_t (* from *)
  | Cinserted of bool (* is whole subtree *) * node_t * node_t (* into *)
  | Cmodified of node_t * node_t
  | Cchanged  of bool (* is_mov *) * node_t * node_t
  | Crenamed  of bool (* is_mov *) * node_t * node_t
  | Cmoved    of node_t * node_t
  | Ccardinality_changed of node_t * node_t

type change_to_triples = change -> Triple.t list
type change_maker = unit -> change list

type change_tag =
  | Tdel
  | Tins
  | Tmod
  | Tcha
  | Tren
  | Tmov
  | Tcar

let hash_change = function
  | Cdeleted(w, nd, from_nd)       -> Hashtbl.hash (Tdel, w, nd#uid, from_nd#uid)
  | Cinserted(w, nd, into_nd)      -> Hashtbl.hash (Tins, w, nd#uid, into_nd#uid)
  | Cmodified(nd1, nd2)            -> Hashtbl.hash (Tmod, nd1#uid, nd2#uid)
  | Cchanged(_, nd1, nd2)          -> Hashtbl.hash (Tcha, nd1#uid, nd2#uid)
  | Crenamed(_, nd1, nd2)          -> Hashtbl.hash (Tren, nd1#uid, nd2#uid)
  | Cmoved(nd1, nd2)               -> Hashtbl.hash (Tmov, nd1#uid, nd2#uid)
  | Ccardinality_changed(nd1, nd2) -> Hashtbl.hash (Tcar, nd1#uid, nd2#uid)

let change_to_string = function
  | Cdeleted(is_whole, nd, from_nd)  ->
      sprintf "%s%s from %s" nd#data#to_string (if is_whole then "*" else "") from_nd#data#to_string

  | Cinserted(is_whole, nd, into_nd) ->
      sprintf "%s%s into %s" nd#data#to_string (if is_whole then "*" else "") into_nd#data#to_string

  | Cmodified(nd1, nd2) -> sprintf "%s -> %s" nd1#data#to_string nd2#data#to_string
  | Cchanged(_, nd1, nd2)  -> sprintf "%s -> %s" nd1#data#to_string nd2#data#to_string
  | Crenamed(_, nd1, nd2)  -> sprintf "%s -> %s" nd1#data#to_string nd2#data#to_string
  | Cmoved(nd1, nd2)    ->
      sprintf "%s: [%s] -> [%s]" nd1#data#label (Loc.to_string nd1#data#src_loc) (Loc.to_string nd2#data#src_loc)

  | Ccardinality_changed(nd1, nd2) ->
      sprintf "%s: %d -> %d" nd1#data#to_string nd1#initial_nchildren nd2#initial_nchildren

type significance = Slow | Smedium | Shigh | Scrucial

let score = function
  | Slow     -> 1
  | Smedium  -> 2
  | Shigh    -> 3
  | Scrucial -> 4




type change_info =
      string * (* description *)
      string * (* anonymized description *)
      string * (* containing unit 1 *)
      Loc.t  * (* location        1 *)
      string * (* containing unit 2 *)
      Loc.t    (* location        2 *)

type changes = (string * int * string list) list

type change_infos = (string * int * change_info list) list

class change_set = object
  val set = Xset.create 0
  val mutable content = []

  method add c =
    let h = hash_change c in
    if not (Xset.mem set h) then begin
      content <- c :: content;
      Xset.add set h
    end

  method iter f = List.iter f content

  method get_list = content

end (* of change_set *)



let mkilit i = Triple.make_literal (string_of_int i)

let p_is_a          = Triple.p_is_a
let p_moved_to      = Triple.p_moved_to
let p_deleted_from  = Triple.p_deleted_from
let p_inserted_into = Triple.p_inserted_into
let p_pruned_from   = Triple.p_pruned_from
let p_grafted_onto  = Triple.p_grafted_onto

let p_gen_removed = Triple.p_gen_removed
let p_gen_added   = Triple.p_gen_added

let p_affects_nesting_depth = Triple.p_affects_nesting_depth
let p_nesting_depth         = Triple.p_nesting_depth
let p_cardinality           = Triple.p_cardinality



let l_true = Triple.l_true


let make_mkent_pair options tree1 tree2 =
  let enc = options#fact_enc in
  let enc_str = Entity.encoding_to_string enc in
  let fid1_str = Triple.encode_fid options tree1 in
  let fid2_str = Triple.encode_fid options tree2 in

  let mkent fid_str tree nd =
    let _ = tree in
    if Triple.is_ghost_ast_node nd then
      Triple.ghost
    else
      let loc = nd#data#src_loc in
      if loc = Loc.dummy then
        [%warn_log "location not defined: %s@%s" nd#data#to_string tree#source_path];
      let range_str = Triple.get_range_str enc loc in
      let fid_str =
        let fid = nd#data#source_fid in
        if fid = "" then
          fid_str
        else
          fid
      in
      Triple.mkent
        (Triple.__make_entity enc_str fid_str range_str nd#data#is_phantom nd#data#is_special)
  in
  let mkent1 = mkent fid1_str tree1 in
  let mkent2 = mkent fid2_str tree2 in

  mkent1, mkent2


let is_ghost nd = Triple.is_ghost_ast_node nd

[%%capture_path
let find_from_or_into tree1 tree2 edits ?(mid_opt=None) tree' map_find node =
  ignore tree1;
  ignore mid_opt;
  let rec scan nd =
    try
      if (* is_phantom nd || *) is_ghost nd then
        scan nd#initial_parent
      else
        try
          let nd' = map_find nd in
          let is_mov =
            if tree' == tree2 then
              edits#mem_mov12 nd nd'
            else
              edits#mem_mov12 nd' nd
          in
          if is_mov then
            raise Not_found;
          nd'
        with
          Not_found -> scan nd#initial_parent

    with
      Otree.Parent_not_found _ -> tree'#root
  in
  let res = scan node#initial_parent in
  [%debug_log "%s -> %s" node#to_string res#to_string];
  res
]


[%%capture_path
module F (L : Spec.LABEL_T) = struct

  let getlab nd = (Obj.obj nd#data#_label : L.t)

  let is_phantom nd = L.is_phantom (getlab nd)

(*
  let adjust_parent parent_nd =
    let rec loop nd =
      if (* is_phantom nd || *) is_ghost nd then
        try
          loop nd#initial_parent
        with
          Otree.Parent_not_found _ -> parent_nd
      else
        nd
    in
    loop parent_nd

  let adjust_child child_nd =
    let rec doit acc nd =
      if (* is_phantom nd || *) is_ghost nd then
        Array.fold_left doit acc nd#initial_children
      else
        nd :: acc
    in
    doit [] child_nd
*)


(* base class *)
  class c
      options
      (tree1 : Spec.tree_t)
      (tree2 : Spec.tree_t)
      (nmapping : node_t Node_mapping.c)
      edits
      get_unit
      get_desc1
      get_desc2
      =
    let mkent1, mkent2 = make_mkent_pair options tree1 tree2 in
    object (self)

      val ed_use_tbl = Hashtbl.create 0
      val mutable removed_eds = []
      val mutable added_eds = []

      val parent_tri_cache = Hashtbl.create 0
      val children_tri_cache = Hashtbl.create 0

      method private mkent1 = mkent1
      method private mkent2 = mkent2

      method private get_p_del is_whole =
        if is_whole then
          p_pruned_from
        else
          p_deleted_from

      method private get_p_ins is_whole =
        if is_whole then
          p_grafted_onto
        else
          p_inserted_into

      method mkt_deleted ?(category=Triple.ghost) = function
        | Cdeleted(is_whole, nd, from_nd) ->
(*          let from_nd = adjust_parent from_nd in *)
            let ent = mkent1 nd in
            let from_ent = mkent2 from_nd in
            let ctris =
              if Triple.is_ghost_node category then
                []
              else
                [(ent, p_is_a, category)]
            in
            (ent, self#get_p_del is_whole, from_ent) :: ctris

        | _ -> []

      method mkt_inserted ?(category=Triple.ghost) = function
        | Cinserted(is_whole, nd, into_nd) ->
(*          let into_nd = adjust_parent into_nd in *)
            let ent = mkent2 nd in
            let into_ent = mkent1 into_nd in
            let ctris =
              if Triple.is_ghost_node category then
                []
              else
                [(ent, p_is_a, category)]
            in
            (ent, self#get_p_ins is_whole, into_ent) :: ctris

        | _ -> []

      method mkt_modified ?(category=Triple.ghost) = function
        | Cmodified(nd1, nd2) ->
            let ent1 = mkent1 nd1 in
            let ent2 = mkent2 nd2 in
            let ctris =
              if Triple.is_ghost_node category then
                []
              else
                [(ent1, p_is_a, category); (ent2, p_is_a, category)]
            in
            (ent1, Triple.p_modified, ent2) :: ctris
        | _ -> []

      method mkt_changed_to ?(category=Triple.ghost) = function
        | Cchanged(is_mov, nd1, nd2) ->
            let ent1 = mkent1 nd1 in
            let ent2 = mkent2 nd2 in
            let pred =
              if is_mov then
                Triple.p_mov_changed_to
              else
                Triple.p_changed_to
            in
            let ctris =
              if Triple.is_ghost_node category then
                []
              else
                [(ent1, p_is_a, category); (ent2, p_is_a, category)]
            in
            (ent1, pred, ent2) :: ctris
        | _ -> []

      method mkt_renamed ?(category=Triple.ghost) = function
        | Crenamed(is_mov, nd1, nd2) ->
            let ent1 = mkent1 nd1 in
            let ent2 = mkent2 nd2 in
            let pred =
              if is_mov then
                Triple.p_mov_renamed
              else
                Triple.p_renamed
            in
            let ctris =
              if Triple.is_ghost_node category then
                []
              else
                [(ent1, p_is_a, category); (ent2, p_is_a, category)]
            in
            (ent1, pred, ent2) :: ctris
        | _ -> []

      method mkt_abstracted_to ?(category=Triple.ghost) = function
        | Crenamed(is_mov, nd1, nd2) -> begin
            ignore category;
            let pred =
              if is_mov then
                Triple.p_abstracted_to
              else
                Triple.p_mov_abstracted_to
            in
            [(mkent1 nd1, pred, mkent2 nd2)]
        end
        | _ -> []

      method mkt_folded_into ?(category=Triple.ghost) = function
        | Crenamed(is_mov, nd1, nd2) -> begin
            ignore category;
            let pred =
              if is_mov then
                Triple.p_folded_into
              else
                Triple.p_mov_folded_into
            in
            [(mkent1 nd1, pred, mkent2 nd2)]
        end
        | _ -> []

      method private find_mid nd1 nd2 =
        try
          Some (edits#find_mid12 nd1 nd2)
        with
          Not_found -> None

      method mkt_moved_to ?(category=Triple.ghost) = function
        | Cmoved(nd1, nd2) ->
            let ent1 = mkent1 nd1 in
            let ent2 = mkent2 nd2 in
            let mid_opt = self#find_mid nd1 nd2 in
            let from_ent =
              mkent2 (self#find_from_or_into ~mid_opt tree2 nmapping#find nd1)
            in
            let into_ent =
              mkent1 (self#find_from_or_into ~mid_opt tree1 nmapping#inv_find nd2)
            in
            let ctris =
              if Triple.is_ghost_node category then
                []
              else
                [(ent1, p_is_a, category); (ent2, p_is_a, category)]
            in
            (ent1, p_moved_to, ent2) ::
            (ent1, p_gen_removed, from_ent) ::
            (ent2, p_gen_added, into_ent) ::
            ctris

        | _ -> []

      method mkt_order_changed ?(category=Triple.ghost) = function
        | Cmoved(nd1, nd2) -> begin
            ignore category;
            let ent1 = mkent1 nd1 in
            let ent2 = mkent2 nd2 in
            let mid_opt = self#find_mid nd1 nd2 in
            let from_ent =
              mkent2 (self#find_from_or_into ~mid_opt tree2 nmapping#find nd1)
            in
            let into_ent =
              mkent1 (self#find_from_or_into ~mid_opt tree1 nmapping#inv_find nd2)
            in
            [
             (ent1, Triple.p_order_changed, ent2);
             (ent1, p_gen_removed, from_ent);
             (ent2, p_gen_added, into_ent);
           ]
        end
        | _ -> []

      method mkt_cardinality ?(category=Triple.ghost) = function
        | Cmodified(nd1, nd2) -> begin
            ignore category;
            let c1 = nd1#initial_nchildren in
            let c2 = nd2#initial_nchildren in
            if c1 <> c2 then
              [ (mkent1 nd1, p_cardinality, mkilit c1);
                (mkent2 nd2, p_cardinality, mkilit c2)
              ]
            else
              []
        end
        | _ -> []

      method _mkt_nesting_depth
          enclosing
          get_depth
          ?(category=Triple.ghost)
          = function
        | Cinserted(is_whole, nd2, into_nd) -> begin
            ignore category;
            let enc2 = enclosing nd2 in
            let d = get_depth enc2 in
            let ent = mkent2 nd2 in
            let into_ent = mkent1 into_nd in
            [ (ent, self#get_p_ins is_whole, into_ent);
              (ent, p_affects_nesting_depth, l_true);
              (mkent2 enc2, p_nesting_depth, mkilit d)
            ]
        end
        | Cdeleted(is_whole, nd1, from_nd) -> begin
            let enc1 = enclosing nd1 in
            let d = get_depth enc1 in
            let ent = mkent1 nd1 in
            let from_ent = mkent2 from_nd in
            [ (ent, self#get_p_del is_whole, from_ent);
              (ent, p_affects_nesting_depth, l_true);
              (mkent1 enc1, p_nesting_depth, mkilit d)
            ]
        end
        | Cmoved(nd1, nd2) -> begin
            let ent1 = mkent1 nd1 in
            let ent2 = mkent2 nd2 in
            let mid_opt = self#find_mid nd1 nd2 in
            let from_ent =
              mkent2 (self#find_from_or_into ~mid_opt tree2 nmapping#find nd1)
            in
            let into_ent =
              mkent1 (self#find_from_or_into ~mid_opt tree1 nmapping#inv_find nd2)
            in
            (ent1, p_moved_to, ent2) ::
            (ent1, p_gen_removed, from_ent) ::
            (ent2, p_gen_added, into_ent) ::
            (try
              let enc_nd2 = enclosing nd2 in
              let d = get_depth enc_nd2 in
              let enc_ent2 = mkent2 enc_nd2 in
              [ (ent2, p_affects_nesting_depth, l_true);
                (enc_ent2, p_nesting_depth, mkilit d)
              ]
            with Not_found -> [])
        end
        | _ -> []



      method private remove_edit ed =
        edits#remove_edit ed;
        removed_eds <- ed :: removed_eds

      method private add_edit ed =
        edits#add_edit ed;
        added_eds <- ed :: added_eds


      method recover_edits : unit =
        List.iter edits#add_edit removed_eds;
        List.iter edits#remove_edit added_eds;
        edits#finalize nmapping (fun _ -> false)

(*
      initializer
        self#eliminate_phantoms (* for facts about phantoms *)
*)
      method private set_used ed =
        let h = EO.hash ed in
        Hashtbl.add ed_use_tbl h true

      method private is_used ed =
        let h = EO.hash ed in
        Hashtbl.mem ed_use_tbl h


      method private eliminate_phantoms = (* assumes that phantoms do not nest *)

        let get_list_of_node_and_new_ex tree nd ex =
          let exns = List.map Info.get_node !ex in
          Array.fold_left
            (fun l n ->
              if not (List.memq n exns) then
                let nex =
                  List.map Info.make
                    (List.filter
                       (fun exn ->
                         tree#is_initial_ancestor n exn
                       ) exns)
                in
                (n, nex) :: l
              else
                l) [] nd#initial_children
        in
        let proc_del_ins tag ed info ex =
          let nd = Info.get_node info in
          if is_phantom nd && nd#initial_nchildren > 0 then begin
            self#remove_edit ed;

            [%debug_log "removed: %s" (EO.to_string ed)];

            let tree =
              match tag with
              | EO.Tdel -> tree1
              | EO.Tins -> tree2
              | _ -> assert false
            in
            List.iter
              (fun (n, nex) ->
                let ned =
                  match tag with
                  | EO.Tdel -> EO.Delete(nex = [], Info.make n, ref nex)
                  | EO.Tins -> EO.Insert(nex = [], Info.make n, ref nex)
                  | _ -> assert false
                in

                [%debug_log "added: %s" (EO.to_string ned)];

                self#add_edit ned

              ) (get_list_of_node_and_new_ex tree nd ex)
          end
        in
        edits#iter
          (fun ed ->
            match ed with
            | EO.Delete(_, info, ex) -> proc_del_ins EO.Tdel ed info ex
            | EO.Insert(_, info, ex) -> proc_del_ins EO.Tins ed info ex

            | EO.Relabel(_, (info1, _), _) ->
                let nd1 = Info.get_node info1 in
                if is_phantom nd1 then
                  self#remove_edit ed

            | EO.Move(mid, kind, (info1, ex1), (info2, ex2)) ->
                let nd1 = Info.get_node info1 in
                let nd2 = Info.get_node info2 in
                if is_phantom nd1 && nd1#initial_nchildren > 0 then begin
                  self#remove_edit ed;

                  [%debug_log "removed: %s" (EO.to_string ed)];

                  let n_nex_list1 = get_list_of_node_and_new_ex tree1 nd1 ex1 in
                  let n_nex_list2 = get_list_of_node_and_new_ex tree2 nd2 ex2 in

                  assert ((List.length n_nex_list1) = (List.length n_nex_list2));

                  List.iter2
                    (fun (n1, nex1) (n2, nex2) ->
                      if edits#mem_mov12 n1 n2 then
                        ()
                      else
                        let ned =
                          EO.Move(ref !mid, kind,
                                  (Info.make n1, ref nex1),
                                  (Info.make n2, ref nex2))
                        in

                        [%debug_log "added: %s" (EO.to_string ned)];

                        self#add_edit ned

                    ) n_nex_list1 n_nex_list2

                end

          );
        edits#finalize


      method make_cardinality_change cond () =
        let changes = new change_set in

        if not options#fact_for_changes_basic_flag then begin
          let changed = self#aggregate_changes cond () in
          List.iter
            (function
              | Cmodified(nd1, nd2) ->
                  if nd1#initial_nchildren <> nd2#initial_nchildren then
                    changes#add (Ccardinality_changed(nd1, nd2))
              | _ -> ()
            ) changed
        end;
        changes#get_list

      method aggregate_changes cond () =

        let changes = new change_set in

        let for_rel_or_mov ed =
          match ed with
          | EO.Relabel(_, (info1, _), (info2, _))
          | EO.Move(_, _, (info1, _), (info2, _)) ->
              let nd1 = Info.get_node info1 in
              let nd2 = Info.get_node info2 in
              let ancestors1 = tree1#initial_ancestor_nodes nd1 in
              let ancestors2 = tree2#initial_ancestor_nodes nd2 in

              List.iter
                (fun a -> if cond a then
                  try
                    let a' = nmapping#find a in
                    if List.memq a' ancestors2 && cond a' then begin
                      changes#add (Cmodified(a, a'))
                    end
                  with
                    Not_found -> ()
                ) ancestors1

          | _ -> assert false
        in (* end of func for_rel_or_mov *)

        edits#iter
          (fun ed ->
            match ed with
            | EO.Delete(_, info, _) ->
                let nd = Info.get_node info in
                List.iter
                  (fun a ->
                    if cond a then begin
                      try
                        let a' = nmapping#find a in
                        if cond a' then
                          changes#add (Cmodified(a, a'))
                      with
                        Not_found -> ()
                    end
                  ) (tree1#initial_ancestor_nodes nd)

            | EO.Insert(_, info, _) ->
                let nd = Info.get_node info in
                List.iter
                  (fun a ->
                    if cond a then begin
                      try
                        let a' = nmapping#inv_find a in
                        if cond a' then
                          changes#add (Cmodified(a', a))
                      with
                        Not_found -> ()
                    end
                  ) (tree2#initial_ancestor_nodes nd)

            | EO.Relabel _ as rel -> for_rel_or_mov rel
            | EO.Move _ as mov -> for_rel_or_mov mov
          );
        changes#get_list
     (* end of func aggregate_changes *)


      method private find_from_or_into ?(mid_opt=None) tree' map_find node =
        find_from_or_into tree1 tree2 edits ~mid_opt tree' map_find node


      method private _make_delete_or_insert tree ?(bypass_set_used=false) check_st cond ed
        info ex changes tag get_from_or_into
          =
        ignore tree;
        if not (self#is_used ed) then begin
          let nd = Info.get_node info in
          let cond_ex =
            if check_st then
              !ex = [] || nd#nchildren = 0
            else
              !ex <> []
          in
          if cond nd && cond_ex then begin
            let from_or_into = get_from_or_into nd in
            let chg =
              match tag with
              | Tdel -> Cdeleted(!ex = [], nd, from_or_into)
              | Tins -> Cinserted(!ex = [], nd, from_or_into)
              | _ -> assert false
            in
            changes#add chg;

            if not bypass_set_used then
              self#set_used ed

          end

        end


      method _make_delete check_st cond () =
        let changes = new change_set in
        edits#iter_deletes_and_inserts
          (fun ed ->
            match ed with
            | EO.Delete(_, info, ex) ->
                self#_make_delete_or_insert tree1 check_st cond ed info ex changes Tdel
                  (self#find_from_or_into tree2 nmapping#find)
            | _ -> ()
          );
        changes#get_list

      method make_delete c () = self#_make_delete false c ()

      method make_delete_st c () = self#_make_delete true c ()


      method _make_insert check_st cond () =
        let changes = new change_set in
        edits#iter_deletes_and_inserts
          (fun ed ->
            match ed with
            | EO.Insert(_, info, ex) ->
                self#_make_delete_or_insert tree2 check_st cond ed info ex changes Tins
                  (self#find_from_or_into tree1 nmapping#inv_find)
            | _ -> ()
          );
        changes#get_list

      method make_insert c () = self#_make_insert false c ()

      method make_insert_st c () = self#_make_insert true c ()

      method private is_order_change mid mov_kind nd1 nd2 =
        let parent_cond =
          try
            let pnd1 = nd1#initial_parent in
            let pnd2 = nd2#initial_parent in
            let c =
              try
                mid <> edits#find_mid12 pnd1 pnd2
              with
                Not_found -> true
            in
            nmapping#has_mapping pnd1 pnd2 && c
          with
            _ -> false
        in
        mov_kind = EO.Mpermutation && parent_cond

      method _make_move extra_cond cond () =
        let changes = new change_set in
        edits#iter_moves
          (fun ed ->
            match ed with
            | EO.Move(mid, sub, (info1, _), (info2, _)) ->
                if not (self#is_used ed) then begin
                  let nd1 = Info.get_node info1 in
                  let nd2 = Info.get_node info2 in
(*
  let c = not (edits#mem_rel12 uid1 uid2) in
 *)
                  if
                    cond nd1 && cond nd2 &&
                    not (self#is_order_change !mid !sub nd1 nd2) &&
                    extra_cond nd1 nd2 (* && c *)
                  then begin
                    changes#add (Cmoved(nd1, nd2));
                    self#set_used ed
                  end
                end
            | _ -> assert false
          );
        changes#get_list

      method make_move cond () = self#_make_move (fun _ _ -> true) cond ()

      method make_renaming2 cond1 cond2 () =
        let changes = new change_set in
        edits#iter_relabels
          (fun ed ->
            match ed with
            | EO.Relabel(_, (info1, _), (info2, _)) ->
                if not (self#is_used ed) then begin
                  let nd1 = Info.get_node info1 in
                  let nd2 = Info.get_node info2 in
                  let is_mov = edits#mem_mov12 nd1 nd2 in
                  if nd1#data#_anonymized_label = nd2#data#_anonymized_label then
                    if cond1 nd1 && cond2 nd2 (* && c *) then begin
                      changes#add (Crenamed(is_mov, nd1, nd2));
                      self#set_used ed
                    end

                end
            | _ -> assert false
          );
        changes#get_list

      method make_renaming cond () = self#make_renaming2 cond cond ()

      method make_changed_to2 cond1 cond2 () =
        let changes = new change_set in
        edits#iter_relabels
          (fun ed ->
            match ed with
            | EO.Relabel(_, (info1, _), (info2, _)) ->
                if not (self#is_used ed) then begin
                  let nd1 = Info.get_node info1 in
                  let nd2 = Info.get_node info2 in
                  let is_mov = edits#mem_mov12 nd1 nd2 in
                  (*if nd1#data#_anonymized_label <> nd2#data#_anonymized_label then*)
                    if cond1 nd1 && cond2 nd2 (* && c *) then begin
                      changes#add (Cchanged(is_mov, nd1, nd2));
                      self#set_used ed
                    end

                end
            | _ -> assert false
          );
        changes#get_list

      method make_changed_to cond () = self#make_changed_to2 cond cond ()

      method make_order_change cond () =
        let changes = new change_set in
        edits#iter_moves
          (fun ed ->
            match ed with
            | EO.Move(mid, sub, (info1, _), (info2, _)) ->
                let nd1 = Info.get_node info1 in
                let nd2 = Info.get_node info2 in
                if
                  cond nd1 && cond nd2 &&
                  (self#is_order_change !mid !sub nd1 nd2)
                then begin
                  changes#add (Cmoved(nd1, nd2));
                  self#set_used ed
                end
            | _ -> assert false
          );
        changes#get_list


      method make_changes_list : unit -> (string * significance * change_maker * change_to_triples) list =
        fun () -> [] (* should be overridden *)


      method infer_loc nd2 =
        let mem n =
          if edits#mem_mov2 n then
            false
          else
            nmapping#mem_cod n
        in
        let an2 = Sourcecode.find_nearest_mapped_ancestor_node mem nd2 in
        let a1 = nmapping#inv_find an2 in
        let unit = get_unit tree1 a1 in
        let al1 = a1#data#src_loc in
        let loc = al1 in
        unit, loc


      method change_to_change_info : change -> change_info = function
        | Cdeleted(is_whole, nd, _) ->
            get_desc1 is_whole tree1 nd,
            nd#data#anonymized_label,
            get_unit tree1 nd,
            nd#data#src_loc,
            "",
            Loc.dummy

        | Cinserted(is_whole, nd, _) ->
            let unit, loc = self#infer_loc nd in
            get_desc1 is_whole tree2 nd,
            nd#data#anonymized_label,
            unit,
            loc,
            get_unit tree2 nd,
            nd#data#src_loc

        | Cmodified(nd1, nd2) | Cchanged(_, nd1, nd2) | Crenamed(_, nd1, nd2) ->
            get_desc2 tree1 tree2 nd1 nd2,
            sprintf "%s -> %s" nd1#data#anonymized_label nd2#data#anonymized_label,
            get_unit tree1 nd1,
            nd1#data#src_loc,
            get_unit tree2 nd2,
            nd2#data#src_loc

        | Cmoved(nd1, nd2)     ->
            get_desc2 tree1 tree2 nd1 nd2,
            nd1#data#anonymized_label,
            get_unit tree1 nd1,
            nd1#data#src_loc,
            get_unit tree2 nd2,
            nd2#data#src_loc

        | Ccardinality_changed(nd1, nd2) ->
            get_desc2 tree1 tree2 nd1 nd2,
            nd1#data#anonymized_label,
            get_unit tree1 nd1,
            nd1#data#src_loc,
            get_unit tree2 nd2,
            nd2#data#src_loc


      method extract (*:
          (string * int * string list) list *
          EO.t list * (string * int * change_info list) list *
          Triple.t Xset.t *)
          =
        let triples = Xset.create 0 in
        let changes_list = self#make_changes_list() in

        let n_change_classes = List.length changes_list in
        let _ = n_change_classes in

        let res, _info, _ =
          List.fold_left
            (fun (chgs_a, info_a, count) (chg_ty, lv, chgsf, chg_to_tris) ->
              let u = score lv in
              let chgs = chgsf() in

              [%debug_log "[%d/%d][%s] %d changes" count n_change_classes chg_ty (List.length chgs)];

              if chgs = [] then
                (chgs_a, info_a, count + 1)
              else begin
                if options#fact_for_changes_flag then
                  List.iter
                    (fun chg ->
                      List.iter (Xset.add triples) (chg_to_tris chg)
                    ) chgs;
                (
                 (chg_ty, u, List.map change_to_string chgs)::chgs_a,
                 (chg_ty, u, List.map self#change_to_change_info chgs)::info_a,
                 count + 1
                )
              end
            ) ([], [], 1) changes_list
        in
        let info = List.rev _info in

        let unused = ref [] in
        edits#iter
          (fun ed ->
            if not (self#is_used ed) then
              unused := ed::!unused
          );

        res,
        !unused,
        info,
        triples

    end (* of class Change_base.F.c *)

end (* of functor Change_base.F *)
]
