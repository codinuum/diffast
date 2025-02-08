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
(* astml/change.ml *)

module Change_base = Diffast_core.Change_base
module Triple = Diffast_core.Triple
module Label = Astml_base.Label

module CCX (L : Label.T) = struct

  (*let sprintf = Printf.sprintf*)

  include Change_base

  module CB = F(L)


  let getlab nd = (Obj.obj nd#data#_label : L.t)

  let is_named nd = L.is_named (getlab nd)

  let is_decl nd    = L.CCX.is_decl (getlab nd)
  let is_fun_def nd = L.CCX.is_fun_def (getlab nd)
  let is_stmt nd    = L.CCX.is_stmt (getlab nd)
  let is_if_stmt nd = L.CCX.is_if_stmt (getlab nd)


(* *)

  let get_unit tree nd =
    try
      let u = tree#get_nearest_containing_unit nd in
      u#data#label
    with
      Not_found -> ""


  let ids_to_str ids =
    if ids = [] then "" else sprintf "{%s}" (String.concat "," ids)

  let subtree_to_str tree nd =
    sprintf "[%s]" (tree#subtree_to_simple_string nd#gindex)

  let get_desc1 (*is_whole*)_ tree nd =
    let ids = tree#get_ident_use_list nd#gindex in
    let extra2 =
      if (* is_whole *) true then
	subtree_to_str tree nd
      else
	""
    in
    nd#data#label^(ids_to_str ids)^extra2

  let get_desc2 tree1 tree2 nd1 nd2 =
    let ids1 = tree1#get_ident_use_list nd1#gindex in
    let ids2 = tree2#get_ident_use_list nd2#gindex in
    sprintf "%s%s%s -> %s%s%s"
      nd1#data#label (ids_to_str ids1) (subtree_to_str tree1 nd1)
      nd2#data#label (ids_to_str ids2) (subtree_to_str tree2 nd2)


  class c options tree1 tree2 uidmapping edits get_unit get_desc1 get_desc2 = object(self)
    inherit CB.c options tree1 tree2 uidmapping edits get_unit get_desc1 get_desc2

    method! make_changes_list () =
      let mkt_del = self#mkt_deleted ~category:Triple.ghost in
      let mkt_ins = self#mkt_inserted ~category:Triple.ghost in
      (*let mkt_mod = self#mkt_modified ~category:Triple.ghost in*)
      let mkt_chgto = self#mkt_changed_to ~category:Triple.ghost in
      let mkt_ren = self#mkt_renamed ~category:Triple.ghost in
      let mkt_mov = self#mkt_moved_to ~category:Triple.ghost in
      let mkt_odrchg = self#mkt_order_changed ~category:Triple.ghost in
(*      let mkt_chgcard _ = [] in *)
      [
(* others *)
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

 end (* of class Astml.Change.CCX.c *)


let extract options tree1 tree2 uidmapping edits =
  let chg = new c options tree1 tree2 uidmapping edits get_unit get_desc1 get_desc2 in
  let res = chg#extract in
  chg#recover_edits;
  res


end (* of functor Astml.Change.CCX *)
