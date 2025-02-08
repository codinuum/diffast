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
 * AST for SystemVerilog (IEEE-1800-2009)
 *
 * ast.ml
 *
 *)

[%%prepare_logger]

module Layeredloc = Langs_common.Layeredloc
module Astloc = Langs_common.Astloc
module Ast_base = Langs_common.Ast_base


open Printf

module Loc = Astloc
module LLoc = Layeredloc
module L = Label

class node
    ?(lloc=LLoc.dummy)
    ?(children=[])
    lab
    =
  object (_ : 'self)
    val mutable lloc = lloc
    val mutable label = (lab : L.t)
    val mutable children = (children : 'self list)

    method label = label
    method lloc = lloc
    method loc = lloc#get_loc
    method orig_loc = lloc#get_orig_loc
    method children = children

    method children_labels =
      List.map (fun n -> n, n#label) children

    method nchildren = List.length children

    method set_lloc l = lloc <- l
    method set_children c = children <- c

    method relab lab = label <- lab

    method add_children_l c = children <- c @ children

    method add_children_r c = children <- children @ c

    method remove_rightmost_child =
      match children with
      | [] -> ()
      | [_] -> children <- []
      | _ ->
          match (List.rev children) with
          | _ :: t -> children <- (List.rev t)
          | _ -> assert false

    method remove_leftmost_child =
      match (List.rev children) with
      | [] -> ()
      | [_] -> children <- []
      | _ :: t -> children <- t

    method to_string =
      sprintf "<%s>%s"
        (L.to_string label)
        (lloc#to_string ?short:(Some true) ())

    method to_tag = L.to_tag label

    method get_identifier = L.get_identifier label

    method get_identifiers = L.get_identifiers label

    method pexpr_to_stmt = label <- L.pexpr_to_stmt label

    method expr_to_stmt = label <- L.expr_to_stmt label


end (* of class Ast.node *)


let get_scope_of_pkg_ctys pkg_ctys =
  let id_of_pkg_scope_id nd =
    nd#get_identifier
  in
  let ids_of_class_type_list xs =
    List.map (fun (_, nd) -> nd#get_identifier) xs
  in
  match List.map (fun nd -> nd#label, nd) pkg_ctys with
  | ((L.PackageScope _), pkg_scoped_id)::class_type_list ->
      (Some (id_of_pkg_scope_id pkg_scoped_id)), (ids_of_class_type_list class_type_list)

  | (L.PackageScopeUnit, _)::class_type_list
  | (L.PackageScopeLocal, _)::class_type_list ->
      None, (ids_of_class_type_list class_type_list)

  | class_type_list ->
      None, (ids_of_class_type_list class_type_list)


[%%capture_path
let get_scope_of_func_id node = (* returns pkg_id option * class_id list *)

  [%debug_log "\"%s\"" (L.to_string node#label)];

  match node#label with
  | L.FuncId _ | L.FuncIdVoid _ -> begin
      let l = List.rev node#children in
      match List.map (fun nd -> nd#label, nd) l with
      | ((L.TfIdScoped _), _)::_ ->
          None, []

      | ((L.ClassScopeId _), nd)::_ ->
          get_scope_of_pkg_ctys nd#children

      | _ -> None, []
  end
  | L.FuncIdNew -> get_scope_of_pkg_ctys node#children

  | _ -> None, []
]

let dummy_node = new node L.Dummy

let empty_node = new node L.Empty

let lloc_of_locs loc0 loc1 =
  let lloc0 = LLoc.of_loc loc0 in
  let lloc1 = LLoc.of_loc loc1 in
  LLoc.merge lloc0 lloc1

let lloc_of_lexposs pos0 pos1 =
  let loc0 = Loc.of_lexpos pos0 in
  let loc1 = Loc.of_lexpos pos1 in
  lloc_of_locs loc0 loc1

[%%capture_path
let mknode start_pos end_pos label children =
  [%debug_log "label=%s %s-%s"
    (L.to_string label) (Loc.lexpos_to_string start_pos) (Loc.lexpos_to_string end_pos)];
  let lloc = lloc_of_lexposs start_pos end_pos in
  new node ~lloc ~children label
]

let mkleaf start_pos end_pos label =
  mknode start_pos end_pos label []

[%%capture_path
let reloc start_pos end_pos node =
  let lloc = lloc_of_lexposs start_pos end_pos in
  [%debug_log "relocating %s: %s -> %s"
    (L.to_string node#label)
    (node#lloc#to_string ?short:(Some true) ()) (lloc#to_string ?short:(Some true) ())];
  node#set_lloc lloc
]

type partial =
  | Pdescription_list      of node list
  | Pmodule_item_list      of node list
  | Pgenerate_item_list    of node list
  | Pblock_decl_stmt_list  of node list
  | Pcase_item_list        of node list
  | Pcase_inside_item_list of node list
  | Pcellpin_list          of node list
  | Plist_of_ports         of node list
  | Pexpr                  of node

let nodes_of_partial = function
  | Pdescription_list      nds
  | Pmodule_item_list      nds
  | Pgenerate_item_list    nds
  | Pblock_decl_stmt_list  nds
  | Pcase_item_list        nds
  | Pcase_inside_item_list nds
  | Pcellpin_list          nds
  | Plist_of_ports         nds
    -> nds
  | Pexpr nd
    -> [nd]

let is_block_item_declaration node =
  match node#label with
  | L.DataDeclarationVar
  | L.TypeDeclaration _
  | L.PackageImportDeclaration
  | L.LocalParameterDeclaration _
  | L.ParameterDeclaration _
  | L.OverloadDeclaration _
  | L.LetDeclaration _ -> true
  | _ -> false

let is_stmt node =
  match node#label with
  | L.Stmt _ -> true
  | _ -> false

let get_last_id node_list =
  match List.rev node_list with
  | last::_ -> begin
      try
        last#get_identifier
      with Not_found -> ""
  end
  | _ -> ""

let get_unquoted quoted =
  try
    String.sub quoted 1 ((String.length quoted) - 2)
  with
    e ->
      let _ = e in
      [%warn_log "%s" (Printexc.to_string e)];
      quoted

let rec visit f node = (* preorder traversal *)
  f node;
  List.iter (visit f) node#children

let size node =
  let sz = ref 0 in
  visit (fun _ -> incr sz) node;
  !sz


class c root = object (self)
  inherit Ast_base.c

  method root = root

  method visit (f : node -> unit) = visit f root

  method size =
    let sz = ref 0 in
    self#visit (fun _ -> incr sz);
    !sz

end (* of class Ast.c *)


(* end of Ast *)
