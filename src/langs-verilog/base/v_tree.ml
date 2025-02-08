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
 * AST for Verilog HDL (for otreediff)
 *
 * verilog/tree.ml
 *
 *)

module Sourcecode = Diffast_core.Sourcecode
module Fname = Langs_common.Fname
module Astloc = Langs_common.Astloc
module Printer = Verilog_parsing.Printer

module P = Printer
module L = V_label

let sprintf = Printf.sprintf

let conv_loc = L.conv_loc

let set_loc nd loc = nd#data#set_loc (conv_loc loc)

module Tree = Sourcecode.Tree (L)
open Tree

let of_ast options ast =

  let rec convl astnd_list =

    let _, _children =
      List.fold_left
        (fun (is_included, l) an ->

          let children_are_included =
            List.for_all (fun c -> c#lloc#get_level > 0) an#children
          in
          if an#lloc#get_level > 0 && children_are_included then begin
            if is_included then begin
              (is_included, l)
            end
            else begin
              let f = Fname.strip (an#lloc#get_loc_of_level 1).Astloc.filename in
              let lab = L.CompilerDirective (L.CompilerDirective.Include ("\""^f^"\"")) in
              let nd = mkleaf options lab in
              set_loc nd (an#lloc#get_loc_of_level 0);
              (true, nd::l)
            end
          end
          else begin
            (false, (conv an)::l)
          end
        ) (false, []) astnd_list
    in
    List.rev _children

  and conv astnd =
    let lab = astnd#label in
    let children = convl astnd#children in
    let nd = mknode options lab children in
    set_loc nd astnd#loc;
    nd
  in
  let root_node =
    match convl [ast#root] with
    | [nd] -> nd
    | _ -> assert false
  in
  let tree = new c options root_node true in
  tree#collapse;
  tree#set_total_LOC ast#lines_read;
  tree#set_ignored_regions (ast#comment_regions @ ast#ignored_regions);
  tree#set_misparsed_regions ast#missed_regions;
  tree
