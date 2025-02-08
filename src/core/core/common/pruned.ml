(*
   Copyright 2012-2024 Codinuum Software Lab <https://codinuum.com>

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
(* pruned.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module UID = Diffast_misc.UID
module GI = Diffast_misc.GIndex
module Otree = Diffast_misc.Otree


let sprintf = Printf.sprintf

let nups = Misc.nups

(*** pruned nodes ***)

type kind =
  | Isomorphic
  | Migratory (* relative move *)
  | Other

type gindex = GI.t

type 'node_t t =
    kind ref
      * (gindex (* leftmost *) * gindex) (* for old tree *)
      * (gindex (* leftmost *) * gindex) (* for new tree *)
      * ('node_t Info.t) (* for old tree *)
      * ('node_t Info.t) (* for new tree *)

let kind_to_string = function
  | Isomorphic -> "ISOMORPHIC"
  | Migratory  -> "MIGRATORY"
  | Other      -> "OTHER"

let to_string (kind, (lgi1, gi1), (lgi2, gi2), info1, info2) =
  let n1 = Info.get_node info1 in
  let n2 = Info.get_node info2 in
  let s = kind_to_string !kind in
  sprintf "[PRUNED(%s)]: (%a:%d-%d)%s -> (%a:%d-%d)%s" s
    nups n1 lgi1 gi1 (Info.to_string info1)
    nups n2 lgi2 gi2 (Info.to_string info2)

let to_string_short (_, (lgi1, gi1), _, info1, info2) =
  let n1 = Info.get_node info1 in
  let n2 = Info.get_node info2 in
  sprintf "<%a-%a(%d)>" nups n1 nups n2 (gi1 - lgi1 + 1)

let is_single (_, (lgi1, gi1), _, _, _) = lgi1 = gi1

let make_isomorphic lgi_gi1 lgi_gi2 info1 info2 =
  (ref Isomorphic, lgi_gi1, lgi_gi2, info1, info2)

let make_migratory lgi_gi1 lgi_gi2 info1 info2 =
  (ref Migratory, lgi_gi1, lgi_gi2, info1, info2)

let make_other lgi_gi1 lgi_gi2 info1 info2 =
  (ref Other, lgi_gi1, lgi_gi2, info1, info2)


[%%capture_path
class ['node_t, 'tree_t] nodes = object (self)
  val mutable list = ([] : 'node_t t list)

  method add_pruned pruned =
    [%debug_log "adding %s" (to_string_short pruned)];
    list <- list @ [pruned]


  method add_pruned_nodes pruned_nodes =
    [%debug_log "adding [%s]" (Xlist.to_string to_string_short "," pruned_nodes)];
    list <- list @ pruned_nodes

  val mutable aborted1 = ([] : 'node_t list)
  method add_aborted1 nd = aborted1 <- nd::aborted1
  method add_abortedl1 nds = aborted1 <- nds @ aborted1
  method aborted1 = aborted1

  val mutable aborted2 = ([] : 'node_t list)
  method add_aborted2 nd = aborted2 <- nd::aborted2
  method add_abortedl2 nds = aborted2 <- nds @ aborted2
  method aborted2 = aborted2

      (* iso which contains aborted deletes or inserts *)
  val mutable para_iso1 = ([] : 'node_t list)
  method add_para_iso1 nds = para_iso1 <- nds @ para_iso1
  method para_iso1 = para_iso1

  val mutable para_iso2 = ([] : 'node_t list)
  method add_para_iso2 nds = para_iso2 <- nds @ para_iso2
  method para_iso2 = para_iso2

  method iter f = List.iter f list
  method find p = List.find p list
  method exists p = List.exists p list

  method get_kind nd1 nd2 =
    let s, _, _, _, _ =
      self#find
        (fun (_, _, _, i1, i2) ->
          let n1 = Info.get_node i1 in
          let n2 = Info.get_node i2 in
          n1 == nd1 && n2 == nd2
        )
    in
    !s

  method set_kind nd1 nd2 kind =
    self#iter
      (fun (s, _, _, i1, i2) ->
        let n1 = Info.get_node i1 in
        let n2 = Info.get_node i2 in
        if n1 == nd1 && n2 = nd2 then s := kind)

(* does pruned subtree (old) contain node_data? *)
  method mem1 (tree1 : 'tree_t) (nd : 'node_t) =
    let _ = tree1 in
    [%debug_log "is_whole=%B" tree1#is_whole];
    self#exists
      (function
          (kind, (lgi, gi), _, info', _) ->
            let nd' = Info.get_node info' in
            match !kind with
            | Other -> nd' == nd
            | _ ->
                let b2 =
                  try
                    let gidx = nd#gindex in
                    lgi <= gidx && gidx <= gi
                  with Not_found -> false
                in
                b2
      )

(* does pruned subtree (new) contain node_data? *)
  method mem2 (tree2 : 'tree_t) (nd : 'node_t) =
    let _ = tree2 in
    [%debug_log "is_whole=%B" tree2#is_whole];
    self#exists
      (function
          (kind, _, (lgi, gi), _, info') ->
            let nd' = Info.get_node info' in
            match !kind with
            | Other -> nd' = nd
            | _ ->
                let b2 =
                  try
                    let gidx = nd#gindex in
                    lgi <= gidx && gidx <= gi
                  with Not_found -> false
                in
                b2
      )


  method to_string = sprintf
      "%d pruned node(s):\n%s" (List.length list)
      (Xlist.to_string
         (fun p -> sprintf "%s" (to_string p))
         "\n" list)

end (* of class Pruned.nodes *)
]
