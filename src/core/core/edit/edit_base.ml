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
(* edit_base.ml *)

[%%prepare_logger]

module Loc = Diffast_misc.Loc

open Stat.File

module Xlist = Diffast_misc.Xlist
module Xset = Diffast_misc.Xset
module Xhash = Diffast_misc.Xhash
module Xfile = Diffast_misc.Xfile
module Xprint = Diffast_misc.Xprint
module Xchannel = Diffast_misc.Xchannel
module Compression = Diffast_misc.Compression
module GI  = Diffast_misc.GIndex
module Otree = Diffast_misc.Otree
module Json = Node_mapping.Json
module Nodetbl = Node.Tbl

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf

let del_bg = "#B8E3B1"
let del_fg = "#000000"
let ins_bg = "#B2CDF9"
let ins_fg = "#000000"
let mov_bg = "#E6DFCF"
let mov_fg = "#000000"
let rel_bg = "#FFC0A9"
let rel_fg = "#000000"
let movrel_bg = "#FFDFCF"
let movrel_fg = "#000000"

type line_match =
  | LM_single of (int * int)      (* (l1, l2) *)
  | LM_multi of (int * int * int) (* (l1, l2, ext) *)

let get_label nd =
  let lab = nd#data#label in
  if nd#data#is_named then
    lab
  else
    let extra =
      Array.fold_left
        (fun labs cnd ->
          if cnd#data#is_named then cnd#data#label :: labs
          else labs
        ) [] nd#children
    in
    if extra = [] then lab
    else lab^"<"^(String.concat ";" extra)^">"

let _same_digest = Comparison._same_digest

let tbl_add tbl key v =
  try
    let l = Hashtbl.find tbl key in
    Hashtbl.replace tbl key (v::l)
  with
    Not_found -> Hashtbl.add tbl key [v]

let tbl_add_s tbl key v =
  let s =
    try
      Hashtbl.find tbl key
    with
      Not_found ->
        let s = Xset.create 0 in
        Hashtbl.add tbl key s;
        s
  in
  Xset.add s v


(* segments *)

type segment = int * int

let sort_segments (segs : segment list) =
  List.fast_sort (fun (s1, _) (s2, _) -> compare s1 s2) segs

let segments_to_string : segment list -> string =
  Xlist.to_string (fun (s, e) -> sprintf "%d %d" s e) " "

[%%capture_path
let merge_segments segs_list =

  begin %debug_block
    [%debug_log "segs list"];
    List.iter (Printf.printf "\t%s\n") (List.map segments_to_string segs_list)
  end;

  let all_segs = List.concat segs_list in
  let phantoms, normals = List.partition (fun (s, e) -> s > e) all_segs in

  let extra =
    List.fold_left
      (fun l (e, s) ->
        if List.mem (s, e) normals then
          l
        else
          (s, s)::l
      ) [] phantoms
  in

  begin %debug_block
    [%debug_log "normals: %s" (segments_to_string normals)];
    [%debug_log "phantoms: %s" (segments_to_string phantoms)];
    [%debug_log "extra: %s" (segments_to_string extra)]
  end;

  let sorted = sort_segments (normals @ extra) in

  let l, last =
    List.fold_left
      (fun (a, cand) (s, e) ->
        match cand with
        | None -> a, Some (s, e)
        | Some (s0, e0) ->
            if s = e0 + 1 then
              a, Some (s0, e)

            else if s > e0 + 1 then
              (s0, e0)::a, Some (s, e)

            else if s0 <= s && e <= e0 then
                a, Some (s0, e0)

            else if s0 <= s && s <= e0 && e > e0 then begin
              [%warn_log "overlap: cand=(%d,%d) elem=(%d,%d)" s0 e0 s e];
              a, Some (s0, e)
            end

            else begin
              [%fatal_log "cand=(%d,%d) elem=(%d,%d)" s0 e0 s e];
              exit 1
            end

      ) ([], None) sorted
  in
  let res =
    match last with
    | None -> List.rev l
    | Some c -> List.rev (c::l)
  in

  [%debug_log "result: %s" (segments_to_string res)];

  res
]

(* edit operations *)
include Editop

let ups = Misc.ups
let nps = Misc.nps
let gps = Misc.gps
let nups = Misc.nups
let ngps = Misc.ngps
let nugps = Misc.nugps
let usps = Misc.usps
let nsps = Misc.nsps
let naps = Misc.naps
let locps = Misc.locps
let labps = Misc.labps

let get_stmt n = Misc.get_p_ancestor (fun x -> x#data#is_statement) n
let get_bn n = Misc.get_p_ancestor (fun x -> x#data#is_boundary) n

let boundary_stable = Comparison.boundary_stable

let get_mid = function
  | Move(mid, _, _, _) -> !mid
  | _ -> assert false

let add tbl n e =
  try
    let e' = Nodetbl.find tbl n in
    if e <> e' then
      [%warn_log "already have %a -> %s (not added: %s)" nups n
        (to_string e') (to_string e)]
  with
    Not_found -> Nodetbl.add tbl n e

let add2 tbl1 tbl2 n1 n2 e =
  let is_ok tbl n =
    try
      let e' = Nodetbl.find tbl n in
      let a =
        if e <> e' then
          "conflicting "
        else
          ""
      in
      let _ = a in
      [%warn_log "already have %s%a -> %s (not added: %s)" a nups n
        (to_string e') (to_string e)];
      false
    with
      Not_found -> true
  in
  let ok1 = is_ok tbl1 n1 in
  let ok2 = is_ok tbl2 n2 in

  if ok1 && ok2 then begin
    Nodetbl.add tbl1 n1 e;
    Nodetbl.add tbl2 n2 e
  end


let gid_of_edit1 = function
  | Delete(_, info, _)
  | Relabel(_, (info, _), _)
  | Move(_, _, (info, _), _) -> Info.get_gid info
  | Insert(_, _, _) -> raise Not_found

let gid_of_edit2 = function
  | Insert(_, info, _)
  | Relabel(_, _, (info, _))
  | Move(_, _, _, (info, _)) -> Info.get_gid info
  | Delete(_, _, _) -> raise Not_found


let comp_edits_topdown gid_of_edit ed1 ed2 =
  let c =
    try
      let gi1, gi2 = gid_of_edit ed1, gid_of_edit ed2 in
      Stdlib.compare gi2 gi1
    with
      Not_found -> 0
  in
  let c' =
    if c = 0 then
      match ed1, ed2 with
      | Move _, Relabel _ -> -1
      | Relabel _, Move _ -> 1
      | _ -> 0
    else
      c
  in
  (* [%debug_log "%s vs %s --> %d" (to_string ed1) (to_string ed2) c']; *)
  c'

let _sort_edit_list_topdown gid_of_edit = List.fast_sort (comp_edits_topdown gid_of_edit)

let sort_edit_list_topdown l =
  let l' = _sort_edit_list_topdown gid_of_edit1 l in
  let l'' = _sort_edit_list_topdown gid_of_edit2 l' in
  l''

let comp_edits_bottomup (*gid_of_edit*)_ ed1 ed2 =
  let c =
    try
      let gi1, gi2 = gid_of_edit1 ed1, gid_of_edit1 ed2 in
      Stdlib.compare gi1 gi2
    with
      Not_found -> 0
  in
  if c = 0 then
    match ed1, ed2 with
    | Relabel _, Move _ -> -1
    | Move _, Relabel _ -> 1
    | _ -> 0
  else
    c

let _sort_edit_list_bottomup gid_of_edit = List.fast_sort (comp_edits_bottomup gid_of_edit)

let sort_edit_list_bottomup l =
  let l' = _sort_edit_list_bottomup gid_of_edit1 l in
  let l'' = _sort_edit_list_bottomup gid_of_edit2 l' in
  l''

let sort_mids_movs mov_compare movl =
  let tbl0 = Hashtbl.create 0 in
  List.iter
    (function
      | Move(mid, _, _, _) as mov -> begin
          tbl_add tbl0 !mid mov
      end
      | _ -> ()
    ) movl;
  let tbl = Hashtbl.create 0 in
  let midl = ref [] in
  Hashtbl.iter
    (fun mid mvl ->
      Hashtbl.add tbl mid (List.fast_sort mov_compare mvl);
      midl := mid :: !midl
    ) tbl0;
  let mid_compare mid0 mid1 =
    let m0 = List.hd (Hashtbl.find tbl mid0) in
    let m1 = List.hd (Hashtbl.find tbl mid1) in
    mov_compare m0 m1
  in
  let sorted_midl = List.fast_sort mid_compare !midl in
  List.concat_map (Hashtbl.find tbl) sorted_midl

let sort_move_list_topdown movl = sort_mids_movs (comp_edits_topdown gid_of_edit1) movl
let sort_move_list_bottomup movl = sort_mids_movs (comp_edits_bottomup gid_of_edit1) movl

let tbl_remove tbl k =
  (*while Hashtbl.mem tbl k do*)
    Nodetbl.remove tbl k
  (*done*)

(* base class for edit sequences *)

exception Found
exception Abort

let is_ghost_node nd = nd#data#src_loc == Loc.ghost

class formatters_base
    ~delete ~insert ~relabel ~move ~align
    ~ignored1 ~ignored2
    ~misparsed1 ~misparsed2
    =
  object
    method delete  = (delete : int -> int -> segment list -> string)
    method insert  = (insert : int -> int -> segment list -> string)
    method relabel = (relabel : bool -> int -> int -> segment list -> int -> int -> segment list -> string)
    method move    = (move : int -> int -> segment list -> int -> int -> segment list -> string)
    method align   = (align : line_match -> string)
    method ignored1   = (ignored1 : segment -> string)
    method ignored2   = (ignored2 : segment -> string)
    method misparsed1 = (misparsed1 : segment -> string)
    method misparsed2 = (misparsed2 : segment -> string)
  end


type move_region_tbl_t = (MID.t, (GI.t*GI.t*GI.t*GI.t)) Hashtbl.t


[%%capture_path
class ['node_t, 'tree_t] seq_base options = object (self : 'edits)

  val mutable del_tbl  = Nodetbl.create 0
  val mutable ins_tbl  = Nodetbl.create 0
  val mutable rel1_tbl = Nodetbl.create 0
  val mutable rel2_tbl = Nodetbl.create 0
  val mutable mov1_tbl = Nodetbl.create 0
  val mutable mov2_tbl = Nodetbl.create 0

  val mutable tables = []

  val mutable mov_gr_tbl = Hashtbl.create 0 (* move id -> group id *)
  val mutable mov_gr_mem_tbl = Hashtbl.create 0 (* move id -> move list *)

  val mutable list = ([] : ('node_t t) list)

  val mutable indivisible_moves = (Xset.create 0 : MID.t Xset.t)

  method _init =
      tables <- [del_tbl; ins_tbl; rel1_tbl; rel2_tbl; mov1_tbl; mov2_tbl]

  initializer
    self#_init

  method _indivisible_moves = indivisible_moves
  method _set_indivisible_moves s = indivisible_moves <- s

  method _set_mov_gr_tbl tbl = mov_gr_tbl <- tbl
  method _set_mov_gr_mem_tbl tbl = mov_gr_mem_tbl <- tbl

  method add_indivisible_move mid =
    [%debug_log "%a" MID.ps mid];
    Xset.add indivisible_moves mid

  method remove_indivisible_move mid =
    [%debug_log "%a" MID.ps mid];
    Xset.remove indivisible_moves mid

  method is_indivisible_move mid =
    let b = Xset.mem indivisible_moves mid in
    [%debug_log "%a -> %B" MID.ps mid b];
    b

  method _mov_gr_tbl = mov_gr_tbl
  method _mov_gr_mem_tbl = mov_gr_mem_tbl

  method find_mov_gr = Hashtbl.find mov_gr_tbl
  method find_mov_gr_mems = Hashtbl.find mov_gr_mem_tbl

  method _del_tbl  = del_tbl
  method _ins_tbl  = ins_tbl
  method _rel1_tbl = rel1_tbl
  method _rel2_tbl = rel2_tbl
  method _mov1_tbl = mov1_tbl
  method _mov2_tbl = mov2_tbl

  method content = list

  method _set_del_tbl tbl  = del_tbl <- tbl
  method _set_ins_tbl tbl  = ins_tbl <- tbl
  method _set_rel1_tbl tbl = rel1_tbl <- tbl
  method _set_rel2_tbl tbl = rel2_tbl <- tbl
  method _set_mov1_tbl tbl = mov1_tbl <- tbl
  method _set_mov2_tbl tbl = mov2_tbl <- tbl

  method copy =
    let eds = new seq_base options in
    eds#_set_del_tbl (Nodetbl.copy self#_del_tbl);
    eds#_set_ins_tbl (Nodetbl.copy self#_ins_tbl);
    eds#_set_rel1_tbl (Nodetbl.copy self#_rel1_tbl);
    eds#_set_rel2_tbl (Nodetbl.copy self#_rel2_tbl);
    eds#_set_mov1_tbl (Nodetbl.copy self#_mov1_tbl);
    eds#_set_mov2_tbl (Nodetbl.copy self#_mov2_tbl);
    eds#_set_indivisible_moves (Xset.copy self#_indivisible_moves);
    eds#_set_mov_gr_tbl (Hashtbl.copy self#_mov_gr_tbl);
    eds#_set_mov_gr_mem_tbl (Hashtbl.copy self#_mov_gr_mem_tbl);
    eds#_init;
    eds

  method private edit_tbl_to_list tbl =
    Nodetbl.fold (fun _ e l -> e::l) tbl []

  method clear =
    [%debug_log "@"];
    list <- [];
    Nodetbl.clear del_tbl;
    Nodetbl.clear ins_tbl;
    Nodetbl.clear rel1_tbl;
    Nodetbl.clear rel2_tbl;
    Nodetbl.clear mov1_tbl;
    Nodetbl.clear mov2_tbl;
    Hashtbl.clear mov_gr_tbl;
    Hashtbl.clear mov_gr_mem_tbl;


  method is_consistent_with ed =
    let result =
      match ed with
      | Delete(w, i, _) ->
          let n = Info.get_node i in
          let eds = self#find1 n in
          begin
            match eds with
            | [] -> true
            | [Delete(w', i', _) as ed'] -> begin
                let n' = Info.get_node i' in
                let _ = ed' in
                let b = w = w' && n == n' in
                begin %debug_block
                  if b then
                    [%debug_log "duplication: %s" (to_string ed)]
                  else
                    [%debug_log "%s conflicts %s" (to_string ed) (to_string ed')]
                end;
                b
            end
            | [ed'; ed''] -> begin
                let _ = ed' in
                let _ = ed'' in
                [%debug_log "%s conflicts %s and %s" (to_string ed) (to_string ed') (to_string ed'')];
                false
            end
            | _ -> begin
                List.iter
                  (fun ed' ->
                    let _ = ed' in
                    [%debug_log "%s conflicts with %s" (to_string ed) (to_string ed')]
                  ) eds;
                assert false
            end
          end

      | Insert(w, i, _)  ->
          let n = Info.get_node i in
          let eds = self#find2 n in
          begin
            match eds with
            | [] -> true
            | [Insert(w', i', _) as ed'] -> begin
                let n' = Info.get_node i' in
                let _ = ed' in
                let b = w = w' && n == n' in
                begin %debug_block
                  if b then
                    [%debug_log "duplication: %s" (to_string ed)]
                  else
                    [%debug_log "%s conflicts %s" (to_string ed) (to_string ed')]
                end;
                b
            end
            | [ed';ed''] -> begin
                let _ = ed' in
                let _ = ed'' in
                [%debug_log "%s conflicts %s and %s" (to_string ed) (to_string ed') (to_string ed'')];
                false
            end
            | _ -> begin
                List.iter
                  (fun ed' ->
                    let _ = ed' in
                    [%debug_log "%s conflicts with %s" (to_string ed) (to_string ed')]
                  ) eds;
                assert false
            end
          end

      | Relabel(_, (i1, _), (i2, _)) ->
          let n1 = Info.get_node i1 in
          let n2 = Info.get_node i2 in
          let eds = self#find12 n1 n2 in
          begin
            match eds with
            | [] -> true
            | [Move(_, _, (i1', _), (i2', _)) as ed'] -> begin
                let n1' = Info.get_node i1' in
                let n2' = Info.get_node i2' in
                let _ = ed' in
                let b = n1 == n1' && n2 == n2' in
                begin %debug_block
                  if not b then
                    [%debug_log "%s conflicts %s" (to_string ed) (to_string ed')]
                end;
                b
            end
            | [ed'] -> begin
                let b = ed = ed' in
                begin %debug_block
                  if b then
                    [%debug_log "duplication: %s" (to_string ed)]
                  else
                    [%debug_log "%s conflicts %s" (to_string ed) (to_string ed')]
                end;
                b
            end
            | [ed';ed''] -> begin
                let _ = ed' in
                let _ = ed'' in
                [%debug_log "%s conflicts %s and %s" (to_string ed) (to_string ed') (to_string ed'')];
                false
            end
            | _ -> begin
                List.iter
                  (fun ed' ->
                    let _ = ed' in
                    [%debug_log "%s conflicts with %s" (to_string ed) (to_string ed')]
                  ) eds;
                assert false
            end
          end

      | Move(m, k, (i1, x), (i2, y)) ->
          let n1 = Info.get_node i1 in
          let n2 = Info.get_node i2 in
          let eds = self#find12 n1 n2 in
          begin
            match eds with
            | [] -> true
            | [Relabel(_, (i1', _), (i2', _)) as ed'] -> begin
                let n1' = Info.get_node i1' in
                let n2' = Info.get_node i2' in
                let _ = ed' in
                let b = n1 == n1' && n2 == n2' in
                begin %debug_block
                  if not b then
                    [%debug_log "%s conflicts %s" (to_string ed) (to_string ed')]
                end;
                b
            end
            | [Move(m', k', (i1', x'), (i2', y')) as ed'] -> begin
                let n1' = Info.get_node i1' in
                let n2' = Info.get_node i2' in
                let _ = ed' in
                let b =
                  n1 == n1' && n2 == n2' && !m = !m' && !k = !k' &&
                  (!x = !x' || !x' = []) && (!y = !y' || !y' = [])
                in
                begin %debug_block
                  if b then
                    [%debug_log "duplication: %s" (to_string ed)]
                  else
                    [%debug_log "%s conflicts %s" (to_string ed) (to_string ed')]
                end;
                b
            end
            | [ed';ed''] when ed = ed' || ed = ed'' -> begin
                [%debug_log "duplication: %s" (to_string ed)];
                true
            end
            | [ed';ed''] -> begin
                let _ = ed' in
                let _ = ed'' in
                [%debug_log "%s conflicts %s and %s" (to_string ed) (to_string ed') (to_string ed'')];
                false
            end
            | _ -> begin
                List.iter
                  (fun ed' ->
                    let _ = ed' in
                    [%debug_log "%s conflicts with %s" (to_string ed) (to_string ed')]
                  ) eds;
                assert false
            end
          end
    in
    result
 (* end of method is_consistent_with *)

  method add_edit edit =

    begin %debug_block
      [%debug_log "%s" (to_string edit)];
      assert (self#is_consistent_with edit)
    end;

    match edit with
    | Delete(_, info, _) -> add del_tbl (Info.get_node info) edit
    | Insert(_, info, _) -> add ins_tbl (Info.get_node info) edit
    | Relabel(_, (info1, _), (info2, _)) -> begin
        let nd1 = Info.get_node info1 in
        let nd2 = Info.get_node info2 in
        add2 rel1_tbl rel2_tbl nd1 nd2 edit
    end
    | Move(_, _, (info1, _), (info2, _)) -> begin
        let nd1 = Info.get_node info1 in
        let nd2 = Info.get_node info2 in
        add2 mov1_tbl mov2_tbl nd1 nd2 edit;
        begin
          try
            match self#find_rel12 nd1 nd2 with
            | Relabel(movrel, _, _) -> movrel := true
            | _ -> assert false
          with
            Not_found -> ()
        end
    end



  method add_edits (edits : 'edits) =
(*
    begin %debug_block
      [%debug_log "%d edit(s)" edits#get_nedits];
      edits#sync;
      List.iter
        (fun ed ->
          [%debug_log "adding: %s" (to_string ed)];
          assert (self#is_consistent_with ed)
        ) edits#content
    end;
*)
    edits#iter self#add_edit



  method remove_edit ed =

    [%debug_log "%s" (to_string ed)];

    match ed with
    | Delete(_, i, _) -> (*Hashtbl.remove*)tbl_remove del_tbl (Info.get_node i)
    | Insert(_, i, _) -> (*Hashtbl.remove*)tbl_remove ins_tbl (Info.get_node i)
    | Relabel(_, (i1, _), (i2, _)) ->
        (*Hashtbl.remove*)tbl_remove rel1_tbl (Info.get_node i1);
        (*Hashtbl.remove*)tbl_remove rel2_tbl (Info.get_node i2)
    | Move(_, _, (i1, _), (i2, _)) -> begin
        let n1 = Info.get_node i1 in
        let n2 = Info.get_node i2 in
        (*Hashtbl.remove*)tbl_remove mov1_tbl n1;
        (*Hashtbl.remove*)tbl_remove mov2_tbl n2;
        begin
          try
            match self#find_rel12 n1 n2 with
            | Relabel(movrel, _, _) -> movrel := false
            | _ -> assert false
          with
            Not_found -> ()
        end
    end


  method remove_del nd =
    [%debug_log "%a" nups nd];
    Nodetbl.remove del_tbl nd

  method remove_ins nd =
    [%debug_log "%a" nups nd];
    Nodetbl.remove ins_tbl nd

  method is_empty = self#get_nedits = 0

  method iter f = (* unordered *)
    List.iter
      (fun tbl ->
        Nodetbl.iter (fun _ ed -> f ed) tbl
      ) [mov1_tbl; rel1_tbl; del_tbl; ins_tbl]

  method iter_deletes_and_inserts f = (* unordered *)
    List.iter
      (fun tbl ->
        Nodetbl.iter (fun _ ed -> f ed) tbl
      ) [del_tbl; ins_tbl]

  method iter_deletes f =
    Nodetbl.iter (fun _ ed -> f ed) del_tbl

  method iter_inserts f =
    Nodetbl.iter (fun _ ed -> f ed) ins_tbl

  method iter_moves f =
    Nodetbl.iter (fun _ ed -> f ed) mov1_tbl

  method iter_moves_topdown f =
    let movs = self#edit_tbl_to_list mov1_tbl in
    List.iter f (sort_move_list_topdown movs)

  method iter_moves_bottomup f =
    let movs = self#edit_tbl_to_list mov1_tbl in
    List.iter f (sort_move_list_bottomup movs)

  method iter_relabels f =
    Nodetbl.iter (fun _ ed -> f ed) rel1_tbl

  method relabel_exists f =
    try
      Nodetbl.iter
        (fun _ ed ->
          if f ed then
            raise Exit
        ) rel1_tbl;
      false
    with
      Exit -> true

  method get_ndeletes =
    Nodetbl.length del_tbl

  method get_ninserts =
    Nodetbl.length ins_tbl

  method get_nmoves =
    let n1 = Nodetbl.length mov1_tbl in
    let n2 = Nodetbl.length mov2_tbl in
    assert (n1 = n2);
    n1

  method get_nmoves_of_move_id_filt filt move_id =
    let count = ref 0 in
    self#iter_moves
      (function
        | Move(mid, _, (inf1, _), (inf2, _)) ->
            if !mid = move_id then
              let n1 = Info.get_node inf1 in
              let n2 = Info.get_node inf2 in
              if filt n1 n2 then
                incr count
        | _ -> assert false
      );
    !count

  method get_nmoves_of_move_id move_id =
    let count = ref 0 in
    self#iter_moves
      (function
        | Move(mid, _, _, _) ->
            if !mid = move_id then
              incr count
        | _ -> assert false
      );
    !count

  method get_nmove_groups = (* count distinct mids *)
    let tbl = Hashtbl.create 0 in
    self#iter_moves
      (function
        | Move(mid, _, _, _) ->
            if not (Hashtbl.mem tbl !mid) then
              Hashtbl.add tbl !mid true
        | _ -> assert false
      );
    Hashtbl.length tbl

  method get_nrelabels =
    let n1 = Nodetbl.length rel1_tbl in
    let n2 = Nodetbl.length rel2_tbl in
(*
    if n1 <> n2 then begin
      [%debug_log "size of rel1_tbl: %d" n1];
      [%debug_log "size of rel2_tbl: %d" n2];

      let eds1 = ref [] in
      let eds2 = ref [] in

      Hashtbl.iter (fun nd ed -> eds1 := ed::!eds1) rel1_tbl;
      Hashtbl.iter (fun nd ed -> eds2 := ed::!eds2) rel2_tbl;

      let isect = Xlist.intersection !eds1 !eds2 in

      [%debug_log "edits only in rel1_tbl:"];
      List.iter (fun e -> [%debug_log "%s" (to_string e)]) (Xlist.subtract !eds1 isect);
      [%debug_log "edits only in rel2_tbl:";
      List.iter (fun e -> [%debug_log "%s" (to_string e)]) (Xlist.subtract !eds2 isect)
    end;
*)
    assert (n1 = n2);
    n1

  method get_nedits =
    let ndel = self#get_ndeletes in
    let nins = self#get_ninserts in
    let nrel = self#get_nrelabels in
    let nmov = self#get_nmoves in
    ndel + nins + nrel + nmov

  method size = self#get_nedits

  method get_ndeleted_nodes =
    let count = ref 0 in
    self#iter_deletes
      (function
        | Delete(_, info, _) ->
            count := !count + (Info.get_size info)
        | _ -> assert false
      );
    !count

  method get_ninserted_nodes =
    let count = ref 0 in
    self#iter_inserts
      (function
        | Insert(_, info, _) ->
            count := !count + (Info.get_size info)
        | _ -> assert false
      );
    !count

  method get_nmoved_nodes ?(minsize=1) () =
    let count_tbl = Hashtbl.create 0 in (* mid -> count *)
    self#iter_moves
      (function
        | Move(mid, _, (inf1, _), (_, _)) ->
            let sz = Info.get_size inf1 in
            begin
              try
                let c = Hashtbl.find count_tbl !mid in
                Hashtbl.replace count_tbl !mid (sz + c)
              with
                Not_found -> Hashtbl.add count_tbl !mid sz
            end
        | _ -> assert false
      );

    begin %debug_block
      let total = ref 0 in
      [%debug_log "* size of moves:"];
      let list =
        List.fast_sort (fun (m1, _) (m2, _) -> Stdlib.compare m1 m2)
          (Hashtbl.fold (fun mid sz l -> (mid, sz)::l) count_tbl [])
      in
      List.iter
        (fun (mid, sz) ->
          total := !total + sz;
          [%debug_log "mid:%a --> %d node%s" MID.ps mid sz (if sz = 1 then "" else "s")]
        ) list;
      [%debug_log "total=%d" !total];
    end;

    let total =
      Hashtbl.fold
        (fun _ c count ->
          if c >= minsize then
            c + count
          else
            count
        ) count_tbl 0
    in
    [%debug_log "total=%d (minsize=%d)" total minsize];
    total

  method get_nrelabeled_nodes ?(orig=false) () =
    let count = ref 0 in
    self#iter_relabels
      (function
        | Relabel(_, (inf1, _), (inf2, _)) when orig -> begin
            let nd1 = Info.get_node inf1 in
            let nd2 = Info.get_node inf2 in
            if nd1#data#is_named_orig || nd2#data#is_named_orig then begin
              let sz = Info.get_size inf1 in
              count := !count + sz
            end
        end
        | Relabel(_, (inf1, _), (_, _)) -> begin
            let sz = Info.get_size inf1 in
            count := !count + sz
        end
        | _ -> assert false
      );
    !count


  method get_nedited_nodes =
    let ndel = self#get_ndeleted_nodes in
    let nins = self#get_ninserted_nodes in
    let nrel = self#get_nrelabeled_nodes() in
    let nmov = self#get_nmoved_nodes() in
    ndel + nins + nrel + nmov


  method get_nmoved_and_relabeled_nodes
      ?(minsize=1)
      ?(orig=false)
      tree1
      nmapping
      =
    let count_tbl = Hashtbl.create 0 in (* mid -> count *)
    self#iter_moves
      (function
        | Move(mid, _, (info1, excl1), _) -> begin
            tree1#scan_initial_cluster
              (Info.get_node info1, List.map Info.get_node !excl1)
              (fun n ->
                try
                  let n' = nmapping#find n in
                  let extra_cond =
                    not orig ||
                    (n#data#is_named_orig ||
                    n'#data#is_named_orig)
                  in
                  if self#mem_rel12 n n' && extra_cond then begin
                    try
                      let c = Hashtbl.find count_tbl !mid in
                      Hashtbl.replace count_tbl !mid (c + 1)
                    with
                      Not_found -> Hashtbl.add count_tbl !mid 1
                  end
                with
                  Not_found -> assert false
              )
        end
        | _ -> assert false
      );
    Hashtbl.fold
      (fun _ c count ->
        if c >= minsize then
          c + count
        else
          count
      ) count_tbl 0



  method get_moved_nodes tree1 = (* valid after final fixup *)
(*
    let count_tbl = Hashtbl.create 0 in
    let add_count mid x =
      try
        let c = Hashtbl.find count_tbl mid in
        Hashtbl.replace count_tbl mid (c + x)
      with
        Not_found -> Hashtbl.add count_tbl mid x
    in
*)
    let nds = Xset.create 0 in
    self#iter_moves
      (function
        | Move(_, _, (info1, excl1), _) ->
            tree1#scan_initial_cluster
              (Info.get_node info1, List.map Info.get_node !excl1)
              (fun n -> Xset.add nds n)
        | _ -> assert false
      );
    (*Xset.to_list *)nds

  method _get_moved_nodes_of_move_id move_id = (* valid before final fixup *)
    let nds = Xset.create 0 in
    self#iter_moves
      (function
        | Move(mid, _, (info1, _), _) ->
            if !mid = move_id then
              let n = Info.get_node info1 in
              Xset.add nds n
        | _ -> assert false
      );
    (*Xset.to_list *)nds

  method private setup_multi_mov_gr_tbl nmapping is_anon =

    if false then begin (* eliminate single move of anonymous entity *)

      let scan_initial_cluster nd nds (f : 'node_t -> unit) =
        let rec scan n =
          f n;
          Array.iter
            (fun c ->
              if List.memq c nds then () else scan c
            ) n#initial_children
        in
        scan nd
      in
      self#iter_moves
        (function
          | Move(mid, _, (info1, excl1), (info2, excl2)) as mov -> begin
              let _ = mid in
              let count = ref 0 in
              let rt1 = Info.get_node info1 in
              let rt2 = Info.get_node info2 in
              scan_initial_cluster rt1 (List.map Info.get_node !excl1)
                (fun _ -> incr count);

              [%debug_log "%a(count=%d): %s -> %s" MID.ps !mid !count rt1#data#label rt2#data#label];
              if !count = 1 && (is_anon rt1 || is_anon rt2) then begin
                [%debug_log "single move of anonymous node: %s" (to_string mov)];
                let _ = nmapping#remove rt1 rt2 in
                self#remove_edit mov;
                begin
                  try
                    match self#find_rel12 rt1 rt2 with
                    | Relabel _ as rel ->
                        self#remove_edit rel
                    | _ -> assert false
                  with
                    Not_found -> ()
                end;
                self#add_edit (Delete(false, info1, excl1));
                self#add_edit (Insert(false, info2, excl2));
              end
          end
          | _ -> assert false
        )
    end;

    let mid_gen = options#moveid_generator in

    let tbl = Hashtbl.create 0 in (* mid -> move list *)

    self#iter_moves
      (function
        | Move(mid, _, _, _) as mov -> begin
            try
              let members = Hashtbl.find tbl !mid in
              Hashtbl.replace tbl !mid (mov::members)
            with
              Not_found -> Hashtbl.add tbl !mid [mov]
        end
        | _ -> assert false
      );

    Hashtbl.iter (* exclude singletons and assign fresh id for members *)
      (fun mid movs ->
        [%debug_log "mid=%a" MID.ps mid];
        if (List.length movs) > 1 then begin
          List.iter
            (function
              | Move(m, _, (i1, _), (i2 ,_)) -> begin
                  let _ = i1 in
                  let _ = i2 in
                  let m' = mid_gen#gen in
                  [%debug_log "%a (%a-%a) -> %a" MID.ps !m
                    nups (Info.get_node i1) nups (Info.get_node i2) MID.ps m'];
                  if self#is_indivisible_move !m then
                    self#add_indivisible_move m';
                  m := m';
                  [%debug_log "%a <- %a" MID.ps mid MID.ps m'];
                  Hashtbl.add mov_gr_tbl m' mid
              end
              | _ -> assert false
            ) movs;
          let sorted_movs = sort_edit_list_topdown movs in
          [%debug_log "%a -> [%s]" MID.ps mid
            (Xlist.to_string MID.to_string ";"
               (Xlist.uniq (List.fast_sort Stdlib.compare (List.map get_mid sorted_movs))))];
          Hashtbl.add mov_gr_mem_tbl mid sorted_movs
        end
      ) tbl

  method finalize (nmapping : 'node_t Node_mapping.c) (is_anon : 'node_t -> bool) =
    self#sync;
    self#setup_multi_mov_gr_tbl nmapping is_anon

  method to_string =
    let buf = Buffer.create 0 in
    Buffer.add_string buf (sprintf "%d edit(s):\n" self#get_nedits);
    self#iter_topdown
      (fun ed ->
        Buffer.add_string buf (to_string ed);
        Buffer.add_string buf "\n"
      );
    Buffer.contents buf

  method to_string_gid =
    let buf = Buffer.create 0 in
    Buffer.add_string buf (sprintf "%d edit(s):\n" self#get_nedits);
    self#iter_topdown
      (fun ed ->
        Buffer.add_string buf (to_string_gid ed);
        Buffer.add_string buf "\n"
      );
    Buffer.contents buf

  method private _find12 table_pairs nd1 nd2 =
    let res = ref [] in
    List.iter
      (fun (tbl1, tbl2) ->
        try
          let e1 = Nodetbl.find tbl1 nd1 in
          let e2 = Nodetbl.find tbl2 nd2 in
          if e1 = e2 then
            res := e1::!res
        with
          Not_found -> ()
      ) table_pairs;

    (*if !res <> [] then
      [%debug_log "%a-%a -> [%s]"
        nups nd1 nups nd2 (Xlist.to_string to_string ";" !res)];*)

    !res

  method find12 nd1 nd2 =
    self#_find12 [(rel1_tbl, rel2_tbl); (mov1_tbl, mov2_tbl)] nd1 nd2

  method find21 nd2 nd1 =
    self#_find12 [(rel1_tbl, rel2_tbl); (mov1_tbl, mov2_tbl)] nd1 nd2

  method find_mov12 nd1 nd2 =
    match self#_find12 [(mov1_tbl, mov2_tbl)] nd1 nd2 with
    | [] -> raise Not_found
    | [ed] -> ed
    | _ -> assert false

  method find_mid12 nd1 nd2 =
    match self#find_mov12 nd1 nd2 with
    | Move(mid, _, _, _) -> !mid
    | _ -> assert false

  method find_rel12 nd1 nd2 =
    match self#_find12 [rel1_tbl, rel2_tbl] nd1 nd2 with
    | [] -> raise Not_found
    | [ed] -> ed
    | _ -> assert false

  method find_maps_of_relabels =
    let res = ref [] in
    Nodetbl.iter
      (fun _ ed ->
        match ed with
        | Relabel(_, (i1, _), (i2, _)) ->
            res := (Info.get_node i1, Info.get_node i2)::!res
        | _ -> ()
      ) rel1_tbl;
    !res

  method find1 nd =
    let res = ref [] in
    List.iter
      (fun tbl ->
        try
          res := (Nodetbl.find tbl nd)::!res
        with
          Not_found -> ()
      ) [del_tbl; rel1_tbl; mov1_tbl];
    !res

  method find_del nd =
    Nodetbl.find del_tbl nd

  method find2 nd =
    let res = ref [] in
    List.iter
      (fun tbl ->
        try
          res := (Nodetbl.find tbl nd)::!res
        with
          Not_found -> ()
      ) [ins_tbl; rel2_tbl; mov2_tbl];
    !res

  method find_ins nd =
    Nodetbl.find ins_tbl nd

  method find_mov1 nd =
    Nodetbl.find mov1_tbl nd

  method find_mov2 nd =
    Nodetbl.find mov2_tbl nd


  method mem1 nd = match self#find1 nd with [] -> false | _ -> true
  method mem2 nd = match self#find2 nd with [] -> false | _ -> true

  method mem_del nd =
    Nodetbl.mem del_tbl nd

  method mem_ins nd =
    Nodetbl.mem ins_tbl nd

  method mem_mov12 nd1 nd2 =
    try
      let e1 = Nodetbl.find mov1_tbl nd1 in
      let e2 = Nodetbl.find mov2_tbl nd2 in
      e1 == e2
    with
      Not_found -> false

  method mem_mov21 nd2 nd1 =
    self#mem_mov12 nd1 nd2

  method mem_mov1 nd = Nodetbl.mem mov1_tbl nd
  method mem_mov2 nd = Nodetbl.mem mov2_tbl nd

  method mem_rel12 nd1 nd2 =
    try
      let e1 = Nodetbl.find rel1_tbl nd1 in
      let e2 = Nodetbl.find rel2_tbl nd2 in
      e1 == e2
    with
      Not_found -> false

  method mem_rel1 nd = Nodetbl.mem rel1_tbl nd
  method mem_rel2 nd = Nodetbl.mem rel2_tbl nd

  method mem12 nd1 nd2 = self#mem_mov12 nd1 nd2 || self#mem_rel12 nd1 nd2

  method sort_topdown =
    list <-
      sort_edit_list_topdown
        (List.concat_map
           self#edit_tbl_to_list
           [del_tbl; ins_tbl; mov1_tbl; rel1_tbl])


  method sync =
    list <-
      List.concat_map
        (fun tbl -> Nodetbl.fold (fun _ e l -> e :: l) tbl [])
        [del_tbl; ins_tbl; rel1_tbl; mov1_tbl];

  method iter_topdown f =
    self#sort_topdown;
    List.iter f list


  method filter f =
    List.iter
      (fun tbl ->
        let to_be_removed = Xset.create 0 in
        Nodetbl.iter
          (fun u e ->
            if not (f e) then begin
              [%debug_log "to be removed: %s" (to_string e)];
              Xset.add to_be_removed u
            end
          ) tbl;
        Xset.iter (Nodetbl.remove tbl) to_be_removed
      ) tables

  method filter_deletes f =
    let to_be_removed = Xset.create 0 in
    Nodetbl.iter
      (fun u e ->
        if not (f e) then begin
          [%debug_log "to be removed: %s" (to_string e)];
          Xset.add to_be_removed u
        end
      ) del_tbl;
    Xset.iter (Nodetbl.remove del_tbl) to_be_removed

  method filter_inserts f =
    let to_be_removed = Xset.create 0 in
    Nodetbl.iter
      (fun u e ->
        if not (f e) then begin
          [%debug_log "to be removed: %s" (to_string e)];
          Xset.add to_be_removed u
        end
      ) ins_tbl;
    Xset.iter (Nodetbl.remove ins_tbl) to_be_removed

  method filter_relabels f =
    List.iter
      (fun tbl ->
        let to_be_removed = Xset.create 0 in
        Nodetbl.iter
          (fun u e ->
            if not (f e) then begin
              [%debug_log "to be removed: %s" (to_string e)];
              Xset.add to_be_removed u
            end
          ) tbl;
        Xset.iter (Nodetbl.remove tbl) to_be_removed
      ) [rel1_tbl; rel2_tbl]

  method filter_moves f =
    List.iter
      (fun tbl ->
        let to_be_removed = Xset.create 0 in
        Nodetbl.iter
          (fun u e ->
            if not (f e) then begin
              [%debug_log "to be removed: %s" (to_string e)];
              Xset.add to_be_removed u
            end
          ) tbl;
        Xset.iter (Nodetbl.remove tbl) to_be_removed
      ) [mov1_tbl; mov2_tbl]


  method get_line_align
      (tree1 : 'tree_t)
      (tree2 : 'tree_t)
      (nmapping : 'node_t Node_mapping.c)
      =
    ignore tree2;
    let moved_nodes = self#get_moved_nodes tree1 in
    let aligns = Xset.create 0 in
    nmapping#iter
      (fun n1 n2 ->
        let l1 = n1#data#src_loc.Loc.start_line in
        let l2 = n2#data#src_loc.Loc.start_line in
        if
          not (Xset.mem moved_nodes n1) &&
          not (self#mem_rel12 n1 n2) &&
          l1 > 0 && l2 > 0
        then
          Xset.add aligns (l1, l2)
      );

    let alignl =
      List.fast_sort (fun (l, _) (l', _) -> Stdlib.compare l l') (Xset.to_list aligns)
    in

    let to_lm = function
      | [p] -> LM_single p
      | [(x0, y0); (x1, y1)] ->
          let dx = x1 - x0 in
          let dy = y1 - y0 in
          if dx = dy && dx > 0 then
            LM_multi (x0, y0, dx)
          else
            assert false
      | _ -> assert false
    in

    let (r, reduced) =
      List.fold_left
        (fun (range, lst) (l1, l2) ->
          match range with
          | [] -> [(l1, l2)], lst

          | [(l1', l2')] ->
              if l1 = l1' + 1 && l2 = l2' + 1 then
                [(l1', l2'); (l1, l2)], lst
              else
                [(l1, l2)], (to_lm range)::lst

          | [(l1', l2'); (l1'', l2'')] ->
              if l1 = l1'' + 1 && l2 = l2'' + 1 then
                [(l1', l2'); (l1, l2)], lst
              else
                [(l1, l2)], (to_lm range)::lst

          | _ -> assert false
        ) ([], []) alignl
    in
    let res =
      List.rev
        (match r with
        | [] -> reduced
        | [_] -> (to_lm r)::reduced
        | [(_, _); (_, _)] -> (to_lm r)::reduced
        | _ -> assert false
        )
    in
    res


  method dump_line_align_ch ~formatters align ch =
    List.iter (fun a -> output_string ch (formatters#align a)) align

  method dump_diff_simple ?(line_align=[]) tree1 tree2 fname =
    Xfile.dump fname (self#dump_diff_simple_ch ~line_align tree1 tree2)

  method dump_diff_simple_ch ?(line_align=[]) (tree1 : 'tree_t) (tree2 : 'tree_t) =
    let formatters =
      new formatters_base
        ~delete:(fun _ _ segs -> sprintf "DELETE %s\n" (segments_to_string segs))
        ~insert:(fun _ _ segs -> sprintf "INSERT %s\n" (segments_to_string segs))
        ~relabel:
        (fun movrel _ _ segs1 _ _ segs2 ->
          let marker =
            if movrel then
              "MOVREL"
            else
              "RELABEL"
          in
          sprintf "%s %s >> %s\n" marker (segments_to_string segs1) (segments_to_string segs2)
        )
        ~move:
        (fun _ _ segs1 _ _ segs2 ->
          sprintf "MOVE %s >> %s\n" (segments_to_string segs1) (segments_to_string segs2)
        )
        ~align:
        (function
          | LM_single (l1, l2) ->
              sprintf "ALIGN %d >> %d\n" l1 l2
          | LM_multi(l1, l2, ext) ->
              sprintf "ALIGN %d:%d >> %d:%d\n" l1 (l1+ext) l2 (l2+ext)
        )
        ~ignored1:(fun (s, e) -> sprintf "IGNORED1 %d %d\n" s e)
        ~ignored2:(fun (s, e) -> sprintf "IGNORED2 %d %d\n" s e)
        ~misparsed1:(fun (s, e) -> sprintf "MISPARSED1 %d %d\n" s e)
        ~misparsed2:(fun (s, e) -> sprintf "MISPARSED2 %d %d\n" s e)
    in
    self#dump_diff_ch ~header:"" ~footer:"" ~formatters ~line_align tree1 tree2

  method dump_diff_json ?(line_align=[]) tree1 tree2 fname =
    Xfile.dump fname (self#dump_diff_json_ch ~line_align tree1 tree2)

  method dump_diff_json_ch ?(line_align=[]) (tree1 : 'tree_t) (tree2 : 'tree_t) =

    let segs_to_json idx ?(st=(-1)) ?(ed=(-1)) _segs =
      let segs = List.filter (fun (s, e) -> s <= e) _segs in
      let seg_to_json (s, e) = sprintf "{\"start\":%d,\"end\":%d}" s e in
      let extra =
        if st >= 0 && st <= ed then
          sprintf "\"start%d\":%d,\"end%d\":%d" idx st idx ed
        else
          ""
      in
      let segs_str =
        if segs = [] then
          ""
        else
          sprintf "\"segments%d\":[%s]" idx (Xlist.to_string seg_to_json "," segs)
      in
      String.concat "," (List.filter (fun x -> x <> "") [extra; segs_str])
(*
      match segs with
      | [] -> ""
      | seg::_ ->
          let last = ref seg in
          let seg_to_json ((s, e) as sg) = last := sg; sprintf "{\"start\":%d,\"end\":%d}" s e in
          let sstr = Xlist.to_string seg_to_json "," segs in
          sprintf "\"start%d\":%d,\"end%d\":%d,\"segments%d\":[%s]"
            idx (fst seg)
            idx (snd !last)
            idx sstr
*)
    in
    let mktag s = sprintf "\"tag\":\"%s\"" s in
    let mksegs1 = segs_to_json 1 in
    let mksegs2 = segs_to_json 2 in
    let mkalign ?(ext=0) l1 l2 =
      sprintf "{%s,\"line1\":%d,\"line2\":%d%s},"
        (mktag "ALIGN") l1 l2 (if ext = 0 then "" else sprintf ",\"ext\":%d" ext)
    in

    let mkfmt0 m idx seg =
      let seg_str = segs_to_json idx [seg] in
      if seg_str = "" then
        ""
      else
        sprintf "{%s,%s}," (mktag m) seg_str
    in
    let mkfmt m idx st ed segs =
      if st <= ed then
        let seg_str = segs_to_json idx ~st ~ed segs in
        if seg_str = "" then
          ""
        else
          sprintf "{%s,%s}," (mktag m) seg_str
      else
        ""
    in
    let mkfmt2 m st1 ed1 segs1 st2 ed2 segs2 =
      if st1 <= ed1 && st2 <= ed2 then
        let seg_str1 = mksegs1 ~st:st1 ~ed:ed1 segs1 in
        let seg_str2 = mksegs2 ~st:st2 ~ed:ed2 segs2 in
        if seg_str1 = "" || seg_str2 = "" then
          ""
        else
          sprintf "{%s,%s,%s}," (mktag m) seg_str1 seg_str2
      else
        ""
    in

    let formatters =
      new formatters_base
        ~delete:(mkfmt "DELETE" 1)
        ~insert:(mkfmt "INSERT" 2)
        ~relabel:
        (fun movrel ->
          let marker =
            if movrel then
              "MOVREL"
            else
              "RELABEL"
          in
          mkfmt2 marker
        )
        ~move:(mkfmt2 "MOVE")
        ~align:
        (function
          | LM_single(l1, l2) -> mkalign l1 l2
          | LM_multi(l1, l2, ext) -> mkalign ~ext l1 l2
        )
        ~ignored1:(mkfmt0 "IGNORED1" 1)
        ~ignored2:(mkfmt0 "IGNORED2" 2)
        ~misparsed1:(mkfmt0 "MISPARSED1" 1)
        ~misparsed2:(mkfmt0 "MISPARSED2" 2)
    in
    self#dump_diff_ch ~header:"[" ~footer:"null]" ~formatters ~line_align tree1 tree2

  method private dump_diff_ch
      ~header ~footer ~formatters
      ?(line_align=[])
      ?(minimal=true)
      (tree1 : 'tree_t) (tree2 : 'tree_t)
      ch
      =
    let ignored1 = tree1#ignored_regions in
    let ignored2 = tree2#ignored_regions in

    [%debug_log "* DUMPING DIFF DATA (%d edit(s))\n" self#get_nedits];

    (*let mkpath tree =
      if Storage.kind_is_fs tree#source_kind then
        tree#source_fullpath
      else
        tree#source_path
    in*)

    let iginfos1 = List.map (Info.of_region (*~fname:(mkpath tree1)*)) ignored1 in
    let iginfos2 = List.map (Info.of_region (*~fname:(mkpath tree2)*)) ignored2 in

    begin %debug_block
      [%debug_log "ignored regions1: %s" (segments_to_string ignored1)];
      [%debug_log "ignored regions2: %s" (segments_to_string ignored2)]
    end;

    let filter iginfos info infos =
      List.filter
        (fun inf ->
          Info.is_included inf info &&
          List.for_all (fun i -> not (Info.is_included inf i)) infos
        ) iginfos
    in

    let get_segments iginfos info excludes =

      begin %debug_block
        [%debug_log "info=%s" (Info.to_string info)];
        [%debug_log "excludes:"];
        List.iter (fun i -> [%debug_log "%s" (Info.to_string i)]) !excludes
      end;

      let excludes' = (filter iginfos info !excludes) @ !excludes in

      let segs = Info.segment (info, (Info.sort_infos excludes')) in

      [%debug_log "result=%s" (segments_to_string segs)];

      sort_segments segs
    in

    let get_mov_segs_pair = function
      | Move(_, _, (info1, excludes1), (info2, excludes2)) ->
          let segs1 = get_segments iginfos1 info1 excludes1 in
          let segs2 = get_segments iginfos2 info2 excludes2 in
          segs1, segs2
      | _ -> assert false
    in

    fprintf ch "%s" header;

    let segment_count = ref 0 in

    self#iter_topdown
      (fun ed ->

        [%debug_log "scanning %s" (to_string ed)];

        try
          match ed with
          | Delete(_, info, excludes) ->
              let loc = Info.get_loc info in
              let st, ed = loc.Loc.start_offset, loc.Loc.end_offset in
              let segs = get_segments iginfos1 info excludes in
              output_string ch (formatters#delete st ed segs)

          | Insert(_, info, excludes) ->
              let loc = Info.get_loc info in
              let st, ed = loc.Loc.start_offset, loc.Loc.end_offset in
              let segs = get_segments iginfos2 info excludes in
              output_string ch (formatters#insert st ed segs)

          | Relabel(movrel, (info1, excludes1), (info2, excludes2)) ->
              let n1 = Info.get_node info1 in
              let n2 = Info.get_node info2 in
              let ok =
                !movrel ||
                not minimal ||
                n1#data#is_named_orig && n2#data#is_named_orig ||
                (not n1#data#is_named && n2#data#is_named || n1#data#is_named && not n2#data#is_named) ||
                (not (n1#data#is_compatible_with ?weak:(Some true) n2#data) &&
                 n1#data#more_anonymized_label <> n2#data#more_anonymized_label) ||
                 n1#data#has_value && n2#data#has_value && n1#data#get_value <> n2#data#get_value ||
                 match n1#data#orig_lab_opt, n2#data#orig_lab_opt with
                 | Some o1, Some o2 -> o1 <> o2
                 | _ -> false
              in
              if ok then begin
                if !movrel || n1#data#_anonymized_label <> n2#data#_anonymized_label then
                  let loc1 = Info.get_loc info1 in
                  let loc2 = Info.get_loc info2 in
                  let segs1 = get_segments iginfos1 info1 excludes1 in
                  let segs2 = get_segments iginfos2 info2 excludes2 in
                  let st1, ed1 = loc1.Loc.start_offset, loc1.Loc.end_offset in
                  let st2, ed2 = loc2.Loc.start_offset, loc2.Loc.end_offset in
                  output_string ch (formatters#relabel !movrel st1 ed1 segs1 st2 ed2 segs2)
                else
                  let loc1, loc2, id_only =
                    let loc1 = Info.get_id_loc info1 in
                    let loc2 = Info.get_id_loc info2 in
                    if loc1 != Loc.dummy && loc2 != Loc.dummy then
                      loc1, loc2, true
                    else
                      Info.get_loc info1, Info.get_loc info2, false
                  in
                  if loc1 != Loc.ghost && loc2 != Loc.ghost then
                    let st1, ed1 as seg1 = loc1.Loc.start_offset, loc1.Loc.end_offset in
                    let st2, ed2 as seg2 = loc2.Loc.start_offset, loc2.Loc.end_offset in
                    let segs1, segs2 =
                      if id_only then
                        [seg1], [seg2]
                      else
                        let segs1 = get_segments iginfos1 info1 excludes1 in
                        let segs2 = get_segments iginfos2 info2 excludes2 in
                        segs1, segs2
                    in
                    output_string ch (formatters#relabel !movrel st1 ed1 segs1 st2 ed2 segs2)
              end

          | Move(mid, _, (info1, _), (info2, _)) as mov ->
              let skip =
                try
                  let movs = self#find_mov_gr_mems (self#find_mov_gr !mid) in
                  (Info.get_node info1)#gindex <
                  (Xlist.max
                     (List.map
                        (function
                          | Move(_, _, (i1, _), _) ->
                              (Info.get_node i1)#gindex
                          | _ -> assert false
                        ) movs))
                with
                  Not_found -> false
              in

              if not skip then begin
                let loc1 = Info.get_loc info1 in
                let loc2 = Info.get_loc info2 in
                let st1, ed1 = loc1.Loc.start_offset, loc1.Loc.end_offset in
                let st2, ed2 = loc2.Loc.start_offset, loc2.Loc.end_offset in

                let segs1, segs2 =
                  try
                    let movs = self#find_mov_gr_mems (self#find_mov_gr !mid) in

                    [%debug_log "* move group %a:\n\t%s" MID.ps !mid
                      (Xlist.to_string to_string "\n\t" movs)];

                    let segs_list1, segs_list2 = List.split (List.map get_mov_segs_pair movs) in
                    merge_segments segs_list1, merge_segments segs_list2
                  with
                    Not_found -> get_mov_segs_pair mov
                in
                output_string ch (formatters#move st1 ed1 segs1 st2 ed2 segs2)
              end
              else
                [%debug_log " -> skipped"]

        with
          Info.Segment ->
            incr segment_count;
            [%debug_log "Info.Segment exception raised!"]
      );
    List.iter (fun seg -> output_string ch (formatters#ignored1 seg)) ignored1;
    List.iter (fun seg -> output_string ch (formatters#ignored2 seg)) ignored2;
    List.iter (fun seg -> output_string ch (formatters#misparsed1 seg)) tree1#misparsed_regions;
    List.iter (fun seg -> output_string ch (formatters#misparsed2 seg)) tree2#misparsed_regions;

    begin %debug_block
      [%debug_log "delete:%d insert:%d relabel:%d move:%d (total:%d)\n"
        self#get_ndeletes self#get_ninserts self#get_nrelabels self#get_nmoves self#get_nedits];
      [%debug_log "%d Segment exception(s) raised" !segment_count]
    end;

    if line_align <> [] then
      self#dump_line_align_ch ~formatters line_align ch;

    fprintf ch "%s" footer

  (* end of method dump_diff_ch *)


  method dump_gdiff_json ?(comp=Compression.none) (tree1 : 'tree_t) (tree2 : 'tree_t) fname =

    let _del_list = ref [] in
    let _ins_list = ref [] in
    let _rel_list = ref [] in
    let _movrel_list = ref [] in
    let _mov_list = ref [] in

    let ins_tbl = Nodetbl.create 0 in

    let mapped_node_tbl = Nodetbl.create 0 in

    let subtree_roots = Xset.create 0 in

    self#iter
      (function
        | Delete(_, info, excludes) -> begin
            let nd = Info.get_node info in
            let nds = List.map Info.get_node !excludes in
            Xset.add subtree_roots nd;
            tree1#scan_initial_cluster (nd, nds) (fun n -> _del_list := n :: !_del_list)
        end
        | Insert(_, info, excludes) -> begin
            let nd = Info.get_node info in
            let nds = List.map Info.get_node !excludes in
            Xset.add subtree_roots nd;
            tree2#scan_initial_cluster (nd, nds)
              (fun n ->
                _ins_list := n :: !_ins_list;
                Nodetbl.add ins_tbl n nd
              );
        end
        | Relabel(movrel, (info1, _), (info2, _)) -> begin
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            Nodetbl.add mapped_node_tbl nd2 nd1;
            Xset.add subtree_roots nd1;
            Xset.add subtree_roots nd2;
            if !movrel then
              _movrel_list := (nd1, nd2) :: !_movrel_list
            else
              _rel_list := (nd1, nd2) :: !_rel_list
        end
      | Move(mid, _, (info1, excludes1), (info2, excludes2)) -> begin
          let _ = mid in
          let nd1 = Info.get_node info1 in
          let nd2 = Info.get_node info2 in
          Nodetbl.add mapped_node_tbl nd2 nd1;
          let nds1 = List.map Info.get_node !excludes1 in
          let nds2 = List.map Info.get_node !excludes2 in
          Xset.add subtree_roots nd1;
          Xset.add subtree_roots nd2;
          let el1 = ref [] in
          let el2 = ref [] in
          let add r n = if not (is_ghost_node n) then r := n :: !r in
          tree1#scan_initial_cluster (nd1, nds1) (add el1);
          tree2#scan_initial_cluster (nd2, nds2) (add el2);
          let nel1 = List.length !el1 in
          let nel2 = List.length !el2 in
          [%debug_log "%a: nd1=%a |el1|=%d nd2=%a |el2|=%d" MID.ps !mid nups nd1 nel1 nups nd2 nel2];
          assert (nel1 = nel2);
          List.iter2
            (fun n1 n2 ->
              Nodetbl.add mapped_node_tbl n2 n1;
              _mov_list := (n1, n2) :: !_mov_list
            ) !el1 !el2
      end);

    let cmp1 n0 n1 = compare n0#gindex n1#gindex in
    let cmp2 (n0, _) (n1, _) = compare n0#gindex n1#gindex in
    let del_list = List.fast_sort cmp1 !_del_list in
    let ins_list = List.fast_sort cmp1 !_ins_list in
    let rel_list = List.fast_sort cmp2 !_rel_list in
    let movrel_list = List.fast_sort cmp2 !_movrel_list in
    let mov_list = List.fast_sort cmp2 !_mov_list in

    let is_subtree_root x =
      x#data#is_statement && (x#data#is_named || x#initial_nchildren > 0) ||
      x#data#is_named_orig(* && x#initial_nchildren > 0*) ||
      Xset.mem subtree_roots x
    in

    let get_gid = Json.get_gid in
    let get_info1 = Json.get_info1 ~is_subtree_root in
    let get_info = Json.get_info ~is_subtree_root tree1 tree2 mapped_node_tbl in
    let _fprintf = Json._fprintf in

    try
      let d = Filename.dirname fname in
      if not (Xfile.dir_exists d) then
        Xfile.mkdir d;
      let ch = new Xchannel.out_channel ~comp (Xchannel.Destination.of_file fname) in
      let dump1 ?(get_root=None) tree ch l =
        let comma_flag = ref false in
        List.iter
          (fun nd ->
            if !comma_flag then
              _fprintf ch ",";
            let info = get_info1 ~get_root tree nd in
            _fprintf ch "[%a,%s]" GI.rs (get_gid nd) info;
            comma_flag := true
          ) l
      in
      let dump2 ch l =
        let comma_flag = ref false in
        List.iter
          (fun (nd1, nd2) ->
            if !comma_flag then
              _fprintf ch ",";
            let info = get_info nd1 nd2 in
            _fprintf ch "[%a,%a,%s]" GI.rs (get_gid nd1) GI.rs (get_gid nd2) info;
            comma_flag := true
          ) l
      in
      _fprintf ch "{\"delete\":["; dump1 tree1 ch del_list;
      let get_root = Some (Nodetbl.find ins_tbl) in
      _fprintf ch "],\"insert\":["; dump1 ~get_root tree2 ch ins_list;
      _fprintf ch "],\"relabel\":["; dump2 ch rel_list;
      _fprintf ch "],\"move+relabel\":["; dump2 ch movrel_list;
      _fprintf ch "],\"move\":["; dump2 ch mov_list;
      _fprintf ch "]}";
      ch#close
    with
    | Xchannel.Error s -> let _ = s in [%warn_log "%s" s]
  (* end of method dump_gdiff_json *)


  method dump_diff_info fname tree1 tree2 =
    Xfile.dump fname (self#dump_diff_info_ch tree1 tree2)


  method dump_diff_info_ch (tree1 : 'tree_t) (tree2 : 'tree_t) ch =
    let get_gid nd =
      let g = nd#data#gid in
      if g > 0 then g else nd#gindex
    in

    let finished_movs = Xset.create 0 in (* mid set *)

    let get_size_of_mov = function
      | Move(_, _, (info1, _), _) -> Info.get_size info1
      | _ -> assert false
    in

    let excludes_to_str ex =
      " ["^
      (Xlist.to_string
         (fun info ->
           sprintf "(%a:%a)" ups (Info.get_uid info) gps (Info.get_gid info)
         ) ";" ex)^
      "]"
    in

    let dump_mov ch tab = function
      | Move(mid, kind, (info1, excludes1), (info2, excludes2)) ->
          let nd1 = Info.get_node info1 in
          let nds1 = List.map Info.get_node !excludes1 in
          let elems1 = ref [] in
          tree1#scan_initial_cluster (nd1, nds1) (fun n -> elems1 := (get_gid n) :: !elems1);

          let kind_str =
            if !kind = Mpermutation then ":PERMUTATION" else ""
          in
          fprintf ch "%sMOVE%a(%d)%s %s%s -> %s%s <%s>\n" tab MID.p !mid
            (Info.get_size info1) kind_str (Info.to_string info1)
            (if !excludes1 = [] then
              ""
            else
              excludes_to_str !excludes1
            )
            (Info.to_string info2)
            (if !excludes2 = [] then
              ""
            else
              excludes_to_str !excludes2
            )
            (GI.list_to_string !elems1)

      | _ -> assert false
    in

    self#iter
      (fun ed ->
        try
          match ed with
          | Delete(_, info, excludes) -> begin
              let nd = Info.get_node info in
              let nds = List.map Info.get_node !excludes in
              let elems = ref [] in
              tree1#scan_initial_cluster (nd, nds) (fun n -> elems := (get_gid n) :: !elems);

              fprintf ch "DELETE(%s) %s%s <%s>\n"
                (sprintf "%d" info.Info.i_size)
                (Info.to_string info)
                (if !excludes = [] then
                  ""
                else
                  excludes_to_str !excludes
                )
                (GI.list_to_string !elems)
          end
          | Insert(_, info, excludes) -> begin
              let nd = Info.get_node info in
              let nds = List.map Info.get_node !excludes in
              let elems = ref [] in
              tree2#scan_initial_cluster (nd, nds) (fun n -> elems := (get_gid n) :: !elems);

              fprintf ch "INSERT(%s) %s%s <%s>\n"
                (sprintf "%d" info.Info.i_size)
                (Info.to_string info)
                (if !excludes = [] then
                  ""
                else
                  excludes_to_str !excludes
                )
                (GI.list_to_string !elems)
          end
          | Relabel(movrel, (info1, excludes1), (info2, excludes2)) -> begin
              let marker =
                if !movrel then
                  "MOVREL"
                else
                  "RELABEL"
              in
              fprintf ch "%s %s%s -> %s%s\n"
                marker
                (Info.to_string info1)
                (if !excludes1 = [] then
                  ""
                else
                  excludes_to_str !excludes1
                )
                (Info.to_string info2)
                (if !excludes2 = [] then
                  ""
                else
                  excludes_to_str !excludes2
                )
          end
          | Move(mid, kind, _, _) as mov ->
              if not (Xset.mem finished_movs !mid) then begin
                try
                  let mg = self#find_mov_gr !mid in
                  let movs = self#find_mov_gr_mems mg in
                  List.iter (Xset.add finished_movs) (List.map get_mid movs);
                  let sz = List.fold_left (fun s m -> s + (get_size_of_mov m)) 0 movs in
                  let kind_str = if !kind = Mpermutation then ":PERMUTATION" else "" in
                  fprintf ch "MOVE(GROUP)(%d)%a%s:\n" sz MID.p mg kind_str;
                  List.iter (dump_mov ch "|- ") movs
                with Not_found ->
                  dump_mov ch "" mov
              end

        with
          Info.Segment ->
            [%debug_log "Info.Segment exception raised!"]
      )
  (* end of method dump_diff_info_ch *)


  method get_diff_summary tree1 tree2 nmapping =

    (* node -> (message * edits) *)
    let to_be_notified_tbl1 = Nodetbl.create 0 in
    let to_be_notified_tbl2 = Nodetbl.create 0 in

    let add_to_tbn tbl nd mes ed =
      try
        let (mes_r, edl_r, _) = Nodetbl.find tbl nd in
        edl_r := ed::!edl_r;
        if !mes_r = "" then mes_r := mes
      with Not_found ->
        Nodetbl.add tbl nd (ref mes, ref [ed], ref 0)
    in
    let make_notification tbl tree nd mes ed =
      if nd#data#to_be_notified then
        add_to_tbn tbl nd mes ed;
      let ancestors = tree#initial_ancestor_nodes nd in
      List.iter
        (fun a ->
          if a#data#to_be_notified then add_to_tbn tbl a "" ed
        ) ancestors
    in
    let make_notification1 =
      make_notification to_be_notified_tbl1 tree1 in

    let make_notification2 =
      make_notification to_be_notified_tbl2 tree2 in

    self#iter
      (fun ed ->
        match ed with
        | Delete(_, info, _) ->
            make_notification1 (Info.get_node info) "DELETED" ed;

        | Insert(_, info, _) ->
            make_notification2 (Info.get_node info) "INSERTED" ed;

        | Relabel(_, (info1, _), _) ->
            make_notification1 (Info.get_node info1) "RENAMED" ed;

        | Move(_, _, (info1, _), _) ->
            make_notification1 (Info.get_node info1) "MOVED" ed;
      );
    Nodetbl.iter
      (fun nd (_, edl_r, _) ->
        try
          let nd1 = nmapping#inv_find nd in
          let (_, edl_r', _) =
            Nodetbl.find to_be_notified_tbl1 nd1
          in
          edl_r' := !edl_r' @ !edl_r;
          Nodetbl.remove to_be_notified_tbl2 nd
        with Not_found -> ()
      ) to_be_notified_tbl2;

    let units_to_be_notified1 = tree1#get_units_to_be_notified in

    let unmodified =
      List.filter
        (fun nd -> not (Nodetbl.mem to_be_notified_tbl1 nd))
        units_to_be_notified1
    in

    nmapping#iter
      (fun nd _ ->
        tree1#iter_initial_ancestor_nodes nd
          (fun an ->
            try
              let (_, _, nmaps_r) =
                Nodetbl.find to_be_notified_tbl1 an
              in
              incr nmaps_r
            with Not_found -> ()
          )
      );

    to_be_notified_tbl1, to_be_notified_tbl2,
    units_to_be_notified1, unmodified
  (* end of method get_diff_summary *)


  method dump_diff_summary fname tree1 tree2 nmapping =
    Xfile.dump fname (self#dump_diff_summary_ch tree1 tree2 nmapping)

  method dump_diff_summary_ch
      (tree1 : 'tree_t)
      (tree2 : 'tree_t)
      nmapping
      ch
      =

    let to_be_notified_tbl1, to_be_notified_tbl2, _, unmodified =
      self#get_diff_summary tree1 tree2 nmapping
    in

    fprintf ch "*** Modified Units ***\n";

    let show tbl =
      Nodetbl.iter
        (fun nd (mes_r, edl_r, nmaps_r) ->
          let ((d, dg), (i, ig), (r, rg), (m, mg)) =
            List.fold_left
              (fun (((d, dg) as dd),
                    ((i, ig) as ii),
                    ((r, rg) as rr),
                    ((m, mg) as mm)) ed
                ->
                  match ed with
                  | Delete(_, info, _) ->
                      (d + (Info.get_size info), dg + 1), ii, rr, mm
                  | Insert(_, info, _) ->
                      dd, (i + (Info.get_size info), ig + 1), rr, mm
                  | Relabel(_, (info, _), _) ->
                      dd, ii, (r + (Info.get_size info), rg + 1), mm
                  | Move(_, _, (info, _), _) ->
                      dd, ii, rr, (m + (Info.get_size info), mg + 1)
              ) ((0, 0), (0, 0), (0, 0), (0, 0)) !edl_r
          in
          let count = d + i + r + m in
          let count_gr = dg + ig + rg + mg in
          fprintf ch "%s(%s): [%s] %d(%d) changed [%s], %d mapped\n"
            (get_label nd) (Loc.to_string nd#data#src_loc)
            (if !mes_r = "" then "MODIFIED" else !mes_r)
            count
            count_gr
            (sprintf
               "d:%d(%d)i:%d(%d)r:%d(%d)m:%d(%d)" d dg i ig r rg m mg)
            !nmaps_r
        ) tbl
    in
    show to_be_notified_tbl1;
    show to_be_notified_tbl2;

    fprintf ch "*** Unmodified Units ***\n";

    List.iter
      (fun nd ->
        fprintf ch "%s(%s)\n"
          nd#data#label (Loc.to_string nd#data#src_loc)
      ) unmodified
  (* end of method dump_diff_summary_ch *)

  method get_spm nmapping =
    let count = ref 0 in
    nmapping#iter
      (fun nd1 nd2 ->
        if self#mem_mov12 nd1 nd2 then
          ()
        else
          if
            nd1#data#eq nd2#data ||
            not nd1#data#is_named_orig && not nd2#data#is_named_orig &&
            nd1#data#more_anonymized_label = nd2#data#more_anonymized_label
          then
            incr count
      );
    !count

  method get_diff_stat tree1 tree2 nmapping =
    let _, _, units, unmodified =
      self#get_diff_summary tree1 tree2 nmapping
    in
    let nunits = List.length units in
    let nunmodified = List.length unmodified in

    let ndels    = self#get_ndeleted_nodes in
    let ninss    = self#get_ninserted_nodes in
    let nrels    = self#get_nrelabeled_nodes() in
    let nmovrels = self#get_nmoved_and_relabeled_nodes tree1 nmapping in
    let nrels_orig    = self#get_nrelabeled_nodes ~orig:true () in
    let nmovrels_orig = self#get_nmoved_and_relabeled_nodes ~orig:true tree1 nmapping in
    let nmovs    = self#get_nmoved_nodes() in

    let nmovrels2 = self#get_nmoved_and_relabeled_nodes ~minsize:2 tree1 nmapping in
    let nmovs2    = self#get_nmoved_nodes ~minsize:2 () in

    let ndelgrs = self#get_ndeletes in
    let ninsgrs = self#get_ninserts in
    let nmovgrs = self#get_nmove_groups in

    let nmaps = nmapping#size in
    let total = ndels + ninss + nrels + (* nmovs *) nmovgrs in
    let nnodes1 = tree1#_initial_size in
    let nnodes2 = tree2#_initial_size in
    let sim =
      if total = 0 then
        "1.0"
      else
        let spm = self#get_spm nmapping(*nmaps - nmovs - nrels_orig + nmovrels_orig*) in
        let _sim = float (spm * 2) /. float (nnodes1 + nnodes2) in
        sprintf "%.6f" _sim
    in
    let cr =
      sprintf "%.6f" ((float_of_int total) /. (float_of_int nmaps))
    in
    let ur =
      sprintf "%.6f"
        ((float_of_int nunmodified) /. (float_of_int nunits))
    in
    let ahs =
      let n = ndels + ninss + nmovs in
      let ng = ndelgrs + ninsgrs + nmovgrs in
      sprintf "%.6f" ((float_of_int n) /. (float_of_int ng))
    in
    { s_nnodes1 = nnodes1; s_nnodes2 = nnodes2;
      s_deletes     = ndels;
      s_deletes_gr  = ndelgrs;
      s_inserts     = ninss;
      s_inserts_gr  = ninsgrs;
      s_relabels    = nrels;
      s_relabels_orig = nrels_orig;
      s_relabels_gr = self#get_nrelabels;
      s_movrels     = nmovrels;
      s_movrels_orig = nmovrels_orig;
      s_moves       = nmovs;
      s_moves_gr    = nmovgrs;
      s_mapping     = nmaps;
      s_units            = nunits;
      s_unmodified_units = nunmodified;
      s_total_changes    = total;
      s_similarity       = sim;
      s_change_ratio     = cr;
      s_unmodified_rate  = ur;
      s_SPSM = nmaps - nmovs - nrels + nmovrels;
      s_SPM  = nmaps - nmovs;
      s_MGSM = nmovs2 - nmovrels2;
      s_MGM  = nmovs2;
      s_AHS  = ahs;
    }
  (* end of method get_diff_stat *)

  method dump_diff_stat_ch ?(short=false) tree1 tree2 (nmapping : 'node_t Node_mapping.c) =
    let s = self#get_diff_stat tree1 tree2 nmapping in
    dump_diff_stat_ch ~short s

  method dump_diff_stat ?(short=false) fname tree1 tree2 nmapping =
    Xfile.dump fname (self#dump_diff_stat_ch ~short tree1 tree2 nmapping)

  method show_diff_stat ?(short=false) tree1 tree2 nmapping =
    if not options#viewer_flag then begin
      self#dump_diff_stat_ch ~short tree1 tree2 nmapping stdout
    end
  (* end of method show_diff_stat *)


  method private get_cluster (*id_gen*)_ label bg fg tree inf excluded =
    let nd = Info.get_node inf in
    let nds = List.map Info.get_node !excluded in

    let buf = Buffer.create 0 in
(*
    Buffer.add_string buf (sprintf "subgraph cluster_%d {\n" (id_gen()));
    Buffer.add_string buf (sprintf "label=\"%s\";\n" label);
*)
    if label <> "" then
      Buffer.add_string buf
        (sprintf "%a [xlabel=\"%s\"];\n" UID.rs nd#uid label);

    tree#scan_initial_cluster (nd, nds)
      (fun n ->
        Buffer.add_string buf
          (sprintf "%a [%sstyle=filled,fillcolor=\"%s\",fontcolor=\"%s\"];\n"
             UID.rs n#uid (if n == nd then "peripheries=2," else "") bg fg)
      );
(*
    Buffer.add_string buf "};\n";
*)
    buf

  method dump_dot_ch1
      ?(final=false)
      tree1
      (*tree2*)_
      (nmapping : 'node_t Node_mapping.c)
      ch
      =
    let mid_tbl = Hashtbl.create 0 in
    self#iter_moves
      (function
        | Move(mid, _, (info1, _), _) ->
            let lab = sprintf "%a" MID.ps !mid in
            let nd1 = Info.get_node info1 in
            Hashtbl.add mid_tbl nd1 lab
        | _ -> assert false
      );

    let mklab =
      if final then
        fun nd ->
          let head =
            try
              sprintf "[%s]\\n" (Hashtbl.find mid_tbl nd)
            with
              Not_found -> ""
          in
          let tail =
            try
              let nd' = nmapping#find nd in
              sprintf "\\n->%a" ngps nd'
            with
              _ -> ""
          in
          head^(Otree.dot_label_of_node_ini nd)^tail
      else
        fun nd -> Otree.dot_label_of_node nd
    in
    let dot1 =
      if final then
        tree1#to_dot_initial ?mklab:(Some mklab) []
      else
        tree1#to_dot ?mklab:(Some mklab) []
    in
    let id_gen =
      let count = ref 0 in
      fun () ->
        let id = !count in
        incr count;
        id
    in
    let buf = Buffer.create 0 in
    Buffer.add_string buf "digraph D1 {\nordering=out;\n";
    Buffer.add_buffer buf dot1;

    self#iter_deletes
      (function
        | Delete(_, info, excluded) ->
            let buf0 =
              self#get_cluster id_gen "" del_bg del_fg tree1 info excluded
            in
            Buffer.add_buffer buf buf0

        | _ -> assert false
      );
    self#iter_moves
      (function
        | Move(_, _, (info1, excluded1), (_, _)) ->
            let lab = ""(*sprintf "MOVE:%a" MID.ps !mid*) in
            let buf0 =
              self#get_cluster id_gen lab mov_bg mov_fg tree1 info1 excluded1
            in
            Buffer.add_buffer buf buf0

        | _ -> assert false
      );
    self#iter_relabels
      (function
        | Relabel(movrel, (info1, _), (_, _)) ->
            let nd1 = Info.get_node info1 in
            Buffer.add_string buf
              (sprintf "%a [style=filled,fillcolor=\"%s\",fontcolor=\"%s\"];\n"
                 UID.rs nd1#uid
                 (if !movrel then movrel_bg else rel_bg)
                 (if !movrel then movrel_fg else rel_fg)
              )

        | _ -> assert false
      );

    Buffer.add_string buf "}\n";

    Buffer.output_buffer ch buf

  (* end of method dump_dot_ch1 *)

  method dump_dot_ch2
      ?(final=false)
      tree2
      (*tree1*)_
      (nmapping : 'node_t Node_mapping.c)
      ch
      =
    let mid_tbl = Hashtbl.create 0 in
    self#iter_moves
      (function
        | Move(mid, _, _, (info2, _)) ->
            let lab = sprintf "%a" MID.ps !mid in
            let nd2 = Info.get_node info2 in
            Hashtbl.add mid_tbl nd2 lab
        | _ -> assert false
      );

    let mklab =
      if final then
        fun nd ->
          let head =
            try
              sprintf "[%s]\\n" (Hashtbl.find mid_tbl nd)
            with
              Not_found -> ""
          in
          let tail =
            try
              let nd' = nmapping#inv_find nd in
              sprintf "\\n%a->" ngps nd'
            with
              _ -> ""
          in
          head^(Otree.dot_label_of_node_ini nd)^tail
      else
        fun nd -> Otree.dot_label_of_node nd
    in
    let dot2 =
      if final then
        tree2#to_dot_initial ?mklab:(Some mklab) []
      else
        tree2#to_dot ?mklab:(Some mklab) []
    in
    let id_gen =
      let count = ref 0 in
      fun () ->
        let id = !count in
        incr count;
        id
    in
    let buf = Buffer.create 0 in
    Buffer.add_string buf "digraph D2 {\nordering=out;\n";
    Buffer.add_buffer buf dot2;

    self#iter_inserts
      (function
        | Insert(_, info, excluded) ->
            let buf0 = self#get_cluster id_gen "" ins_bg ins_fg tree2 info excluded in
            Buffer.add_buffer buf buf0

        | _ -> assert false
      );
    self#iter_moves
      (function
        | Move(_, _, (_, _), (info2, excluded2)) ->
            let lab = ""(*sprintf "MOVE:%a" MID.ps !mid*) in
            let buf0 =
              self#get_cluster id_gen lab mov_bg mov_fg tree2 info2 excluded2
            in
            Buffer.add_buffer buf buf0

        | _ -> assert false
      );
    self#iter_relabels
      (function
        | Relabel(movrel, (_, _), (info2, _)) ->
            let nd2 = Info.get_node info2 in
            Buffer.add_string buf
              (sprintf "%a [style=filled,fillcolor=\"%s\",fontcolor=\"%s\"];\n"
                 UID.rs nd2#uid
                 (if !movrel then movrel_bg else rel_bg)
                 (if !movrel then movrel_fg else rel_fg)
              )

        | _ -> assert false
      );

    Buffer.add_string buf "}\n";

    Buffer.output_buffer ch buf

  (* end of method dump_dot_ch2 *)

  method dump_dot1 ?(final=false) fname (tree1 : 'tree_t) (tree2 : 'tree_t) (nmapping : 'node_t Node_mapping.c) =
    Xfile.dump fname (self#dump_dot_ch1 ~final tree1 tree2 nmapping)

  method dump_dot2 ?(final=false) fname (tree2 : 'tree_t) (tree1 : 'tree_t) (nmapping : 'node_t Node_mapping.c) =
    Xfile.dump fname (self#dump_dot_ch2 ~final tree2 tree1 nmapping)


  (* checks whether this edit seq is correct or not *)
  (* NB: this function modifies the trees in-place *)
  method check
      (tree1 : 'tree_t)
      (tree2 : 'tree_t)
      ((*nmapping*)_ : 'node_t Node_mapping.c)
      =
    begin %debug_block
      [%debug_log "checking result"];
      [%debug_log "%s" self#to_string]
    end;

    let normal_flag = ref true in

    let node_eq =
      if options#ignore_non_orig_relabel_flag && not options#weak_eq_flag then
        fun n1 n2 ->
          if not n1#data#is_named_orig && not n2#data#is_named_orig then
            n1#data#elem_name_for_delta = n2#data#elem_name_for_delta
          else
            match n1#data#orig_lab_opt, n2#data#orig_lab_opt with
            | Some o1, Some o2 -> o1 = o2
            | _ -> n1#data#eq n2#data
      else
        fun n1 n2 -> n1#data#eq n2#data
    in
    let tree_eq t1 t2 =
      let rec scan nds1 nds2 =
        match nds1, nds2 with
        | [], [] -> true
        | nd1::rest1, nd2::rest2 ->

            [%debug_log "%a - %a" nups nd1 nups nd2];

            (if node_eq nd1 nd2 then
              let cl1 = Array.to_list nd1#children in
              let cl2 = Array.to_list nd2#children in
              let sub = scan cl1 cl2 in
              sub
            else begin
              [%warn_log "%s != %s" (nd1#to_string) (nd2#to_string)];
              false
            end)
              &&
            (scan rest1 rest2)
        | nd::_, [] ->
            let _ = nd in
            [%warn_log "number of children mismatch: (>) %s [%s,...]"
              (nd#parent#to_string) (nd#to_string)];
            false

        | [], nd::_ ->
            let _ = nd in
            [%warn_log "number of children mismatch: (<) %s [%s,...]"
              (nd#parent#to_string) (nd#to_string)];
            false
      in
      scan [t1#root] [t2#root]
    in

    (* initializing trees *)
    if options#recover_orig_ast_flag then begin
      let _ = tree1#recover_true_children ~initial_only:false () in
      let _ = tree2#recover_true_children ~initial_only:false () in
      ()
    end;
    tree1#init;
    tree2#init;

    [%debug_log "after initialization:\nT1:\n%s\nT2:\n%s"
      tree1#to_string tree2#to_string];

    (* relabeling nodes in tree1 *)
    [%debug_log "relabeling nodes in tree1"];
    self#iter_relabels
      (function
        | Relabel(_, (info1, infos1), (info2, infos2)) ->
            let n1 = Info.get_node info1 in
            let n2 = Info.get_node info2 in
            let ns1 = List.map Info.get_node !infos1 in
            let ns2 = List.map Info.get_node !infos2 in

            (* do relabel *)
            let targetq = Queue.create() in
            begin
              try
                [%debug_log "adding relabel targets %a[%a]-%a[%a]" nups n1 nsps ns1 nups n2 nsps ns2];

                tree2#scan_cluster
                  (n2, ns2)
                  (fun nd -> Queue.add nd targetq);

                [%debug_log "relabeling %a-%a" nups n1 nups n2];

                tree1#scan_cluster (n1, ns1)
                  (fun nd ->
                    let nd' = Queue.take targetq in
                    let d = nd'#data in
                    if nd#data#equals d then begin
                      normal_flag := false;
                      [%warn_log "relabel: not a relabel: %a-%a" nups n1 nups n2];
                      [%warn_log "relabel: <%a> = <%a>" nps nd nps nd']
                    end;
                    nd#set_data d)
              with
                Queue.Empty ->
                  normal_flag := false;
                  [%warn_log "relabel failed: %a > %a" nups n1 nups n2];
            end;
            if not (Queue.is_empty targetq) then begin
              normal_flag := false;
              [%warn_log "relabel failed: %a < %a" nups n1 nups n2]
            end
        | _ -> assert false
      ); (* end of relabeling *)

    [%debug_log "before node deletion:\nT1:\n%s\nT2:\n%s"
      tree1#to_string tree2#to_string];

    let get_nodes infos = List.map (fun i -> Info.get_node i) infos in

    [%debug_log "deleting nodes from T1 and T2"];

    (* deleting nodes from tree1 and tree2 *)
    let deleted1 = Nodetbl.create 0 in (* node -> node list *)
    let deleted2 = Nodetbl.create 0 in (* node -> node list *)
    let upd tbl nd =
      let rec follow n =
        try
          let ns = Nodetbl.find tbl n in
          List.concat_map follow ns
        with Not_found -> [n]
      in
      follow nd
    in
    self#iter
      (function
        | Delete(_, info, infos) -> begin
            let nd = Info.get_node info in
            try
              let nds = get_nodes !infos in
              Nodetbl.add deleted1 nd nds;
              let upd_nds = upd deleted1 nd in

              [%debug_log "deleting (del) %a(pos=%d,parent=%a) [%a] -> [%a]"
                nups nd nd#pos nups nd#parent nsps nds nsps upd_nds];

              tree1#prune_cluster nd upd_nds
            with
              Not_found -> [%debug_log "already deleted: %a" nups nd]
          end
        | Insert(_, info, infos) -> begin
            let nd = Info.get_node info in
            try
              let nds = get_nodes !infos in
              Nodetbl.add deleted2 nd nds;
              let upd_nds = upd deleted2 nd in

              [%debug_log "deleting (ins) %a(pos=%d,parent=%a[%a]) [%a] -> [%a]"
                nups nd nd#pos nups nd#parent usps nd#parent#children_uids nsps nds nsps upd_nds];

              tree2#prune_cluster nd upd_nds
            with
              Not_found -> [%debug_log "already deleted: %a" nups nd]
        end
        | Move(mid, _, (info1, infos1), (info2, infos2)) ->
            let _ = mid in
            let nd1 = Info.get_node info1 in
            let nd2 = Info.get_node info2 in
            Nodetbl.add deleted1 nd1 (get_nodes !infos1);
            Nodetbl.add deleted2 nd2 (get_nodes !infos2);
            let nds1 = upd deleted1 nd1 in
            let nds2 = upd deleted2 nd2 in

            [%debug_log "deleting (mid:%a) %a(pos=%d,parent=%a) [%a] - %a(pos=%d,parent=%a) [%a]"
              MID.ps !mid
              nups nd1 nd1#pos nups nd1#parent nsps nds1
              nups nd2 nd2#pos nups nd2#parent nsps nds2];

            let q = Queue.create() in
            tree2#scan_cluster (nd2, nds2) (fun n -> Queue.add n q);
            tree1#scan_cluster (nd1, nds1)
              (fun n ->
                let n' = Queue.take q in
                if not (node_eq n n') then begin
                  normal_flag := false;
                  [%warn_log "move: <%a> != <%a>" nps n nps n']
                end
              );

            tree1#prune_cluster nd1 nds1;
            tree2#prune_cluster nd2 nds2

        | _ -> ()
      );

    tree1#init; tree2#init;

    [%debug_log "AFTER node deletion (before equality check):\nT1:\n%s\nT2:\n%s"
      tree1#to_string tree2#to_string];

    (* now tree1 should equals to tree2 *)
    let result = tree_eq tree1 tree2 && !normal_flag in

    result


  method remove_unmapped
      (tree1 : 'tree_t)
      (tree2 : 'tree_t)
      =
    tree1#init;
    tree2#init;

    let get_nodes infos = List.map (fun i -> Info.get_node i) infos in

    [%debug_log "deleting nodes from T1 and T2"];

    (* deleting nodes from tree1 and tree2 *)
    let deleted1 = Nodetbl.create 0 in (* node -> node list *)
    let deleted2 = Nodetbl.create 0 in (* node -> node list *)
    let upd tbl nd =
      let rec follow n =
        try
          let ns = Nodetbl.find tbl n in
          List.concat_map follow ns
        with Not_found -> [n]
      in
      follow nd
    in
    let deleted_nodes1 = ref [] in
    let deleted_nodes2 = ref [] in
    self#iter
      (function
        | Delete(_, info, infos) -> begin
            let nd = Info.get_node info in
            try
              Nodetbl.add deleted1 nd (get_nodes !infos);
              let nds = upd deleted1 nd in

              [%debug_log "deleting (del) %a(pos=%d,parent=%a) [%a]"
                nups nd nd#pos nups nd#parent nsps nds];

              tree1#prune_cluster nd nds;

              if (Info.get_size info) > options#dump_size_threshold then
                deleted_nodes1 := nd::!deleted_nodes1

            with
              Not_found -> [%debug_log "already deleted: %a" nups nd]
          end
        | Insert(_, info, infos) -> begin
            let nd = Info.get_node info in
            try
              Nodetbl.add deleted2 nd (get_nodes !infos);
              let nds = upd deleted2 nd in

              [%debug_log "deleting (ins) %a(pos=%d,parent=%a[%a]) [%a]"
                nups nd nd#pos nups nd#parent naps nd#parent#children nsps nds];

              tree2#prune_cluster nd nds;

              if (Info.get_size info) > options#dump_size_threshold then
                deleted_nodes2 := nd::!deleted_nodes2

            with
              Not_found -> [%debug_log "already deleted: %a" nups nd]
        end
        | _ -> ()
      );
    (!deleted_nodes1, !deleted_nodes2)
   (* end of method remove_unmapped *)


  method ungroup (tree1 : 'tree_t) (tree2 : 'tree_t)
      =
    [%debug_log "before ungrouping:\n%s" self#to_string];
    [%debug_log "ungrouping..."];

    (*let group_tbl = Hashtbl.create 0 in*)

    let gensubedits tree ?(whole=false) ?(exclude=[]) node =
      [%debug_log "node=%a%!" nups node];
      let res = ref [] in
      let rec doit nd =
        [%debug_log "nd=%a%!" nups nd];
        if not (List.memq nd exclude) then begin
          let ex =
            List.map
              Info.make
              (List.filter
                 (tree#is_initial_ancestor node)
                 exclude)
          in
          res := (Info.make nd, ex)::!res;
          Array.iter doit nd#initial_children
        end
      in
      if whole then
        doit node
      else
        Array.iter doit node#initial_children;
      !res
    in

    let process_delete_or_insert ed inf ex =

      [%debug_log "processing %s..." (to_string ed)];

      let edit_list = ref [] in
      let add_edit e = edit_list := e :: !edit_list in

      let nd = Info.get_node inf in

      if !ex = [] then begin
        self#remove_edit ed;
        match ed with
        | Delete _ ->
            List.iter
              (fun (i, e) ->
                let ed' = Delete(e = [], i, ref e) in
                (*tbl_add group_tbl ed ed';*)
                add_edit ed'
              ) (gensubedits tree1 ~whole:true nd)

        | Insert _ ->
            List.iter
              (fun (i, e) ->
                let ed' = Insert(e = [], i, ref e) in
                (*tbl_add group_tbl ed ed';*)
                add_edit ed'
              ) (gensubedits tree2 ~whole:true nd)

        | _ -> assert false

      end
      else begin
        let exnds = List.map Info.get_node !ex in
        let processed = ref [] in

        let tree =
          match ed with
          | Delete _ -> tree1
          | Insert _ -> tree2
          | _ -> assert false
        in

        let sz = tree#size_of_initial_cluster (nd, exnds) in
        [%debug_log "size of initial cluster: %d" sz];

        if sz > 1 then begin

          self#remove_edit ed;

          tree#scan_initial_cluster (nd, exnds)
            (fun n ->
              [%debug_log "n=%a" nups n];
              if
                not (List.exists (fun p -> tree#initial_subtree_mem p n) !processed) &&
                not (is_ghost_node n)
              then begin

                let new_info = Info.make n in
                let new_ex =
                  List.map
                    Info.make
                    (List.filter (tree#is_initial_ancestor n) exnds)
                in
                let whole = new_ex = [] in

                let new_ed =
                  match ed with
                  | Delete _ -> Delete(whole, new_info, ref new_ex)
                  | Insert _ -> Insert(whole, new_info, ref new_ex)
                  | _ -> assert false
                in
                (*tbl_add group_tbl ed new_ed;*)
                add_edit new_ed;

                if whole then begin
                  begin
                    match ed with
                    | Delete _ ->
                        List.iter
                          (fun (i, e) ->
                            let ed' = Delete(e = [], i, ref e) in
                            (*tbl_add group_tbl ed ed';*)
                            add_edit ed'
                          ) (gensubedits tree1 n)

                    | Insert _ ->
                        List.iter
                          (fun (i, e) ->
                            let ed' = Insert(e = [], i, ref e) in
                            (*tbl_add group_tbl ed ed';*)
                            add_edit ed'
                          ) (gensubedits tree2 n)

                    | _ -> assert false
                  end;
                  processed := n :: !processed
                end

              end
            )

        end

      end;
      !edit_list
    in (* end of func process_delete_or_insert *)


    let to_be_added = Xset.create 0 in
    let add_ed ed =
      [%debug_log "%s" (to_string ed)];
      Xset.add to_be_added ed
    in

    let process_move ed mid kind inf1 ex1 inf2 ex2 =

      [%debug_log "processing %s..." (to_string ed)];

      let nd1 = Info.get_node inf1 in
      let nd2 = Info.get_node inf2 in

      if !ex1 = [] && !ex2 = [] then begin
        self#remove_edit ed;
        List.iter2
          (fun (i1, e1) (i2, e2) ->
            let ed' = Move(mid, kind, (i1, ref e1), (i2, ref e2)) in
            (*tbl_add group_tbl ed ed';*)
            add_ed ed'
          ) (gensubedits tree1 ~whole:true nd1) (gensubedits tree2 ~whole:true nd2)
      end
      else begin
        let exnds1 = List.map Info.get_node !ex1 in
        let exnds2 = List.map Info.get_node !ex2 in

        [%debug_log "exnds1=[%a]" nsps exnds1];
        [%debug_log "exnds2=[%a]" nsps exnds2];

        let processed = ref [] in

        if tree1#size_of_initial_cluster (nd1, exnds1) > 1 then begin
          self#remove_edit ed;

          let nds1 = ref [] in
          let nds2 = ref [] in

          tree1#scan_initial_cluster (nd1, exnds1) (fun n1 -> nds1 := n1 :: !nds1);
          tree2#scan_initial_cluster (nd2, exnds2) (fun n2 -> nds2 := n2 :: !nds2);

          List.iter2
            (fun n1 n2 ->
              [%debug_log "n1=%a n2=%a" nups n1 nups n2];
              if
                not (List.exists (fun p -> tree1#initial_subtree_mem p n1) !processed) &&
                not (is_ghost_node n1)
              then begin

                let mk_inf tree n exnds =
                  let new_info = Info.make n in
                  let new_ex =
                    List.map
                      Info.make
                      (List.filter (tree#is_initial_ancestor n) exnds)
                  in
                  new_info, new_ex
                in

                let new_info1, new_ex1 = mk_inf tree1 n1 exnds1 in
                let new_info2, new_ex2 = mk_inf tree2 n2 exnds2 in

                let whole = new_ex1 = [] && new_ex2 = [] in

                let new_ed =
                  Move(mid, kind, (new_info1, ref new_ex1), (new_info2, ref new_ex2))
                in
                [%debug_log "adding move: mid=%a %a --> %a (whole=%B)%!" MID.ps !mid nups n1 nups n2 whole];

                (*tbl_add group_tbl ed new_ed;*)
                add_ed new_ed;

                if whole then begin
                  let se1 = gensubedits tree1 n1 in
                  let se2 = gensubedits tree2 n2 in
                  [%debug_log "number of subedits: %a->%d, %a->%d"
                    nups n1 (List.length se1) nups n2 (List.length se2)];
                  List.iter2
                    (fun (i1, e1) (i2, e2) ->
                      [%debug_log "adding move: mid=%a %a --> %a%!" MID.ps !mid nups n1 nups n2];
                      let ed' = Move(mid, kind, (i1, ref e1), (i2, ref e2)) in
                      (*tbl_add group_tbl ed ed';*)
                      add_ed ed'
                    ) se1 se2;
                  processed := n1 :: !processed
                end

              end
            ) !nds1 !nds2;

        end (* if tree1#size_of_initial_cluster (nd1, exnds1) > 1 *)
      end

    in (* end of func process_move *)

    let editll_to_be_added = ref [] in
    let add_editl el = editll_to_be_added := el :: !editll_to_be_added in
    self#iter
      (fun ed ->
        match ed with
        | Delete(_, inf, ex) -> add_editl (process_delete_or_insert ed inf ex)
        | Insert(_, inf, ex) -> add_editl (process_delete_or_insert ed inf ex)
        | Move(mid, kind, (inf1, ex1), (inf2, ex2)) -> process_move ed mid kind inf1 ex1 inf2 ex2
        | _ -> ()
      );
    List.iter (fun el -> List.iter self#add_edit el) !editll_to_be_added;

    Xset.iter
      (fun ed ->
        [%debug_log "adding %s" (to_string ed)];
        self#add_edit ed
      ) to_be_added;

    (*group_tbl*)
  (* end of method ungroup *)

  method private get_non_ghost_children node =
    let rec get nd =
      List.concat_map
        (fun n ->
          if is_ghost_node n then get n else [n]
        ) (Array.to_list nd#initial_children)
    in
    get node

  method cleanup_ghost (tree1 : 'tree_t) (tree2 : 'tree_t) =
    [%debug_log "cleaning up ghost..."];

    let is_ghost_info info = is_ghost_node (Info.get_node info) in
    let cleanup tree info ex =
      let rec proc_ex rt = function
        | [] -> []
        | inf::rest ->
            let nd = Info.get_node inf in
            let infos = proc_ex rt rest in
            if tree#is_initial_ancestor rt nd then
              if is_ghost_node nd then
                (List.map Info.make (self#get_non_ghost_children nd)) @ infos
              else
                inf :: infos
            else
              infos
      in
      let node = Info.get_node info in
      if is_ghost_node node then begin
        let nodes = self#get_non_ghost_children node in
        List.rev
          (List.fold_left
             (fun l n ->
               let new_ex = proc_ex n ex in
               let new_exnds = List.map Info.get_node new_ex in
               if List.memq n new_exnds then
                 l
               else
                 (Info.make n, new_ex)::l
             ) [] nodes)
      end
      else
        [info, proc_ex node ex]
    in

    let to_be_converted info ex =
      is_ghost_info info || List.exists is_ghost_info !ex
    in

    let eds_for_ghost = ref [] in
    let add ed = eds_for_ghost := ed :: !eds_for_ghost in

    self#filter
      (function
        | Delete(_, info, ex) ->
            let b = to_be_converted info ex in
            if b then begin
              List.iter
                (fun (i, e) ->
                  add (Delete(e = [], i, ref e)))
                (cleanup tree1 info !ex)
            end;
            not b

        | Insert(_, info, ex) ->
            let b = to_be_converted info ex in
            if b then begin
              List.iter
                (fun (i, e) -> add (Insert(e = [], i, ref e)))
                (cleanup tree2 info !ex)
            end;
            not b

        | Relabel(_, (info1, ex1), (info2, ex2)) ->
            let isw info = (Info.get_node info)#initial_nchildren = 0 in
            let b1 = to_be_converted info1 (ref []) in
            let b2 = to_be_converted info2 (ref []) in

            if b1 then
              add (Insert(isw info2, info2, ex2));

            if b2 then
              add (Delete(isw info1, info1, ex1));

            not (b1 || b2)

        | Move(mid, k, (info1, ex1), (info2, ex2)) ->
            let b1 = to_be_converted info1 ex1 in
            let b2 = to_be_converted info2 ex2 in
            if b1 || b2 then begin

              let q = Queue.create() in
              let nd1 = Info.get_node info1 in
              let nd2 = Info.get_node info2 in
              let nds1 = List.map Info.get_node !ex1 in
              let nds2 = List.map Info.get_node !ex2 in
              let mkxs n =
                List.map Info.make (self#get_non_ghost_children n)
              in
              tree2#scan_cluster (nd2, nds2) (fun n -> Queue.add n q);
              tree1#scan_cluster (nd1, nds1)
                (fun n ->
                  let n' = Queue.take q in
                  match is_ghost_node n, is_ghost_node n' with
                  | true, false -> begin
                      let xs' = mkxs n' in
                      add (Insert(xs' = [], Info.make n', ref xs'))
                  end
                  | false, true -> begin
                      let xs = mkxs n in
                      add (Delete(xs = [], Info.make n, ref xs))
                  end
                  | false, false -> begin
                      let xs = mkxs n in
                      let xs' = mkxs n' in
                      add (Move(mid, k,
                                (Info.make n, ref xs),
                                (Info.make n', ref xs')))
                  end
                  | true, true -> ()
                );

            end;
            not (b1 || b2)
      );
    List.iter self#add_edit !eds_for_ghost;
    [%debug_log "done."]



  method shrink_moves_rp (* shrink moves to improve SPSM (for move root pairs) *)
      (cenv : ('node_t, 'tree_t) Comparison.c)
      (tree1 : 'tree_t)
      (tree2 : 'tree_t)
      nmapping
      (move_region_tbl : move_region_tbl_t)
      =

    [%debug_log "nmapping:\n%s\n" nmapping#to_string];
    [%debug_log "nmapping (gindex):\n%s\n" nmapping#to_string_gid];

    let same_digest = _same_digest tree1 tree2 in

    let gen_cands tree tree' nmap nmap' mem_mov_nn mem_mov_n' mem_del_or_ins is_mov nd nd0 =

      [%debug_log "nd:%a nd0:%a" nps nd nps nd0];

      let cands = ref [] in

      Array.iter
        (fun cnd ->

          [%debug_log "cnd:%a" nups cnd];

          try
            let cnd' = nmap cnd in
            if not (mem_mov_nn cnd cnd') then
              let nd' = cnd'#initial_parent in

              [%debug_log "nd':%a" nups nd'];

              let cond0 =
                not (List.memq nd' !cands) &&
                (nd'#data#eq nd#data(* ||
                  (try not nd'#initial_parent#data#is_boundary with _ -> false) &&
                  (try not nd#initial_parent#data#is_boundary with _ -> false) &&
                  not nd'#data#is_named_orig && not nd#data#is_named_orig &&
                  nd'#data#anonymized_label = nd#data#anonymized_label*)
                ) &&
                (mem_del_or_ins nd' || (mem_mov_n' nd' && nd0 != nd')) &&
                (not (is_mov nd nd'))
              in

              [%debug_log "not (List.memq nd' !cands) --> %B" (not (List.memq nd' !cands))];
              [%debug_log "nd'#data#eq nd#data --> %B"
                (nd'#data#eq nd#data(* ||
                not nd'#data#is_named_orig && not nd#data#is_named_orig &&
                nd'#data#anonymized_label = nd#data#anonymized_label*))];
              [%debug_log "mem_del_or_ins uid' || (mem_mov_u' uid' && uid0 <> uid') --> %B"
                (mem_del_or_ins nd' || (mem_mov_n' nd' && nd0 != nd'))];
              [%debug_log "not (is_mov nd nd') --> %B" (not (is_mov nd nd'))];
              [%debug_log "cnd:%a --> cond0:%B" nups cnd cond0];

              if cond0 then
                let cond1 =
                  try
                    tree#fast_scan_whole_initial_subtree nd
                      (fun n ->
                        if n != nd then
                          try
                            let n' = nmap n in
                            if not (mem_mov_nn n n') then
                              if not (tree'#is_initial_ancestor nd' n') then
                                raise Exit
                          with
                            Not_found -> ()
                      );
                    true
                  with
                    Exit -> false
                in
                [%debug_log "cnd:%a --> cond1:%B" nups cnd cond1];

                if cond1 then begin
                  [%debug_log "adding %a" nps nd'];
                  cands := nd' :: !cands
                end
          with
            _ -> ()
        ) nd#initial_children;


      (* candidates from stable parents *)
      let extra_node_pair_tbl = Hashtbl.create 0 in

      if !cands = [] then begin
        try
          let pnd = nd#initial_parent in
          [%debug_log "pnd: %a" nps pnd];
          if
            not nd#data#is_op &&
            not pnd#data#is_sequence && not pnd#data#is_op
          then begin
            try
              let pnd' = nmap pnd in
              if not (mem_mov_nn pnd pnd') then begin
                if
                  (not (pnd'#data#is_named_orig && pnd#data#is_named_orig) || pnd'#data#eq pnd#data) &&
                  (
                   pnd'#data#is_named_orig && pnd#data#is_named_orig ||
                   pnd#data#_anonymized_label = pnd'#data#_anonymized_label
                  )
                then begin
                  let nd' = pnd'#initial_children.(nd#initial_pos) in
                  [%debug_log "nd': %a" nps nd'];
                  let cond0 =
                    not (List.memq nd' !cands) &&
                    (nd'#data#eq nd#data) &&
                    (mem_del_or_ins nd' || (mem_mov_n' nd' && nd0 != nd'))(* &&
                    try
                      let n = (nmap' nd') in
                      [%debug_log "n=%a" nps n];
                      not (is_mov n nd') || not (same_digest n nd')
                    with _
                      -> true*)
                  in
                  [%debug_log "pnd:%a cond0=%B" nups pnd cond0];
                  if cond0 then begin

                    let is_mapped map n =
                      try
                        let _ = map n in
                        true
                      with
                        Not_found -> false
                    in

                    let stable_node_pairs = ref [] in

                    let cond1 =
                      let stable_count = ref 0 in
                      try
                        tree#fast_scan_whole_initial_subtree nd
                          (fun n ->
                            if n != nd then
                              try
                                let n' = nmap n in
                                if not (mem_mov_nn n n') then
                                  if
                                    n#data#eq n'#data &&
                                    tree'#is_initial_ancestor nd' n'
                                  then begin
                                    [%debug_log "stable: %a - %a" nps n nps n'];
                                    stable_node_pairs := (n, n') :: !stable_node_pairs;
                                    incr stable_count
                                  end
                                  else
                                    raise Exit
                              with
                                Not_found -> ()
                          );
                        !stable_count > 0
                      with
                        Exit -> false
                    in
                    [%debug_log "pnd:%a cond1=%B" nups pnd cond1];

                    let deferred_ops = ref [] in

                    let cond2 () =
                      let b =
                        not nd#data#is_sequence &&
                        nd#initial_nchildren = nd'#initial_nchildren &&
                        let ca' = nd'#initial_children in
                        let flag = ref false in
                        Array.iter
                          (fun c ->
                            let c' = ca'.(c#initial_pos) in
                            let b =
                              _same_digest tree tree' ~leaf_comparison:false c c' ||
                              c#initial_nchildren = 0 && c'#initial_nchildren = 0 &&
                              c#data#is_named_orig && c'#data#is_named_orig &&
                              c#data#get_orig_name = c'#data#get_orig_name
                            in
                            if b then begin
                              flag := true;
                              deferred_ops :=
                                (fun () ->
                                  [%debug_log "extra: %a - %a" nps c nps c'];
                                  tbl_add_s extra_node_pair_tbl nd' (c, c')
                                ) :: !deferred_ops
                            end
                          ) nd#initial_children;
                        !flag
                      in
                      [%debug_log "%B" b];
                      b
                    in

                    let cond3 map n =
                      not n#data#is_boundary &&
                      let b =
                        try
                          let bn = get_bn n in
                          let moveon x = x != bn in
                          let x =
                            Misc.get_p_ancestor ~moveon
                              (fun a ->
                                a#data#eq n#data && not (is_mapped map a)
                              ) n
                          in
                          let _ = x in
                          [%debug_log "found: %a" nps x];
                          false
                        with
                          _ -> true
                      in
                      [%debug_log "%a -> %B" nps n b];
                      b
                    in

                    let rec check_children tbl n n' =
                      let mapchk x x' =
                        let b =
                          try
                            let x_ = nmap x in
                            let x_' = nmap' x' in
                            [%debug_log "x_=%a x_'=%a" nps x_ nps x_'];
                            not (x_#data#subtree_equals x_'#data)
                          with
                            _ -> true
                        in
                        [%debug_log "%a %a -> %B" nps x nps x' b];
                        b
                      in
                      if
                        n#initial_nchildren = 1 && n'#initial_nchildren = 1
                      then begin
                        let c = n#initial_children.(0) in
                        let c' = n'#initial_children.(0) in
                        if
                          (*c#data#_anonymized_label = c'#data#_anonymized_label &&*)
                          c#data#eq c'#data &&
                          not (try nmap c == c' with _ -> false) &&
                          mapchk c c'
                        then begin
                          [%debug_log "extra: %a - %a" nps c nps c'];
                          tbl_add_s tbl nd' (c, c')
                        end;
                        check_children tbl c c'
                      end
                      else if
                        n#data#eq n'#data &&
                        (*not n#data#is_sequence && not n'#data#is_sequence &&*)
                        n#initial_nchildren = n'#initial_nchildren
                      then begin
                        Array.iter2
                          (fun c c' ->
                            if
                              (*c#data#_anonymized_label = c'#data#_anonymized_label &&*)
                              c#data#eq c'#data &&
                              not (try nmap c == c' with _ -> false) &&
                              mapchk c c'
                            then begin
                              [%debug_log "extra: %a - %a" nps c nps c'];
                              tbl_add_s tbl nd' (c, c')
                            end;
                            check_children tbl c c'
                          ) n#initial_children n'#initial_children
                      end
                      else if
                        n#data#eq n'#data && n#data#is_sequence && n'#data#is_sequence
                      then begin
                        [%debug_log "abort: %a - %a" nps n nps n'];
                        raise Abort
                      end
                    in

                    let check_matched_subtrees ?(spairs=[]) r r' =
                      [%debug_log "r=%a r'=%a" nps r nps r'];
                      let npairs = ref spairs in
                      let add ?(parent_only=false) x x' =
                        [%debug_log "extra: %a - %a" nps x nps x'];
                        let npair = x, x' in
                        if not parent_only then begin
                          npairs := npair :: !npairs;
                          tbl_add_s extra_node_pair_tbl nd' npair
                        end;
                        try
                          let px = x#initial_parent in
                          let px' = x'#initial_parent in
                          if
                            (*px#initial_nchildren = 1 && px'#initial_nchildren = 1 &&*)
                            px != r && px' != r' &&
                            px#data#eq px'#data
                          then begin
                            [%debug_log "another extra: %a - %a" nps px nps px'];
                            let npair = px, px' in
                            npairs := npair :: !npairs;
                            tbl_add_s extra_node_pair_tbl nd' npair
                          end
                        with _ -> ()
                      in
                      List.iter (fun (x, x') -> add ~parent_only:true x x') spairs;

                      tree#(*fast_rev_scan_whole_initial_subtree*)fast_scan_whole_initial_subtree r
                        (fun n ->
                          [%debug_log "n=%a" nps n];
                          match n#data#_digest with
                          | None -> ()
                          | Some d -> begin
                              [%debug_log "d=%s" (Xhash.to_hex d)];
                              try
                                match cenv#multiple_subtree_matches#find d with
                                | [], _, _ | _, [], _ -> ()
                                | _l, _l', _ -> begin
                                    let rev = tree#mem_uid (fst (List.hd _l'))#uid in
                                    let l =
                                      List.filter (fun (x, _) -> tree#is_initial_ancestor r x)
                                        (if rev then _l' else _l)
                                    in
                                    let l' =
                                      List.filter (fun (x', _) -> tree'#is_initial_ancestor r' x')
                                        (if rev then _l else _l')
                                    in
                                    match l, l' with
                                    | [x, _], [x', _] -> begin
                                        [%debug_log "x=%a x'=%a" nps x nps x'];
                                        let is_crossing = Node_mapping.is_crossing x x' in
                                        let is_incompat =
                                          Node_mapping.is_incompatible tree tree' x x'
                                        in
                                        if
                                          List.mem (x, x') spairs ||
                                          not
                                            (List.exists
                                               (fun (y, y') -> is_crossing y y' || is_incompat y y')
                                               !npairs)
                                        then
                                          add x x'
                                    end
                                    | _ -> ()
                                end
                              with _ -> ()
                          end
                        )
                    in

                    if (cond1 || cond2()) && cond3 nmap' nd' then begin
                      let tbl = Hashtbl.create 0 in
                      try
                        check_children tbl nd nd';
                        List.iter (fun f -> f()) !deferred_ops;
                        Hashtbl.iter
                          (fun k vs ->
                            Xset.iter
                              (fun v ->
                                begin %debug_block
                                  let x1, x2 = v in
                                  [%debug_log "extra: %a - %a" nps x1 nps x2]
                                end;
                                tbl_add_s extra_node_pair_tbl k v
                              ) vs
                          ) tbl;
                        check_matched_subtrees ~spairs:!stable_node_pairs nd nd';
                        [%debug_log "!!!!!!!! adding %a (nd: %a)" nps nd' nps nd];
                        cands := nd' :: !cands
                      with
                        Abort -> ()
                    end

                  end
                end
              end
            with
              Not_found -> ()
          end
        with
          _ -> ()
      end;
      (* candidates from stable parents *)

      !cands, extra_node_pair_tbl
    in (* gen_cands *)

    let move_region_list =
      List.fast_sort
        (fun (_, _, gi, _, _) (_, _, gi', _, _) -> Stdlib.compare gi gi')
        (Hashtbl.fold
           (fun mid (lgi1, gi1, lgi2, gi2) l ->
             (mid, lgi1, gi1, lgi2, gi2) :: l
           ) move_region_tbl [])
    in

    let removed_move_tbl = Hashtbl.create 0 in

    List.iter
      (fun (mid, lgi1, gi1, lgi2, gi2) ->
        let _ = mid in

        let nd1 = tree1#search_node_by_gindex gi1 in
        let nd2 = tree2#search_node_by_gindex gi2 in

        (*if nmapping#is_locked_mapping nd1 nd2 then begin
          [%debug_log "!!!!!!!! locked mapping: %a-%a" nups nd1 nups nd2];
        end
        else*)

        let l1 = gi1 - lgi1 in
        let l2 = gi2 - lgi2 in

        [%debug_log "checking root pairs of %a (%a-%a) [%a]-[%a] %a-%a [%a:%a(%d)]-[%a:%a(%d)]..."
          MID.ps mid nups nd1 nups nd2 locps nd1 locps nd2 labps nd1 labps nd2
          gps lgi1 gps gi1 (l1+1) gps lgi2 gps gi2 (l2+1)];

        let moveon =
          let b =
          if same_digest ~digest_for_all:true nd1 nd2 then begin
            assert (l1 = l2);
            let rec loop i =
              if i > l1 then
                false
              else
                let n1 = tree1#search_node_by_gindex (lgi1 + i) in
                let n2 = tree2#search_node_by_gindex (lgi2 + i) in
                if not (nmapping#has_mapping n1 n2) then
                  true
                else
                  loop (i + 1)
            in
            loop 0
          end
          else
            true
          in
          [%debug_log "%B" b];
          b
        in

        if moveon then begin

          let is_mov1 n1 n2 = self#is_crossing_with_untouched nmapping n1 n2 in
          let is_mov2 n2 n1 = self#is_crossing_with_untouched nmapping n1 n2 in

          let node_pairs = ref [] in

          let nd1x, nd2x = ref nd1, ref nd2 in

          let cands01, cands02 = ref [], ref [] in

          let extra_node_pair_tbl01 = ref (Hashtbl.create 0) in
          let extra_node_pair_tbl02 = ref (Hashtbl.create 0) in

          let lv = ref 0 in

          begin
            try
              while true do
                let _cands01, _extra_node_pair_tbl01 =
                  gen_cands tree2 tree1 nmapping#inv_find nmapping#find
                    self#mem_mov21 self#mem_mov1 self#mem_del is_mov2 !nd2x !nd1x
                in
                cands01 := _cands01;
                extra_node_pair_tbl01 := _extra_node_pair_tbl01;

                let _cands02, _extra_node_pair_tbl02 =
                  gen_cands tree1 tree2 nmapping#find nmapping#inv_find
                    self#mem_mov12 self#mem_mov2 self#mem_ins is_mov1 !nd1x !nd2x
                in
                cands02 := _cands02;
                extra_node_pair_tbl02 := _extra_node_pair_tbl02;

                [%debug_log "[%d] cands01(%a): [%a]" !lv nups !nd2x nsps !cands01];
                [%debug_log "[%d] cands02(%a): [%a]" !lv nups !nd1x nsps !cands02];

                if !cands01 <> [] || !cands02 <> [] then begin
                  node_pairs := (!nd1x, !nd2x) :: !node_pairs;
                  raise Exit
                end;

                [%debug_log "nd1x=%a(%d) nd2x=%a(%d)"
                  nups !nd1x !nd1x#initial_nchildren nups !nd2x !nd2x#initial_nchildren];

                if (!nd1x)#initial_nchildren = 1 && (!nd2x)#initial_nchildren = 1 then begin
                  let nx1 = (!nd1x)#initial_children.(0) in
                  let nx2 = (!nd2x)#initial_children.(0) in
                  if self#mem_mov12 nx1 nx2 then begin
                    node_pairs := (!nd1x, !nd2x) :: !node_pairs;
                    nd1x := nx1;
                    nd2x := nx2;
                  end
                  else
                    raise Exit
                end
                else
                  raise Exit;

                incr lv
              done
            with
              Exit -> ()
          end;

          let remove_edit ?(from_parent=false) e =
            self#remove_edit e;
            if from_parent then begin
              match e with
              | Move(mid, _, _, _) -> tbl_add removed_move_tbl !mid e
              | _ -> ()
            end
          in

          let remove_orig ?(from_parent=false) () =
            List.iter
              (fun (n1, n2) ->
                [%debug_log "%a-%a" nups n1 nups n2];

                let es1 = self#find1 n1 in
                List.iter (remove_edit ~from_parent) es1;

                let es2 = self#find2 n2 in
                List.iter (remove_edit ~from_parent) es2;

                ignore (nmapping#remove n1 n2)

              ) !node_pairs
          in

          let check1 n1 =
            let b =
              let pn1 = ref n1 in
              try
                List.iter
                  (fun (_, n2) ->
                    if self#is_crossing_with_untouched nmapping !pn1 n2 then
                      raise Exit;
                    pn1 := (!pn1)#initial_parent
                  ) !node_pairs;
                true
              with
                Exit -> false
            in
            [%debug_log "%a --> %B" nups n1 b];
            b
          in

          let check2 n2 =
            let b =
              let pn2 = ref n2 in
              try
                List.iter
                  (fun (n1, _) ->
                    if self#is_crossing_with_untouched nmapping n1 !pn2 then
                      raise Exit;
                    pn2 := (!pn2)#initial_parent
                  ) !node_pairs;
                true
              with
                Exit -> false
            in
            [%debug_log "%a --> %B" nups n2 b];
            b
          in

          let handle_extra ?(from_parent=false) r1 r2 =
            [%debug_log "%a-%a" nups r1 nups r2];
            let handle n1 n2 =
              [%debug_log "%a-%a" nups n1 nups n2];

              if self#mem_del n1 then
                remove_edit ~from_parent (self#find_del n1)
              else if self#mem_mov1 n1 then begin
                let n1' = nmapping#find n1 in
                [%debug_log "n1=%a n1'=%a" nups n1 nups n1'];
                List.iter (remove_edit ~from_parent) (self#find12 n1 n1');
                let _ = nmapping#remove n1 n1' in
                self#add_edit (make_insert n1')
              end;

              if self#mem_ins n2 then
                remove_edit ~from_parent (self#find_ins n2)
              else if self#mem_mov2 n2 then begin
                let n2' = nmapping#inv_find n2 in
                [%debug_log "n2'=%a n2=%a" nups n2' nups n2];
                List.iter (remove_edit ~from_parent) (self#find12 n2' n2);
                let _ = nmapping#remove n2' n2 in
                self#add_edit (make_delete n2')
              end;

              let conflict1, conflict2 = nmapping#add_unsettled n1 n2 in
              begin
                match conflict1 with
                | Some n1 -> begin
                    [%debug_log "n1=%a" nups n1];
                    List.iter (remove_edit ~from_parent) (self#find1 n1);
                    self#add_edit (make_delete n1)
                end
                | _ -> ()
              end;
              begin
                match conflict2 with
                | Some n2 -> begin
                    [%debug_log "n2=%a" nups n2];
                    List.iter (remove_edit ~from_parent) (self#find2 n2);
                    self#add_edit (make_insert n2)
                end
                | _ -> ()
              end;

              if not (n1#data#eq n2#data) then
                self#add_edit (make_relabel n1 n2)
            in
            let nl1 = ref [] in
            let nl2 = ref [] in
            let ncl1 = ref [] in
            let ncl2 = ref [] in
            let add nl ncl n = nl := n :: !nl; ncl := n#initial_nchildren :: !ncl in
            tree1#fast_scan_whole_initial_subtree r1 (add nl1 ncl1);
            tree2#fast_scan_whole_initial_subtree r2 (add nl2 ncl2);
            if List.length !nl1 = List.length !nl2 && !ncl1 = !ncl2 then begin
              List.iter2 handle !nl1 !nl2
            end
            else begin
              handle r1 r2
            end
          in

          let node_pair_set_to_list s =
            List.fast_sort
              (fun x0 x1 -> Stdlib.compare (fst x1)#gindex (fst x0)#gindex)
              (Xset.to_list s)
          in

          let handle1 ?(from_parent=false) n1 =
            [%debug_log "n1:%a" nups n1];
            let pn1 = ref n1 in
            List.iter
              (fun (_, n2) ->
                if self#mem_del !pn1 then begin
                  [%debug_log "%a -> del" nups !pn1];
                  remove_edit ~from_parent (self#find_del !pn1)
                end
                else if self#mem_mov1 !pn1 then begin
                  [%debug_log "%a -> mov1" nups !pn1];
                  let pn1' = nmapping#find !pn1 in
                  List.iter (remove_edit ~from_parent) (self#find12 !pn1 pn1');
                  let _ = nmapping#remove !pn1 pn1' in
                  self#add_edit (make_insert pn1')
                end;
                ignore (nmapping#add_unsettled !pn1 n2);

                if not ((!pn1)#data#eq n2#data) && not (self#mem_rel12 !pn1 n2) then
                  self#add_edit (make_relabel !pn1 n2);

                pn1 := (!pn1)#initial_parent;
              ) !node_pairs;
            try
              List.iter
                (fun (n2, n1) -> handle_extra ~from_parent n1 n2)
                (node_pair_set_to_list (Hashtbl.find !extra_node_pair_tbl01 n1))
            with
              Not_found -> ()
          in

          let handle2 ?(from_parent=false) n2 =
            [%debug_log "n2:%a" nups n2];
            let pn2 = ref n2 in
            List.iter
              (fun (n1, _) ->
                if self#mem_ins !pn2 then begin
                  [%debug_log "%a -> ins" nups !pn2];
                  remove_edit ~from_parent (self#find_ins !pn2)
                end
                else if self#mem_mov2 !pn2 then begin
                  [%debug_log "%a -> mov2" nups !pn2];
                  let pn2' = nmapping#inv_find !pn2 in
                  List.iter (remove_edit ~from_parent) (self#find12 pn2' !pn2);
                  let _ = nmapping#remove pn2' !pn2 in
                  self#add_edit (make_delete pn2')
                end;
                ignore (nmapping#add_unsettled n1 !pn2);

                if not (n1#data#eq (!pn2)#data) && not (self#mem_rel12 n1 !pn2) then
                  self#add_edit (make_relabel n1 !pn2);

                pn2 := (!pn2)#initial_parent;
              ) !node_pairs;
            try
              List.iter
                (fun (n1, n2) -> handle_extra ~from_parent n1 n2)
                (node_pair_set_to_list (Hashtbl.find !extra_node_pair_tbl02 n2))
            with
              Not_found -> ()
          in

          cands01 := List.filter check1 !cands01;
          cands02 := List.filter check2 !cands02;

          match !cands01, !cands02 with
          | [nd1'], [nd2'] -> begin
              let from_parent =
                Hashtbl.mem !extra_node_pair_tbl01 nd1' ||
                Hashtbl.mem !extra_node_pair_tbl02 nd2'
              in
              remove_orig ~from_parent ();
              handle1 ~from_parent nd1';
              handle2 ~from_parent nd2'
          end
          | [nd1'], [] -> begin
              let from_parent = Hashtbl.mem !extra_node_pair_tbl01 nd1' in
              remove_orig ~from_parent ();
              handle1 ~from_parent nd1';
              List.iter
                (fun (n1, _) ->
                  if not (nmapping#mem_dom n1) then begin
                    [%debug_log "making del: %a" nups n1];
                    self#add_edit (make_delete n1)
                  end
                ) !node_pairs
          end
          | [], [nd2'] -> begin
              let from_parent = Hashtbl.mem !extra_node_pair_tbl02 nd2' in
              remove_orig ~from_parent ();
              handle2 ~from_parent nd2';
              List.iter
                (fun (_, n2) ->
                  if not (nmapping#mem_cod n2) then begin
                    [%debug_log "making ins: %a" nups n2];
                    self#add_edit (make_insert n2)
                  end
                ) !node_pairs
          end
          | _ -> ()

        end
      ) move_region_list;
    removed_move_tbl
    (* end of method shrink_moves_rp *)


  method shrink_moves (* shrink moves to improve SPSM *)
      (cenv : ('node_t, 'tree_t) Comparison.c)
      (tree1 : 'tree_t)
      (tree2 : 'tree_t)
      (nmapping : 'node_t Node_mapping.c)
      (move_region_tbl : move_region_tbl_t)
      (removed_move_tbl : (MID.t, 'node_t t list) Hashtbl.t)
      =

    let make_subtree_copy1 =
      (tree1#make_subtree_copy : ?find_hook:('node_t -> 'node_t -> unit) -> 'node_t -> 'tree_t)
    in
    let make_subtree_copy2 = tree2#make_subtree_copy in

    let same_digest = _same_digest tree1 tree2 in

    let move_root_tbl = Hashtbl.create 0 in (* mid -> root node pair list *)

    self#iter_moves
      (function
        | Move(mid, _, (i1, _), (i2, _)) -> begin
            let n1 = Info.get_node i1 in
            let n2 = Info.get_node i2 in
            [%debug_log "mid:%a %a-%a" MID.ps !mid nups n1 nups n2];
            if not (self#mem_rel12 n1 n2) (* && !k <> Mpermutation *) then begin

              [%debug_log "digests: %a(%s) %a(%s)" nups n1 n1#data#_digest_string nups n2 n2#data#_digest_string];

              let digest_for_leaf = n1#data#has_non_trivial_value || n1#data#is_named in

              if same_digest ~digest_for_leaf n1 n2 then begin
                let gi1, gi2 = n1#gindex, n2#gindex in
                let lgi1 = (tree1#initial_leftmost n1)#gindex in
                let lgi2 = (tree2#initial_leftmost n2)#gindex in
                try
                  let add_ok = ref true in
                  let pairs =
                    List.filter
                      (fun (cand1, cand2) ->
                        let cgi1, cgi2 = cand1#gindex, cand2#gindex in
                        let clgi1 = (tree1#initial_leftmost cand1)#gindex in
                        let clgi2 = (tree2#initial_leftmost cand2)#gindex in

                        if clgi1 <= gi1 && gi1 < cgi1 && clgi2 <= gi2 && gi2 < cgi2 then
                          add_ok := false;

                        let b = lgi1 <= cgi1 && cgi1 < gi1 && lgi2 <= cgi2 && cgi2 < gi2 in
                        not b
                      ) (Hashtbl.find move_root_tbl !mid)
                  in
                  [%debug_log "add_ok=%B" !add_ok];
                  let pairs' =
                    if !add_ok then
                      (n1, n2)::pairs
                    else
                      pairs
                  in
                  Hashtbl.replace move_root_tbl !mid pairs'

                with
                  Not_found ->
                    [%debug_log "%a --> %a-%a" MID.ps !mid nups n1 nups n2];

                    Hashtbl.add move_root_tbl !mid [n1, n2]
              end

            end (* if not (self#mem_rel12 u1 u2) *)
        end
        | _ -> assert false
      );

    begin %debug_block
      [%debug_log "move_root_tbl:"];
      Hashtbl.iter
        (fun mid pairs ->
          List.iter
            (fun (nd1, nd2) ->
              [%debug_log "%a -> %a-%a (%a-%a)" MID.ps mid nups nd1 nups nd2 ngps nd1 ngps nd2]
            ) pairs
        ) move_root_tbl
    end;

    let rec find_stably_mapped_ancestor tree nmap find nd =
      try
        let pnd = nd#initial_parent in
        try
          let pnd' = nmap pnd in
          match find pnd pnd' with
          | [] | [Relabel _] -> pnd, pnd'
          | _ -> find_stably_mapped_ancestor tree nmap find pnd (* raise Not_found *)
        with
          Not_found -> find_stably_mapped_ancestor tree nmap find pnd (* raise Not_found *)
      with
        Otree.Parent_not_found _ -> raise Not_found
    in

    let contain_stably_mapped tree root nmap find =
      try
        tree#fast_scan_whole_initial_subtree root
          (fun n ->
            try
              let n' = nmap n in
              match find n n' with
              | [] | [Relabel _] -> raise Found
              | _ -> ()
            with
              Not_found -> ()
          );
        false
      with
        Found -> true
    in

    let full_tree_matcher t1 t2 =
      let _, m, _ = Treediff.find t1 t2 in
      List.filter
        (fun (nd1, nd2) ->
          nd1#data#eq nd2#data
        )
        (List.map
           (fun (i, j) ->
             tree1#search_node_by_gindex (t1#get i)#gindex,
             tree2#search_node_by_gindex (t2#get j)#gindex
           ) m)
    in
    let fast_tree_matcher t1 t2 =
      let matches = ref [] in
      let rec scan (nd1, nd2) =
        if nd1#data#eq nd2#data then
          matches := (nd1, nd2)::!matches;
        let c1, c2 = nd1#children, nd2#children in
        let mk nd = nd#data#_label in
        let cdat1 = Array.map mk c1 in
        let cdat2 = Array.map mk c2 in
        let mat, rel, _, _ = Adiff.adiff cdat1 cdat2 in
        List.iter
          scan
          (List.map
             (fun (i1, i2) ->
               try
                 c1.(i1), c2.(i2)
               with Invalid_argument _ -> assert false
             ) (mat @ rel))
      in
      scan (t1#root, t2#root);
      List.map
        (fun (n1, n2) ->
          tree1#search_node_by_gindex n1#gindex, tree2#search_node_by_gindex n2#gindex
        ) !matches
    in
    let tree_matcher t1 t2 =
(*
      begin %debug_block
        [%debug_log "t1:"];
        Printf.printf "%s\n" t1#to_string;
        [%debug_log "t2:"];
        Printf.printf "%s\n" t2#to_string
      end;
*)
      if t1#size > options#match_algo_threshold || t2#size > options#match_algo_threshold then
        fast_tree_matcher t1 t2
      else
        full_tree_matcher t1 t2
    in

    let nodes_to_be_excluded = Xset.create 0 in

    let label_find tree an nd =
      [%debug_log "finding %s edited below %a" nd#data#label nups an];
      let cands = ref [] in
      let dcands = ref [] in
      let acands = ref [] in
      let lab = nd#data#_label in
      let alab = nd#data#_anonymized_label in
      tree#preorder_scan_whole_initial_subtree an
        (fun n ->
          if n != an && not (Xset.mem nodes_to_be_excluded n) then

            if n#data#_label = lab then begin

              if _same_digest tree tree ~digest_for_leaf:true nd n && nd#data#weight > 1 then begin
                [%debug_log "digest match: %a-%a (weight=%d)" nups n nups nd nd#data#weight];
                dcands := n :: !dcands
              end;

              if
                self#mem_del n || self#mem_ins n ||
                self#mem_mov1 n || self#mem_mov2 n ||
                self#mem_rel1 n || self#mem_rel2 n
              then begin
                cands := n :: !cands;
                acands := n :: !acands
              end;
(*
              [%debug_log "dcands: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" !dcands)];
              [%debug_log "cands: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" !cands)];
              [%debug_log "acands: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" !acands)];
*)
            end
            else if n#data#_anonymized_label = alab then begin

              if _same_digest tree tree ~digest_for_leaf:true nd n && nd#data#weight > 1 then begin
                [%debug_log "digest match: %a-%a (weight=%d)" nups n nups nd nd#data#weight];
                dcands := n :: !dcands
              end;

              if
                self#mem_del n || self#mem_ins n ||
                self#mem_mov1 n || self#mem_mov2 n ||
                self#mem_rel1 n || self#mem_rel2 n
              then
                acands := n :: !acands;
(*
              [%debug_log "dcands: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" !dcands)];
              [%debug_log "cands: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" !cands)];
              [%debug_log "acands: [%s]" (Xlist.to_string (fun n -> UID.to_string n#uid) ";" !acands)];
*)
            end

        );
      match !cands with
      | [] -> begin
          if !acands = [] then
            !dcands <> [], !dcands
          else
            false, !acands
      end
      | _ -> false, !cands
    in (* label_find *)

    let is_crossing = Node_mapping.is_crossing in
    (*let is_incompatible = Node_mapping.is_incompatible tree1 tree2 in*)

    [%debug_log "-----"];

    let cand_tbl = Hashtbl.create 0 in

    Hashtbl.iter
      (fun mid pairs ->
        [%debug_log "* checking move %a..." MID.ps mid];

        let root_pair_opt =
          List.fold_left
            (fun pair_opt mov ->
              match mov with
              | Move(_, _, (info1, _), (info2, _)) -> begin
                  [%debug_log "removed move: %s" (to_string mov)];
                  let n1 = Info.get_node info1 in
                  let n2 = Info.get_node info2 in
                  Xset.add nodes_to_be_excluded n1;
                  Xset.add nodes_to_be_excluded n2;
                  match pair_opt with
                  | Some (_n1, _n2) -> begin
                      if tree1#is_initial_ancestor n1 _n1 && tree2#is_initial_ancestor n2 _n2 then
                        Some (n1, n2)
                      else
                        pair_opt
                  end
                  | None -> Some (n1, n2)
              end
              | _ -> assert false
            ) None (try Hashtbl.find removed_move_tbl mid with _ -> [])
        in

        List.iter
          (fun (nd1, nd2) ->

            [%debug_log "  move %a-%a:" nups nd1 nups nd2];

            let nd1, nd2 =
              match root_pair_opt with
              | Some (n1, n2) -> begin
                  if tree1#is_initial_ancestor n1 nd1 && tree2#is_initial_ancestor n2 nd2 then begin
                    [%debug_log "  --> %a-%a (taken from removed moves)" nups n1 nups n2];
                    n1, n2
                  end
                  else
                    nd1, nd2
              end
              | None -> nd1, nd2
            in

            let cands1, c1an =
              try
                let an1, an2 = find_stably_mapped_ancestor tree2 nmapping#find self#find12 nd1 in
                [%debug_log "an1=%a an2=%a" nps an1 nps an2];
                if tree2#is_initial_ancestor an2 nd2 then begin
                  if nd1#initial_parent == an1 && nd2#initial_parent == an2 then begin
                    match nd1#data#_digest with
                    | Some d -> begin
                        [%debug_log "d=%s" (Xhash.to_hex d)];
                        try
                          match cenv#multiple_subtree_matches#find d with
                          | [], _, _ | _, [], _ -> [], None
                          | l1, l2, _ -> begin
                              let cands = ref [] in
                              List.iter
                                (fun (x1, mems1) ->
                                  List.iter
                                    (fun (x2, mems2) ->
                                      if
                                        x2 == nd2 &&
                                        not (self#is_crossing_with_untouched nmapping x1 x2)
                                      then begin
                                        cands := (mems1, mems2)::!cands
                                      end
                                    ) l2
                                ) l1;
                              match !cands with
                              | [] -> [], None
                              | l ->
                                  (List.map (fun (ms1, ms2) -> List.combine ms1 ms2) l),
                                  Some (an1, an2)
                          end
                        with
                          Not_found -> [], None
                    end
                    | None -> [], None
                  end
                  else
                    [], None
                end
                else begin
                  begin %debug_block
                    let au1, au2 = an1#uid, an2#uid in
                    [%debug_log "    stably_mapped_ancestor: %a-%a (%a-%a)" ups au1 ups au2 ngps an1 ngps an2]
                  end;

                  let is_extra2, rcands2 = label_find tree2 an2 nd1 in

                  [%debug_log "    rcands2: [%a]%s" nsps rcands2 (if is_extra2 then " (EXTRA)" else "")];

                  let count = ref 0 in

                  let rcands2' =
                    try
                      List.filter
                        (fun n2 ->
                          if !count > 1 then
                            raise Exit;

                          let b =
                            is_extra2 ||
                            let crossing =
                              try
                                tree1#fast_scan_whole_initial_subtree an1
                                  (fun n ->
                                    try
                                      let n' = nmapping#find n in
                                      match self#find12 n n' with
                                      | [] | [Relabel _] ->
                                          if
                                            is_crossing nd1 n2 n n' ||
                                            cenv#is_incompatible nd1 n2 n n'
                                          then
                                            raise Found
                                      | _ -> ()
                                    with
                                      Not_found -> ()
                                  );
                                false
                              with
                                Found -> true
                            in
                            not
                              (
                               crossing ||
                               tree2#is_initial_ancestor n2 nd2 ||
                               tree2#is_initial_ancestor nd2 n2 ||
                               (
                                n2#initial_nchildren > 0 &&
                                contain_stably_mapped tree2 n2 nmapping#inv_find self#find21
                               )
                              )
                          in
                          if b then
                            incr count;
                          b
                        ) rcands2
                    with
                      Exit -> []
                  in

                  [%debug_log "    rcands2': [%a]" nsps rcands2'];

                  match rcands2' with
                  | [] -> [], None
                  | [_] -> begin
                      try
                        let t1 = make_subtree_copy1 nd1 in
                        List.map
                          (fun r2 ->
                            if r2 == nd2 then
                              []
                            else
                              let t2 = make_subtree_copy2 r2 in
                              tree_matcher t1 t2
                          ) rcands2',
                        Some (an1, an2)
                      with
                        Invalid_argument _ -> [], None
                  end
                  | _ -> [], None
                end
              with
                Not_found -> [], None

            in (* cands1, c1an *)

            begin
              match c1an with
              | None -> ()
              | Some (an1, an2) -> begin
                  try
                    let l = Hashtbl.find cand_tbl (an1, an2) in
                    Hashtbl.replace cand_tbl (an1, an2) (cands1 @ l)
                  with
                    Not_found -> Hashtbl.add cand_tbl (an1, an2) cands1
              end
            end;

            let cands2, c2an =
              try
                let an2, an1 = find_stably_mapped_ancestor tree1 nmapping#inv_find self#find21 nd2 in
                [%debug_log "an1=%a an2=%a" nps an1 nps an2];
                if tree1#is_initial_ancestor an1 nd1 then begin
                  if nd1#initial_parent == an1 && nd2#initial_parent == an2 then begin
                    match nd2#data#_digest with
                    | Some d -> begin
                        [%debug_log "d=%s" (Xhash.to_hex d)];
                        try
                          match cenv#multiple_subtree_matches#find d with
                          | [], _, _ | _, [], _ -> [], None
                          | l1, l2, _ -> begin
                              let cands = ref [] in
                              List.iter
                                (fun (x1, mems1) ->
                                  List.iter
                                    (fun (x2, mems2) ->
                                      if
                                        x1 == nd1 &&
                                        not (self#is_crossing_with_untouched nmapping x1 x2)
                                      then begin
                                        cands := (mems1, mems2)::!cands
                                      end
                                    ) l2
                                ) l1;
                              match !cands with
                              | [] -> [], None
                              | l ->
                                  (List.map (fun (ms1, ms2) -> List.combine ms1 ms2) l),
                                  Some (an1, an2)
                          end
                        with
                          Not_found -> [], None
                    end
                    | None -> [], None
                  end
                  else
                    [], None
                end
                else begin
                  begin %debug_block
                    let au1, au2 = an1#uid, an2#uid in
                    [%debug_log "    stably_mapped_ancestor: %a-%a (%a-%a)" ups au1 ups au2 ngps an1 ngps an2]
                  end;

                  let is_extra1, rcands1 = label_find tree1 an1 nd2 in

                  [%debug_log "    rcands1: [%a]%s" nsps rcands1 (if is_extra1 then " (EXTRA)" else "")];

                  let count = ref 0 in

                  let rcands1' =
                    try
                      List.filter
                        (fun n1 ->
                          if !count > 1 then
                            raise Exit;

                          let b =
                            is_extra1 ||
                            let crossing =
                              try
                                tree2#fast_scan_whole_initial_subtree an2
                                  (fun n ->
                                    try
                                      let n' = nmapping#inv_find n in
                                      match self#find12 n' n with
                                      | [] | [Relabel _] ->
                                          if
                                            is_crossing n1 nd2 n' n ||
                                            cenv#is_incompatible n1 nd2 n' n
                                          then
                                            raise Found
                                      | _ -> ()
                                    with
                                      Not_found -> ()
                                  );
                                false
                              with
                                Found -> true
                            in
                            not
                              (
                               crossing ||
                               tree1#is_initial_ancestor n1 nd1 ||
                               tree1#is_initial_ancestor nd1 n1 ||
                               (
                                n1#initial_nchildren > 0 &&
                                contain_stably_mapped tree1 n1 nmapping#find self#find12
                               )
                              )
                          in

                          if b then
                            incr count;
                          b
                        ) rcands1
                    with
                      Exit -> []
                  in

                  [%debug_log "    rcands1': [%a]" nsps rcands1'];

                  match rcands1' with
                  | [] -> [], None
                  | [_] -> begin
                      try
                        let t2 = make_subtree_copy2 nd2 in
                        List.map
                          (fun r1 ->
                            if r1 == nd1 then
                              []
                            else
                              let t1 = make_subtree_copy1 r1 in
                              tree_matcher t1 t2
                          ) rcands1',
                        Some (an1, an2)
                      with
                        Invalid_argument _ -> [], None
                  end
                  | _ -> [], None
                end
              with
                Not_found -> [], None
            in (* cands2, c2an *)

            begin
              match c2an with
              | None -> ()
              | Some (an1, an2) -> begin
                  try
                    let l = Hashtbl.find cand_tbl (an1, an2) in
                    Hashtbl.replace cand_tbl (an1, an2) (cands2 @ l)
                  with
                    Not_found -> Hashtbl.add cand_tbl (an1, an2) cands2
              end
            end

          ) pairs

      ) move_root_tbl;

    [%debug_log "-----"];


    (* reducing candidates *)
    Hashtbl.iter
      (fun (an1, an2) cands ->

        [%debug_log "stably mapped: %a - %a:" nps an1 nps an2];

        let stable_matches = ref [] in

        tree1#fast_scan_whole_initial_subtree an1
          (fun n1 ->
            if n1 != an1 then
              try
                let n2 = nmapping#find n1 in
                if tree2#initial_subtree_mem an2 n2 then begin
                  match self#find12 n1 n2 with
                  | [] | [Relabel _] -> stable_matches := (n1, n2) :: !stable_matches
                  | _ -> ()
                end
              with
                Not_found -> ()
          );

        begin %debug_block
          [%debug_log "stable matches: [%s]"
            (Xlist.to_string
               (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" !stable_matches)]
        end;


        let is_directly_connected n1 n2 =
          n1 == n2#initial_parent ||
          n2 == n1#initial_parent
        in
        let is_directly_connected_pair (n11, n12) (n21, n22) =
          is_directly_connected n11 n21 && is_directly_connected n12 n22
        in

        let get_largest_connected_subset pairs =
          let tbl = Hashtbl.create 0 in
          List.iter
            (fun (nd1, nd2) ->
              let set = Xset.create 0 in
              List.iter
                (fun (n1, n2) ->
                  if nd1 != n1 && nd2 != n2 then
                    if is_directly_connected_pair (nd1, nd2) (n1, n2) then
                      Xset.add set (n1, n2)
                ) pairs;
              Hashtbl.add tbl (nd1, nd2) set
            ) pairs;

          let trace_pair pair =
            let set = Xset.create 0 in
            let rec trace pair =
              let len_before = Xset.length set in
              Xset.add set pair;
              if Xset.length set <> len_before then
                Xset.iter trace (Hashtbl.find tbl pair)
            in
            trace pair;
            set
          in
          let connected_subsets =
            List.fold_left
              (fun l pair ->
                let s = trace_pair pair in
                if List.for_all (fun x -> not (Xset.equals s x)) l then
                  s :: l
                else
                  l
              ) [] pairs
          in

          let connected_cands = List.map Xset.to_list connected_subsets in

          [%debug_log "[%s] -> %s"
            (Xlist.to_string (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" pairs)
            (Xlist.to_string
               (fun cand ->
                 sprintf "[%s]"
                   (Xlist.to_string
                      (fun (n1, n2) ->
                        sprintf "%a-%a" nups n1 nups n2
                      ) ";" cand)
               ) ";" connected_cands)];

          connected_cands
        in

        let directly_connected_to_stable_match (n1, n2) =
          let stable = (an1, an2)::!stable_matches in
          List.exists (is_directly_connected_pair (n1, n2)) stable
        in
        let stable_matches1, stable_matches2 = List.split !stable_matches in
        let is_invalid_cand cand =
          let b =
            List.exists (fun (n1, _) -> List.memq n1 stable_matches1) cand ||
            List.exists (fun (_, n2) -> List.memq n2 stable_matches2) cand
          in
          [%debug_log "[%s] -> %B" (Xlist.to_string (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" cand) b];
          b
        in

        let not_contained_in_move cand =
          let ns1, ns2 = List.split cand in
          let sort ns =
            List.fast_sort (fun n1 n2 -> Stdlib.compare n2#gindex n1#gindex) ns
          in
          let sorted_ns1 = sort ns1 in
          let sorted_ns2 = sort ns2 in
          let b =
            match sorted_ns1, sorted_ns2 with
            | [], [] -> false
            | n1::_, n2::_ -> begin
                let g1, g2 = n1#gindex, n2#gindex in
                try
                  Hashtbl.iter
                    (fun mid (lgi1, gi1, lgi2, gi2) ->
                      let _ = mid in
                      if (lgi1 < g1 && g1 < gi1) || (lgi2 < g2 && g2 < gi2) then begin
                        [%debug_log "  contained in mid:%a" MID.ps mid];
                        raise Found
                      end
                    ) move_region_tbl;
                  true
                with
                  Found -> false
            end
            | _ -> assert false
          in
          [%debug_log "[%s] -> %B" (Xlist.to_string (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" cand) b];
          b
        in

        let filter_cands cs =
          List.filter
            (fun cand ->
              not (is_invalid_cand cand) &&
              (List.exists directly_connected_to_stable_match cand ||
              List.length cand > 2 ||
              not_contained_in_move cand(* ||
              match cand with
              | [n1, n2] -> n1#data#equals n2#data
              | _ -> false*)
              )
            ) cs
        in

        let cands = (* extract connected pairs *)
          List.concat_map get_largest_connected_subset cands
        in

        let filtered_cands =
          List.map
            (fun cand ->
              List.fast_sort
                (fun (n0, _) (n1, _) -> Stdlib.compare n1#gindex n0#gindex)
                cand
            ) (filter_cands cands)
        in

        begin %debug_block
          List.iter
            (fun cand ->
              [%debug_log "filtered cand: [%s]"
                (Xlist.to_string
                   (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" cand)]
            ) filtered_cands
        end;

        let cands =
          List.map
            (fun cand ->
              match cand with
              | (r1, r2)::_ ->
                  if same_digest r1 r2 && r1#data#weight > 1 then
                    if
                      List.for_all
                        (fun (sn1, sn2) ->
                          (tree1#initial_subtree_mem r1 sn1 || tree2#initial_subtree_mem r2 sn2) ||
                          (not (cenv#is_incompatible sn1 sn2 r1 r2) &&
                           not (Node_mapping.is_crossing sn1 sn2 r1 r2))
                          ) !stable_matches
                    then
                      cand
                    else
                      []
                  else
                    List.filter
                      (fun (n1, n2) ->
                        List.for_all
                          (fun (sn1, sn2) ->
                            (not (cenv#is_incompatible sn1 sn2 n1 n2) &&
                             not (Node_mapping.is_crossing sn1 sn2 n1 n2))
                          ) !stable_matches
                      ) cand
              | [] -> []
            ) filtered_cands
        in
        let cands = filter_cands cands in

(*
        let get_top cand = match cand with (n, _)::_ -> n | _ -> assert false in
        let cands =
          List.fast_sort
            (fun cand0 cand1 ->
              let len0 = List.length cand0 in
              let len1 = List.length cand1 in
              let top0 = get_top cand0 in
              let top1 = get_top cand1 in
              if len0 = len1 then
                Stdlib.compare top1#gindex top0#gindex
              else
                Stdlib.compare len1 len0
            ) cands
        in
*)
        begin %debug_block
          List.iter
            (fun cand ->
              [%debug_log "cand: [%s]"
                (Xlist.to_string
                   (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" cand)]
            ) cands
        end;

        match cands with
        | [] -> Hashtbl.remove cand_tbl (an1, an2)
        | [c] -> Hashtbl.replace cand_tbl (an1, an2) [c]
        | _ ->
            let ctbl = Hashtbl.create 0 in
            let get_top_pair_len cand =
              match cand with
              | (n1, n2)::_ ->
                  Hashtbl.add ctbl (n1, n2) cand;
                  n1, n2, Comparison.weight_of_int (List.length cand)
              | _ -> assert false
            in
            let pair_weight_list = List.map get_top_pair_len cands in
            let compat, _ =
              cenv#select_compatible_and_not_crossing_pairs pair_weight_list
            in
            let selected = List.map (fun (n1, n2, _) -> Hashtbl.find ctbl (n1, n2)) compat in
            Hashtbl.replace cand_tbl (an1, an2) selected
(*
        | c::_ -> (* Crossing candidates are not yet checked. We can however select one safely *)
            Hashtbl.replace cand_tbl (an1, an2) [c]
*)
      ) cand_tbl;



    (* *)
    [%debug_log "-----"];

    let find_ed1 nd =
      try
        [self#find_del nd], [], []
      with
        Not_found ->
          let eds = self#find1 nd in
          let m, ad =
            match eds with
            | [Move(_, _, (i1, _), (i2, _))]
            | [Relabel(_, (i1, _), (i2, _))]
            | [Move(_, _, (i1, _), (i2, _));Relabel _]
            | [Relabel _;Move(_, _, (i1, _), (i2, _))] -> begin
                let n1 = Info.get_node i1 in
                let n2 = Info.get_node i2 in
                (n1, n2), make_insert n2
            end
            | [] -> raise Not_found
            | _ -> assert false
          in
          eds, [m], [ad]
    in
    let find_ed2 ?(rms_only=false) nd =
      try
        [self#find_ins nd], [], []
      with
        Not_found ->
          let eds = self#find2 nd in
          if rms_only then
            eds, [], []
          else
            let m, ad =
              match eds with
              | [Move(_, _, (i1, _), (i2, _))]
              | [Relabel(_, (i1, _), (i2, _))]
              | [Move(_, _, (i1, _), (i2, _));Relabel _]
              | [Relabel _;Move(_, _, (i1, _), (i2, _))] -> begin
                  let n1 = Info.get_node i1 in
                  let n2 = Info.get_node i2 in
                  (n1, n2), make_delete n1
              end
              | [] -> raise Not_found
              | _ -> assert false
            in
            eds, [m], [ad]
    in

    let used_matches = ref [] in

    Hashtbl.iter
      (fun (an1, an2) cands ->
        let _ = an1 in
        let _ = an2 in
        let cands' =
          List.map
            (fun cand ->
              Xlist.subtract cand (Xlist.intersection cand !used_matches)
            ) cands
        in

        begin %debug_block
          let an1an2 = sprintf "%a-%a" nups an1 nups an2 in
          [%debug_log "cands (%s):" an1an2];
          List.iter
            (fun cand ->
              [%debug_log "[%s]"
                (Xlist.to_string (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" cand)]
            ) cands;
          [%debug_log "cands' (%s):" an1an2];
          List.iter
            (fun cand ->
              [%debug_log "[%s]"
                (Xlist.to_string (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" cand)]
            ) cands'
        end;

        List.iter
          (fun cand ->

            [%debug_log "  cand: [%s]"
              (Xlist.to_string (fun (n1, n2) -> sprintf "%a-%a" nups n1 nups n2) ";" cand)];

            List.iter
              (fun (nd1, nd2) ->
                try
                  let to_be_removed, nmap_to_be_removed, to_be_added =
                    try
                      let nd1' = nmapping#find nd1 in
                      if nd1' == nd2 then begin
                        let es = self#find12 nd1 nd1' in
                        try
                          let rms, ms, ad = find_ed2 ~rms_only:true nd2 in
                          Xlist.unionq rms es, ms, ad
                        with
                          Not_found -> raise Abort
                      end
                      else begin
                        let m = nd1, nd1' in
                        let es = self#find12 nd1 nd1' in
                        let ins = make_insert nd1' in
                        try
                          let rms, ms, ad = find_ed2 nd2 in
                          Xlist.unionq rms es, m :: ms, ins :: ad
                        with
                          Not_found -> raise Abort
                      end
                    with
                      Not_found ->
                        try
                          let nd2' = nmapping#inv_find nd2 in
                          let m = nd2', nd2 in
                          let es = self#find12 nd2' nd2 in
                          let del = make_delete nd2' in
                          try
                            let rms, ms, ad = find_ed1 nd1 in
                            Xlist.unionq rms es, m :: ms, del :: ad
                          with
                            Not_found -> raise Abort
                        with
                          Not_found ->
                            let dels = try [self#find_del nd1] with Not_found -> [] in
                            let inss = try [self#find_ins nd2] with Not_found -> [] in
                            dels @ inss, [], []
                  in

                  List.iter self#remove_edit to_be_removed;
                  List.iter
                    (fun (n1, n2) ->
                      [%debug_log "removing %a-%a" nups n1 nups n2];

                      let _ = nmapping#remove n1 n2 in

                      assert (not (nmapping#mem_cod n2));

                    ) nmap_to_be_removed;
                  List.iter self#add_edit to_be_added;

                  [%debug_log "adding %a-%a" nups nd1 nups nd2];

                  ignore (nmapping#add_unsettled nd1 nd2);
                  used_matches := (nd1, nd2) :: !used_matches
                with
                  Abort -> ()
              ) cand

          ) cands'

      ) cand_tbl;

    Xprint.verbose options#verbose_flag "%d matches added by move shrinkage" (List.length !used_matches)

    (* end of method shrink_moves *)

  method is_crossing_with_untouched
      ?(full_scan=false)
      ?(mask=[])
      ?(incompatible_only=false)
      ?(weak=true)
      (nmapping : 'node_t Node_mapping.c)
      nd1 nd2
      =
    begin %debug_block
      [%debug_log "[full_scan=%B][incompatible_only=%B][weak=%B] %a-%a"
        full_scan incompatible_only weak nups nd1 nups nd2];
      List.iter
        (fun (n1, n2) -> [%debug_log "masked: %a-%a" nups n1 nups n2])
        mask
    end;

    let iter =
      if incompatible_only then
        if full_scan then
          nmapping#iter_incompatible_mapping
        else
          nmapping#iter_incompatible_mapping_rep
      else
        if full_scan then
          nmapping#iter_crossing_or_incompatible_mapping
        else
          let is_move = self#mem_mov12 in
          nmapping#iter_crossing_or_incompatible_mapping_rep is_move
    in
    let flag = ref false in
    try
      iter nd1 nd2
        (fun n1 n2 ->

          [%debug_log "checking %a-%a" nups n1 nups n2];

          if
            not (is_ghost_node n1) && not (is_ghost_node n2) &&
            not (List.mem (n1, n2) mask)
          then begin

            if self#mem_mov12 n1 n2 then begin
              [%debug_log "mem_mov12 %a %a --> true" nups n1 nups n2];
              flag := true
            end
            else begin
              [%debug_log "mem_mov12 %a %a --> false" nups n1 nups n2];
              begin %debug_block
                let mes =
                  if incompatible_only then
                    "is crossing with"
                  else
                    "is crossing or incompatible with"
                in
                [%debug_log "%a-%a %s %a-%a" nugps nd1 nugps nd2 mes nugps n1 nugps n2];
              end;
              raise Exit
            end

          end
        );
      let b = weak && !flag in
      [%debug_log "%B" b];
      b
    with
      Exit ->
        [%debug_log "true"];
        true

  method dump_delta
      ?(extra_ns_decls=([] : (string * string) list))
      ?(info_file_path="")
      ((*tree1*)_ : 'tree_t)
      ((*tree2*)_ : 'tree_t)
      ((*nmapping*)_ : 'node_t Node_mapping.c)
      ((*edits_copy*)_ : 'edits)
      ((*fname*)_ : string)
      =
    ignore extra_ns_decls;
    ignore info_file_path;
    ()

end (* of class Edit_base.seq_base *)
]
