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
(* delta_common.ml *)

[%%prepare_logger]

module UID   = Diffast_misc.UID
module GI    = Diffast_misc.GIndex
module Otree = Diffast_misc.Otree
module MID   = Moveid
module SB    = Spec_base
module CB    = Change_base

open Delta_base


let del_bg = "#B8E3B1"
let del_fg = "#000000"
let ins_bg = "#B2CDF9"
let ins_fg = "#000000"

exception Found

let verbose_msg options x = Xprint.verbose options#verbose_flag x

let mids_to_string mids =
  String.concat ";" (List.map MID.to_string mids)

let array_range_exists f a st ed =
  try
    for i = st to ed do
      if f a.(i) then
        raise Exit
    done;
    false
  with
    Exit -> true

let array_range_forall f a st ed =
  try
    for i = st to ed do
      if not (f a.(i)) then
        raise Exit
    done;
    true
  with
    Exit -> false

let get_range l = (* (min, max) *)
  match l with
  | [] -> invalid_arg "get_range"
  | h::t ->
    let max = ref h in
    let min = ref h in
    List.iter
      (fun x ->
        if x > !max then
          max := x;

        if x < !min then
          min := x
      ) t;
    !min, !max


type 'data node_t = 'data SB.node_t
type 'tree tree_t = ('data node_t #SB.tree_t_shared as 'tree)


[%%capture_path
let get_rel_path hpath path =
  try
    Path.remove_head hpath path
  with
    exn ->
      [%debug_log "head=%s, path=%s" (Path.to_string hpath) (Path.to_string path)];
      raise exn
]

let str_opt_to_string = function
  | Some s -> s
  | None -> ""

let bool_opt_to_string = function
  | Some b -> string_of_bool b
  | None -> ""

let int_opt_to_string = function
  | Some i -> string_of_int i
  | None -> ""

let mid_opt_to_string = function
  | Some mid -> MID.to_raw mid
  | None -> ""

let attrs_to_string l =
  String.concat "," (List.map (fun (a,s) -> sprintf "%s:%s" a s) l)

let nodes_to_string nds =
  Xlist.to_string (fun (nd : 'data node_t) -> nd#initial_to_string) "\n" nds

let node_to_uid_string nd =
  sprintf "%a(%a)" UID.ps nd#uid GI.ps nd#gindex

let nodes_to_uids_string nds =
  String.concat ";" (List.map node_to_uid_string nds)

let nps () = node_to_uid_string
let nsps () = nodes_to_uids_string

let get_frontier_nodes nds =
  List.rev
    (List.fold_left
       (fun l nd ->
         let p = nd#initial_parent in
         if List.memq p l then
           l
         else
           p::l
       ) [] nds)

let mknmap tree' umap =
  fun n -> tree'#search_node_by_uid (umap n#uid)

[%%capture_path
let scan_initial_cluster nd nds (f : 'data node_t -> unit) =
  [%debug_log "nds=[%s]" (nodes_to_uids_string nds)];
  let rec scan n =
    f n;
    Array.iter
      (fun c ->
	if List.memq c nds then () else scan c
      ) n#initial_children
  in
  scan nd
]

let scan_whole_initial_subtree ?(moveon=(fun _ -> true)) nd (f : 'node -> unit) =
  let rec do_scan nd =
    if moveon nd then
      Array.iter do_scan nd#initial_children;
    f nd
  in
  do_scan nd

let preorder_scan_whole_initial_subtree ?(moveon=(fun _ -> true)) nd (f : 'node -> unit) =
  let rec do_scan nd =
    f nd;
    if moveon nd then
      Array.iter do_scan nd#initial_children
  in
  do_scan nd

let rev_scan_whole_initial_subtree ?(moveon=(fun _ -> true)) nd (f : 'node -> unit) =
  let rec do_scan nd =
    f nd;
    if moveon nd then begin
      for i = nd#initial_nchildren - 1 downto 0 do
        do_scan nd#initial_children.(i)
      done
    end
  in
  do_scan nd

[%%capture_path
let rec get_p_descendants ?(keep_going=false) ?(moveon=fun _ -> true) pred nd =
  if moveon nd then
    List.concat_map
      (fun n ->
        (*[%debug_log "n=%a" nps n];*)
        if pred n then
          n ::
          (if keep_going && moveon n then begin
            let l = get_p_descendants ~moveon pred n in
            if l <> [] then
              [%debug_log "!!!! n=%a l=[%a]" nps n nsps l];
            l
          end
          else
            [])
        else
          get_p_descendants ~moveon pred n
      )
      (Array.to_list nd#initial_children)
  else
    []
]

let has_p_descendant ?(moveon=fun _ -> true) pred nd =
  let rec _has_p_descendant ?(moveon=fun _ -> true) pred nd =
    if moveon nd then
      List.iter
        (fun n ->
          if pred n then
            raise Exit
          else
            _has_p_descendant ~moveon pred n
        )
        (Array.to_list nd#initial_children)
  in
  try
    _has_p_descendant ~moveon pred nd;
    false
  with
    Exit -> true

let has_p_sibling pred nd =
  Array.exists
    (fun x ->
      x != nd && pred x
    ) nd#initial_parent#initial_children

let has_p_ancestor ?(limit_opt=None) pred nd =
  let moveon =
    match limit_opt with
    | Some r -> fun x -> x != r
    | _ -> fun _ -> true
  in
  try
    let cur = ref nd#initial_parent in
    while true do
      if moveon !cur then begin
        if pred !cur then
          raise Found
        else
          cur := (!cur)#initial_parent
      end
      else
        raise Exit
    done;
    false
  with
  | Found -> true
  | _ -> false

let get_p_ancestor ?(moveon=fun _ -> true) pred nd =
  try
    let cur = ref nd#initial_parent in
    while moveon !cur && not (pred !cur) do
      cur := (!cur)#initial_parent
    done;

    if not (moveon !cur) then
      raise Not_found;

    !cur
  with
    Otree.Parent_not_found _ -> raise Not_found

let get_p_left_nodes ?(moveon=fun _ -> true) ?(reset=fun _ -> false) pred nd rt =
  let cur = ref nd in
  let l = ref [] in
  begin
    try
      while !cur != rt do
        let pn = (!cur)#initial_parent in
        if reset !cur then
          l := []
        else begin
          let children = pn#initial_children in
          let pos = (!cur)#initial_pos in
          for i = pos - 1 downto 0 do
            let c = children.(i) in
            if moveon c then
              if pred c then
                l := [c] :: !l
              else
                l := (get_p_descendants ~moveon pred c) :: !l
          done
        end;
        cur := pn
      done
    with
      Otree.Parent_not_found _ -> ()
  end;
  List.flatten !l

let get_p_right_nodes ?(moveon=fun _ -> true) ?(reset=fun _ -> false) pred nd rt =
  let cur = ref nd in
  let l = ref [] in
  begin
    try
      while !cur != rt do
        let pn = (!cur)#initial_parent in
        if reset !cur then
          l := []
        else begin
          let children = pn#initial_children in
          let pos = (!cur)#initial_pos in
          for i = pos + 1 to (Array.length children) - 1 do
            let c = children.(i) in
            if moveon c then
              if pred c then
                l := [c] :: !l
              else
                l := (get_p_descendants ~moveon pred c) :: !l
          done
        end;
        cur := pn
      done
    with
      Otree.Parent_not_found _ -> ()
  end;
  List.flatten (List.rev !l)

let scan_ancestors ?(moveon=fun _ -> true) nd f =
  let visited = ref [nd] in
  try
    let cur = ref nd in
    while (moveon !cur) do
      let parent = (!cur)#initial_parent in
      if List.memq parent !visited then begin
        [%warn_log "infinite loop detected: cur=%a parent=%a visited=[%a]"
          nps !cur nps parent nsps !visited];
        raise Exit
      end
      else
        cur := parent;
      visited := parent :: !visited;
      f !cur
    done
  with
  | Exit -> ()
  | Otree.Parent_not_found _ -> ()

[%%capture_path
let get_ancestors ?(limit=None) nd =
  let l = ref [] in
  begin
    try
      let cur = ref nd in
      while true do
        let pos = (!cur)#initial_pos in
        cur := (!cur)#initial_parent;
        l := (!cur, pos) :: !l;
        match limit with
        | Some x when x == !cur -> raise Exit
        | _ -> ()
      done
    with
    | Exit
    | Otree.Parent_not_found _ -> ()
  end;
  [%debug_log "%a -> [%s]" nps nd
    (Xlist.to_string (fun (n, pos) -> sprintf "(%a,%d)" nps n pos) ";" !l)];
  !l
]

let is_ancestor a n =
  try
    scan_ancestors n
      (fun x ->
        if x == a then
          raise Found);
    false
  with
  | Found -> true
  | Otree.Parent_not_found _ -> false

let get_ancestor_below nd pnd =
  let cur = ref nd in
  try
    while (!cur)#initial_parent != pnd do
      cur := (!cur)#initial_parent
    done;
    !cur
  with
    _ -> raise Not_found

let get_left_sibling_opt nd =
  try
    Some (nd#initial_parent#initial_children.(nd#initial_pos-1))
  with
    _ -> None

let get_right_sibling_opt nd =
  try
    Some (nd#initial_parent#initial_children.(nd#initial_pos+1))
  with
    _ -> None

let sort_nodes_by_gindex ?(descending=false) nds =
  let cmp =
    if descending then
      fun n0 n1 -> Stdlib.compare n1#gindex n0#gindex
    else
      fun n0 n1 -> Stdlib.compare n0#gindex n1#gindex
  in
  List.fast_sort cmp nds

let postorder_node_sort rt nds = (* when gindexes not set *)
  let tbl = Hashtbl.create 0 in
  List.iter (fun n -> Hashtbl.add tbl n 0) nds;
  let i = ref 1 in
  scan_whole_initial_subtree rt
    (fun n ->
      try
        if Hashtbl.mem tbl n then begin
          Hashtbl.replace tbl n !i;
          incr i
        end
      with
        Not_found -> ()
    );
  let cmp n0 n1 =
    let i0 = Hashtbl.find tbl n0 in
    let i1 = Hashtbl.find tbl n1 in
    if i0 = 0 || i1 = 0 then
      failwith "postorder_node_sort";
    Stdlib.compare i0 i1
  in
  List.fast_sort cmp nds

[%%capture_path
let get_adjusted_path
    ?(get_group=fun _ -> raise Not_found)
    ?(group_heads=[])
    ?(get_iparent_opt=(None : ('data node_t -> 'data node_t) option))
    get_ipos get_iofs
    get_mem_pos
    pos_cache
    is_simple_ins
    _is_excluded
    is_excluded
    is_stable
    root
    rel_path
    =
  [%debug_log "root=%a rel_path=%s" nps root (Path.to_string rel_path)];

  let adjusted = ref Path.root in
  let cur = ref root in

  let elems = Path.get_elems rel_path in
  let nelems = List.length elems in

  List.iteri
    (fun idx elem ->
      let lv = nelems - 1 - idx in
      [%debug_log "lv=%d elem=%s" lv (Elem.to_string elem)];
      let pos = elem.Elem.pos in
      let children = (!cur)#initial_children in
      let child = children.(pos) in

      let is_simple_ins_map = Array.map is_simple_ins children in

      let is_excluded_map = Array.map (is_excluded lv) children in

      let stable_descendant_map =
        Array.map (fun c -> List.length (get_p_descendants is_stable c)) children
      in

      [%debug_log "lv=%d children=[%a] pos=%d" lv nsps (Array.to_list children) pos];

      if is_excluded_map.(pos) then begin
        [%debug_log "%a is excluded" nps child];

        if
          (try
            is_excluded_map.(pos-1) &&
            (is_stable child || is_simple_ins_map.(pos-1) <> Some true)
          with _ -> false) ||
          (try is_excluded_map.(pos+1) with _ -> false)
        then begin
          [%debug_log "position translation is available"];
          ()(* position translation is available  *)
        end
        ;(*else *)begin
          Array.iteri
            (fun i b ->
              if lv = 0 && i < pos then
              match is_simple_ins_map.(i) with
              | Some true -> begin
                  if b then begin
                    [%debug_log "is_excluded_map: %d -> false" i];
                    is_excluded_map.(i) <- false
                  end
              end
              | Some false -> begin
                  let ci = children.(i) in
                  if
                    not b && _is_excluded ci && not (is_stable ci) &&
                    stable_descendant_map.(i) = 0
                  then begin
                    [%debug_log "is_excluded_map: %d -> true" i];
                    is_excluded_map.(i) <- true
                  end
              end
              | _ -> ()
            ) is_excluded_map
        end;

        let count = ref 0 in
        let offset = ref 0 in
        let pos' = ref 0 in

        let incr_count =
          let incr_ x =
            [%debug_log "%d -> %d" !x (!x + 1)];
            incr x
          in
          match get_iparent_opt with
          | Some f -> begin
              let d_list = ref [] in
              fun c ->
                try
                  let d = f c in
                  match !d_list with
                  | h::_ -> begin
                      if d != h then begin
                        d_list := d :: !d_list;
                        incr_ count
                      end
                  end
                  | [] -> begin
                      d_list := [d];
                      incr_ count
                  end
                with
                  Not_found -> incr_ count
          end
          | None -> fun _ -> incr_ count
        in

        begin
          let cur_grp_opt = ref None in
          try
            Array.iteri
              (fun i c ->
                let c_is_excluded = is_excluded_map.(i) in
                begin %debug_block
                  let c_is_simple_ins = is_simple_ins_map.(i) in
                  let is_simple_ins_str =
                    match c_is_simple_ins with
                    | Some true -> ", is_simple_ins"
                    | Some false -> ", not_simple_ins"
                    | _ -> ""
                  in
                  [%debug_log "  %d %a (is_excluded=%B, is_stable=%B%s)"
                    i nps c c_is_excluded (is_stable c) is_simple_ins_str];
                end;
                try
                  if lv > 0 then
                    raise Not_found;

                  let mem_pos = get_mem_pos c in
                  [%debug_log "mem_pos: %a -> %d" nps c mem_pos];
                  if i < pos || i > pos then begin
                    let o = pos - i in
                    [%debug_log "offset: %d -> %d" !offset o];
                    offset := o;
                    pos' := mem_pos;
                    count := mem_pos + 1;
                    if i > pos then
                      raise Exit
                  end
                  else if i = pos then
                    raise Exit
                  else
                    assert false
                with
                  Not_found ->

                if c_is_excluded then begin
                  try
                    match !cur_grp_opt with
                    | Some (i0, g) when i <= pos && g == get_group c -> begin
                        let _ = i0 in
                        [%debug_log "i=%d < pos=%d: i0=%d g=%a c=%a" i pos i0 nps g nps c];
                        let o = pos - i + 1 in
                        [%debug_log "offset: %d -> %d" !offset o];
                        offset := o
                    end
                    | _ -> ()
                  with _ -> ()
                end
                else (*if not c_is_excluded then *)begin
                  let incr_flag = ref true in
                  begin
                    try
                      let g = get_group c in
                      begin
                        match !cur_grp_opt with
                        | Some (i', g') -> begin
                            [%debug_log "grp: (%d,%a) -> (%d,%a)" i' nps g' i nps g];
                            if (i' = pos - 1 || i' < i) && g' == g then
                              incr_flag := false
                        end
                        | _ -> ()
                      end;
                      [%debug_log "grp: (%d,%a)" i nps g];
                      cur_grp_opt := Some (i, g)
                    with _ -> ()
                  end;
                  if !incr_flag then
                    incr_count c;
                  if i < pos || i > pos then begin
                    let o = pos - i in
                    [%debug_log "offset: %d -> %d" !offset o];
                    offset := o;
                    begin
                      try
                        pos' := get_ipos c;
                        [%debug_log "offset=%d pos'=%d (ipos)" !offset !pos']
                      with
                        Not_found ->
                          pos' := !count - 1;
                          [%debug_log "offset=%d pos'=%d" !offset !pos'];
                    end;

                    if i > pos then
                      raise Exit
                  end
                  else if i = pos then
                    raise Exit
                  else
                    assert false
                end
              ) children
          with
            Exit -> ()
        end;
        [%debug_log "count=%d" !count];
        [%debug_log "pos'=%d" !pos'];
        let elem' =
          if !count > 0 then begin
            [%debug_log "offset=%d, pos'=%d" !offset !pos'];
            Elem.make ~ofs:(float !offset) !pos'
          end
          else begin
            let ofs =
              try
                float (get_iofs child)
              with
                Not_found ->
                  let count = ref 0 in
                  let group = ref root in
                  begin
                    let headless = ref [] in
                    try
                      Array.iteri
                        (fun i c ->
                          if i <(*<=*) pos then begin
                            let inc =
                              if is_stable c then
                                1
                              else
                                stable_descendant_map.(i)
                            in
                            [%debug_log "inc=%d" inc];
                            if inc > 0 then begin
                              try
                                let g = get_group c in
                                if g != !group then begin
                                  if List.memq c group_heads then begin
                                    [%debug_log "group=%a" nps g];
                                    group := g
                                  end
                                  else
                                    headless := g :: !headless;
                                  raise Not_found
                                end
                              with
                                Not_found -> count := !count + inc
                            end
                          end
                          else if i = pos then begin
                            [%debug_log "headless groups: [%a]" nsps !headless];
                            try
                              let g = get_group c in
                              [%debug_log "g=%a" nps g];
                              if g == !group && not (List.memq g !headless) then
                                decr count
                            with
                              Not_found -> ()
                          end
                          else
                            raise Exit
                        ) children
                    with
                      Exit -> ()
                  end;
                  float !count
            in
            Elem.make ~ofs 0
          end
        in
        [%debug_log "elem'=%s" (Elem.to_string elem')];

        adjusted := Path.append !adjusted elem';

        [%debug_log "adjusted=%s" (Path.to_string !adjusted)]

      end
      else begin (* not (is_excluded child) *)
        let pos' = ref 0 in
        begin
          try
            pos' := Hashtbl.find pos_cache child
          with
            Not_found ->
              Array.iteri
                (fun i c ->
                  if i < pos && not (is_excluded lv c) then
                    incr pos'
                ) children;
              [%debug_log "pos'=%d" !pos'];
              Hashtbl.add pos_cache child !pos'
        end;

        adjusted := Path.append !adjusted (Elem.make !pos');

        [%debug_log "adjusted=%s" (Path.to_string !adjusted)]

      end;

      cur := child

    ) elems;

  !adjusted
]

