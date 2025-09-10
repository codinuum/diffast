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
(* dirtree.ml *)

[%%prepare_logger]

module Xprint = Diffast_misc.Xprint
module Xstring = Diffast_misc.Xstring
module Xset = Diffast_misc.Xset
module Xlist = Diffast_misc.Xlist
module Xhash = Diffast_misc.Xhash
module Xchannel = Diffast_misc.Xchannel
module Storage = Diffast_misc.Storage
module Fs = Diffast_misc.Fs

module T     = Triple
module UID   = Diffast_misc.UID
module Otree = Diffast_misc.Otree
module S     = Stat
module SF    = Stat.File
module SD    = Stat.Dir


let sprintf = Printf.sprintf
let printf  = Printf.printf
let fprintf = Printf.fprintf


let auxfile_exts = [".jj"; ".jjt"; ".properties"]

let is_auxfile name =
  List.exists (Xstring.endswith name) auxfile_exts

let path_concat l =
  List.fold_left (fun p x -> Filename.concat p x) "" l

let union ll =
  let len =
    List.fold_left (fun n l -> n + (List.length l)) 0 ll
  in
  let s = Xset.create len in
  List.iter (List.iter (Xset.add s)) ll;
  Xset.to_list s

class node_data (tree : Storage.tree) (entry : Storage.entry_t) =
  let default_digest =
    match entry#dir_digest with
    | Some d -> Some d
    | None -> None
  in
  object (self : 'self)
    inherit Otree.data2

    val mutable _digest = default_digest
    method _digest = _digest

    method xdigest = self#_digest

    val mutable digest = None
    method digest = digest
    method set_digest d =
      match _digest with
      | None ->
          digest <- Some d;
          _digest <- Some d
      | Some d ->
          digest <- Some d

    method reset_digest = digest <- None

    val mutable content_digest = None
    method content_digest = content_digest
    method get_content_digest =
      match content_digest with
      | Some d -> d
      | None -> raise Not_found
    method set_content_digest c =  content_digest <- Some c

    method content_digest_string =
      match content_digest with
      | None -> ""
      | Some c -> Xhash.to_hex c

    method is_dir = entry#is_dir
    method is_file = content_digest <> None

    val mutable is_auxfile = false
    method set_is_auxfile = is_auxfile <- true
    method is_auxfile = is_auxfile

    method get_name = entry#name
    method get_stripped_name = entry#name

    method label = entry#name
    method _label = entry#name
    method dirname = entry#dirname
    method path = entry#path

    method relabel_allowed (_: 'self) = true
    method stripped_label = self#label
    method _stripped_label = self#label
    method anonymized_label = self#label
    method _anonymized_label = self#label
    method anonymized2_label = self#label
    method _anonymized2_label = self#label

    method id = sprintf "%s%s" self#path
      (match _digest with
      | Some d -> "("^(Xhash.to_hex d)^")"
      | None -> "")

    method to_string = self#id
    method to_rep =
      sprintf "%s%s" entry#name
	(match self#digest, self#content_digest with
	| None, None -> ""
	| Some d, None -> String.concat "" ["<";d;">"]
	| None, Some c -> String.concat "" ["<";c;">"]
	| Some d, Some c -> String.concat "" ["<";d;":";c;">"]
	)

    method to_xrep = self#to_rep

    method to_elem_data = self#to_string, [], ""

(*
    method to_tag = sprintf "<%s>" self#to_string
    method to_tags = let s = self#to_string in sprintf "<%s>" s, sprintf "</%s>" s
*)
    method eq ndat = entry#name = ndat#label
    method equals ndat = self#eq ndat && digest = ndat#digest
    method quasi_eq (ndat : 'self) = entry#name = ndat#label

    method feature = self#_label, (None : Xhash.t option)

    method get_content_channel_for_xml() =
      let ich = tree#get_channel entry#path in
      new Xchannel.base64_input_channel ich

  end (* of class Dirtree.node_data *)


type node_t = node_data Otree.node2

class c options (root : node_t) ?(id="") is_top = object (self)
  inherit [ 'node ] Otree.otree2 ~hash:options#hash_algo root is_top as super

  method id = if id = "" then root#data#id else id

  method path idx = (self#get idx)#data#path

  method! digest =
    match root#data#_digest with
    | Some d -> d
    | None -> super#digest

end (* of class Dirtree.c *)



let _tbl_add tbl d nd =
  try
    let nds = Hashtbl.find tbl d in
    Hashtbl.replace tbl d (nd::nds)
  with
    Not_found -> Hashtbl.add tbl d [nd]


[%%capture_path
let collapse_tree tree =
  let tbl = Hashtbl.create 0 in
  tree#scan_all
    (fun nd ->
      if nd == tree#root then
	tree#set_digest_of_root
      else
	if not nd#is_leaf then begin
	  tree#collapse_node nd;

	  [%debug_log "collapsed \"%s/\" digest=%s"
	    nd#data#label nd#data#digest_string];

          _tbl_add tbl nd#data#digest nd
	end
    );
  tree#init;
  tbl
]


exception To_be_skipped


[%%capture_path
let of_tree options mktbl (tree : Storage.tree) =
  Xprint.verbose options#verbose_flag "building dirtree \"%s\"...%!" tree#name;

  let uid_gen = options#uid_generator in

  let tbl = Hashtbl.create 0 in

  let rec file_to_node is_top entry =

    let name = entry#name in

    if
      (not is_top) &&
      (name = Filename.current_dir_name || name = Filename.parent_dir_name)
    then
      raise To_be_skipped;


    if entry#is_dir then begin (* directory node *)

      let obj = new node_data tree entry in

      let nodes =
        Xlist.filter_map
          (fun e ->
            try
              Some (file_to_node false e)
            with
            | To_be_skipped -> None
            | exn ->
                Xprint.warning "%s" (Printexc.to_string exn);
                None
          ) entry#entries
      in

      if nodes = [] then
	raise To_be_skipped;

      [%debug_log "dirname=\"%s\" name=\"%s\" <DIR>" entry#dirname name];

      let cmp nd1 nd2 = compare nd1#data#label nd2#data#label in
      let nd =
        let children = Array.of_list (List.fast_sort cmp nodes) in
	Otree.create_node2 uid_gen obj children
      in
      nd
    end
    else begin (* file node *)

      let is_aux =
        if
          not (options#is_disabled_parser "java") &&
          (options#designated_parser = "" || options#designated_parser = "java")
        then
          is_auxfile name
        else
          false
      in

      if options#check_extension name || is_aux then begin

	let ndat = new node_data tree entry in

        if is_aux then
          ndat#set_is_auxfile;

	let di = entry#file_digest in

        [%debug_log "dirname=\"%s\" name=\"%s\" <%s>" entry#dirname name (Xhash.to_hex di)];

	ndat#set_content_digest di;

	let nd = Otree.create_leaf2 uid_gen ndat in

	if mktbl then
          _tbl_add tbl di nd;

	nd
      end
      else begin
        raise To_be_skipped
      end
    end
  in
  let root = tree#get_entry "" in
  let dtree = new c options (file_to_node true root) ~id:tree#name true in

  if options#verbose_flag then
    printf "done.\n%!";

  dtree, tbl
]


let of_dir options mktbl path =
  let fstree = new Fs.tree options path in
  of_tree options mktbl fstree


let split get_key l = (* 'a list -> (key, 'a list) Hashtbl.t *)
  let add tbl k v =
    try
      let l = Hashtbl.find tbl k in
      Hashtbl.replace tbl k (v::l)
    with
      Not_found -> Hashtbl.add tbl k [v]
  in
  let key_tbl = Hashtbl.create 0 in
  List.iter (fun x -> add key_tbl (get_key x) x) l;
  key_tbl



let get_cache_path1 options dtree =
  options#get_cache_path_for_dir_digest1 dtree#digest

let get_cache_path2 options dtree1 dtree2 =
  options#get_cache_path_for_dir_digest2 dtree1#digest dtree2#digest


let get_cache_path_for_dir1 options tree =
  try
    let dtree, _ = of_tree options false tree in
    get_cache_path1 options dtree
  with
    To_be_skipped -> "<n/a>"


let get_cache_path_for_dir2 options old_tree new_tree =
  try
    let dtree1, _ = of_tree options false old_tree in
    let dtree2, _ = of_tree options false new_tree in
    get_cache_path2 options dtree1 dtree2
  with
    To_be_skipped -> "<n/a>"



let mkfile t nd = new Storage.file (Storage.Tree t) ~digest_opt:nd#data#content_digest nd#data#path

let mkfiles t = List.map (mkfile t)

let fid_of_nd ?(force_PVF=false) options pr kv nd =
  T.__make_file_entity ~force_PVF options ~digest:nd#data#get_content_digest ~path:nd#data#path pr kv

let fent_of_nd options ?(force_PVF=false) pr kv nd =
  T._make_file_entity ~force_PVF options ~digest:nd#data#get_content_digest ~path:nd#data#path pr kv

let create_fact_buf = Fact_base.create_fact_buf

let _extract_fact fact_buf options pr kv all_leaves =
  let stree_id = T.__make_srctree_entity options kv in
  let stree_ent = T.mkent stree_id in
  let vent = T.make_version_entity kv in

  if not (T.is_ghost_node vent) then begin
    fact_buf#add (vent, T.p_is_a, T.c_version);
    fact_buf#add (stree_ent, T.p_version, vent);
  end;
  fact_buf#add (stree_ent, T.p_is_a, T.c_srctree);

  List.iter
    (fun nd ->
      let ent = fent_of_nd options pr kv nd in
      fact_buf#add (ent, T.p_is_a, T.c_file);
      fact_buf#add (ent, T.p_in_srctree, stree_ent);
      fact_buf#add (stree_ent, T.p_contains_file, ent);

      if not (T.is_ghost_node vent) then
        fact_buf#add (ent, T.p_version, vent);

      let loc_lit = T.make_literal nd#data#path in

      if nd#data#is_auxfile then begin
        fact_buf#add (ent, T.p_is_a, T.c_auxfile);
	let gp = Triple.p_guard T.p_file_location in
	let bn = Triple.gen_blank_node() in
        fact_buf#add_group
          [(ent, T.p_file_location, loc_lit);
           (bn, gp, ent);(bn, gp, loc_lit);(bn, T.p_version, vent)]
      end
      else
        fact_buf#add (ent, T.p_file_location, loc_lit);

    ) all_leaves;

  stree_id, stree_ent


let extract_fact options ~dtree_opt ~proj_root ~version tree =
  try
    let dtree =
      match dtree_opt with
      | Some dt -> dt
      | None -> let dt, _ = of_tree options false tree in dt
    in

    let cache_path = get_cache_path1 options dtree in

    Cache.prepare_cache_dir options cache_path;

    Xprint.verbose options#verbose_flag "cache: %s" cache_path;

    let all_leaves = dtree#get_whole_initial_leaves in
    let all_files = mkfiles tree all_leaves in

    if options#fact_flag then begin
      let into_virtuoso = options#fact_into_virtuoso <> "" in
      let into_directory = options#fact_into_directory <> "" in

      let fact_buf = create_fact_buf options ~into_virtuoso ~into_directory cache_path in

      let _, _ = _extract_fact fact_buf options proj_root version all_leaves in

      if not fact_buf#is_closed then
        fact_buf#close
    end;

    cache_path, dtree, all_files

  with
  | To_be_skipped -> begin
      Xprint.message "no relevant source files found.";
      exit 0
  end
  | T.Lock_failed -> begin
      Xprint.warning "fact buffer is already locked.";
      exit 0
  end
