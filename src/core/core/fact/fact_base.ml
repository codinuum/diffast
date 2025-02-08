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
(* fact_base.ml *)

module Xhash = Diffast_misc.Xhash
module Xprint = Diffast_misc.Xprint
module Otree = Diffast_misc.Otree
module Loc = Diffast_misc.Loc


let mkver vkind ver = Triple.make_version_entity (vkind, ver)
let mklit = Triple.make_literal

let p_is_a          = Triple.p_is_a
let p_version       = Triple.p_version
let p_file_location = Triple.p_file_location

class virtual fact_buffer_tbl = object
  method virtual find : string -> Triple.buffer
  method virtual add : string -> Triple.buffer -> unit
  method virtual iter : (string -> Triple.buffer -> unit) -> unit
end

class separate_fact_buffer_tbl = object
  inherit fact_buffer_tbl
  val tbl = Hashtbl.create 0
  method find key = Hashtbl.find tbl key
  method add key buf = Hashtbl.add tbl key buf
  method iter f = Hashtbl.iter f tbl
end

class unified_fact_buffer_tbl = object
  inherit fact_buffer_tbl
  val mutable _buf = Triple.dummy_buffer
  method find (*key*)_ = _buf
  method add (*key*)_ buf = _buf <- buf
  method iter f = f "" _buf
end


let _apply_to_vkey_v vkind ver =
  if not (Entity.vkind_is_unknown vkind) && ver <> "" then
    let vkey = Entity.mkvkey vkind ver in
    let v = mkver vkind ver in
    fun f -> f vkind vkey v
  else
    fun _ -> ()

[%%capture_path
let create_fact_buf
    options
    ?(acquire_lock=(fun () -> ()))
    ?(fact_file_path="")
    ?(cache_name="")
    ~into_virtuoso
    ~into_directory
    cache_path
    =
  let fact_file_path =
    if fact_file_path = "" then
      Filename.concat cache_path Stat.fact_file_name
    else
      fact_file_path
  in
  let cache_name =
    if cache_name = "" then
      Cache.get_cache_name options cache_path
    else
      cache_name
  in
  let buf =
    if into_virtuoso then begin
      [%debug_log "preparing fact buffer for virtuoso..."];
      assert (not into_directory);
(*
      try
*)
        acquire_lock();
        new Triple.buffer_virtuoso options
(*
      with
      | Triple.Lock_failed -> Triple.dummy_buffer
*)
    end
    else if into_directory then begin
      [%debug_log "preparing fact buffer for directory..."];
(*
      try
*)
        acquire_lock();
        new Triple.buffer_directory options cache_name
(*
      with
      | Triple.Lock_failed -> Triple.dummy_buffer
*)
    end
    else begin
      [%debug_log "preparing fact buffer..."];
      try
        new Triple.buffer ~overwrite:false options fact_file_path
      with
      | Triple.File_exists s ->
          Xprint.warning "file exists: \"%s\"" s;
          Triple.dummy_buffer
    end
  in
  [%debug_log "done."];
  buf
]


[%%capture_path
class fact_store ?(lock=true) options cache_path =
  let fact_file_path =
    Filename.concat cache_path Stat.fact_file_name
  in
  let _ = [%debug_log "cache_path: %s" cache_path] in
  let _ = [%debug_log "fact_file_path: %s" fact_file_path] in
  let cache_name = Cache.get_cache_name options cache_path in
  let lock_fd = ref None in
  let acquire_lock() =
    if lock then
      let fd = Triple.lock_fact cache_path in
      lock_fd := Some fd
  in
  let into_virtuoso = options#fact_into_virtuoso <> "" in
  let into_directory = options#fact_into_directory <> "" in
  object (self)

    method id = ""

    method warning_msg : 'a. ('a, unit, string, unit) format4 -> 'a =
      Xprint.warning ~head:(if self#id = "" then "" else "["^self#id^"]") ~out:stderr

    method verbose_msg : 'a. ('a, unit, string, unit) format4 -> 'a =
      Xprint.verbose options#verbose_flag


    val fact_buf =
      create_fact_buf
        options
        ~acquire_lock ~fact_file_path ~into_virtuoso ~into_directory
        cache_path

    val a_fact_buf_tbl =
      if into_virtuoso || into_directory then begin
        let tbl = new unified_fact_buffer_tbl in
        if into_virtuoso then
          tbl#add "" (new Triple.buffer_virtuoso options)
        else if into_directory then
          tbl#add "" (new Triple.buffer_directory options cache_name);
        tbl
      end
      else
        new separate_fact_buffer_tbl


    method close =
      fact_buf#close;
      a_fact_buf_tbl#iter (fun _ buf -> buf#close);
      match !lock_fd with
      | None -> ()
      | Some fd -> Triple.unlock_fact fd


    method add (tri : Triple.t) =
      if not (Triple.is_ghost tri) then
        fact_buf#add tri

    method add_group (tri_list : Triple.t list) =
      if List.for_all (fun t -> not (Triple.is_ghost t)) tri_list then
        fact_buf#add_group tri_list

    method add_a (key : string) (tri_list : Triple.t list) =
      if List.for_all (fun t -> not (Triple.is_ghost t)) tri_list then
        try
          let buf = a_fact_buf_tbl#find key in
          buf#add_group tri_list
        with
        | Not_found -> begin
            let buf =
              try
                new Triple.buffer ~overwrite:false options (Triple.make_a_name key fact_file_path)
              with
                Triple.File_exists s ->
                  self#warning_msg "file exists: \"%s\"" s;
                  Triple.dummy_buffer
            in
            buf#add_group tri_list;
            a_fact_buf_tbl#add key buf
        end

    method add_vg key ((s, p, o) as tri : Triple.t) v =
      if not (Triple.is_ghost tri) then begin
        let gp = Triple.p_guard p in
        let bn = Triple.gen_blank_node() in
        let tri_l = [tri;(bn, gp, s);(bn, gp, o);(bn, p_version, v)] in
        self#add_a key tri_l
      end

    method _set_version (vkind, ver) ent =
      (_apply_to_vkey_v vkind ver)
        (fun (*vkind*)_ vkey v -> self#add_a vkey [ent, p_version, v])

    method _set_file_location (vkind, ver) ent floc  =
      let setfloc (*vkind*)_ vkey v =
        if floc <> "" then
          let floc_lit = mklit floc in
          self#add_vg vkey (ent, p_file_location, floc_lit) v
      in
      (_apply_to_vkey_v vkind ver) setfloc

    method _set_ver_class (vkind, ver) =
      let set_v_class vkind vkey v =
        let get_ver_class = function
          | Entity.V_REL -> Triple.c_release
          | Entity.V_SVNREV -> Triple.c_svnrev
          | Entity.V_GITREV -> Triple.c_gitrev
          | Entity.V_VARIANT -> Triple.c_variant
          | _ -> raise Not_found
        in
        try
          self#add_a vkey [v, p_is_a, get_ver_class vkind]
        with
          Not_found -> ()
      in
      (_apply_to_vkey_v vkind ver) set_v_class;


  end (* of class fact_store *)
]


[%%capture_path
module F (L : Spec.LABEL_T) = struct

  let mkent    = Triple.mkent
  let mkproj   = Triple.mkproj
  let mkrel    = Triple.mkrel
  let mksvnrev = Triple.mksvnrev
  let mkgitrev = Triple.mksvnrev
  let mkext    = Triple.mkext
  let mklit    = mklit

  let lit_ty_string = Triple.lit_ty_string
  let lit_ty_int    = Triple.lit_ty_int
  let lit_ty_nn_int = Triple.lit_ty_nn_int
  let lit_ty_real   = Triple.lit_ty_real

  let mksrcres = Triple.mksrcres

  let mkjres = Triple.mkjres
  let mkcres = Triple.mkcres
  let mkpres = Triple.mkpres
  let mkvres = Triple.mkvres
  let mkfres = Triple.mkfres
  let mkcppres = Triple.mkcppres

  let mkccxres = Triple.mkccxres

  let mkver = mkver

  let p_is_a        = p_is_a
  let p_parent      = Triple.p_parent
  let p_children    = Triple.p_children
  let p_child0      = Triple.p_child0
  let p_childx      = Triple.p_childx
  let p_value       = Triple.p_value
  let p_tree_digest = Triple.p_tree_digest


  let p_version     = p_version
  let p_file_digest = Triple.p_file_digest
  let p_in_file     = Triple.p_in_file
  let p_in_project  = Triple.p_in_project

  let p_file_location = p_file_location

  let p_binding     = Triple.p_binding


  let l_true = Triple.l_true
  let l_false = Triple.l_false




  let getlab nd = (Obj.obj nd#data#_label : L.t)
  let getannot nd = (Obj.obj nd#data#_annotation : L.annotation)
  let getloc nd = Loc.to_string nd#data#src_loc

  exception Node_found of Spec.node_t

  let rec find_node is_x nd =
    if is_x (getlab nd) then
      nd
    else
      try
        Array.iter
          (fun n ->
            try
              raise (Node_found (find_node is_x n))
            with
              Not_found -> ()
          ) nd#initial_children;
        raise Not_found
      with
        Node_found res -> res

  let get_surrounding_xxxs is_xxx nd =
    let xxxs = ref [] in
    let rec scan n =
      try
        let p = n#initial_parent in
        let plab = getlab p in
        if is_xxx plab then
          xxxs := p::!xxxs;
        scan p
      with
        Otree.Parent_not_found _ -> ()
    in
    scan nd;
    !xxxs

  let get_nearest_surrounding_xxx is_xxx nd =
    let rec scan n =
      try
        let p = n#initial_parent in
        let plab = getlab p in
        if is_xxx plab then
          p
        else
          scan p
      with
        Otree.Parent_not_found _ -> raise Not_found
    in
    scan nd






  class extractor_base options cache_path tree =
    let enc = options#fact_enc in
  object (self)

    inherit fact_store options cache_path as super

    val mutable lang_prefix = ""
    method set_lang_prefix p = lang_prefix <- p


    method set_version = super#_set_version (tree#vkind, tree#version)

    method set_file_location ent =
      let floc = Triple.get_proj_rel_path tree#proj_root tree#source_path in
      super#_set_file_location (tree#vkind, tree#version) ent floc


    val mutable fileentity = Triple.ghost

    val enc_str = Entity.encoding_to_string enc
    val fid_str = Triple.encode_fid options tree

    val mkextname = Triple.make_extname options tree

    method mkentity (nd : Spec.node_t) =
      let loc = nd#data#src_loc in
      [%debug_log "%s" nd#to_string];
      if loc = Loc.dummy then begin
        self#warning_msg "location not defined: %s@%s" nd#data#to_string tree#source_path;
        Triple.ghost
      end
      else if Triple.is_ghost_ast_node nd then begin
        Triple.ghost
      end
      else
        let range_str = Triple.get_range_str enc loc in
        let fid_str =
          let fid = nd#data#source_fid in
          [%debug_log "fid=%s" fid];
          if fid = "" then
            fid_str
          else
            fid
        in
        Triple.mkent
          (Triple.__make_entity
             enc_str fid_str range_str nd#data#is_phantom nd#data#is_special)


    method private mkfileentity =
      Triple.make_file_entity options tree

    method fileentity =
      if fileentity = Triple.ghost then begin
        fileentity <- self#mkfileentity;
        fileentity
      end
      else
        fileentity

    method mkbinding ?(loc_opt=None) bid = Triple.make_binding ~loc_opt options tree bid

    method mkextname lname = mkextname ~lang:lang_prefix lname

    method add_surrounding_xxx is_xxx (nd : Spec.node_t) ent pred =
      if not (Triple.is_ghost_node ent || Triple.is_ghost_ast_node nd) then begin
        try
          let pnd = tree#find_true_parent nd#uid in
          if is_xxx (getlab pnd) then
            self#add (ent, pred, self#mkentity pnd)
          else
            raise Not_found
        with
          Not_found ->
            try
              let xxx = get_nearest_surrounding_xxx is_xxx nd in
              self#add (ent, pred, self#mkentity xxx);
            with
              Not_found -> ()
      end

    method scanner_body_before_subscan
        ((*nd*)_ : Spec.node_t) ((*lab*)_ : L.t) ((*entity*)_ : Triple.node)
        = ()
    method scanner_body_after_subscan
        ((*nd*)_ : Spec.node_t) ((*lab*)_ : L.t) ((*entity*)_ : Triple.node)
        = ()

    val hash_algo = Xhash.algo_to_string Xhash.MD5 (* currently MD5 is used *)

    method get_tree_digest nd =
      match nd#data#_digest with
      | Some d -> String.concat Entity.sub_sep [hash_algo; Xhash.to_hex d]
      | _ -> raise Not_found


    method scan ?(parent_ent=None) nd =
      [%debug_log "nd=\"%s\"" nd#to_string];

      let entity = self#mkentity nd in
      let lab = getlab nd in
      let is_ghost = Triple.is_ghost_node entity in

      if is_ghost then begin
        let entl =
          Array.fold_left
            (fun l n ->
              l @ (self#scan ~parent_ent n)
            ) [] nd#initial_children
        in
        entl
      end
      else begin
        self#scanner_body_before_subscan nd lab entity;

        begin
          try
            let v = nd#data#get_value in
            self#add (entity, p_value, mklit v)
          with
            Not_found -> ()
        end;

        begin
          try
            let d = self#get_tree_digest nd in
            self#add (entity, p_tree_digest, mklit d)
          with
            Not_found -> ()
        end;

        let ent_a =
          Array.of_list
            (Array.fold_left
               (fun l n ->
                 l @ (self#scan ~parent_ent:(Some entity) n)
               ) [] nd#initial_children
            )
        in

        if options#fact_for_ast_flag then begin
          begin
            match parent_ent with
            | None -> ()
            | Some pent -> self#add (entity, p_parent, pent)
          end;
          if ent_a <> [||] then begin
            let target, ts = Triple.make_rdf_list ent_a in
            self#add_group ((entity, p_children, target) :: ts)
          end
        end;

        self#scanner_body_after_subscan nd lab entity;

        [entity]

      end


    method extract_before_scan =
      let ent = self#fileentity in
      self#add (ent, p_is_a, Triple.c_file);
      self#_set_ver_class (tree#vkind, tree#version);
      self#set_version ent;
      self#set_file_location ent;
      self#add (ent, p_file_digest, mklit tree#encoded_source_digest);


    method extract =
      self#verbose_msg "fact compression: %B" options#fact_compress_flag;
      self#extract_before_scan;
      ignore (self#scan tree#root);
      self#close



  end (* of class Fact_base.F.extractor_base *)


end (* of functor Fact_base.F *)
]
