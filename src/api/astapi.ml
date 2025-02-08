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
 *
 * astcore.ml
 *
 *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xhash = Diffast_misc.Xhash
module Xfile = Diffast_misc.Xfile
module Xprint = Diffast_misc.Xprint
module Loc = Diffast_misc.Loc
module Storage = Diffast_misc.Storage
module Stat = Diffast_core.Stat
module Spec_base = Diffast_core.Spec_base
module Spec = Diffast_core.Spec
module Cache = Diffast_core.Cache
module Entity = Diffast_core.Entity
module Triple = Diffast_core.Triple
module Astml = Diffast_core.Astml
module Misc = Diffast_core.Misc
module Dirtree_base = Diffast_core.Dirtree_base
module Fact_base = Diffast_core.Fact_base
module Lang_base = Diffast_core.Lang_base
module GIDfragment = Diffast_core.GIDfragment

open Printf

module DTB = Dirtree_base
module S   = Stat
module SF  = Stat.File
module SD  = Stat.Dir
module OC  = Spec_base.OutChannel


exception Skip of string


type frag_dump_mode = M_ORIGIN | M_ENDING


[%%capture_path
class virtual base_c options = object (self)

  val extra_source_file_tbl  = Hashtbl.create 0 (* path -> file *)

  val extra_source_file_tbl1 = Hashtbl.create 0
  val extra_source_file_tbl2 = Hashtbl.create 0

  method virtual __parse_file : ?proj_root:string -> ?version:Entity.version -> Storage.file -> Spec.tree_t

  method private _add_extra_source_file tbl ext file =
    let fp = file#fullpath in
    if not (Hashtbl.mem tbl fp) then begin
      self#verbose_msg "extra source file: \"%s\" ext=\"%s\"" fp ext;
      file#set_extra_ext ext;
      Hashtbl.add tbl fp file
    end

  method private _extra_source_files tbl =
    Hashtbl.fold (fun _ f l -> f :: l) tbl []

  method add_extra_source_file  = self#_add_extra_source_file extra_source_file_tbl

  method add_extra_source_files ext  = List.iter (self#add_extra_source_file ext)
  method extra_source_files  = self#_extra_source_files extra_source_file_tbl

  method add_extra_source_file1 = self#_add_extra_source_file extra_source_file_tbl1
  method add_extra_source_file2 = self#_add_extra_source_file extra_source_file_tbl2

  method add_extra_source_files1 ext = List.iter (self#add_extra_source_file1 ext)
  method add_extra_source_files2 ext = List.iter (self#add_extra_source_file2 ext)

  method extra_source_files1 = self#_extra_source_files extra_source_file_tbl1
  method extra_source_files2 = self#_extra_source_files extra_source_file_tbl2


  method verbose_msg : 'a. ('a, unit, string, unit) format4 -> 'a =
    Xprint.verbose options#verbose_flag

  method get_cache_path1 = options#get_cache_path_for_file1


  method search_cache_for_info cache_path =
    let paths =
      Cache.search_cache
        ~fuzzy:options#fuzzy_cache_flag
        ~local_cache_name:options#local_cache_name
        cache_path
        S.info_file_name
    in
    paths

  method search_cache_for_stat cache_path =
    Cache.search_cache
      ~fuzzy:options#fuzzy_cache_flag
      ~completion:true
      ~local_cache_name:options#local_cache_name
      cache_path
      S.stat_file_name

  method is_processed_tree dtree_opt_ref tree =
    let cache_name =
      match tree#kind with
      | Storage.K_GIT _ -> (Cache.make_cache_name_for_dir1 tree#id)
      | Storage.K_FS ->
          let dtree, _ = DTB.of_tree options false tree in
          dtree_opt_ref := Some dtree;
          Cache.make_cache_name_for_dir1 (Xhash.to_hex dtree#digest)
      | _ -> assert false
    in
    let cache_path = Cache.create_cache_path options cache_name in
    self#verbose_msg "cache path: %s" cache_path;
    self#search_cache_for_info cache_path <> []


  method private _dump_dir_info cache_path dtree ast_nodes =
    let path = Filename.concat cache_path S.info_file_name in
    Xfile.dump path (SD.dump_info_ch dtree ast_nodes)


  method private dump_coverage_ch (nknown, nnodes, cov) ch =
    fprintf ch "origin known: %d\nnodes: %d\ncoverage: %f" nknown nnodes cov

  method private dump_coverage path (nknown, nnodes, cov) =
    Xfile.dump path (self#dump_coverage_ch (nknown, nnodes, cov))

  method private mkfragfilepath cache_path fname revindex =
    sprintf "%s-%d" (Filename.concat cache_path fname) revindex

  method private dump_fragment mode path nds_tbl =
    let l = ref [] in
    Hashtbl.iter
      (fun nd nds ->
        let sz = (* nodes originated from macros excluded *)
          List.fold_left
            (fun s n ->
              if n#data#not_frommacro then s + 1 else s
            ) 0 nds
        in
        let gids = List.map (fun n -> n#gindex) nds in
        let frag = GIDfragment.from_list gids in
        let ndat = nd#data in
        l := [(match mode with M_ORIGIN -> "ORIGIN" | M_ENDING -> "ENDING");
              (match mode with M_ORIGIN -> ndat#origin | M_ENDING -> ndat#ending);
              Loc.to_string ndat#src_loc;
              string_of_int sz;
              ndat#label;
              frag#to_string;
            ]::!l
      ) nds_tbl;
    let get_sz line = int_of_string (List.nth line 3) in
    let csv =
      List.fast_sort
        (fun x y ->
          Stdlib.compare (get_sz y) (get_sz x)
        ) !l
    in
    Csv.save path csv



  method parse_file
      ?(fact_store=None)
      ?(show_info=false)
      ?(proj_root="")
      ?(version=Entity.unknown_version)
      ?(versions=[])
      ?(get_cache_dir_only=false)
      file
      =
    let r =
      self#_parse_file
        ~fact_store
        ~show_info
        ~proj_root ~version ~versions
        ~get_cache_dir_only file
    in
    file#free_local_file;
    r

  method handle_file_versions ?(lock=true)
      fact_store cache_path proj_root file versions
      =
    if
      List.exists (fun v -> v <> Entity.unknown_version) versions
    then begin
      if options#fact_flag then begin
        try
          let store =
            match fact_store with
            | Some st -> st
            | None -> new Fact_base.fact_store ~lock options cache_path
          in
          List.iter
            (fun ver ->
              if ver <> Entity.unknown_version then begin
                let fent =
                  Triple.file_entity_of_tree_entry options proj_root ver file
                in
                store#_set_ver_class ver;
                store#_set_version ver fent;
                let loc = Triple.get_proj_rel_path proj_root file#path in
                store#_set_file_location ver fent loc
              end
            ) versions;
          match fact_store with
          | Some _ -> ()
          | None -> store#close
        with
        | Triple.Lock_failed ->
            Xprint.warning "fact buffer is already locked."
      end
      else begin
        List.iter
          (fun ver ->
            S._dump_source_path cache_path ver file#path
          ) versions
      end
    end


  method _parse_file
      ?(fact_store=None)
      ?(show_info=false)
      ?(proj_root="")
      ?(version=Entity.unknown_version)
      ?(versions=[])
      ?(get_cache_dir_only=false)
      file
      =
    let cache_path = self#get_cache_path1 file in

    [%debug_log "cache_path=\"%s\"" cache_path];

    if get_cache_dir_only then begin
      printf "%s\n" cache_path;
      SF.dummy_info
    end
    else begin
      let info_paths = self#search_cache_for_info cache_path in
      if
        info_paths <> [] &&
        not
          (
           options#dump_ast_flag ||
           (*options#dump_src_flag ||*)
           (*options#dump_origin_flag ||*)
           options#clear_cache_flag
          )
      then begin

        if show_info then
          self#verbose_msg "using caches%s:\n%s"
            (if options#local_cache_name = "" then
              ""
            else
              sprintf " (local cache name: %s)" options#local_cache_name)
            (Xlist.to_string
               (fun x -> "\""^x.Cache.sr_cache_path^"\"") "\n" info_paths);


        self#handle_file_versions ~lock:false fact_store cache_path proj_root file
          (version :: versions);

        let info = SF.scan_info info_paths in

        if show_info then
          SF.show_info info;

        info

      end
      else begin (* not processed || dump_ast || dump_src || dump_origin || clear_cache *)
        let _ = Cache.prepare_cache_dir options cache_path in
        let tree = self#__parse_file ~proj_root ~version file in

        if options#recover_orig_ast_flag then
          tree#recover_true_children ~initial_only:true ();

        if options#dump_dot_flag then begin
          let fname_dot = file#basename^".dot" in
          let dot = tree#to_dot_initial (*file#basename*) [] in
          Xfile.dump fname_dot
            (fun ch ->
              let buf = Buffer.create 0 in
              Buffer.add_string buf "digraph {";
              Buffer.add_buffer buf dot;
              Buffer.add_string buf "}";
              Buffer.output_buffer ch buf
            );
          self#verbose_msg "AST (in DOT) saved in \"%s\"" fname_dot
        end;

        if options#dump_ast_flag then begin
          let fname_astml = file#fullpath^Astml.extension in
          match Misc.find_file_name_with_exts fname_astml Astml.extensions with
          | Some fn -> Xprint.warning "already exists: \"%s\"" fn
          | None ->
              tree#dump_astml ~comp:options#ast_compression fname_astml;
              self#verbose_msg "AST (in ASTML) saved in \"%s\"" fname_astml
        end;

        if options#dump_src_flag then begin
          let opening = options#dump_src_out <> "" in
          let ch =
            if opening then
              open_out options#dump_src_out
            else
              Stdlib.stdout
          in
          tree#unparse_ch (OC.of_pervasives ch);
          if opening then
            close_out ch
        end;

        S._dump_source cache_path tree;
        S._dump_parser cache_path tree;
        SF.dump_info cache_path tree;

        self#handle_file_versions ~lock:false fact_store cache_path proj_root file
          (version :: versions);

        let info = SF.get_tree_info tree in

        if show_info then begin
          SF.dump_info_ch info stdout;
          flush stdout
        end;

        info

      end (* if not processed *)

    end (* if not get_cache_dir_only *)


  method private parse_file_and_handle_info ?(head="") fact_store proj_root version file handler =
    let head =
      if options#fact_proj <> "" then
        head^"["^options#fact_proj^"]"
      else
        head
    in
    try
      let info = self#parse_file ~fact_store ~proj_root ~version file in
      handler info
    with
    | Failure msg                        -> Xprint.warning ~head:(head^"[FAILURE]") "%s" msg
    | Lang_base.Error msg                -> Xprint.warning ~head:(head^"[LANG]") "%s" msg
    | Lang_base.Parse_error(head', msg)  -> Xprint.warning ~head:(head^head') "%s" msg
    | Astml.External_parser_not_found pn -> Xprint.warning ~head "external parser not found: \"%s\"" pn

  method virtual __force_to_process : bool

  method extract_fact_from_dir tree =
    let dtree_opt_ref = ref None in
    let is_processed =
      self#is_processed_tree dtree_opt_ref tree &&
      not self#__force_to_process
    in
    if is_processed then
      Xprint.message "already processed: \"%s\"" tree#name
    else
      let proj_root =
        try
          options#fact_proj_roots.(0)
        with
        | _ -> ""
      in
      let version =
        try
          options#fact_versions.(0)
        with
        | _ -> Entity.unknown_version
      in
      let cache_path, dtree, files =
        DTB.extract_fact options ~dtree_opt:(!dtree_opt_ref) ~proj_root ~version tree
      in
      let ast_nodes = ref 0 in

      let fact_store =
        if options#fact_flag then
          let _fact_store = new Fact_base.fact_store ~lock:false options cache_path in
          Some _fact_store
        else
          None
      in

      let proc ?(head="") =
        List.iter
          (fun file ->
            self#parse_file_and_handle_info ~head fact_store proj_root version file
              (fun info -> ast_nodes := !ast_nodes + info.SF.i_nodes)
          )
      in
      proc ~head:"[dir]" files;

      let extra = self#extra_source_files in

      if extra <> [] then
        self#verbose_msg "parsing extra source files...";

      proc ~head:"dir:extra" extra;

      begin
        match fact_store with
        | Some _fact_store -> _fact_store#close
        | None -> ()
      end;

      self#_dump_dir_info cache_path dtree !ast_nodes


end (* of class Astcore.base_c *)
]

[%%capture_path
class c options = object (self)
  inherit base_c options

  method __force_to_process =
    options#dump_ast_flag || options#clear_cache_flag

  method __parse_file ?(proj_root="") ?(version=Entity.unknown_version) file =
    [%debug_log "parsing \"%s\"" file#fullpath];
    printf "parsing \"%s\"\n" file#fullpath;

    let ext = file#get_extension in
    let lang = Lang_base.search options ext in
    let builder = lang#make_tree_builder options in
    let tree = builder#build_tree file in

    begin
      let extra = builder#extra_source_files in
      match options#fact_versions with
      | [|_|] -> self#add_extra_source_files ext extra
      | _ -> ()
    end;

    if proj_root <> "" then
      tree#set_proj_root proj_root;

    if version <> Entity.unknown_version then begin
      let k, v = version in
      tree#set_vkind k;
      tree#set_version v
    end;

    if options#fact_flag then begin
      let cache_path = self#get_cache_path1 file in
      self#verbose_msg "extracting source fact...";
      lang#extract_fact options cache_path tree;
      self#verbose_msg "done.";
    end;

    tree

end (* of class Astcore.c *)
]
