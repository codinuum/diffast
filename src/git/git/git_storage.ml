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
(* Git_storage *)

[%%prepare_logger]

module Xhash = Diffast_misc.Xhash
module Xprint = Diffast_misc.Xprint
module Xfile = Diffast_misc.Xfile
module Xoption = Diffast_misc.Xoption
module Xchannel = Diffast_misc.Xchannel
module Storage = Diffast_misc.Storage

open Lwt
open Printf

[%%capture_path
module F (S: Git.S) = struct

  module Hash   = S.Hash
  module Value  = S.Value
  module Commit = Value.Commit
  module Blob   = Value.Blob
  module Tag    = Value.Tag
  module Tree   = Value.Tree
  module User   = Git.User

  let dir_sep_pat = Str.regexp_string Filename.dir_sep


  class entry ~dirname ~name ~is_dir ~digest ?(blob_handle=None) es : Storage.entry_t = object

    method path = Filename.concat dirname name
    method dirname = dirname
    method name = name
    method is_dir = is_dir
    method size = 0
    method file_digest = digest

    method get_content () =
      match blob_handle with
      | None -> ""
      | Some x -> x

    method dir_digest =
      if is_dir then
        Some digest
      else
        None

    method entries =
      [%debug_log "name=\"%s\" entries=[%s]"
        name (String.concat ";" (List.map (fun e -> e#name) es))];
      es

  end (* of class Git_storage.F.entry *)


  class entry_cache = object
    val sha1_tbl = (Hashtbl.create 0 : (Hash.t, (string, Storage.entry_t) Hashtbl.t) Hashtbl.t)

    method add sha1 dirname name (ent : Storage.entry_t) =
      [%debug_log "sha1=%s dirname=\"%s\" name=\"%s\" -> <%s>" (Hash.to_hex sha1) dirname name ent#path];
      let path = Filename.concat dirname name in
      let tbl =
        try
          Hashtbl.find sha1_tbl sha1
        with
          Not_found ->
            let t = Hashtbl.create 0 in
            Hashtbl.add sha1_tbl sha1 t;
            t
      in
      Hashtbl.add tbl path ent

    method find sha1 dirname name =
      [%debug_log "sha1=%s dirname=\"%s\" name=\"%s\"" (Hash.to_hex sha1) dirname name];
      try
        let tbl = Hashtbl.find sha1_tbl sha1 in
        let path = Filename.concat dirname name in
        try
          let e = Hashtbl.find tbl path in
          Some e
        with
          Not_found -> begin
            let e0_opt =
              Hashtbl.fold
                (fun _ e x_opt ->
                  match x_opt with
                  | Some _ -> x_opt
                  | None ->
                      let rec conv dn x =
                        let dn' = Filename.concat dn x#name in
                        let es = List.map (conv dn') x#entries in
                        new entry ~dirname:dn ~name:x#name ~is_dir:x#is_dir ~digest:x#file_digest es
                      in
                      let e_ = conv dirname e in
                      [%debug_log "  -> <%s>" e_#path];
                      Some e_
                ) tbl None
            in
            match e0_opt with
            | Some e ->
                Hashtbl.add tbl path e;
                e0_opt
            | None -> None
          end

      with
        Not_found -> None


  end (* of Git_storage.F.entry_cache *)


  class path_entry_cache = object (self)
    val tbl = (Hashtbl.create 0 : (string, Storage.entry_t) Hashtbl.t)

    method size = Hashtbl.length tbl

    method add path (ent : Storage.entry_t) =
      [%debug_log "\"%s\" -> <%s>" path ent#path];
      match self#find path with
      | Some _ -> ()
      | None -> Hashtbl.add tbl path ent

    method find path =
      [%debug_log "path=\"%s\"" path];
      try
        let e = Hashtbl.find tbl path in
        [%debug_log "  -> <%s>" e#path];
        Some e
      with
        Not_found -> None

  end (* of class Git_storage.F.path_entry_cache *)


  let ieq s0 s =
    let b =
      (String.length s0 = String.length s) &&
      try
        let _ =
          String.iteri
            (fun i c0 -> if c0 <> Char.lowercase_ascii s.[i] then raise Exit)
            s0
        in
        true
      with
        Exit -> false
    in
    [%debug_log "\"%s\" vs \"%s\" -> %B" s0 s b];
    b


  class tree options ?(cache=new path_entry_cache) kind tmp_path_tbl id root = object (self)
    inherit Storage.tree

    val local_path_tbl = Hashtbl.create 0 (* path -> local path *)

    method hash_algo = options#hash_algo

    method kind = kind

    method id = id

    (* relative normalized path assumed *)
    method get_entry ?(ignore_case=false) _rpath =
      match cache#find _rpath with
      | Some e -> e
      | None -> begin
          let rpath =
            if ignore_case then String.lowercase_ascii _rpath else _rpath
          in
          let find_child ent n =
            let rec scan = function
              | [] -> raise Not_found
              | e::r ->
                  let cond =
                    if ignore_case then
                      ieq n e#name
                    else
                      e#name = n
                  in
                  if cond then
                    e
                  else
                    scan r
            in
            scan ent#entries
          in
          match rpath with
          | "" -> root
          | _ -> begin
              match cache#find (Filename.dirname rpath) with
              | Some e -> find_child e (Filename.basename rpath)
              | None -> begin

                  let p = Str.split dir_sep_pat rpath in

                  let _, entry =
                    List.fold_left
                      (fun (depth, parent) name ->

                        if depth > 0 then
                          cache#add
                            (if ignore_case then
                              String.lowercase_ascii parent#path
                            else
                              parent#path)
                            parent;

                        (depth + 1, find_child parent name)

                      ) (0, root) p
                  in
                  [%debug_log "\"%s\" --> %s" rpath entry#name];
                  cache#add _rpath entry;
                  entry
              end
          end
      end

    method get_channel ?(ignore_case=false) rpath =
      [%debug_log "\"%s\"" rpath];
      let e = self#get_entry ~ignore_case rpath in
      match e#get_content() with
      | "" -> raise Not_found
      | lpath -> new Xchannel.input_channel_ch (open_in lpath)

    method private _get_local_file path =
      [%debug_log "path=\"%s\"" path];
      try
        let lpath = Hashtbl.find local_path_tbl path in
        if Sys.file_exists lpath then begin
          [%debug_log "  -> \"%s\"" lpath];
          Some lpath
        end
        else begin
          Hashtbl.remove local_path_tbl path;
          None
        end
      with
        Not_found -> None

    method private reg_local_file ?(keep=false) path lpath =
      [%debug_log "path=\"%s\" lpath=\"%s\"" path lpath];
      Hashtbl.add local_path_tbl path lpath;
      if keep then
        self#keep_local_path path

    method get_local_file ?(ignore_case=false) path =
      [%debug_log "path=\"%s\"" path];
      match self#_get_local_file path with
      | Some local_path -> local_path
      | None -> begin
          let e = self#get_entry ~ignore_case path in
          let lpath = e#get_content() in

          if lpath = "" then
            raise Not_found;

          let keep = options#keep_filtered_temp_file_flag in
          let ext = Xfile.get_extension path in
          [%debug_log "keep=%B ext=\"%s\"" keep ext];

          try
            let filt = self#get_filter_by_ext ext in
            let buf = Buffer.create 128 in
            let ch = open_in lpath in
            begin
              try
                while true do
                  let line = input_line ch in
                  Buffer.add_string buf (filt line);
                  Buffer.add_string buf "\n"
                done
              with
                End_of_file -> ()
            end;
            close_in ch;
            let local_path, ch = Storage.open_temp_file path in
            Xprint.verbose options#verbose_flag "writing to \"%s\"..." local_path;
            [%debug_log "writing to \"%s\"..." local_path];
            output_string ch (Buffer.contents buf);
            close_out ch;
            self#reg_local_file ~keep path local_path;
            local_path
          with
            exn -> begin
              let _ = exn in
              [%debug_log "%s" (Printexc.to_string exn)];
              self#reg_local_file ~keep path lpath;
              lpath
            end
      end

    method free_local_file path =
      [%debug_log "path=\"%s\"" path];

      begin
        try
          let lpath = Hashtbl.find tmp_path_tbl path in
          [%debug_log "removing \"%s\"..." lpath];
          Sys.remove lpath;
          Hashtbl.remove tmp_path_tbl path;
        with
          exn -> begin
            let _ = exn in
            [%debug_log "%s" (Printexc.to_string exn)]
          end
      end;

      if self#is_kept_local_path path then
        ()
      else
        match self#_get_local_file path with
        | Some lpath -> begin
            try
              Sys.remove lpath;
              Hashtbl.remove local_path_tbl path;
            with
            | _ ->
                failwith
                  (Printf.sprintf
                     "Git_storage.F.tree#free_local_file: failed to remove \"%s\"" lpath)
        end
        | None -> ()

  end (* of class Git_storage.F.tree *)

  let opt_to_str = Xoption.to_string (fun x -> x)

  let dump_value sha1 = function
    | Git.Value.Commit commit -> begin
        printf "COMMIT: %s\n" (Hash.to_hex sha1);
        printf "  PARENT(S): %s\n"
          (String.concat " " (List.map Hash.to_hex (Commit.parents commit)));
        printf "  AUTHOR: \"%s\"\n" (Commit.author commit).User.name;
        printf "  COMMITTER: \"%s\"\n" (Commit.committer commit).User.name;
        printf "  MESSAGE: \"%s\"\n" (opt_to_str (Commit.message commit));
        printf "  TREE: %s\n" (Hash.to_hex (Commit.tree commit))
    end
    | Git.Value.Blob _ -> begin
        printf "BLOB: %s\n" (Hash.to_hex sha1)
    end
    | Git.Value.Tag tag -> begin
        printf "TAG: \"%s\":%s\n" (Tag.tag tag) (Hash.to_hex sha1);
        printf "  OBJECT: %s\n" (Hash.to_hex (Tag.obj tag));
        printf "  KIND: \"%s\"\n"
          (match Tag.kind tag with
          | Git.Tag.Blob -> "Blob" | Git.Tag.Commit -> "Commit" | Git.Tag.Tag -> "Tag"
          | Git.Tag.Tree -> "Tree");
        printf "  TAGGER: \"%s\"\n"
          (match Tag.tagger tag with None -> "" | Some u -> u.User.name);
        printf "  MESSAGE: \"%s\"\n" (opt_to_str (Tag.message tag));
    end
    | Tree tree -> begin
        printf "TREE:%s\n" (Hash.to_hex sha1);
        printf "  ENTRIES:\n";
        List.iter (fun e -> printf "    %s\n" e.Git.Tree.name) (Tree.to_list tree)
    end

  let is_dir e =
    match e.Git.Tree.perm with
    | `Dir -> true
    | _ -> false

  let is_dir_or_file e =
    match e.Git.Tree.perm with
    | `Dir
    | `Normal -> true
    | `Exec -> true
    | _ -> false

  type obj = Tree of tree | File of Storage.file


  let make_obj options repo_name t sha1_list =

    let cache = new entry_cache in

    let tmp_path_tbl = Hashtbl.create 0 in

    let make_blob_handle blob path =
      let str = Blob.to_string blob in
      let local_path, ch = Storage.open_temp_file path in
      [%debug_log "dumping \"%s\" into \"%s\"..." path local_path];
      output_string ch str;
      close_out ch;
      Hashtbl.add tmp_path_tbl path local_path;
      Some local_path
    in

    let rec make_entry _cache ?(read=true) dirname name sha1 =
      match cache#find sha1 dirname name with
      | Some e -> return e
      | None -> begin

          [%debug_log "read=%B dirname=\"%s\" name=\"%s\"" read dirname name];

          let digest = Xhash.of_hex (Hash.to_hex sha1) in

          if read then begin
            S.read_exn t sha1 >>= fun v -> begin
              match v with
              | Git.Value.Commit c -> make_entry _cache "" "" (Commit.tree c)

              | Git.Value.Tree tree -> begin
                  let filt e =
                    is_dir e || options#check_extension e.Git.Tree.name
                    (*true*)
                  in
                  let path = Filename.concat dirname name in
                  Lwt_list.map_s
                    (fun e ->
                      let read = is_dir_or_file e in

                      if read then
                        [%debug_log "TO BE READ: \"%s\" %s" e.Git.Tree.name (Hash.to_hex e.Git.Tree.node)];

                      make_entry _cache ~read path e.Git.Tree.name e.Git.Tree.node

                    ) (List.filter filt (Tree.to_list tree))
                    >>= fun es ->
                      List.iter (fun e -> _cache#add e#path e) es;
                      let ent = new entry ~dirname ~name ~is_dir:true ~digest es in
                      cache#add sha1 dirname name ent;
                      _cache#add path ent;
                      return ent
              end
              | Git.Value.Blob blob -> begin
                  let path = Filename.concat dirname name in
                  let blob_handle = make_blob_handle blob path in
                  let ent = new entry ~dirname ~name ~is_dir:false ~digest ~blob_handle [] in
                  (*cache#add sha1 dirname name ent;*)
                  return ent
              end
              | Git.Value.Tag _ ->
                  raise (Invalid_argument "make_entry: Tag")
            end
          end
          else begin
            let ent = new entry ~dirname ~name ~is_dir:false ~digest [] in
            return ent
          end
      end
    in (* make_entry *)

    let rec obj_of_sha1 sha1 =

      let _cache = new path_entry_cache in

      S.read_exn t sha1 >>= function
        | Git.Value.Commit commit -> begin
            let tree_sha1 = Commit.tree commit in
            make_entry _cache "" "" tree_sha1 >>= fun root ->
              let tree =
                let kind = Storage.kind_git repo_name in
                new tree options ~cache:_cache kind tmp_path_tbl (Hash.to_hex tree_sha1) root
              in
              [%debug_log "got tree for %s" (Hash.to_hex tree_sha1)];
              return (Tree tree)
        end
        | Git.Value.Tree _ -> begin
            make_entry _cache "" "" sha1 >>= fun root ->
              let tree =
                let kind = Storage.kind_git repo_name in
                new tree options ~cache:_cache kind tmp_path_tbl (Hash.to_hex sha1) root
              in
              [%debug_log "got tree for %s" (Hash.to_hex sha1)];
              return (Tree tree)
        end
        | Git.Value.Tag tag -> begin
            obj_of_sha1 (Tag.obj tag)
        end
        | Git.Value.Blob blob -> begin
            let h = Hash.to_hex sha1 in
            let digest = Xhash.of_hex h in
            [%debug_log "got blob for %s" h];
            let blob_handle = make_blob_handle blob h in
            let ent = new entry ~dirname:"" ~name:h ~is_dir:false ~digest ~blob_handle [] in
            let f = new Storage.file (Storage.Entry ent) h in
            return (File f)
        end
    in
    Lwt_list.map_s obj_of_sha1 sha1_list


end (* of functor Git_storage.F *)
]
