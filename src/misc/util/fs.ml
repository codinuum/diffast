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
(* Fs : abstraction of file system *)

[%%prepare_logger]


let strip_slashes name =
  let res = ref name in
  while Filename.check_suffix !res "/" do
    res := Filename.chop_suffix name "/"
  done;
  !res

let abspath p = Xfile.abspath (strip_slashes p)
let normpath p = Xfile.normpath (strip_slashes p)

[%%capture_path
class entry options _root_path _path : Storage.entry_t =
  let root_path = if _root_path = "" then "" else abspath _root_path in
  let path = normpath _path in
  object (self)

    initializer
      (*[%debug_log "root_path=\"%s\" path=\"%s\"" root_path path];*)
      ()

    method private abspath = Filename.concat root_path path

    method path = path

    method dirname = Filename.dirname path

    method name = Filename.basename path

    method size = Xfile.get_file_size self#abspath

    method is_dir =
      try
        Xfile.is_dir self#abspath
      with
      | _ -> false
      (*| Xfile.No_such_file_or_directory f ->
          Xprint.warning "\"%s\": no such file or directory" self#abspath;
          false
      | exn ->
          Xprint.warning "%s" (Printexc.to_string exn);
          false*)

    method entries =
      if self#is_dir then
        let dpath = self#abspath in
        (*[%debug_log "dpath=%s" dpath];*)
        let dirh = Unix.opendir dpath in
        let ns = ref [] in
        begin
          try
            while true do
              let e = Unix.readdir dirh in
              if e <> Filename.current_dir_name && e <> Filename.parent_dir_name then begin
                ns := (new entry options root_path (Filename.concat path e)) :: !ns
              end
            done
          with
            End_of_file -> ()
        end;
        Unix.closedir dirh;
        List.rev !ns
      else
        []

    method file_digest =
      if options#git_hash_flag then
        Xhash.git_digest_of_file self#abspath
      else
        Xhash.digest_of_file options#hash_algo self#abspath

    method dir_digest = None

    method get_content () = ""

end (* of class Fs.entry *)
]

let get_case_insensitive_path ?(prefix="") path =
  match Xfile.find_case_insensitive_path ~prefix path with
  | [] -> raise Not_found
  | [p] -> p
  | (p :: _) as ps -> begin
      match List.filter (fun x -> x = path) ps with
      | [_] -> path
      | _ -> p
  end

class entry_cache = object (self)
  val tbl = (Hashtbl.create 0 : (string, Storage.entry_t) Hashtbl.t)

  method size = Hashtbl.length tbl

  method add path ent =
    try
      let _ = self#find path in
      ()
    with
      Not_found ->
        Hashtbl.add tbl path ent

  method find path =
    Hashtbl.find tbl path

end

let scan_dir f root =
  let rec scan f dpath rdpath =
    Array.iter
      (fun name ->
        let path = Filename.concat dpath name in
        let path' = Filename.concat rdpath name in
        try
          if Sys.is_directory path then
            scan f path path'
          else
            f path path'
        with
          Sys_error _ -> ()
      ) (Sys.readdir dpath)
  in
  scan f root ""

[%%capture_path
class tree options _path =
  let root_path =
    if _path = "" then
      ""
    else
      abspath _path
  in
  object (self)
    inherit Storage.tree

    val mutable case_insensitive_root_path = ""

    val cache = new entry_cache

    val local_path_tbl = Hashtbl.create 0 (* path -> local path *)

    initializer
      [%debug_log "root_path=\"%s\"" root_path];

      if root_path <> "" then
        scan_dir
          (fun _ rpath ->
            let ent = new entry options root_path rpath in
            cache#add rpath ent
          ) root_path


    method private abspath rpath = Filename.concat root_path rpath


    method hash_algo = options#hash_algo

    method kind = Storage.kind_fs

    method id = root_path

    method private get_case_insensitive_rpath rpath =

      let root_path' =
        if case_insensitive_root_path = "" then
          case_insensitive_root_path <- get_case_insensitive_path root_path;
        case_insensitive_root_path
      in
      let rpath' = get_case_insensitive_path ~prefix:root_path' rpath in
      rpath'

    method private case_insensitive_abspath rpath =
      let rpath' = self#get_case_insensitive_rpath rpath in
      Filename.concat case_insensitive_root_path rpath'


    method get_entry ?(ignore_case=false) rpath = (* relative path *)
      try
        cache#find rpath
      with
        Not_found ->
          let ent =
            if ignore_case then begin
              let rpath' = self#get_case_insensitive_rpath rpath in
              new entry options case_insensitive_root_path rpath'
            end
            else begin
              let p = self#abspath rpath in
              if Xfile.file_exists p then
                new entry options root_path rpath
              else begin
                raise Not_found
              end
            end
          in
          cache#add rpath ent;
          ent

    method get_channel ?(ignore_case=false) rpath =
      let rp =
        if ignore_case then
          self#case_insensitive_abspath rpath
        else
          self#abspath rpath
      in
      new Xchannel.input_channel_ch (Stdlib.open_in rp)

    method private reg_local_file ?(keep=false) path lpath =
      Hashtbl.replace local_path_tbl path lpath;
      if keep then
        self#keep_local_path path

    method private _get_local_file path =
      try
        let lpath = Hashtbl.find local_path_tbl path in
        if Sys.file_exists lpath then
          Some lpath
        else begin
          Hashtbl.remove local_path_tbl path;
          None
        end
      with
        Not_found -> None

    method get_local_file ?(ignore_case=false) rpath =
      let ext = Xfile.get_extension rpath in
      let rp =
        if ignore_case then
          self#case_insensitive_abspath rpath
        else
          self#abspath rpath
      in
      try
        let filt = self#get_filter_by_ext ext in
        match self#_get_local_file rpath with
        | Some local_path -> local_path
        | None ->
            let local_path, ch = Storage.open_temp_file rpath in
            Xprint.verbose options#verbose_flag "writing to \"%s\"..." local_path;
            begin
              let ich = open_in rp in
              try
                while true do
                  let line = input_line ich in
                  output_string ch (filt line);
                  output_string ch "\n"
                done
              with
                End_of_file -> close_in ich
            end;
            close_out ch;
            self#reg_local_file ~keep:(options#keep_filtered_temp_file_flag) rpath local_path;
            local_path
      with
        _ -> rp

    method free_local_file rpath =
      if self#is_kept_local_path rpath then
        ()
      else
        match self#_get_local_file rpath with
        | Some lpath -> begin
            try
              Sys.remove lpath;
              Hashtbl.remove local_path_tbl rpath
            with
            | _ ->
                failwith
                  (Printf.sprintf
                     "Fs.F.tree#free_local_file: failed to remove \"%s\"" lpath)
        end
        | None -> ()

end (* of class Fs.tree *)
]

let make options ?(path="") () = new tree options path

[%%capture_path
let file_of_path options path =
  [%debug_log "path=\"%s\"" path];
  let apath = Xfile.abspath path in
  let is_dir =
    try
      Xfile.is_dir apath
    with
      Sys_error _ -> false
  in
  if is_dir then begin
    new Storage.file (Storage.Tree (make options ~path ())) ""
  end
  else begin
    if options#root_path <> "" then begin
      [%debug_log "root path=\"%s\"" options#root_path];
      let relpath = Xfile.relpath options#root_path path in
      if relpath <> path then
        new Storage.file (Storage.Tree (make options ~path:options#root_path ())) relpath
      else
        new Storage.file (Storage.Tree (make options ())) apath
    end
    else begin
      new Storage.file (Storage.Tree (make options ())) apath
    end
  end
]
