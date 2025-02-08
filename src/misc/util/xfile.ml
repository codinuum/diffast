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
(* xfile.ml *)


exception No_such_file_or_directory of string
exception No_extension of string
exception Error of string

open Printf


let dir_sep_pat = Str.regexp_string Filename.dir_sep

let split_path ?(add_current_dir_name=true) path =
  let _ns = Str.split dir_sep_pat path in
  let ns =
    if Filename.is_relative path then
      if add_current_dir_name then
        Filename.current_dir_name :: _ns
      else
        _ns
    else
      Filename.dir_sep :: _ns
  in
  ns

let find_case_insensitive_path ?(prefix="") path =
  if path = "" then
    [""]
  else
    let ns, ini =
      if prefix = "" then
        split_path path, []
      else
        split_path ~add_current_dir_name:false path, [(prefix, "")]
    in
    try
      List.map (fun ((*p*)_, r) -> r)
        (List.fold_left
           (fun ps n ->
             match ps with
             | [] -> [(n, n)]
             | _ ->
                 if n = Filename.current_dir_name then
                   ps
                 else
                   let lcn = String.lowercase_ascii n in
                   List.concat_map
                     (fun (p, rel) ->
                       let xs = Array.to_list (Sys.readdir p) in
                       let filtered =
                         List.filter (fun x -> String.lowercase_ascii x = lcn) xs
                       in
                       if filtered = [] then
                         raise Exit
                       else
                         List.map
                           (fun x ->
                             if p = Filename.current_dir_name then
                               x, x
                             else
                               Filename.concat p x, Filename.concat rel x
                           ) filtered
                     ) ps
           ) ini ns)
    with
      Exit -> []


let normpath path =
  let normalize p =
    let sep = Filename.dir_sep in
    let pat0 = Str.regexp (sep^"+") in
    let pat1 = Str.regexp (sep^"\\."^sep) in
    let pat2 = Str.regexp (sep^"[^"^sep^" \\.]+"^sep^"\\.\\."^sep) in
    let pat3 = Str.regexp (sep^"[^"^sep^" \\.]+"^sep^"\\.\\.$") in
    let pat4 = Str.regexp (sep^"\\.$") in
    List.fold_left
      (fun s pat ->
        Str.global_replace pat sep s
      ) p [pat0; pat1; pat2; pat3; pat4]
  in
  let p = ref path in
  try
    while true do
      let n = normalize !p in
      if n = !p then
        raise Exit
      else
        p := n
    done;
    path
  with
    Exit -> !p

let abspath p =
  if Filename.is_relative p then
    normpath (Filename.concat (Sys.getcwd()) p)
  else
    normpath p

let relpath root_path path =
  if root_path = "" then begin
    path
  end
  else begin
    let sep = Filename.dir_sep in
    let r = Xstring.rstrip  ~strs:[sep] (normpath (abspath root_path)) in
    let p = normpath (abspath path) in
    let p' = Str.replace_first (Str.regexp ("^"^r)) "" p in
    if p = p' then
      path
    else
      let _rel = Xstring.lstrip ~strs:[sep] p' in
      let rel =
        if Filename.dir_sep <> "/" then
          Str.global_replace (Str.regexp_string Filename.dir_sep) "/" _rel
        else
          _rel
      in
      rel
  end

let common_dir_path paths =
  let rec doit acc ll =
    if List.mem [] ll then
      List.rev acc
    else
      let heads = List.map List.hd ll in
      let elem = List.hd heads in
      if List.for_all ((=) elem) (List.tl heads) then
        doit (elem::acc) (List.map List.tl ll)
      else
        List.rev acc
  in
  match paths with
  | [] -> ""
  | [p] -> p
  | _ ->
      let ll =
        List.map
          (fun p ->
            let l = Str.split (Str.regexp_string Filename.dir_sep) p in
            if Filename.is_relative p then
              l
            else
              "" :: l
          ) paths
      in
      String.concat Filename.dir_sep (doit [] ll)


let make_temp_dir ?(temp_dir=Filename.get_temp_dir_name()) prefix suffix =
  let prng = Random.State.make_self_init() in

  let make_temp_file_name temp_dir prefix suffix =
    let rnd = (Random.State.bits prng) land 0xffffff in
    Filename.concat temp_dir (sprintf "%s%06x%s" prefix rnd suffix)
  in

  let rec try_name counter =
    let name = make_temp_file_name temp_dir prefix suffix in
    try
      Unix.mkdir name 0o775;
      name
    with
    | Unix.Unix_error (Unix.EEXIST, "mkdir", _) as e ->
        if counter >= 100 then
          raise e
        else
          try_name (counter + 1)
    | e -> raise e
  in
  try_name 0



let get_file_size path =
  let sz = (Unix.stat path).Unix.st_size in
  sz


let file_exists path = Sys.file_exists path

let dir_exists path =
  try
    Sys.is_directory path
  with
    Sys_error _ -> false

let is_dir path =
  try
    Sys.is_directory path
  with
    Sys_error _ -> raise (No_such_file_or_directory path)


let rec scan_dir f dirname =
  try
    let h = Unix.opendir dirname in
    try
      while true do
        let n = Unix.readdir h in
        if n <> "." && n <> ".." then
          let fname = Filename.concat dirname n in
          if is_dir fname then
            scan_dir f fname
          else
            f fname
      done
    with
      End_of_file -> Unix.closedir h;
  with
    Unix.Unix_error(err, s1, s2) ->
      match err with
      | Unix.ENOENT -> ()
      | _ ->
          raise (Error (sprintf "%s: %s (%s)" s2 (Unix.error_message err) s1))


let rec rmdir dirname =
  [%info_log "removing \"%s\"" dirname];
  try
    let h = Unix.opendir dirname in
    try
      while true do
        let n = Unix.readdir h in
        if n <> "." && n <> ".." then
          let fname = Filename.concat dirname n in
          try
            if is_dir fname then
              rmdir fname
            else begin
              (* printf "removing: %s\n" fname; *)
              Unix.unlink fname
            end
          with
          | _ -> ()
      done
    with
      End_of_file ->
        begin
          Unix.closedir h;
          try
            Unix.rmdir dirname
          with
          | _ -> [%warn_log "not empty: %s" dirname]
        end
  with
    Unix.Unix_error(err, s1, s2) ->
      match err with
      | Unix.ENOENT -> ()
      | _ ->
          raise (Error (sprintf "%s: %s (%s)" s2 (Unix.error_message err) s1))


let change_extension fname ext =
  sprintf "%s%s" (Filename.chop_extension fname) ext

let add_extension fname ext = sprintf "%s.%s" fname ext

let add_extension_xml fname = add_extension fname "xml"


let get_extension fname =
  let len0 = String.length fname in
  try
    let len = String.length (Filename.chop_extension fname) in
    String.sub fname len (len0 - len)
  with
    Invalid_argument _ ->
      raise (No_extension fname)

let has_extension fname =
  try
    let _ = get_extension fname in
    true
  with
    No_extension _ -> false

let touch fname =
  try
    let ch = open_out fname in
    try
      close_out ch
    with
      Sys_error s -> let _ = s in [%warn_log "%s" s]
  with
    Sys_error s -> let _ = s in [%warn_log "%s" s]

let rec mkdir ?(perm=0o755) dir =
  [%info_log "creating \"%s\"" dir];
  try
    Unix.mkdir dir perm
  with
  | Unix.Unix_error(Unix.EEXIST, _, _) -> ()
  | Unix.Unix_error(Unix.ENOENT, _, _) ->
      mkdir ~perm (Filename.dirname dir);
      mkdir ~perm dir
  | Unix.Unix_error(err, f, a) ->
      raise (Error (sprintf "%s: \"%s\": %s" f a (Unix.error_message err)))

let move path path_ =
  let dir_ = Filename.dirname path_ in
  if not (dir_exists dir_) then
    mkdir dir_;
  Sys.rename path path_

let copy_file ?(buf_size=8192) ?(perm=0o666) path path_ =
  let buf = Bytes.create buf_size in
  try
    let dir_ = Filename.dirname path_ in
    if not (dir_exists dir_) then
      mkdir dir_;

    let f_in = Unix.openfile path [Unix.O_RDONLY] 0 in
    let f_out = Unix.openfile path_ [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] perm in
    let rec copy_loop () =
      match Unix.read f_in buf 0 buf_size with
      | 0 -> ()
      | r ->
          ignore (Unix.write f_out buf 0 r);
          copy_loop()
    in
    copy_loop();
    Unix.close f_in;
    Unix.close f_out
  with
  | Unix.Unix_error(err, f, a) ->
      raise (Error (sprintf "%s: \"%s\": %s" f a (Unix.error_message err)))


let dump ?(lock=true) ?(dir_perm=0o755) fname (dumper : out_channel -> unit) =
  let dn = Filename.dirname fname in
  if not (dir_exists dn) then begin
    mkdir ~perm:dir_perm dn;
  end;
  try
    let ch = open_out fname in
    let fd = Unix.descr_of_out_channel ch in
    let locked = ref false in
    begin
      try
        if lock then begin
          Unix.lockf fd Unix.F_TLOCK 0;
          locked := true
        end;
        dumper ch
      with
      | Sys_error s -> let _ = s in [%warn_log "%s" s]
      | Unix.Unix_error (err, _, _) ->
          let _ = err in
          [%warn_log "aborting dump to \"%s\" (%s)" fname (Unix.error_message err)]
    end;
    if !locked then begin
      try
        Unix.lockf fd Unix.F_ULOCK 0
      with
        Sys_error s -> let _ = s in [%warn_log "%s" s]
    end;
    begin
      try
        close_out ch
      with
        Sys_error s -> let _ = s in [%warn_log "%s" s]
    end
  with
    Sys_error s -> let _ = s in [%warn_log "%s" s]


let load ?(lock=false) fname (loader : in_channel -> 'a) =
  try
    let ch = open_in fname in
    let fd = Unix.descr_of_in_channel ch in
    let locked = ref false in

    let fini() =
      if !locked then begin
        try
          Unix.lockf fd Unix.F_ULOCK 0
        with
        | Unix.Unix_error(err, _, _) ->
            let _ = err in
            [%warn_log "%s" (Unix.error_message err)];
            ()
            (*failwith "Xfile.load: unlock"*)
      end;
      begin
        try
          close_in ch
        with
        | Unix.Unix_error(err, _, _) ->
            let _ = err in
            [%warn_log "%s" (Unix.error_message err)];
            ()
            (*failwith "Xfile.load: close"*)
      end
    in

    let result =
      try
        if lock then begin
          Unix.lockf fd Unix.F_TRLOCK 0;
          locked := true
        end;
        loader ch
      with
      | Sys_error s ->
          fini();
          let _ = s in
          [%warn_log "%s" s];
          failwith "Xfile.load"

      | Unix.Unix_error (err, _, _) ->
          fini();
          let _ = err in
          [%warn_log "failed to load \"%s\" (%s)" fname (Unix.error_message err)];
          failwith "Xfile.load"
    in
    fini();
    result

  with
  | Sys_error s ->
      let _ = s in
      [%warn_log "%s" s];
      failwith "Xfile.load"
