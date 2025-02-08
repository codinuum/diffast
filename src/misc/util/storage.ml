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
(* Storage *)

[%%prepare_logger]


let open_temp_file rpath =
  let rp = "_" ^ (Str.global_replace (Str.regexp_string Filename.dir_sep) "_" rpath) in
  let temp_dir = Filename.concat (Filename.get_temp_dir_name()) "diffast" in
  if not (Sys.file_exists temp_dir) then
    Sys.mkdir temp_dir 0o775;
  Filename.open_temp_file ~temp_dir "" rp

type kind =
  | K_DUMMY
  | K_FS
  | K_GIT of string
  | K_UNKNOWN

let kind_fs = K_FS
let kind_git r = K_GIT r
let kind_dummy = K_DUMMY
let kind_unknown = K_UNKNOWN

let kind_to_string = function
  | K_DUMMY   -> "dummy"
  | K_UNKNOWN -> "unknown"
  | K_FS      -> "fs"
  | K_GIT r   -> "git:"^r

let kind_is_fs = function
  | K_FS -> true
  | _ -> false

let kind_is_git = function
  | K_GIT _ -> true
  | _ -> false

class type entry_t = object
  method path        : string
  method dirname     : string
  method name        : string
  method is_dir      : bool
  method size        : int
  method entries     : entry_t list
  method file_digest : Xhash.t
  method dir_digest  : Xhash.t option
  method get_content : unit -> string
end (* of class type Storage.entry_t *)

let rec scan_dir (* for files *)
    ?(recursive=true)
    dent
    (f : entry_t -> unit)
    =
  List.iter
    (fun ent ->
      try
        if ent#is_dir then
          if recursive then
            scan_dir ent f
          else
            ()
        else
          f ent
      with
        exn ->
          Xprint.warning "%s" (Printexc.to_string exn)
    ) dent#entries

let rec scan_dir_for_dirs exists dent (f : entry_t -> unit) =
  List.iter
    (fun ent ->
      if exists ent#path then
        if ent#is_dir then begin
          f ent;
          scan_dir_for_dirs exists ent f
        end
    ) dent#entries


[%%capture_path
class virtual tree = object (self)
  method virtual hash_algo       : Xhash.algo
  method virtual kind            : kind
  method virtual id              : string
  method virtual get_entry       : ?ignore_case:bool -> string -> entry_t (* "" means root *)
  method virtual get_channel     : ?ignore_case:bool -> string -> Xchannel.input_channel
  method virtual get_local_file  : ?ignore_case:bool -> string -> string
  method virtual free_local_file : string -> unit

  val kept_local_path_set = (Xset.create 0 : string Xset.t) (* path to be kept *)

  method keep_local_path path =
    Xset.add kept_local_path_set path

  method is_kept_local_path path =
    Xset.mem kept_local_path_set path

  val filter_tbl = (Hashtbl.create 0 : (string, (string -> string)) Hashtbl.t)

  method set_filter extl filt =
    List.iter (fun ext -> Hashtbl.add filter_tbl (String.lowercase_ascii ext) filt) extl

  method get_filter_by_ext ext = Hashtbl.find filter_tbl (String.lowercase_ascii ext)

  method get_filter_by_name name =
    let ext = Xfile.get_extension name in
    self#get_filter_by_ext ext

  method name =
    Printf.sprintf "%s:%s" (kind_to_string self#kind) self#id

  method exists ?(ignore_case=false) path =
    try
      let _ = self#get_entry ~ignore_case path in
      true
    with
      _ -> false

  method is_dir ?(ignore_case=false) path =
    try
      (self#get_entry ~ignore_case path)#is_dir
    with
      _ -> false

  method is_file ?(ignore_case=false) path =
    try
      not (self#get_entry ~ignore_case path)#is_dir
    with
      _ -> false

  method search_path ?(ignore_case=false) root_path path =
    [%debug_log "%s\n%!" path];
    let dent = self#get_entry ~ignore_case root_path in
    let found = ref [] in
    scan_dir_for_dirs (self#exists ~ignore_case) dent
      (fun ent ->
        let p = Xfile.normpath (Filename.concat ent#path path) in
        if self#exists ~ignore_case p then begin
          [%debug_log "found %s\n%!" p];
          found := (ent, p) :: !found
        end
      );
    !found

end (* of class Storage.tree *)
]

type obj_t = Tree of tree | Entry of entry_t

class file ?(digest_opt=None) ?(ignore_case=false) (obj : obj_t) (_path : string) =
  let path =
    if ignore_case then
      match obj with
      | Tree t -> (t#get_entry ~ignore_case:true _path)#path
      | Entry e -> e#path
    else
      _path
  in
  object (self)

  val mutable digest_opt = digest_opt

  val mutable extra_ext = None

  method set_extra_ext ext =
    extra_ext <- Some ext

  method set_digest d =
    digest_opt <- Some d

  method tree =
    match obj with
    | Tree t -> t
    | _ -> raise Not_found

  method fullpath =
    match obj with
    | Tree t -> Xfile.normpath (Filename.concat t#id path)
    | _ -> path

  method path          = path
  method basename      = Filename.basename path
  method dirname       = Filename.dirname path
  method is_dir        = self#get_entry#is_dir

  method exists =
    match obj with
    | Tree t -> t#exists path
    | Entry _ -> true

  method size = self#get_entry#size
  method kind =
    match obj with
    | Tree t -> t#kind
    | Entry _ -> kind_unknown

  method digest =
    match digest_opt with
    | Some d -> d
    | None -> self#get_entry#file_digest

  method get_extension   =
    match extra_ext with
    | None -> Xfile.get_extension path
    | Some x -> x

  method get_entry =
    match obj with
    | Tree t -> t#get_entry path
    | Entry e -> e

  method get_channel =
    match obj with
    | Tree t -> t#get_channel path
    | Entry e ->
        let str = e#get_content() in
        let ch = new Xchannel.input_channel_str str in
        ch

  method get_local_file =
    match obj with
    | Tree t -> t#get_local_file path
    | _ -> raise Not_found

  method free_local_file =
    match obj with
    | Tree t -> t#free_local_file path
    | _ -> ()

  method set_filter extl filt =
    match obj with
    | Tree t -> t#set_filter extl filt
    | _ -> ()

end (* of class Storage.file *)


class dummy_entry : entry_t = object
  method path    = "<dummy>"
  method dirname = "<dummy>"
  method name    = "<dummy>"
  method is_dir  = false
  method size    = 0
  method entries = []
  method file_digest  = ""
  method dir_digest = None
  method get_content() = ""
end

let dummy_entry = new dummy_entry

class dummy_tree = object
  inherit tree
  method hash_algo = Xhash.SHA256
  method kind      = K_DUMMY
  method id        = "<dummy>"
  method get_entry ?(ignore_case=false) _ = let _ = ignore_case in dummy_entry
  method! exists ?(ignore_case=false) _ = let _ = ignore_case in false

  method get_channel ?(ignore_case=false) _ =
    let _ = ignore_case in
    new Xchannel.input_channel_str "<dummy>"

  method get_local_file ?(ignore_case=false) _ =
    let _ = ignore_case in "<dummy>"

  method free_local_file _ = ()
end

let dummy_tree = new dummy_tree



let stdin = new file (Tree dummy_tree) "<stdin>"

