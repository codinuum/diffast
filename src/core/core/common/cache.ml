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
(* cache.ml *)

module Xfile = Diffast_misc.Xfile
module Xprint = Diffast_misc.Xprint

let completion_file_name = "COMPLETE"


let make_cache_name_for_file2 h1 h2 = Printf.sprintf "%s-%s" h1 h2

let make_cache_name_for_dir1 h = Printf.sprintf "d.%s" h
let make_cache_name_for_dir2 h1 h2 = Printf.sprintf "d.%s-%s" h1 h2

let get_cache_name options cache_path =
  let bn = Filename.basename cache_path in
  if options#local_cache_name = "" then
    bn
  else
    if options#local_cache_name = bn then
      let n = Filename.basename (Filename.dirname cache_path) in
      Filename.concat n bn
    else
      assert false


let create_layered_cache_path options cache_name =
  let sub0 = String.sub cache_name 0 2 in
  let sub =
    if sub0 = "d." then
      String.sub cache_name 2 2
    else
      sub0
  in
  let res =
    Filename.concat (Filename.concat options#cache_dir_base sub) cache_name
  in
  res

let create_cache_path options cache_name =
  if options#layered_cache_flag then
    create_layered_cache_path options cache_name
  else
    Filename.concat options#cache_dir_base cache_name

let prepare_dir perm dir =
  if not (Xfile.dir_exists dir) then
    Xfile.mkdir ~perm dir

let prepare_cache_dir options cache_path =
  if Xfile.file_exists cache_path then
    if not (Xfile.is_dir cache_path) then
      raise (Invalid_argument "Cache.prepare_cache");

  let base = Filename.dirname cache_path in
  prepare_dir options#default_dir_permission base;

  if options#clear_cache_flag then begin
    Xprint.verbose options#verbose_flag "cleaning up and preparing directory: %s" cache_path;
    Xfile.rmdir cache_path
  end;
  Xfile.mkdir cache_path

let prepare_cache options cache_name =
  let cache_path = create_cache_path options cache_name in
  prepare_cache_dir options cache_path;
  cache_path


let put_completion_mark cache_path =
  Xfile.touch (Filename.concat cache_path completion_file_name)


let is_completed cache_path =
  let fexists n = Xfile.file_exists (Filename.concat cache_path n) in
  fexists completion_file_name

(*
let has_files files cache_path =
  let res =
    List.for_all (fun n -> Xfile.file_exists (Filename.concat cache_path n)) files
  in
  DEBUG_MSG "\"%s\" --> %B" cache_path res;
  res
*)

type search_result = { sr_cache_path : string;
                       sr_path       : string;
                     }

let mkres cache_path name =
  { sr_cache_path=cache_path;
    sr_path=Filename.concat cache_path name
  }

let search_cache ?(fuzzy=true) ?(completion=false) ?(local_cache_name="") cache_path name =

  if Xfile.file_exists cache_path then begin

    let search fn =
      let fpath = Filename.concat cache_path fn in
      if Xfile.file_exists fpath then
        [ {sr_cache_path=cache_path; sr_path=fpath} ]
      else if not fuzzy && local_cache_name = "" then
        []
      else begin

        let bname = Filename.basename cache_path in
        if bname = local_cache_name then begin
          let dpath = Filename.dirname cache_path in
          try
            let other_cache_names =
              Array.to_list (Sys.readdir dpath)
            in
            List.filter
              (fun r -> Xfile.file_exists r.sr_path)
              (List.map
                 (fun cn ->
                   mkres (Filename.concat dpath cn) fn
                 ) other_cache_names)
          with
            _ -> []
        end
        else if fuzzy && local_cache_name = "" then begin
          try
            let other_cache_names =
              Array.to_list (Sys.readdir cache_path)
            in
            List.filter
              (fun r -> Xfile.file_exists r.sr_path)
              (List.map
                 (fun cn ->
                   mkres (Filename.concat cache_path cn) fn
                 ) other_cache_names)
          with
            _ -> []
        end
        else
          []

      end
    in
    let paths =
      if completion then
        if (search completion_file_name) <> [] then
          search name
        else
          []
      else
        search name
    in
    paths

  end
  else
    []
