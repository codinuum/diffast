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
(* classinfo.ml *)

[%%prepare_logger]

module Xset = Diffast_misc.Xset
module Storage = Diffast_misc.Storage

open Common

exception Found of string


[%%capture_path
class classtbl_c = object (self)

  (* package name -> local name set (for standard library) *)
  val stdtbl = Classtbl.stdtbl

  (* package name -> local name set *)
  val pkg_mem_class_tbl = Hashtbl.create 0

  val mutable pkgs = Hashtbl.create 0 (* package name -> path *)

  val mutable searched_packages = []

  val mutable source_dir = None


  method set_source_dir d = source_dir <- Some d
  method has_source_dir =
    match source_dir with
    | None -> false
    | Some _ -> true

  method get_source_dir =
    match source_dir with
    | None -> raise Not_found
    | Some d -> d


  method private clear_packages = Hashtbl.clear pkgs


  method add_package ?(dir=Storage.dummy_entry) pname =
    try
      if pname = "" then
        raise Exit;

      [%debug_log "ADDING PACKAGE \"%s\"" pname];
      [%debug_log "               dir=%s" dir#path];

      Hashtbl.replace pkgs pname dir;

      let d, recursive =
        if dir == Storage.dummy_entry then begin
          match source_dir with
          | None -> raise Exit
          | Some srcdir -> srcdir, true
        end
        else
          dir, false
      in

      [%debug_log "SEARCHING %s for \"%s\"..." d#path pname];

      let pname_path = pkg_to_path pname in

      Storage.scan_dir ~recursive d
        (fun ent ->
          let path = ent#path in
	  if String.ends_with ~suffix:".java" path then
	    if String.ends_with ~suffix:pname_path ent#dirname then
	      let lname = Filename.chop_extension ent#name in
	      self#add pname lname
        )
    with
      Exit -> ()

  method add_api_package pname =
    try
      if pname = "" then
        raise Exit;

      [%debug_log "ADDING API PACKAGE \"%s\"" pname];

      Hashtbl.replace pkgs pname Storage.dummy_entry;

    with
      _ -> ()

  method private add pname lname =
    [%debug_log "ADDING: \"%s\" -> \"%s\"" pname lname];
    let s =
      try
        Hashtbl.find pkg_mem_class_tbl pname
      with
	Not_found ->
          let s' = Xset.create 1 in
          Hashtbl.add pkg_mem_class_tbl pname s';
          s'
    in
    Xset.add s lname

  method add_fqn fqn =
    let pname, lname = decompose_qname fqn in
    self#add pname lname

  method private __resolve tbl pname lname =
    let mems = Hashtbl.find tbl pname in
    if Xset.mem mems lname then
      pname^"."^lname
    else
      raise Not_found

  method _resolve lname =
    Hashtbl.iter
      (fun pkg _ ->
	try
	  raise (Found (self#__resolve pkg_mem_class_tbl pkg lname))
	with
	  Not_found -> ()
      ) pkgs;
    Hashtbl.iter
      (fun pkg _ ->
	try
	  raise (Found (self#__resolve stdtbl pkg lname))
	with
	  Not_found -> ()
      ) pkgs

  method resolve lname =
    [%debug_log "lname=\"%s\"" lname];
    try
      self#_resolve lname;
      self#__resolve stdtbl "java.lang" lname
    with
      Found fqn ->
        [%debug_log "found: \"%s\"" fqn];
	fqn

  method is_resolvable lname =
    try
      let _ = self#resolve lname in
      true
    with
      _ -> false

  method is_package qname =
    (Hashtbl.mem pkgs qname) || (Hashtbl.mem stdtbl qname)


  (* due to nested classes *)
  method get_package_name qname = (* qname = "a.b.c.lname" *)
    [%debug_log "qname=\"%s\"" qname];

    let rec find_pkg_prefix tbl qn =
      try
        let prefix, (*base*)_ = decompose_qname qn in
        if Hashtbl.mem tbl prefix then begin
          [%debug_log "found: \"%s\"" prefix];
          prefix
        end
        else
          find_pkg_prefix tbl prefix
      with
        Invalid_argument _ -> raise Not_found
    in
    try
      find_pkg_prefix pkgs qname
    with
      Not_found ->
        [%debug_log "searching stdtbl..."];
        find_pkg_prefix stdtbl qname


  method _resolve_qualified_type_name pkg qname =
    [%debug_log "pkg=%s qname=%s" pkg qname];
    if pkg = qname then
      failwith "Classinfo#_resolve_qualified_type_name";
    let lname = Str.replace_first (Str.regexp_string (pkg^".")) "" qname in
    [%debug_log "lname=%s" lname];
    let lname = replace_dot_with_dollar lname in
    if pkg = "" then
      lname
    else
      pkg^"."^lname

  method resolve_qualified_type_name qname =
    [%debug_log "qname=%s" qname];
    let pkg = self#get_package_name qname in
    [%debug_log "pkg=\"%s\"" pkg];
    self#_resolve_qualified_type_name pkg qname


end (* class Classinfo.classtbl_c *)
]
