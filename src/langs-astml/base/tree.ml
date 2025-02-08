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
(* astml/tree.ml *)

[%%prepare_logger]

module Xhash = Diffast_misc.Xhash
module Sourcecode = Diffast_core.Sourcecode
module Triple = Diffast_core.Triple

open Common
open Label

module Tree = Sourcecode.Tree (Label)
open Tree


let comment_tag = "Comment"
let ignored_tag = "Ignored"

[%%capture_path
let conv_loc loc =
  try
    Scanf.sscanf loc "%d:%d(%d)-%d:%d(%d)"
      (fun sl sc so el ec eo ->
        Loc.make so eo sl sc el ec
      )
  with _ -> try
    Scanf.sscanf loc "%d(%d)-%d(%d)"
      (fun sl so el eo ->
        Loc.make so eo sl (-1) el (-1)
      )
  with _ -> try
    Scanf.sscanf loc "%d-%d"
      (fun so eo ->
        Loc.make so eo (-1) (-1) (-1) (-1)
      )
  with _ -> try
    Scanf.sscanf loc "%dL,%dC-%dC(%d-%d)"
      (fun sl sc ec so eo -> Loc.make so eo sl sc sl ec)
  with _ -> try
    Scanf.sscanf loc "%dL(%d-%d)"
      (fun sl so eo -> Loc.make so eo sl (-1) sl (-1))
  with _ -> try
    Scanf.sscanf loc "%dL,%dC-%dL,%dC(%d-%d)"
      (fun sl sc el ec so eo -> Loc.make so eo sl sc el ec)
  with _ -> try
    Scanf.sscanf loc "%dL-%dL(%d-%d)"
      (fun sl el so eo -> Loc.make so eo sl (-1) el (-1))

  with
  | _ ->
      [%debug_log "illegal location format: %s" loc];
      Loc.dummy
]



let conv_attrs attrs =
  List.map
    (fun (n, v) -> (n, v))
    (List.filter (* filter out non-label attributes *)
       (fun (n, _) -> not (is_non_label_attr n))
       attrs
    )

exception Ignore


(* toplevel conversion function *)
[%%capture_path
let of_file (options : #Parser_options.c) parser_name file doc =

  let ignored_regions = ref [] in

  let ast_ns = (get_conf parser_name)#ast_ns in

  [%debug_log "file=\"%s\" astns=\"%s\"" file#path ast_ns];

  let rec scan_xnode ?(ast_ns="") xnode =
    if xnode#localname = comment_tag || xnode#localname = ignored_tag then begin
      let v = xnode#get_attr location_attr_name in
      let l = conv_loc v in
      ignored_regions := (l.Loc.start_offset, l.Loc.end_offset) :: !ignored_regions;
      raise Ignore
    end;

    let children = scan_xnodes ~ast_ns xnode#children in
(*
  [%debug_log "elem=%s attrs=[%s]"
  name
  (Xlist.to_string
  (fun (n, v) -> sprintf "%s='%s'" n v)"; " xnode#attr_list)];
 *)
    let nd =
      mknode options
        { elem_name   = xnode#localname;
          elem_attrs  = conv_attrs xnode#attr_list;
          elem_parser = parser_name;
          elem_ast_ns = ast_ns;
        }
        children
    in
    let attr = xnode#get_attr in

    let is_initializer_list =
      try
        let v = attr is_initializer_list_attr_name in
        v = "true"
      with
        Not_found -> false
    in
    let nd =
      if
        is_initializer_list &&
        options#ignore_huge_arrays_flag &&
        (List.length children) >= options#huge_array_threshold
      then
        let hash = (new c options nd false)#digest in
        mknode options
          { elem_name   = "HugeArray";
            elem_attrs  = ("hash",Xhash.to_hex hash)::(conv_attrs xnode#attr_list);
            elem_parser = parser_name;
            elem_ast_ns = ast_ns;
          } []
      else
        nd
    in
    begin
      try
        let v = attr location_attr_name in
        let l = conv_loc v in
        nd#data#set_loc l
      with
        Not_found -> ()
    end;
    begin
      try
        let v = attr frommacro_attr_name in
        nd#data#set_frommacro v
      with
        Not_found -> ()
    end;
    begin
      try
        let v = attr gid_attr_name in
        let gid = int_of_string v in
        nd#data#set_gid gid
      with
        Not_found -> ()
    end;
    nd


  and scan_xnodes ?(ast_ns="") nodes =
    List.fold_right
      (fun n l -> try (scan_xnode ~ast_ns n)::l with Ignore -> l) nodes []
  in

  let root = doc in

  let nd =
    match root#children with
    | [xnode] -> scan_xnode ~ast_ns xnode
    | _ -> Xprint.failure "\"%s\": invalid ASTML" file#path
  in

  [%debug_log "got nodes"];

  let tree = new c options nd true in

  tree#set_ignored_regions !ignored_regions;

  begin
    try
      let p = root#get_attr Astml.parser_attr_name in
      tree#set_parser_name p;
      [%debug_log "parser_name <- %s" p]
    with
      Not_found -> warning_msg "parser name not found in \"%s\"" file#path
  end;
  begin
    try
      let s = root#get_attr Astml.source_attr_name in
      tree#set_source_path s;
      [%debug_log "source_path <- %s" s]
    with
      Not_found -> warning_msg "source name not found in \"%s\"" file#path
  end;
  begin
    try
      let d = root#get_attr Astml.source_digest_attr_name in
      tree#set_source_digest (Xhash.of_hex (decode_digest d));
      [%debug_log "source_digest <- %s" d]
    with
      Not_found -> warning_msg "source digest not found in \"%s\"" file#path
  end;

  [%debug_log "tree built"];

  tree#collapse;

  [%debug_log "tree collapsed"];

  tree
]
