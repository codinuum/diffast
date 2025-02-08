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
(* astml/lib_base.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xhash = Diffast_misc.Xhash
module XML = Diffast_misc.XML
module Storage = Diffast_misc.Storage
module Fs = Diffast_misc.Fs
module Astml = Diffast_core.Astml
module Sourcecode = Diffast_core.Sourcecode
module Lang_base = Diffast_core.Lang_base
module Cache = Diffast_core.Cache

open Common

let sprintf = Printf.sprintf

let comp_ext_list = Astml.comp_ext_list

let decomp = Sastml.decomp

let gen_temp_file_path () = Filename.temp_file "diffast_" Astml.extension


let setup_ns_mgr ns_mgr =
(*
  ns_mgr#add_ns Astml.default_prefix Astml.default_ns;
  ns_mgr#add_ns Astml.diffts_prefix  Astml.diffts_ns;
*)
  ns_mgr#add_ns Astml.c_prefix       Astml.c_ns;
  ns_mgr#add_ns Astml.cx_prefix      Astml.cx_ns;
  ns_mgr#add_ns Astml.ccx_prefix     Astml.ccx_ns;
  ns_mgr#add_ns Astml.java_prefix    Astml.java_ns;
  ns_mgr#add_ns Astml.python_prefix  Astml.python_ns;
  ns_mgr#add_ns Astml.verilog_prefix Astml.verilog_ns;
  ns_mgr#add_ns Astml.fortran_prefix Astml.fortran_ns


let xexists file =
  let tree = file#tree in
  List.exists
    (fun ext ->
      let f = new Storage.file (Storage.Tree tree) (file#path^ext) in
      f#exists
    ) comp_ext_list

let check_comp file = (* AST -> (AST[.COMPRESSION] * IS_COMPRESSED * COMP_EXT) *)
  let rec sea = function
    | [] ->
        failwith
          (sprintf "ASTML file \"%s{%s}\" not found"
             file#path (Xlist.to_string (fun x -> x) "," comp_ext_list))

    | ext::rest ->
        let f = new Storage.file (Storage.Tree file#tree) (file#path^ext) in
        if f#exists then
          (f, ext <> "", ext)
        else
          sea rest
  in
  sea comp_ext_list


[%%capture_path
let build_tree options file =

  [%debug_log "parsing \"%s\"..." file#path];

  let ns_mgr = new XML.ns_manager in
  setup_ns_mgr ns_mgr;

  let doc =
    let path = file#get_local_file in
    try
      XML.parse_file ~ns:ns_mgr path
    with
      _ ->
        let rec find = function
          | ext::rest -> begin
              let path_ = path^ext in
              try
                XML.parse_file ~ns:ns_mgr path_
              with
                _ ->
                  if rest = [] then
                    Xprint.failure "\"%s\": not found" path_
                  else
                    find rest
          end
          | [] -> raise Not_found
        in
        find comp_ext_list
  in

  [%debug_log "parsed"];

(*
  let line_terminator =
    let s =
      try
        Label.pxp_att_value_to_string
          (doc#root#attribute Tree.line_terminator_attr_name)
      with
        Not_found ->
          [%warn_log "'%s' does not contain attribute %s. assuming 'LF'..."
          file Tree.line_terminator_attr_name];
        "\010"
    in
    match s with
    | "CR" -> "\013"
    | "CRLF" -> "\013\010"
    | "LF" -> "\010"
    | _ ->
        [%warn_log        "'%s': illegal line terminator. assuming 'LF'..." s];
        "\010"
  in
*)
  begin %debug_block
    [%debug_log "root node: %s" doc#to_string];
    List.iter
      (fun (a, v) -> [%debug_log "%s = '%s'" a v])
      doc#attr_list;
  end;

  (* checking root element *)
  if doc#tag <> "" then
    () (* OK *)
  else
    Xprint.failure "\"%s\": not an ASTML file: root=%s"
      file#path doc#to_string;

  let parser_name =
    try
      doc#get_attr Label.parser_attr_name
    with
    | Not_found ->
        Xprint.failure "\"%s\" does not have %s attribute in root node"
          file#path Astml.parser_attr_name
  in

  [%debug_log "building tree..."];
  let tree = Tree.of_file options parser_name file doc in
  [%debug_log "done."];

  tree#set_parser_name parser_name;
(*  tree#set_line_terminator line_terminator; *)

  tree
(* end of func build_tree *)
]


type astml_header =
    { mutable h_parser        : string;
      mutable h_source        : string;
      mutable h_source_digest : string;
    }

let make_null_header() =
    { h_parser        = "";
      h_source        = "";
      h_source_digest = "";
    }

(*exception Got_header of astml_header*)
exception Header_not_found

let get_header astml =
  let ns_mgr = new XML.ns_manager in
  let _ = setup_ns_mgr ns_mgr in
  let root = XML.parse_file ~ns:ns_mgr astml in
  if root#localname = "astml" then begin
    let h = make_null_header() in
    List.iter
      (fun ((p, la), v) ->
        if ns_mgr#find p = Some (Astml.ast_ns) then
          if la = Astml.local_parser_attr_name then
            h.h_parser <- v
          else if la = Astml.local_source_attr_name then
            h.h_source <- v
          else if la = Astml.local_source_digest_attr_name then
            h.h_source_digest <- v
          else
            raise Header_not_found
        else
          raise Header_not_found
      ) root#raw_attr_list;
    if h.h_parser <> "" && h.h_source <> "" && h.h_source_digest <> "" then begin
      [%debug_log       "got source digest from the header: source=\"%s\" digest=\"%s\""
         h.h_source h.h_source_digest];
      h
    end
    else
      raise Header_not_found
  end
  else
    raise Header_not_found


module T         = Sourcecode.Tree (Label)
module FactCCX   = Fact.CCX (Label)


let file_digest_hex file =
  let ccs_mode = file#get_extension = Astml.ccs_ext in

  let get_digest_hex decompressed =
    if ccs_mode then
      Xhash.digest_hex_of_file file#tree#hash_algo decompressed
    else
      try
        let h = get_header decompressed in
        decode_digest h.h_source_digest
      with
        Not_found -> Xprint.failure "\"%s\": malformed ASTML file" file#path
  in

  let ast, comp_flag, comp_ext = check_comp file in

  if comp_flag then begin
    let astml = gen_temp_file_path() in
    decomp comp_ext ast astml;
    let d = get_digest_hex astml in
    begin
      try
        Sys.remove astml
      with
        Sys_error s -> Xprint.failure "cannot remove: %s" s
    end;
    d
  end
  else
    let d = get_digest_hex ast#get_local_file in
    d

(*
let digest options file =
  [%debug_log "parsing %s" file#path];
  let tree = build_tree options file in
  Xhash.to_hex tree#digest

let equal options file1 file2 =
  let d1 = digest options file1 in
  let d2 = digest options file2 in
  d1 = d2
*)

let extract_fact (*options*)_ (*cache_path*)_ (*tree*)_ =
()


class tree_builder options = object
  inherit Lang_base.tree_builder
  method from_xnode = T.of_xnode options
  method build_tree file = build_tree options file
end



(* for external parsers *)

let ext_file_digest_hex file =
  try
    Xhash.to_hex file#digest
  with
  | _ -> Xprint.failure "failed to compute file digest: %s" file#path


class ext_tree_builder xpname options = object (self)
  inherit Lang_base.tree_builder

  method from_xnode = T.of_xnode options

  method private get_astml_file src =
    let astml_file = new Storage.file (Storage.Tree src#tree) (src#path^Astml.extension) in
    if xexists astml_file then
      astml_file
    else begin
      [%debug_log "not found: \"%s\"" astml_file#path];
      let cache_path = options#get_cache_path_for_file1 src in
      let p = Filename.concat cache_path Astml.default_file_name in
      let astml_file = Fs.file_of_path options p in
      if xexists astml_file then
        astml_file
      else begin
        [%debug_log "not found: \"%s\"" astml_file#path];
        let spath = src#get_local_file in
        try
          let cmd = sprintf "%s %s" (options#get_external_parser xpname) spath in
          [%debug_log "parsing \"%s\"..." spath];
          [%debug_log "command=\"%s\"" cmd];
          if Sys.command cmd <> 0 then
            warning_msg "failed to execute \"%s\"" cmd
          else begin
            let apath = spath^Astml.extension in
            let p = astml_file#fullpath in
            Cache.prepare_dir options#default_dir_permission (Filename.dirname p);
            Sys.rename apath p;
            let cmd = sprintf "gzip %s" p in
            [%debug_log "compressing \"%s\"..." p];
            [%debug_log "command=\"%s\"" cmd];
            if Sys.command cmd <> 0 then
              warning_msg "failed to execute \"%s\"" cmd
          end;
          astml_file
        with
          Not_found -> raise (Astml.External_parser_not_found xpname)
      end
    end

  method build_tree file = build_tree options (self#get_astml_file file)
end
