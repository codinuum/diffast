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
(* lang.ml *)

[%%prepare_logger]

module Xhash = Diffast_misc.Xhash
module Xprint = Diffast_misc.Xprint
module XML = Diffast_misc.XML
module S  = Diffast_misc.Storage
module SB = Spec_base

open Spec


exception Parse_error of string * string
exception Error of string

type ignored = (int * int) list

class virtual tree_builder = object (self)

  method virtual from_xnode : XML.node -> tree_t

  method virtual build_tree : S.file -> tree_t


  method digest file =
    let tree = self#build_tree file in
    Digest.string tree#to_rep

  method equal file1 file2 =
    let d1 = self#digest file1 in
    let d2 = self#digest file2 in
    d1 = d2

  method extra_source_files : S.file list = []
end


class tree_factory options (tree_builder : tree_builder) = object

  method namespace_manager = new XML.ns_manager

  method from_xnode = tree_builder#from_xnode

  method from_file (file : S.file) =
    if options#check_extension file#path then begin
      let tree = tree_builder#build_tree file in
      (tree : tree_t)
    end
    else
      failwith (Printf.sprintf "Lang.tree_factory: not supported: \"%s\"" file#get_extension)

end (* of class Lang.tree_factory *)



type opts_t = Parser_options.c

class type lang_t =
  object
    method name                 : string
    method subname              : string

    method make_tree_builder    : opts_t -> tree_builder
    method get_cache_key        : S.file -> string
    method extract_fact         : opts_t -> string -> tree_t -> unit
    method node_filter          : opts_t -> node_t -> bool
  end



class c
    ?(subname="")
    ~make_tree_builder
    ~extract_fact
    ?(get_cache_key=(fun f -> Xhash.to_hex f#digest))
    ?(node_filter=(fun _ _ -> true))
    name
    =
  object (_ : 'self)

    constraint 'self = #lang_t

    method name              = name
    method subname           = subname

    method make_tree_builder = make_tree_builder

    method get_cache_key     = get_cache_key

    method extract_fact      = extract_fact
    method node_filter       = node_filter

  end


let _register_spec pname_tbl pname extensions =
  List.iter
    (fun _ext ->
      let ext = String.lowercase_ascii _ext in
      Hashtbl.replace pname_tbl ext pname
    ) extensions

let _register_external_specs xpname_tbl pname xpname_extensions_list =
  List.iter
    (fun (xpname, extensions) ->
      List.iter
        (fun _ext ->
          let ext = String.lowercase_ascii _ext in
          Hashtbl.replace xpname_tbl ext (pname, xpname)
        ) extensions
    ) xpname_extensions_list

let register_spec, register_external_specs,
  find_pname, find_xpname, iter_pname_map, iter_xpname_map, remove_pname_map, remove_xpname_map
    =
  let pname_tbl = (* extension -> parser name *)
    Hashtbl.create 0
  in
  let xpname_tbl = (* extension -> parser name * external parser name *)
    Hashtbl.create 0
  in
  (_register_spec pname_tbl),
  (_register_external_specs xpname_tbl),
  (Hashtbl.find pname_tbl),
  (Hashtbl.find xpname_tbl),
  (fun f -> Hashtbl.iter f pname_tbl),
  (fun f -> Hashtbl.iter f xpname_tbl),
  (Hashtbl.remove pname_tbl),
  (Hashtbl.remove xpname_tbl)


[%%capture_path
let _register_external disabled_ps xfuncs_tbl pname xpname mklang =
  if not (Xset.mem disabled_ps xpname) then begin
    [%debug_log "pname=%s xpname=%s" pname xpname];
    Hashtbl.replace xfuncs_tbl xpname (mklang xpname pname)
  end
]

[%%capture_path
let _register disabled_ps funcs_tbl pname mklang =
  if not (Xset.mem disabled_ps pname) then begin
    [%debug_log"pname=%s" pname];
    Hashtbl.replace funcs_tbl pname (mklang pname)
  end
]

let _search get_module_name funcs_tbl xfuncs_tbl options _ext =
  Xprint.verbose options#verbose_flag "lang modules:";
  List.iter
    (fun p ->
      Xprint.verbose options#verbose_flag " %s" p;
    ) (Sites.Plugins.Langs.list());

  let dynlink pname =
    try
      let mname = get_module_name pname in
      Xprint.verbose options#verbose_flag "loading \"%s\"..." mname;
      Sites.Plugins.Langs.load mname;
      Xprint.verbose options#verbose_flag "\"%s\" loaded." mname
    with
      exc -> raise (Error (Printexc.to_string exc))
  in

  let ext = String.lowercase_ascii _ext in

  let from_external ext =
    let pname, xpname = find_xpname ext in
    if options#is_disabled_parser xpname then
      raise Not_found
    else
      try
        Hashtbl.find xfuncs_tbl xpname
      with
        Not_found ->
          dynlink pname;
          Hashtbl.find xfuncs_tbl xpname
  in
  let _from_internal pname =
    if options#is_disabled_parser pname then
      raise Not_found
    else
      try
        Hashtbl.find funcs_tbl pname
      with
        Not_found ->
          dynlink pname;
          Hashtbl.find funcs_tbl pname
  in
  let from_internal ext =
    let pname = find_pname ext in
    _from_internal pname
  in

  let funcs =
    try
      if options#parser_designated then begin
        _from_internal options#designated_parser
      end
      else if options#external_parser_flag then begin
        try
          from_external ext
        with
          Not_found ->
            from_internal ext
      end
      else begin
        try
          from_internal ext
        with
          Not_found ->
            from_external ext
      end
    with
      Not_found ->
        raise (Error (Printf.sprintf "parser for \"%s\" not found" ext))
  in
  funcs


let load_lang_specs options () =
  Xprint.verbose options#verbose_flag "loading lang specs...";
  List.iter
    (fun p ->
      Xprint.verbose options#verbose_flag " %s" p;
    ) (Sites.Plugins.Lang_specs.list());
  Sites.Plugins.Lang_specs.load_all();
  Xprint.verbose options#verbose_flag "done."


let _setup_options disabled_ps funcs_tbl xfuncs_tbl search options =
  load_lang_specs options ();

  let exts = Xset.create 0 in
  let disabled_exts = Xset.create 0 in
  let f get_pname =
    let designated = options#designated_parser in
    if designated <> "" then
      fun e x ->
        let pname = get_pname x in
        if pname = designated then
          Xset.add exts e
        else begin
          Xset.add disabled_ps pname;
          Xset.add disabled_exts e
        end
    else
      fun e x  ->
        let pname = get_pname x in
        if options#is_disabled_parser pname then begin
          Xset.add disabled_ps pname;
          Xset.add disabled_exts e
        end
        else
          Xset.add exts e
  in
  let get_cache_name1 options file =
    let lang = search options file#get_extension in
    lang#get_cache_key file
  in
  iter_pname_map (f Fun.id);
  iter_xpname_map (f (fun (_, x) -> x));

  Xset.iter
    (fun pname ->
      Hashtbl.remove funcs_tbl pname;
      Hashtbl.remove xfuncs_tbl pname
    ) disabled_ps;

  Xset.iter
    (fun ext ->
      if not (Xset.mem exts ext) then begin
        remove_pname_map ext;
        remove_xpname_map ext
      end
    ) disabled_exts;

  if options#verbose_flag then begin
    Xset.iter
      (fun pn ->
        Xprint.verbose true "parser \"%s\" disabled" pn
      ) disabled_ps
  end;

  options#add_extensions (Xset.to_list exts);
  options#set_get_cache_name_for_file1 (get_cache_name1 options)



let register_external, register, search, setup_options
    =
  let disabled_ps = Xset.create 0 in
  let funcs_tbl = (* parser name -> functions *)
    Hashtbl.create 0
  in
  let xfuncs_tbl = (* external parser name -> functions *)
    Hashtbl.create 0
  in
  let get_module_name pname = Printf.sprintf "diffast_langs_%s_p" pname in

  let (search : opts_t -> string -> lang_t) =
    _search get_module_name funcs_tbl xfuncs_tbl
  in
  (_register_external disabled_ps xfuncs_tbl
     : string -> string -> (string -> string -> lang_t) -> unit),
  (_register disabled_ps funcs_tbl),
  search,
  (_setup_options disabled_ps funcs_tbl xfuncs_tbl search
     : opts_t -> unit)



type tie_id = string * string (* exact * anonymous *)

let null_tid = ("", "")
let mktid e a = (e, a)
let tid_to_string (e, a) =
  if e = "" then
    a
  else if a = "" then
    (* "" *) e
  else
    e^";"^a

let hash_of_tid ((h, _) : tie_id) = h


let anonymize_tid ?(more=false) ((_, a) : tie_id) =
  if more then
    ("", "")
  else
    ("", a)

let mkstmttidattr ((e, a) : tie_id) =
  (Astml.stmttid_attr_name,XML.encode_string e) ::
  (if a = "" then [] else [Astml.ar_stmttid_attr_name,XML.encode_string a])

let mktidattr ((e, a) : tie_id) =
  (Astml.tid_attr_name,XML.encode_string e) ::
  (if a = "" then [] else [Astml.ar_tid_attr_name,XML.encode_string a])



let tree_of_file options file =
  let ext = file#get_extension in
  let lang = search options ext in
  let builder = lang#make_tree_builder options in
  let tree = builder#build_tree file in
  tree

