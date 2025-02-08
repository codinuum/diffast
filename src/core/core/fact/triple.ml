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
(* triple.ml *)
(* format based on N-Triples *)

module Xhash = Diffast_misc.Xhash
module Xfile = Diffast_misc.Xfile
module Xchannel = Diffast_misc.Xchannel
module Xstring = Diffast_misc.Xstring
module Xset = Diffast_misc.Xset
module Xprint = Diffast_misc.Xprint
module C = Diffast_misc.Compression
module XML = Diffast_misc.XML
module Loc = Diffast_misc.Loc
module A = Astml
module BID = Diffast_misc.Binding.ID

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf



type lit_ty =
  | LT_string
  | LT_int
  | LT_nn_int
  | LT_real

let lit_ty_to_string = function
  | LT_string -> "xsd:string"
  | LT_int    -> "xsd:integer"
  | LT_nn_int -> "xsd:nonNegativeInteger"
  | LT_real   -> "xsd:double"


let lit_ty_string = LT_string
let lit_ty_int = LT_int
let lit_ty_nn_int = LT_nn_int
let lit_ty_real = LT_real


type node =
  | N_URI of string
  | N_QName of string * string
  | N_Literal of string * lit_ty
  | N_Blank of string
  | N_Ghost


type t = node * node * node


exception Invalid_QName of string

let node_to_string = function
  | N_URI s -> "<"^s^">"
  | N_QName(prefix, local) -> prefix^":"^local
  | N_Literal(s, ty) -> "\""^s^"\"^^"^(lit_ty_to_string ty)
  | N_Blank s -> "_:"^s
  | N_Ghost -> "<GHOST>"


let make_uri s = N_URI s

let make_qname prefix local = N_QName(prefix, XML.encode_string local)

let get_local_name = function
  | N_QName(_, local) -> local
  | _ -> raise (Invalid_argument "Triple.get_local_name")



let make_literal ?(ty=LT_string) s = N_Literal(Xstring.ntriples_escaped s, ty)
let make_int_literal i = make_literal ~ty:LT_int (string_of_int i)
let make_nn_int_literal i = make_literal ~ty:LT_nn_int (string_of_int i)
let make_real_literal r = make_literal ~ty:LT_real (string_of_float r)

let minus_pat = Str.regexp_string "-"

let gen_blank_node() =
  let uuid = Uuidm.v4_gen (Random.State.make_self_init ()) () in
  let uuid_str = sprintf "u%s" (Uuidm.to_string ~upper:true uuid) in
  N_Blank (Str.global_replace minus_pat "x" uuid_str)

let ghost = N_Ghost

let is_ghost_ast_node nd = nd#data#src_loc = Loc.ghost
let is_ghost_node = function
  | N_Ghost -> true
  | _ -> false
let is_ghost (s, _, o) = is_ghost_node s || is_ghost_node o


let to_string (s, p, o) =
  String.concat " " [node_to_string s; node_to_string p; node_to_string o]


(* XML Schema vocabulary *)
let xsd_ns = "http://www.w3.org/2001/XMLSchema#"
let xsd_prefix = "xsd"

(* RDF vocabulary *)
let rdf_ns = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let rdf_prefix = "rdf"
let mkrdfres s = N_QName(rdf_prefix, XML.encode_string s)

let p_rdf_first = mkrdfres "first"
let p_rdf_rest  = mkrdfres "rest"
let rdf_nil     = mkrdfres "nil"
let p_rdf_type  = mkrdfres "type"
let p_is_a      = p_rdf_type

(* source code vocabulary *)
let src_ns = "http://codinuum.com/ontologies/2012/10/source-code-entity#"
let src_prefix = "src"
let mksrcres s = make_qname src_prefix s

(* primitive change vocabulary *)
let change_ns = "http://codinuum.com/ontologies/2012/10/primitive-change#"
let change_prefix = "chg"
let mkchangeres s = make_qname change_prefix s

(* versioning vocabulary *)
let ver_ns = "http://codinuum.com/ontologies/2012/10/versioning#"
let ver_prefix = "ver"
let mkverres s = make_qname ver_prefix s

let guard_pred_prefix = "guard"

(* common vocabulary *)
let common_base_ns = "http://codinuum.com/fact/"
let project_ns     = common_base_ns^"project/"
let srctree_ns     = common_base_ns^"sourcetree/"
let version_ns     = common_base_ns^"version/"
let entity_ns      = common_base_ns^"entity/"
let svn_ns         = version_ns^"svn/"
let git_ns         = version_ns^"git/"

let guard_ns       = common_base_ns^"guard/"

let binding_ns     = common_base_ns^"binding/"

let proj_prefix     = "proj"
let release_prefix  = "rel"
let svnrev_prefix   = "svnrev"
let gitrev_prefix   = "gitrev"
let variant_prefix  = "variant"
let entity_prefix   = "ent"
let external_prefix = "ext"

let binding_prefix  = "b"

let entity_pair_ns = common_base_ns^"entity-pair/"
let entity_pair_prefix = "entpair"

let external_ns = common_base_ns^"external-name/"

let chg_inst_ns = common_base_ns^"change/"
let chg_inst_prefix = "chginst"

let delta_ns = "http://codinuum.com/ontologies/2016/05/delta#"
let delta_prefix = "delta"

let ns_tbl = (Hashtbl.create 0 : (string, string) Hashtbl.t)

let _ =
  let l =
    [ rdf_prefix,         rdf_ns;
      xsd_prefix,         xsd_ns;

      src_prefix,         src_ns;
      change_prefix,      change_ns;
      ver_prefix,         ver_ns;

      proj_prefix,        project_ns;
      release_prefix,     version_ns^"release/";
      svnrev_prefix,      svn_ns^"revision/";
      gitrev_prefix,      git_ns^"revision/";
      variant_prefix,     version_ns^"variant/";

      entity_prefix,      entity_ns;
      external_prefix,    external_ns;

      external_prefix^A.cpp_prefix,     external_ns^"cpp/";
      external_prefix^A.java_prefix,    external_ns^"java/";
      external_prefix^A.fortran_prefix, external_ns^"fortran/";
      external_prefix^A.python_prefix,  external_ns^"python/";
      external_prefix^A.verilog_prefix, external_ns^"verilog/";
      external_prefix^A.c_prefix,       external_ns^"c/";

      binding_prefix,     binding_ns;

      entity_pair_prefix, entity_pair_ns;

      chg_inst_prefix, chg_inst_ns;
      delta_prefix, delta_ns;

      A.c_prefix,       A.c_ns;
      A.cx_prefix,      A.cx_ns;
      A.ccx_prefix,     A.ccx_ns;
      A.java_prefix,    A.java_ns;
      A.python_prefix,  A.python_ns;
      A.verilog_prefix, A.verilog_ns;
      A.fortran_prefix, A.fortran_ns;
      A.cpp_prefix,     A.cpp_ns;
    ]
  in
  List.iter
    (fun (prefix, _uri) ->
      let uri =
        if Xstring.endswith _uri "/" then
          _uri
        else if Xstring.endswith _uri "#" then
          _uri
        else
          _uri^"/"
      in
      Hashtbl.add ns_tbl prefix uri
    ) l


let format_xsd lname =
  try
    sprintf "<%s%s>" (Hashtbl.find ns_tbl xsd_prefix) lname
  with
    Not_found ->
      [%warn_log "undefined prefix \"%s\"" xsd_prefix];
      ""

let format_lit_ty = function
  | LT_string -> ""
  | LT_int    -> format_xsd "integer"
  | LT_nn_int -> format_xsd "nonNegativeInteger"
  | LT_real   -> format_xsd "double"


let p_guard = function
  | N_URI s ->
      make_uri (sprintf "%s?orig=%s" guard_ns s)

  | N_QName(prefix, local) as qn ->
      begin
        try
          let u = Hashtbl.find ns_tbl prefix in
          make_uri (sprintf "%s?orig=%s%s" guard_ns u local)
        with
          Not_found ->
            [%warn_log "undefined prefix \"%s\"" prefix];
            raise (Invalid_QName (node_to_string qn))
      end

  | _ -> raise (Invalid_argument "Triple.p_guard")



let mkproj s   = make_qname proj_prefix s
let mkrel s    = make_qname release_prefix s
let mksvnrev s = make_qname svnrev_prefix s
let mkgitrev s = make_qname gitrev_prefix s
let mkvariant s = make_qname variant_prefix s

let mkchginst s = make_qname chg_inst_prefix s

let mkdeltares s = make_qname delta_prefix s

let mkent s    = make_qname entity_prefix s
let mkext ?(lang="") s    = make_qname (external_prefix^lang) s
(*let mkext s = make_literal s *)

let mkjres s = make_qname A.java_prefix s
let mkcres s = make_qname A.c_prefix s
let mkpres s = make_qname A.python_prefix s
let mkvres s = make_qname A.verilog_prefix s
let mkfres s = make_qname A.fortran_prefix s
let mkcppres s = make_qname A.cpp_prefix s

let mkccxres s = make_qname A.ccx_prefix s

let p_xml = mkdeltares "xml"
let p_entity1 = mkdeltares "entity1"
let p_entity2 = mkdeltares "entity2"

let p_version       = mkverres "version"
let p_file_digest   = mkverres "fileDigest"
let p_proj_rel_path = mkverres "path"
let c_version       = mkverres "Version"
let c_release       = mkverres "Release"
let c_gitrev        = mkverres "GitRevision"
let c_svnrev        = mkverres "SVNRevision"
let c_variant       = mkverres "Variant"
let c_file_digest   = mkverres "FileDigest"

let p_in_srctree    = mksrcres "inSourceTree"
let p_contains_file = mksrcres "containsFile"
let c_srctree       = mksrcres "SourceTree"
let p_binding       = mksrcres "binding"
let p_file_location = mksrcres "location"
let p_in_file       = mksrcres "inFile"
let p_in_project    = mksrcres "inProject"
let p_parent        = mksrcres "parent"
let p_children      = mksrcres "children"
let p_child0        = mksrcres "child0"
let p_childx nth    = mksrcres (sprintf "child%d" nth)
let p_tree_digest   = mksrcres "treeDigest"
let p_value         = mksrcres "value"
let p_name          = mksrcres "name"
let p_nth           = mksrcres "nth"
let p_path          = mksrcres "path"
let c_file          = mksrcres "File"
let c_auxfile       = mksrcres "Auxfile"
let c_project       = mksrcres "Project"
let c_tree_digest   = mksrcres "TreeDigest"
let c_position      = mksrcres "Position"
let c_binding       = mksrcres "Binding"
let c_external_name = mksrcres "ExternalName"
let c_loc           = mksrcres "Location"

let p_mapped_neq_to = mkchangeres "mappedNeqTo"
let p_mapped_eq_to  = mkchangeres "mappedEqTo"
let p_changed_to    = mkchangeres "changedTo"
let p_mov_changed_to = mkchangeres "movChangedTo"
let p_moved_to      = mkchangeres "movedTo"
let p_renamed       = mkchangeres "renamed"
let p_mov_renamed   = mkchangeres "movRenamed"
let p_deleted_from  = mkchangeres "deletedFrom"
let p_order_changed = mkchangeres "orderChanged"
let p_inserted_into = mkchangeres "insertedInto"
let p_modified      = mkchangeres "modified"
let p_pruned_from   = mkchangeres "prunedFrom"
let p_grafted_onto  = mkchangeres "graftedOnto"

let p_copied_from   = mkchangeres "copiedFrom"
let p_glued_to      = mkchangeres "gluedTo"

let p_gen_added   = mkchangeres "genAdded"
let p_gen_removed = mkchangeres "genRemoved"

let p_abstracted_to         = mkchangeres "abstractedTo"
let p_mov_abstracted_to     = mkchangeres "movAbstractedTo"
let p_folded_into           = mkchangeres "foldedInto"
let p_mov_folded_into       = mkchangeres "movFoldedInto"
let p_affects_nesting_depth = mkchangeres "affectsNestingDepth"
let p_nesting_depth         = mkchangeres "nestingDepth"
let p_cardinality           = mkchangeres "cardinality"

let p_orig_file    = mkchangeres "originalFile"
let p_mod_file     = mkchangeres "modifiedFile"
let p_orig_srctree = mkchangeres "originalSourceTree"
let p_mod_srctree  = mkchangeres "modifiedSourceTree"
let p_file_pair    = mkchangeres "filePair"
let p_srctree_pair = mkchangeres "sourceTreePair"

let c_file_pair    = mkchangeres "FilePair"
let c_srctree_pair = mkchangeres "SourceTreePair"
let c_del          = mkchangeres "Deletion"
let c_ins          = mkchangeres "Insertion"
let c_rel          = mkchangeres "Relabeling"
let c_mov          = mkchangeres "Move"


let l_true  = make_literal "true"
let l_false = make_literal "false"


(*
exception Proj_root_not_set
*)

let get_proj_rel_path proj_root path =
  Xfile.relpath proj_root path

let encode_path proj_root path =
  let rel = get_proj_rel_path proj_root path in
  Xstring.encode rel

let make_version_entity (vkind, ver) =
  match vkind with
  | Entity.V_REL     -> mkrel ver
  | Entity.V_SVNREV  -> mksvnrev ver
  | Entity.V_GITREV  -> mkgitrev ver
  | Entity.V_VARIANT -> mkvariant ver
  | Entity.V_UNKNOWN -> ghost

let _encode_fid options ?(force_PVF=false) ~digest ~path (*proj_root*)_ (vkind, version) =
  let enc = options#fact_enc in
  String.concat Entity.sub_sep
    (if force_PVF || Entity.is_PVF_encoding enc then begin
      let path_str = Xstring.encode path in
      let ver_str =
        (Entity.vkind_to_string vkind)^
        Entity.sub_sub_sep^
        (Xstring.encode version)
      in
      (if options#fact_proj = "" then
        [ ver_str; path_str ]
      else
        [ Xstring.encode options#fact_proj; ver_str; path_str ]
      )
    end
    else if Entity.is_FD_encoding enc then begin
      let algo = options#fact_algo in
      [ (Xhash.algo_to_string algo);
        (Xhash.to_hex digest);
      ]
    end
    else
      raise (Invalid_argument "Triple._encode_fid")
    )

let encode_fid ?(force_PVF=false) options tree =
  _encode_fid ~force_PVF options
    ~digest:tree#source_digest ~path:tree#source_path tree#proj_root (tree#vkind, tree#version)

let get_enc_str options ?(force_PVF=false) () =
  let enc = options#fact_enc in
  let enc_str =
    if force_PVF || Entity.is_PVF_encoding enc then
        Entity.encoding_to_string Entity.PVF
    else if Entity.is_FD_encoding enc then
        Entity.encoding_to_string Entity.FD
    else
      raise (Invalid_argument "Triple.get_enc_str")
  in
  enc_str

let ___make_file_entity enc_str fid_str =
  String.concat Entity.sep [enc_str; fid_str]

let __make_file_entity options ?(force_PVF=false) ~digest ~path proj_root (vkind, version) =
  let enc_str = get_enc_str options ~force_PVF () in
  let file_id_str =
    _encode_fid options ~force_PVF ~digest ~path proj_root (vkind, version)
  in
  ___make_file_entity enc_str file_id_str

let _make_file_entity options ?(force_PVF=false) ~digest ~path proj_root vkind_version =
  mkent (__make_file_entity options ~force_PVF ~digest ~path proj_root vkind_version)


let fid_of_tree_entry options proj_root (vkind, version) file =
  __make_file_entity options ~digest:file#digest ~path:file#path proj_root (vkind, version)

let file_entity_of_tree_entry options proj_root (vkind, version) file =
  _make_file_entity options ~digest:file#digest ~path:file#path proj_root (vkind, version)

let make_file_entity ?(force_PVF=false) options ast =
  _make_file_entity ~force_PVF options
    ~digest:ast#source_digest ~path:ast#source_path ast#proj_root (ast#vkind, ast#version)

let _make_binding options ~digest ~path proj_root (vkind, version) bid =
  let enc = options#fact_enc in
  let enc_str =
    if Entity.is_FD_encoding enc then
        Entity.encoding_to_string Entity.FD
    else if Entity.is_PVF_encoding enc then
        Entity.encoding_to_string Entity.PVF
    else
      raise (Invalid_argument "Triple._make_binding")
  in
  let file_id_str =
    _encode_fid options ~digest ~path proj_root (vkind, version)
  in
  make_qname binding_prefix (String.concat Entity.sep [enc_str; file_id_str; BID.to_raw bid])

let make_binding ?(loc_opt=None) options tree bid =
  if BID.is_local bid then begin
    let digest, path =
      match loc_opt with
      | Some loc ->
          let fn = loc.Loc.filename in
          if Filename.is_relative fn then begin
            let d =
              let fn_ = Filename.concat tree#proj_root fn in
              try
                Xhash.digest_of_file options#fact_algo fn_
              with
                _ -> begin
                  [%warn_log "failed to compute digest of \"%s\"" fn_];
                  fn
                end
            in
            (if d <> tree#source_digest then tree#source_digest^d else d), fn
          end
          else begin
            let d =
              try
                Xhash.digest_of_file options#fact_algo fn
              with
                _ -> begin
                  [%warn_log "failed to compute digest of \"%s\"" fn];
                  fn
                end
            in
            let p = Xfile.relpath tree#proj_root fn in
            (if d <> tree#source_digest then tree#source_digest^d else d), p
          end
      | None -> tree#source_digest, tree#source_path
    in
    _make_binding options ~digest ~path tree#proj_root (tree#vkind, tree#version) bid
  end
  else
    make_qname binding_prefix (BID.to_raw bid)



let __make_srctree_entity options (vkind, version) =
  let proj = options#fact_proj in
  let enc_str = Entity.encoding_to_string Entity.PV in
  let ver_str =
    (Entity.vkind_to_string vkind)^
    Entity.sub_sub_sep^
    (Xstring.encode version)
  in
  let id =
    String.concat Entity.sub_sep [ Xstring.encode proj; ver_str ]
  in
  String.concat Entity.sep [enc_str; id]

let _make_srctree_entity options (vkind, version) =
  mkent (__make_srctree_entity options (vkind, version))

let make_srctree_entity options tree =
  _make_srctree_entity options (tree#vkind, tree#version)

let make_extname (*options*)_ (*tree*)_ ?(lang="") lname =
(*
  let srctree_id = __make_srctree_entity options (tree#vkind, tree#version) in
  mkext ~lang (srctree_id ^ Entity.sep ^ lname)
*)
  mkext ~lang lname

let get_range_str enc loc =
  let int_to_str i =
    if i = -1 then
      "U"
    else
      string_of_int i
  in
  String.concat Entity.sub_sep
    (match enc with
    | Entity.FDLCO | Entity.PVFLCO ->
        [ int_to_str loc.Loc.start_line;
          int_to_str loc.Loc.start_char;
          int_to_str loc.Loc.start_offset;
          int_to_str loc.Loc.end_line;
          int_to_str loc.Loc.end_char;
          int_to_str loc.Loc.end_offset;
        ]

    | Entity.FDLO | Entity.PVFLO ->
        [ int_to_str loc.Loc.start_line;
          int_to_str loc.Loc.start_offset;
          int_to_str loc.Loc.end_line;
          int_to_str loc.Loc.end_offset;
        ]

    | Entity.FDLC | Entity.PVFLC ->
        [ int_to_str loc.Loc.start_line;
          int_to_str loc.Loc.start_char;
          int_to_str loc.Loc.end_line;
          int_to_str loc.Loc.end_char;
        ]

    | Entity.FDO | Entity.PVFO ->
        [ int_to_str loc.Loc.start_offset;
          int_to_str loc.Loc.end_offset;
        ]

    | Entity.FD | Entity.PVF ->
        [%warn_log "file entity encoding is used"];
        []
    | Entity.PV ->
        [%warn_log "source tree entity encoding is used"];
        []
    )

let rec avoid_ghost node =
  if is_ghost_ast_node node then
    avoid_ghost node#initial_parent
  else
    node

let __make_entity enc_str fid_str range_str is_phantom is_special =
  let l =
    if is_phantom then
      [enc_str; fid_str; range_str; "P"]
    else if is_special then
      [enc_str; fid_str; range_str; "S"]
    else
      [enc_str; fid_str; range_str]
  in
  String.concat Entity.sep l

let _make_entity options tree nd =
  if is_ghost_ast_node nd then
    invalid_arg "Triple._make_entity"
  else
    let enc = options#fact_enc in

    let loc = nd#data#src_loc in

    if loc = Loc.dummy then
      [%warn_log "location not defined: %s@%s" nd#data#to_string tree#source_path];

    let enc_str = Entity.encoding_to_string enc in

    let fid_str =
      let fid = nd#data#source_fid in
      if fid = "" then
        encode_fid options tree
      else
        fid
    in

    let range_str = get_range_str enc loc in

    __make_entity enc_str fid_str range_str nd#data#is_phantom nd#data#is_special

let make_entity options tree nd =
  if is_ghost_ast_node nd then
    ghost
  else
    mkent (_make_entity options tree nd)

let make_entity_pair id1 id2 =
  make_qname entity_pair_prefix (String.concat Entity.sep [id1; id2])


let format_node = function
  | N_URI s -> sprintf "<%s>" s
  | N_QName(prefix, local) as qn -> begin
      try
        let u = Hashtbl.find ns_tbl prefix in
        sprintf "<%s%s>" u local
      with
        Not_found ->
          [%warn_log "undefined prefix \"%s\"" prefix];
          raise (Invalid_QName (node_to_string qn))
  end
  | N_Literal(s, ty) ->
      sprintf "\"%s\"%s" s (let t = format_lit_ty ty in if t = "" then "" else "^^"^t)

  | N_Blank s -> sprintf "_:%s" s
  | N_Ghost -> raise (Invalid_argument "Triple.format_node")

let format_triple (s, p, o) =
  String.concat " " [format_node s; format_node p; format_node o]



let make_rdf_list resource_a =
  let triples = ref [] in
  let add t = triples := t :: !triples in
  let n = Array.length resource_a in
  if n = 0 then
    rdf_nil, []
  else begin (* n > 0 *)
    let bn0 = gen_blank_node() in
    let bn = ref bn0 in
    let cur = ref 0 in
    for _ = 0 to n - 2 do
      let bn1 = gen_blank_node() in
      add (!bn, p_rdf_rest, bn1);
      add (!bn, p_rdf_first, resource_a.(!cur));
      bn := bn1;
      incr cur
    done;
    add (!bn, p_rdf_rest, rdf_nil);
    add (!bn, p_rdf_first, resource_a.(!cur));
    bn0, !triples
  end


exception File_exists of string

class dumper_gen ?(overwrite=true) ?(comp=C.none) (dest : Xchannel.Destination.t) = object (self)

  val ch = new Xchannel.out_channel ~overwrite ~comp dest

  method _printf fmt =
    Printf.ksprintf (fun s -> ignore (ch#output_ s 0 (String.length s))) fmt

  method output_triple tri =
    try
      self#_printf "%s .\n" (format_triple tri)
    with
    | e ->
        let _ = e in
        [%warn_log "cannot put triple \"%s\": %s" (to_string tri) (Printexc.to_string e)]

  method close =
    ch#close

  end (* of class Triple.dumper_gen *)

class dumper ?(overwrite=true) ?(comp=C.none) fname =
  let filename =
    if not (Xstring.endswith fname comp#ext) then
      fname^comp#ext
    else
      fname
  in
  object
    inherit dumper_gen ~overwrite ~comp (Xchannel.Destination.of_file filename)

    method original_output_file_name = fname
    method real_output_file_name = filename

  end (* of class Triple.dumper *)


let dump options ?(overwrite=true) ?(comp=C.none) fname triples = (* N-Triples *)
  let ntriples = Xset.length triples in
  if ntriples > 0 then begin
    let dumper = new dumper ~overwrite ~comp fname in
    Xprint.verbose options#verbose_flag "dumping %d triples into \"%s\"" ntriples dumper#real_output_file_name;
    Xset.iter dumper#output_triple triples;
    dumper#close
  end

let make_a_name a fname =
  fname^"."^a

let dump_a options ?(comp=C.none) fname (tbl : (string, t Xset.t) Hashtbl.t) =
  Hashtbl.iter
    (fun a triples ->
      dump options ~comp (make_a_name a fname) triples
    ) tbl



exception ODBC_error of string
exception Malformed_ODBC_conf of string
exception Lock_failed

let fact_lock_file_name = "fact.lck"



let _lock_cache_file cache_path fname =
  let path = Filename.concat cache_path fname in
  if Sys.file_exists path then begin
    [%warn_log "fact lock already exists: path=\"%s\"" path];
    raise Lock_failed
  end
  else
    let fd = Unix.openfile path [Unix.O_CREAT;Unix.O_WRONLY] 0o644 in
    try
      Unix.lockf fd Unix.F_TLOCK 0;
      fd
    with
    | Unix.Unix_error(Unix.EAGAIN, _, _) -> begin
        [%warn_log "fact lock already acquired: path=\"%s\"" path];
        raise Lock_failed
    end
    | e -> raise e

let lock_fact cache_path = _lock_cache_file cache_path fact_lock_file_name

let unlock_fact fd =
  try
    Unix.lockf fd Unix.F_ULOCK 0;
    Unix.close fd
  with
  | e -> let _ = e in [%warn_log "%s" (Printexc.to_string e)]

let filter_sql_error =
  let pat = Str.regexp "password <.+>" in
  let filt msg =
    Str.global_replace pat "password <***>" msg
  in
  filt


let read_odbc_conf fname =
  let path = Parser_options.search_conf_file fname in
  try
    let rows = Csv.load path in
    match rows with
    | [dsn;uid;passwd]::_ -> dsn, uid, passwd
    | _ -> raise (Malformed_ODBC_conf path)
  with
  | _ -> raise (Malformed_ODBC_conf path)


(* DISABLED DUE TO UNSTABLE ODBC IMPLEMENTATION *)
let _connect_odbc (*conf_file_name*)_ = raise (ODBC_error "disabled")
let _disconnect_odbc (*odbc_connection*)_ = if true then raise (ODBC_error "disabled") else ()
(*
let _connect_odbc conf_file_name =
  try
    let dsn, uid, pwd = read_odbc_conf conf_file_name in
    new Ocamlodbc.data_base dsn uid pwd
  with
  | Ocamlodbc.SQL_Error msg -> raise (ODBC_error (filter_sql_error msg))
  | Not_found -> raise (ODBC_error (sprintf "conf file not found: \"%s\"" conf_file_name))

let _disconnect_odbc odbc_connection =
  try
    odbc_connection#disconnect()
  with
  | Ocamlodbc.SQL_Error msg -> raise (ODBC_error (filter_sql_error msg))
*)

let _output_triples_into_virtuoso options odbc_connection triples =
  let _temp_file = Filename.temp_file ~temp_dir:options#fact_virtuoso_temp_dir "" "" in
  let temp_file = Xfile.abspath _temp_file in
  dump options temp_file triples;
(*
  let q = "log_enable (2)" in
  let rc, _ = odbc_connection#execute q in
  if rc <> 0 then
    raise (ODBC_error (sprintf "data load setup failed: query=\"%s\" code=%d" q rc));
*)
  let sbuf = Buffer.create 0 in
  assert (options#fact_into_virtuoso <> "");
  let uri = options#fact_into_virtuoso in
  Buffer.add_string sbuf
    (sprintf "DB.DBA.TTLP_MT (file_to_string_output ('%s'), '', '%s', 0, 2, 2)" temp_file uri);
  let q = Buffer.contents sbuf in
  let rc, _ = odbc_connection#execute q in
  if rc <> 0 then
    raise (ODBC_error (sprintf "data load failed: query=\"%s\" code=%d" q rc));
(*
  let q = "checkpoint" in
  let rc, _ = odbc_connection#execute q in
  if rc <> 0 then
    raise (ODBC_error (sprintf "checkpointing failed: query=\"%s\" code=%d" q rc));
*)
  Xprint.verbose options#verbose_flag "removing \"%s\"..." temp_file;
  Sys.remove temp_file



class buffer_base options = object (self)
  val buf = Xset.create 0
  val mutable is_closed = false

  method is_closed = is_closed

  method clear = Xset.clear buf

  method length = Xset.length buf

  method add (tri : t) =
    if self#length >= options#fact_size_threshold then
      self#flush;
    Xset.add buf tri

  method add_group (tri_list : t list) =
    let len = List.length tri_list in

    if len > options#fact_size_threshold then
      [%warn_log "too large triple group: length=%d" len];

    if self#length + len > options#fact_size_threshold then
      self#flush;
    List.iter (Xset.add buf) tri_list

  method add_triples (triples : t Xset.t) =
    Xset.iter self#add triples

  method flush = ()
  method close = ()
end

let dummy_buffer = new buffer_base (new Parser_options.c)

class buffer options ?(overwrite=true) path = object (self)
  inherit buffer_base options

  val dumper =
    try
      new dumper ~overwrite ~comp:options#fact_compression path
    with
    | Xchannel.File_exists s -> raise (File_exists s)


  method! flush =
    Xset.iter dumper#output_triple buf;
    self#clear

  method! close =
    if not self#is_closed then begin
      self#flush;
      dumper#close;
      is_closed <- true
    end

end (* of class Triple.buffer *)


let _create_cache_path_lv2 base_dir cache_name =
  let sub0 = String.sub cache_name 0 2 in
  let sub1, sub2 =
    if sub0 = "d." then
      String.sub cache_name 2 2, String.sub cache_name 4 1
    else
      sub0, String.sub cache_name 2 1
  in
  let res =
    Filename.concat
      (Filename.concat
         (Filename.concat base_dir sub1) sub2)
      cache_name
  in
  res

class buffer_directory options cache_name =
  let dir = _create_cache_path_lv2 options#fact_into_directory cache_name in
  object (self)
    inherit buffer_base options

    initializer
      if not (Xfile.dir_exists dir) then
        Xfile.mkdir dir

    method! flush =
      let _temp_file = Filename.temp_file ~temp_dir:dir "" ".nt.gz" in
      let temp_file = Xfile.abspath _temp_file in
      dump options ~comp:C.gzip temp_file buf;
      self#clear

    method! close =
      if not self#is_closed then begin
        self#flush;
        is_closed <- true
      end

  end (* of class Triple.buffer_directory *)


class buffer_odbc options conf_file_name = object (self)
  inherit buffer_base options

  val odbc_connection = _connect_odbc conf_file_name

  method virtual flush : unit

  method! close =
    if not self#is_closed then begin
      self#flush;
      _disconnect_odbc odbc_connection;
      is_closed <- true
    end

end (* of Triple.buffer_odbc *)


class buffer_virtuoso options = object (self)
  inherit buffer_odbc options "virtuoso.odbc"

  method! flush =
    _output_triples_into_virtuoso options odbc_connection buf;
    self#clear

end (* of Triple.buffer_virtuoso *)

let dump_into_virtuoso options triples =
  let ntriples = Xset.length triples in
  if ntriples > 0 then begin
    Xprint.verbose options#verbose_flag "dumping %d triples into virtuoso" ntriples;
    let buf = new buffer_virtuoso options in
    buf#add_triples triples;
    buf#close
(*
    let odbc_connection = _connect_odbc "virtuoso.odbc" in
    Xprint.verbose options#verbose_flag "dumping %d triples into virtuoso" ntriples;
    _output_triples_into_virtuoso options odbc_connection triples;
    _disconnect_odbc odbc_connection
*)
  end

let dump_a_into_virtuoso options (tbl : (string, t Xset.t) Hashtbl.t) =
  Hashtbl.iter
    (fun _ triples ->
      dump_into_virtuoso options triples
    ) tbl

let dump_into_directory options cache_name triples =
  let ntriples = Xset.length triples in
  if ntriples > 0 then begin
    Xprint.verbose options#verbose_flag "dumping %d triples into directory \"%s\"" ntriples options#fact_into_directory;
    let buf = new buffer_directory options cache_name in
    buf#add_triples triples;
    buf#close
  end



let to_dot_ch triples ch =
  let node_tbl = Hashtbl.create 0 in
  let node_count = ref 0 in
  let reg n =
    if not (Hashtbl.mem node_tbl n) then begin
      Hashtbl.add node_tbl n !node_count;
      incr node_count
    end
  in
  let get_nid n = Hashtbl.find node_tbl n in

  List.iter (fun (s, (*p*)_, o) -> reg s; reg o) triples;

  Xprint.message "to_dot_ch: %d nodes and %d edges found"
    !node_count (List.length triples);

  fprintf ch "digraph fact {\n";
  Hashtbl.iter
    (fun n id ->
      fprintf ch "%d [label=\"%s\"];\n" id n
    ) node_tbl;
  List.iter
    (fun (s, p, o) ->
      fprintf ch "%d -> %d [label=\"%s\"];\n" (get_nid s) (get_nid o) p
    ) triples;
  fprintf ch "}\n"

let to_dot fname triples = Xfile.dump fname (to_dot_ch triples)
