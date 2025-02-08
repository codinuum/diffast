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


module S  = Diffast_misc.Storage
module SB = Spec_base

open Spec
open Change_base
open Lang_base

type extracted_change =
    changes *
      (node_t Editop.t) list *
      change_infos *
      Triple.t Xset.t


class virtual tree_comparator = object
  method virtual compare : Stat.File.diff_stat

  method virtual extra_source_files1 : S.file list
  method virtual extra_source_files2 : S.file list
end

class virtual tree_patcher = object
  method virtual _patch :
      ?fail_on_error:bool -> ?reverse:bool -> ?normalized_delta:bool ->
        S.file -> XML.node -> bool -> SB.OutChannel.t -> unit

  method virtual patch :
      ?fail_on_error:bool -> ?reverse:bool -> S.file -> string -> SB.OutChannel.t -> unit
end

class make_null_tree_patcher _ _ = object
  inherit tree_patcher

  method _patch
      ?(fail_on_error=true)
      ?(reverse=false)
      ?(normalized_delta=false)
      (*file*)_
      (*delta_doc_root*)_
      (*reversible*)_
      (*ch*)_
      =
    ignore fail_on_error;
    ignore reverse;
    ignore normalized_delta;
    failwith "Lang.null_tree_patcher: not implemented yet"

  method patch
      ?(fail_on_error=true)
      ?(reverse=false)
      (*file*)_
      (*delta*)_
      (*ch*)_
      =
    ignore fail_on_error;
    ignore reverse;
    failwith "Lang.null_tree_patcher: not implemented yet"

end


type opts_t = Options.c

type ('node, 'tree) edits_t = ('node, 'tree) Edit_base.seq_base
type ('node, 'tree) cmp_t = ('node, 'tree) Comparison.c
type nmapping_t = node_t Node_mapping.c

class type lang_t =
  object
    method name                 : string
    method subname              : string

    method make_tree_builder    : opts_t -> tree_builder
    method get_cache_key        : S.file -> string
    method extract_fact         : opts_t -> string -> tree_t -> unit
    method node_filter          : opts_t -> node_t -> bool

    method make_tree_comparator : opts_t -> ?cache_path:string -> S.file -> S.file -> tree_comparator
    method extract_change       : opts_t -> tree_t -> tree_t -> nmapping_t -> (node_t, tree_t) edits_t -> extracted_change
    method node_pair_filter     : opts_t -> node_t -> node_t -> bool
    method elaborate_edits      : (opts_t -> (node_t, tree_t) cmp_t -> nmapping_t -> (node_t, tree_t) edits_t -> unit) option
    method has_elaborate_edits  : bool
    method make_tree_patcher    : opts_t -> tree_patcher
  end



class c
    ?(subname="")
    ~make_tree_builder
    ~make_tree_comparator
    ~extract_change
    ~extract_fact
    ?(get_cache_key=(fun f -> Xhash.to_hex f#digest))
    ?(node_filter=(fun _ _ -> true))
    ?(node_pair_filter=(fun _ _ _ -> true))
    ?(elaborate_edits=None)
    ?(make_tree_patcher=(new make_null_tree_patcher))
    name
    =
  object (self : 'self)

    constraint 'self = #lang_t

    method name                 = name
    method subname              = subname

    method make_tree_builder    = make_tree_builder

    method get_cache_key        = get_cache_key

    method extract_fact         = extract_fact
    method node_filter          = node_filter


    val mutable _make_tree_comparator = Obj.magic ()

    initializer
      _make_tree_comparator <- make_tree_comparator (self :> lang_t)

    method make_tree_comparator = _make_tree_comparator
    method extract_change       = extract_change
    method node_pair_filter     = node_pair_filter
    method elaborate_edits      = elaborate_edits

    method private make_tree_factory options =
      new tree_factory options (make_tree_builder options)

    method make_tree_patcher options =
      make_tree_patcher options (self#make_tree_factory options)

    method has_elaborate_edits =
      match elaborate_edits with
      | Some _ -> true
      | None -> false
  end


let _extract_mapping_fact options nmapping filter path tree1 tree2 =

  let fact_buf =
    let into_virtuoso = options#fact_into_virtuoso <> "" in
    let into_directory = options#fact_into_directory <> "" in
    if into_virtuoso then begin
      assert (not into_directory);
      new Triple.buffer_virtuoso options
    end
    else if into_directory then
      let cache_name = Cache.get_cache_name options (Filename.dirname path) in
      new Triple.buffer_directory options cache_name
    else
      new Triple.buffer ~overwrite:false options path
  in

  let add tri = fact_buf#add tri in

  let mkent1, mkent2 = make_mkent_pair options tree1 tree2 in

  let f (*settled*)_ =
    fun nd1 nd2 ->

      if (filter nd1 nd2) then begin
	let ent1 = mkent1 nd1 in
	let ent2 = mkent2 nd2 in

	if ent1 <> Triple.ghost && ent2 <> Triple.ghost then begin (* exclude ghost nodes *)

	  if nd1#data#eq nd2#data then
	    add (ent1, Triple.p_mapped_eq_to, ent2)
	  else
	    add (ent1, Triple.p_mapped_neq_to, ent2)

(*
	  if nd1#initial_children = [||] && nd2#initial_children = [||] then (* leaves *)
	    if nd1#data#eq nd2#data then
	      add (ent1, Triple.p_mapped_eq_to, ent2)
	    else
	      add (ent1, Triple.p_mapped_neq_to, ent2)

	  else (* internal nodes *)
	    if settled then
	      add (ent1, Triple.p_mapped_eq_to, ent2)
	    else
	      if nd1#data#_digest <> None && nd2#data#_digest <> None then
		if nd1#data#subtree_equals nd2#data then
		  add (ent1, Triple.p_mapped_eq_to, ent2)
		else
		  add (ent1, Triple.p_mapped_neq_to, ent2)

	      else (* no subtree digests *)
		let d1 =
		  match nd1#data#_digest with
		  | Some d -> d
		  | None ->
		      let subtree1 = tree1#_make_subtree nd1 in
		      subtree1#digest
		in
		let d2 =
		  match nd2#data#_digest with
		  | Some d -> d
		  | None ->
		      let subtree2 = tree2#_make_subtree nd2 in
		      subtree2#digest
		in
		if d1 = d2 then
		  add (ent1, Triple.p_mapped_eq_to, ent2)
		else
		  add (ent1, Triple.p_mapped_neq_to, ent2)
*)
	end

      end
  in
  nmapping#iter_unsettled (f false);
  nmapping#iter_settled (f true);

  fact_buf#close


let extract_mapping_fact options lang nmapping path tree1 tree2 =

  let filter = lang#node_pair_filter options in

  Xprint.verbose options#verbose_flag "extracting mapping fact...";

  let restricted_flag_backup = options#fact_restricted_flag in

  if options#fact_for_mapping_restricted_flag then
    options#set_fact_restricted_flag;

  begin
    try
      _extract_mapping_fact options nmapping filter path tree1 tree2;
    with
      Triple.File_exists mes -> Xprint.warning "%s" mes
  end;

  if options#fact_for_mapping_restricted_flag then
    if restricted_flag_backup then
      options#set_fact_restricted_flag
    else
      options#clear_fact_restricted_flag;

  Xprint.verbose options#verbose_flag "done."



let register_external, register, search, setup_options
    =
  let disabled_ps = Xset.create 0 in
  let funcs_tbl = (* parser name -> functions *)
    Hashtbl.create 0
  in
  let xfuncs_tbl = (* external parser name -> functions *)
    Hashtbl.create 0
  in
  let get_module_name pname = Printf.sprintf "diffast_langs_%s" pname in

  let (search : opts_t -> string -> lang_t) =
    _search get_module_name funcs_tbl xfuncs_tbl
  in
  let get_lang2 options file1 file2 =
    let ext1 = file1#get_extension in
    let ext2 = file2#get_extension in
    let lang1 = search options ext1 in
    let lang2 = search options ext2 in
    if lang1 == lang2 then
      lang1
    else begin
      if ext1 <> ext2 then
        Xprint.warning "different extensions: %s and %s" ext1 ext2;
      failwith "Lang.get_lang2"
    end
  in
  let get_cache_name2 options file1 file2 =
    let lang = get_lang2 options file1 file2 in
    let get_cache_key = lang#get_cache_key in
    let cache_key1 = get_cache_key file1 in
    let cache_key2 = get_cache_key file2 in
    let cache_name =
      Cache.make_cache_name_for_file2 cache_key1 cache_key2
    in
    cache_name
  in
  let setup_options options =
    _setup_options disabled_ps funcs_tbl xfuncs_tbl search options;
    options#set_get_cache_name_for_file2 (get_cache_name2 options)
  in
  (_register_external disabled_ps xfuncs_tbl
     : string -> string -> (string -> string -> lang_t) -> unit),
  (_register disabled_ps funcs_tbl),
  search,
  setup_options

