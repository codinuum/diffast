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
(* parser_options.ml *)

module Xfile = Diffast_misc.Xfile
module Xset = Diffast_misc.Xset
module Xprint = Diffast_misc.Xprint
module Xhash = Diffast_misc.Xhash
module Comp  = Diffast_misc.Compression
module UID = Diffast_misc.UID
module Storage = Diffast_misc.Storage
module Binding = Diffast_misc.Binding
module Base_options = Diffast_misc.Base_options
module Fs_options = Diffast_misc.Fs_options


let default_java_lang_spec = 11

let get_dist_dir () =
  Filename.dirname (Filename.dirname (Xfile.abspath Sys.executable_name))

let conf_search_paths =
  let dist_dir = get_dist_dir() in
  [ Filename.concat dist_dir "etc";
    Filename.concat (Filename.concat dist_dir "etc") "cca";
  ]

let parser_search_paths =
  let dist_dir = get_dist_dir() in
  [ Filename.concat dist_dir "parsers";
    Filename.concat (Filename.concat (Filename.concat dist_dir "lib") "cca") "parsers";
  ]

let module_search_paths =
  let dist_dir = get_dist_dir() in
  [ Filename.concat dist_dir "modules";
    Filename.concat (Filename.concat (Filename.concat dist_dir "lib") "cca") "modules";
  ]

let _search_file name search_paths fname =
  let rec search = function
    | [] -> begin
        Xprint.warning ~head:"[file search]" "%s not found: \"%s\"" name fname;
        raise Not_found
    end
    | h::t ->
        let p = Filename.concat h fname in
        if Xfile.file_exists p then
          p
        else
          search t
  in
  search search_paths

let search_conf_file = _search_file "conf file" conf_search_paths
let search_module = _search_file "module" module_search_paths
let search_parser = _search_file "parser" parser_search_paths


class c = object (self)
  inherit Base_options.c
  inherit Fs_options.c
  inherit Fact_options.c

  val uid_generator = new UID.generator
  method uid_generator = uid_generator

  val bid_generator = new Binding.ID.generator
  method bid_generator = bid_generator

  val mutable dump_dot_flag    = false
  method dump_dot_flag = dump_dot_flag
  method set_dump_dot_flag = dump_dot_flag <- true
  method clear_dump_dot_flag = dump_dot_flag <- false


  (* cache *)
  val mutable layered_cache_flag = true
  val mutable clear_cache_flag   = false
  val mutable fuzzy_cache_flag   = false

  val mutable cache_dir_base = "" (* set in the initializer *)
  method cache_dir_base = cache_dir_base
  method set_cache_dir_base x = cache_dir_base <- x

  val mutable default_dir_permission  = 0o755
  method default_dir_permission = default_dir_permission
  method set_default_dir_permission x = default_dir_permission <- x

  val mutable default_file_permission = 0o644
  method default_file_permission = default_file_permission
  method set_default_file_permission x = default_file_permission <- x

  method layered_cache_flag = layered_cache_flag
  method set_layered_cache_flag = layered_cache_flag <- true
  method clear_layered_cache_flag = layered_cache_flag <- false

  method clear_cache_flag = clear_cache_flag
  method set_clear_cache_flag = clear_cache_flag <- true
  method clear_clear_cache_flag = clear_cache_flag <- false

  method fuzzy_cache_flag = fuzzy_cache_flag
  method set_fuzzy_cache_flag = fuzzy_cache_flag <- true
  method clear_fuzzy_cache_flag = fuzzy_cache_flag <- false

  val mutable get_cache_name_for_file1 =
    fun (_ : Storage.file) -> ""

  val mutable local_cache_name = ""

  method set_get_cache_name_for_file1 f = get_cache_name_for_file1 <- f

  method get_cache_name_for_file1 = get_cache_name_for_file1

  method get_cache_path_for_file1 file =
    let p = Cache.create_cache_path self (self#get_cache_name_for_file1 file) in
    if local_cache_name = "" then
      p
    else
      Filename.concat p local_cache_name

  method get_cache_path_for_dir_digest1 d =
    let h = Xhash.to_hex d in
    let p = Cache.create_cache_path self (Cache.make_cache_name_for_dir1 h) in
    if local_cache_name = "" then
      p
    else
      Filename.concat p local_cache_name


  method local_cache_name = local_cache_name
  method set_local_cache_name n = local_cache_name <- n


  (* langs *)
  val disabled_parsers = Xset.create 0
  val mutable external_parser_flag = false
  val mutable designated_parser = ""

  (* output *)
  val mutable dump_ast_flag    = false

  val mutable compress_ast_flag = false
  val mutable ast_compression   = Comp.none
  val mutable dump_src_flag = false
  val mutable dump_src_out = ""

  (* mode *)
  val mutable recursive_flag       = false
  val mutable incomplete_info_flag = false

  val mutable no_collapse_flag     = false
  method no_collapse_flag = no_collapse_flag
  method set_no_collapse_flag = no_collapse_flag <- true
  method clear_no_collapse_flag = no_collapse_flag <- false

  val mutable ast_reduction_flag = false
  method ast_reduction_flag = ast_reduction_flag
  method set_ast_reduction_flag = ast_reduction_flag <- true
  method clear_ast_reduction_flag = ast_reduction_flag <- false

  val mutable normalize_ast_flag = false
  method normalize_ast_flag = normalize_ast_flag
  method set_normalize_ast_flag = normalize_ast_flag <- true
  method clear_normalize_ast_flag = normalize_ast_flag <- false

  val mutable rely_on_naming_convention_flag = false
  method rely_on_naming_convention_flag = rely_on_naming_convention_flag
  method set_rely_on_naming_convention_flag = rely_on_naming_convention_flag <- true
  method clear_rely_on_naming_convention_flag = rely_on_naming_convention_flag <- false

  val mutable partial_name_resolution_flag = false
  method partial_name_resolution_flag = partial_name_resolution_flag
  method set_partial_name_resolution_flag = partial_name_resolution_flag <- true
  method clear_partial_name_resolution_flag = partial_name_resolution_flag <- false

  val mutable partial_typename_resolution_flag = false
  method partial_typename_resolution_flag = partial_typename_resolution_flag
  method set_partial_typename_resolution_flag = partial_typename_resolution_flag <- true
  method clear_partial_typename_resolution_flag = partial_typename_resolution_flag <- false

  val mutable no_implicit_name_resolution_flag = false
  method no_implicit_name_resolution_flag = no_implicit_name_resolution_flag
  method set_no_implicit_name_resolution_flag = no_implicit_name_resolution_flag <- true
  method clear_no_implicit_name_resolution_flag = no_implicit_name_resolution_flag <- false

  val mutable use_binding_info_flag = true
  method use_binding_info_flag = use_binding_info_flag
  method set_use_binding_info_flag = use_binding_info_flag <- true
  method clear_use_binding_info_flag = use_binding_info_flag <- false

  val mutable no_binding_trace_flag = false
  method no_binding_trace_flag = no_binding_trace_flag
  method set_no_binding_trace_flag = no_binding_trace_flag <- true
  method clear_no_binding_trace_flag = no_binding_trace_flag <- false

  (* *)
  val mutable latest_target = ""
  method latest_target = latest_target
  method set_latest_target x = latest_target <- x

  val mutable sort_unordered_flag = false (* build ASTs with sorting unordered constructs *)
  method sort_unordered_flag = sort_unordered_flag
  method set_sort_unordered_flag = sort_unordered_flag <- true
  method clear_sort_unordered_flag = sort_unordered_flag <- false

  val mutable strip_empty_flag = false (* strip empty constructs *)
  method strip_empty_flag = strip_empty_flag
  method set_strip_empty_flag = strip_empty_flag <- true
  method clear_strip_empty_flag = strip_empty_flag <- false

  val mutable recover_orig_ast_flag = true (* recover original AST when generating edits *)
  method recover_orig_ast_flag = recover_orig_ast_flag
  method set_recover_orig_ast_flag = recover_orig_ast_flag <- true
  method clear_recover_orig_ast_flag = recover_orig_ast_flag <- false

  val mutable weak_eq_flag = false (* weaken node equation *)
  method weak_eq_flag = weak_eq_flag
  method set_weak_eq_flag = weak_eq_flag <- true
  method clear_weak_eq_flag = weak_eq_flag <- false

  val mutable anonymize_int_flag = false
  method anonymize_int_flag = anonymize_int_flag
  method set_anonymize_int_flag = anonymize_int_flag <- true
  method clear_anonymize_int_flag = anonymize_int_flag <- false

  val mutable anonymize_float_flag = false
  method anonymize_float_flag = anonymize_float_flag
  method set_anonymize_float_flag = anonymize_float_flag <- true
  method clear_anonymize_float_flag = anonymize_float_flag <- false

  val mutable anonymize_string_flag = false
  method anonymize_string_flag = anonymize_string_flag
  method set_anonymize_string_flag = anonymize_string_flag <- true
  method clear_anonymize_string_flag = anonymize_string_flag <- false


  (* searchast *)
  val mutable sim_threshold = 0.8
  val mutable str_threshold = 0.8
  val mutable size_threshold = 32
  val mutable continuity_threshold = 0.5
  val mutable origin_file_name = "origin"
  val mutable coverage_file_name = "coverage"
  val mutable fragment_file_name = "fragment"
  val mutable ending_file_name = "ending"
  val mutable coverage_file_name_ending = "coverage_ending"
  val mutable fragment_file_name_ending = "fragment_ending"
  val mutable gmap_ext = ".gmap"
  val mutable clone_map_file_name = "" (* set in the initializer *)

  method sim_threshold = sim_threshold
  method set_sim_threshold x = sim_threshold <- x

  method str_threshold = str_threshold
  method set_str_threshold x = str_threshold <- x

  method size_threshold = size_threshold
  method set_size_threshold x = size_threshold <- x

  method continuity_threshold = continuity_threshold
  method set_continuity_threshold x = continuity_threshold <- x

  method origin_file_name = origin_file_name
  method set_origin_file_name x = origin_file_name <- x

  method coverage_file_name = coverage_file_name
  method set_coverage_file_name x = coverage_file_name <- x

  method fragment_file_name = fragment_file_name
  method set_fragment_file_name x = fragment_file_name <- x

  method ending_file_name = ending_file_name
  method set_ending_file_name x = ending_file_name <- x

  method coverage_file_name_ending = coverage_file_name_ending
  method set_coverage_file_name_ending x = coverage_file_name_ending <- x

  method fragment_file_name_ending = fragment_file_name_ending
  method set_fragment_file_name_ending x = fragment_file_name_ending <- x

  method gmap_ext = gmap_ext
  method set_gmap_ext x = gmap_ext <- x

  method clone_map_file_name = clone_map_file_name
  method set_clone_map_file_name x = clone_map_file_name <- x

  (* configuration *)
  val mutable keep_going_flag = false


  val mutable ignore_identifiers_flag = false
  method ignore_identifiers_flag  = ignore_identifiers_flag
  method set_ignore_identifiers_flag  = ignore_identifiers_flag <- true
  method clear_ignore_identifiers_flag  = ignore_identifiers_flag <- false

  val mutable ignore_huge_arrays_flag = true
  method ignore_huge_arrays_flag  = ignore_huge_arrays_flag
  method set_ignore_huge_arrays_flag  = ignore_huge_arrays_flag <- true
  method clear_ignore_huge_arrays_flag  = ignore_huge_arrays_flag <- false

  val mutable huge_array_threshold = 1000
  method huge_array_threshold = huge_array_threshold
  method set_huge_array_threshold x = huge_array_threshold <- x

  val mutable ignore_huge_exprs_flag = true
  method ignore_huge_exprs_flag = ignore_huge_exprs_flag
  method set_ignore_huge_exprs_flag = ignore_huge_exprs_flag <- true
  method clear_ignore_huge_exprs_flag = ignore_huge_exprs_flag <- false

  val mutable huge_expr_threshold = 512
  method huge_expr_threshold = huge_expr_threshold
  method set_huge_expr_threshold x = huge_expr_threshold <- x

  val mutable flatten_if_flag = true
  method flatten_if_flag = flatten_if_flag
  method set_flatten_if_flag = flatten_if_flag <- true
  method clear_flatten_if_flag = flatten_if_flag <- false

  (*val mutable deep_if_threshold = 0
  method deep_if_threshold = deep_if_threshold
  method set_deep_if_threshold x = deep_if_threshold <- x*)

  (* pre-processor *)
  val mutable ignore_if0_flag = true
  method ignore_if0_flag = ignore_if0_flag
  method set_ignore_if0_flag = ignore_if0_flag <- true
  method clear_ignore_if0_flag = ignore_if0_flag <- false

  (* Java *)
  val mutable java_anon_ctor_body_flag = false
  val mutable java_lang_spec = default_java_lang_spec

  (* Python *)
  val mutable python_with_stmt_disabled_flag = false
  val mutable python_ignore_docstring_flag = false
  val mutable python_ignore_comment_flag = true

  (* Fortran *)
  val mutable fortran_max_line_length = -1
  val mutable fortran_parse_d_lines_flag = false
  val mutable fortran_ignore_include_flag = false

  (* Verilog *)
  val mutable verilog_ignore_include_flag = false

  (* yacfe *)
  val mutable yacfe_defs_builtins = ""
  val mutable yacfe_env = ""
  val mutable yacfe_cfg_flag = true
  val mutable yacfe_skip_expanded_flag = false
  val mutable yacfe_skip_other_directives_flag = false

  (* external parser *)
  val external_parser_cache = Hashtbl.create 0


(* langs *)
  method disable_parser (pname : string) = Xset.add disabled_parsers pname
  method is_disabled_parser pname = Xset.mem disabled_parsers pname

  method parser_designated = designated_parser <> ""
  method designated_parser = designated_parser
  method designate_parser p = designated_parser <- p
  method clear_designated_parser = designated_parser <- ""

(* flags getter/setter *)
  method keep_going_flag = keep_going_flag
  method set_keep_going_flag = keep_going_flag <- true
  method clear_keep_going_flag = keep_going_flag <- false

  method external_parser_flag = external_parser_flag
  method set_external_parser_flag = external_parser_flag <- true
  method clear_external_parser_flag = external_parser_flag <- false

  (* output *)
  method dump_ast_flag = dump_ast_flag
  method set_dump_ast_flag = dump_ast_flag <- true
  method clear_dump_ast_flag = dump_ast_flag <- false

  method compress_ast_flag = compress_ast_flag
  method set_compress_ast_flag =
    compress_ast_flag <- true;
    ast_compression <- Comp.gzip

  method clear_compress_ast_flag =
    compress_ast_flag <- false;
    ast_compression <- Comp.none

  method ast_compression = ast_compression

  method dump_src_flag = dump_src_flag
  method set_dump_src_flag = dump_src_flag <- true
  method clear_dump_src_flag = dump_src_flag <- false
 
  method dump_src_out = dump_src_out
  method set_dump_src_out s = dump_src_out <- s

  (* mode *)
  method recursive_flag = recursive_flag
  method set_recursive_flag = recursive_flag <- true
  method clear_recursive_flag = recursive_flag <- false

  method incomplete_info_flag = incomplete_info_flag
  method set_incomplete_info_flag = incomplete_info_flag <- true
  method clear_incomplete_info_flag = incomplete_info_flag <- false


(* configurations getter/setter *)
  (* Java *)
  method java_anon_ctor_body_flag = java_anon_ctor_body_flag
  method set_java_anon_ctor_body_flag = java_anon_ctor_body_flag <- true
  method clear_java_anon_ctor_body_flag = java_anon_ctor_body_flag <- false

  method java_lang_spec = java_lang_spec
  method set_java_lang_spec lv = java_lang_spec <- lv
  method reset_java_lang_spec = java_lang_spec <- default_java_lang_spec

  (* Python *)
  method python_with_stmt_disabled_flag = python_with_stmt_disabled_flag
  method set_python_with_stmt_disabled_flag = python_with_stmt_disabled_flag <- true
  method clear_python_with_stmt_disabled_flag = python_with_stmt_disabled_flag <- false

  method python_ignore_docstring_flag = python_ignore_docstring_flag
  method set_python_ignore_docstring_flag = python_ignore_docstring_flag <- true
  method clear_python_ignore_docstring_flag = python_ignore_docstring_flag <- false

  method python_ignore_comment_flag = python_ignore_comment_flag
  method set_python_ignore_comment_flag = python_ignore_comment_flag <- true
  method clear_python_ignore_comment_flag = python_ignore_comment_flag <- false

  (* Fortran *)
  method fortran_max_line_length = fortran_max_line_length
  method set_fortran_max_line_length n = fortran_max_line_length <- n

  method fortran_parse_d_lines_flag = fortran_parse_d_lines_flag
  method set_fortran_parse_d_lines_flag = fortran_parse_d_lines_flag <- true
  method clear_fortran_parse_d_lines_flag = fortran_parse_d_lines_flag <- false

  method fortran_ignore_include_flag = fortran_ignore_include_flag
  method set_fortran_ignore_include_flag = fortran_ignore_include_flag <- true
  method clear_fortran_ignore_include_flag = fortran_ignore_include_flag <- false

  (* Verilog *)
  method verilog_ignore_include_flag = verilog_ignore_include_flag
  method set_verilog_ignore_include_flag = verilog_ignore_include_flag <- true
  method clear_verilog_ignore_include_flag = verilog_ignore_include_flag <- false


  (* external parser *)
  method get_external_parser pname =
    try
      Hashtbl.find external_parser_cache pname
    with
      Not_found ->
        let p = search_parser pname in
        Hashtbl.add external_parser_cache pname p;
        p

  initializer
    clone_map_file_name <- "clone_map"^gmap_ext;
    cache_dir_base <- Filename.concat (Filename.concat (Misc.get_home_dir()) ".cca") "cache"

end (* of class Parser_options.c *)
