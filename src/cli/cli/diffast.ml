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
(* command line driver for Diff/AST *)

module Xlist = Diffast_misc.Xlist
module Xhash = Diffast_misc.Xhash
module Xprint = Diffast_misc.Xprint
module Xfile = Diffast_misc.Xfile
module Fs = Diffast_misc.Fs
module Options = Diffast_core.Options
module Entity = Diffast_core.Entity
module Lang_base = Diffast_core.Lang_base
module Lang = Diffast_core.Lang
module Dirtree_base = Diffast_core.Dirtree_base
module Cache = Diffast_core.Cache
module Sourcecode = Diffast_core.Sourcecode
module Version = Diffast_api.Version
module Astapi = Diffast_api.Astapi
module Diffastapi = Diffast_api.Diffastapi

module A  = Diffast_core.Analyzing
module DT = Diffast_core.Dirtree
module S  = Diffast_core.Stat

let sprintf = Printf.sprintf
let printf = Printf.printf

let options = new Options.c

let verbose_msg = Xprint.verbose options#verbose_flag

let show_version_flag = ref false
let get_cache_dir_only = ref false
let parseonly_flag = ref false
let align_fragments_flag = ref false

let filenames = (ref [] : string list ref)
let keyword = ref ""

(*let _ = options#set_split_hunk_flag!!!!!*)

(* setters *)

let set_weak_flags() =
  options#set_weak_eq_flag;
  options#set_strip_empty_flag;
  options#set_ignore_non_orig_relabel_flag;
  options#set_ignore_move_of_unordered_flag;
  options#clear_recover_orig_ast_flag;
  options#set_sort_unordered_flag

let set_minimize_delta_flags() =
  options#set_ignore_non_orig_relabel_flag;
  options#set_minimize_delta_flag

let set_minimize_delta_more_flags() =
  set_minimize_delta_flags();
  (*options#set_strip_empty_flag;*)
  options#set_ignore_move_of_unordered_flag;
  (*options#clear_recover_orig_ast_flag;*)
  options#set_sort_unordered_flag

(*let set_viewer_mode_flags() =
  options#set_viewer_flag*)

let set_dist_mode_flags() =
  options#set_dist_flag

let set_external_parser_flags() =
  options#set_external_parser_flag

let set_dump_ast_flags() =
  parseonly_flag := true;
  options#set_dump_ast_flag;
  options#set_no_collapse_flag

let set_dump_compressed_ast_flags() =
  set_dump_ast_flags();
  options#set_compress_ast_flag

let set_dump_src_out s =
  parseonly_flag := true;
  options#set_dump_src_out s;
  options#set_dump_src_flag;
  options#set_no_collapse_flag

let set_dump_src_flag() =
  parseonly_flag := true;
  options#set_dump_src_flag;
  options#set_no_collapse_flag

let set_dump_delta_flag () =
  options#set_dump_delta_flag;
  options#set_java_anon_ctor_body_flag

let set_dump_delta_out s =
  options#set_dump_delta_out s;
  set_dump_delta_flag()

(*let set_dump_rev_delta() =
  options#clear_irreversible_flag;
  set_dump_delta_flag()*)

(*let set_dump_irrev_delta() =
  options#set_irreversible_flag;
  set_dump_delta_flag()*)

let set_dump_compressed_delta() =
  options#set_compress_delta_flag;
  set_dump_delta_flag()

let clear_prematch_flags() =
  options#set_prematch_flag
(*  options#clear_prematch_named_flag *)


let set_align_fragments_flags() =
  align_fragments_flag := true;
  options#set_no_collapse_flag

let set_fact_enc_FDLC() =
  options#set_fact_enc Entity.FDLC
let set_fact_enc_FDO() =
  options#set_fact_enc Entity.FDO
let set_fact_enc_FDLO() =
  options#set_fact_enc Entity.FDLO
let set_fact_enc_FDLCO() =
  options#set_fact_enc Entity.FDLCO

let set_fact_enc_PVFLC() =
  options#set_fact_enc Entity.PVFLC
let set_fact_enc_PVFO() =
  options#set_fact_enc Entity.PVFO
let set_fact_enc_PVFLO() =
  options#set_fact_enc Entity.PVFLO
let set_fact_enc_PVFLCO() =
  options#set_fact_enc Entity.PVFLCO

let set_fact_algo_MD5() =
  options#set_fact_algo Xhash.MD5
let set_fact_algo_SHA1() =
  options#set_fact_algo Xhash.SHA1
let set_fact_algo_SHA256() =
  options#set_fact_algo Xhash.SHA256
let set_fact_algo_RIPEMD160() =
  options#set_fact_algo Xhash.RIPEMD160
let set_fact_algo_GIT() =
  options#set_git_hash_flag;
  set_fact_algo_SHA1()
let set_fact_algo_PATH() =
  options#set_path_hash_flag;
  set_fact_algo_SHA1()


let set_fact_version str =
  let kind, ver = Entity.vkind_ver_of_string str in
  options#set_fact_versions
    (Array.of_list ((Array.to_list options#fact_versions) @ [(kind, ver)]))

let set_fact_proj s = options#set_fact_proj s

let set_fact_proj_root s =
  options#set_fact_proj_roots
    (Array.of_list ((Array.to_list options#fact_proj_roots) @ [s]))

let set_fact_for_changes_basic() =
  options#set_fact_for_changes_flag;
  options#set_fact_for_changes_basic_flag

let set_fact_for_mapping_restricted() =
  options#set_fact_for_mapping_flag;
  options#set_fact_for_mapping_restricted_flag


let usage_msg = sprintf "usage: %s [OPTIONS] FILE..\nOPTIONS:" Xprint.cmd_name

let speclist =
  [
   "-version", Arg.Set show_version_flag, "\tshow version";
   "-verbose", Arg.Unit (fun () -> options#set_verbose_flag), "\tdisplay verbose messages";

   "-check", Arg.Unit (fun () -> options#set_check_flag), "\tcheck result";
   "-r", Arg.Unit (fun () -> options#set_recursive_flag), "\t\tcompare files recursively";
   "-I", Arg.String options#add_search_path, "PATH\tadd search path";
   "-k", Arg.Unit (fun () -> options#set_keep_going_flag), "\t\tcontinue parsing despite errors";
   (*"-splithunk", Arg.Unit (fun () -> options#set_split_hunk_flag), "\tsplit delta hunks";!!!!!*)
   "-keep-filtered-temp-file", Arg.Unit (fun () -> options#set_keep_filtered_temp_file_flag),
                               "\tkeep filtered temporary file";
   "-parser:external", Arg.Unit set_external_parser_flags, "\t\trely on external parsers";
   "-parser:fortran", Arg.Unit (fun () -> options#designate_parser "fortran"),
                      "\t\tforce to use Fortran parser";
   "-parser:c", Arg.Unit (fun () -> options#designate_parser "c"), "\t\t\tforce to use C parser";
   "-parser:cpp", Arg.Unit (fun () -> options#designate_parser "cpp"),
                  "\t\t\tforce to use C++ parser";
   "-parser:disable", Arg.String options#disable_parser, "PARSER_ID\tdisable parser";
   "-parser:reduce-ast", Arg.Unit (fun () -> options#set_ast_reduction_flag), "\t\treduce AST";
   "-parser:normalize-ast", Arg.Unit (fun () -> options#set_normalize_ast_flag), "\tnormalize AST";
   "-parser:rely-on-naming-convention", Arg.Unit
                                        (fun () -> options#set_rely_on_naming_convention_flag),
                                        "\trely on naming convention";
   "-parser:partial-name-resolution", Arg.Unit (fun () -> options#set_partial_name_resolution_flag),
                                      "\tresolve names partially";
   "-parser:no-implicit-name-resolution",
     Arg.Unit (fun () -> options#set_no_implicit_name_resolution_flag),
     "\tdisable name resolution";

(* output *)
   "-dump:ast", Arg.Unit set_dump_ast_flags, "\t\tdump AST";
   "-dump:ast:compress", Arg.Unit set_dump_compressed_ast_flags, "\tdump compressed AST";
   "-dump:ccs", Arg.Unit (fun () -> options#set_dump_ccs_flag), "\t\tdump common code structure";
   "-dump:dot", Arg.Unit (fun () -> options#set_dump_dot_flag), "\t\tdump diff in DOT file";
   "-dump:origin", Arg.Unit (fun () -> options#set_dump_origin_flag), "\t\tdump origin file";
   "-dump:dots", Arg.Unit (fun () -> options#set_dots_flag),
                 "\t\toutput DOTs for intermediate trees";
   "-dump:src", Arg.Unit set_dump_src_flag, "\t\tdump unparsed AST";
   "-dump:src:out", Arg.String set_dump_src_out, "FILE\tdump unparsed AST into file";

(* delta *)
   "-dump:delta", Arg.Unit set_dump_delta_flag, "\t\tdump delta (Java only)";
   "-dump:delta:out", Arg.String set_dump_delta_out, "FILE\tdump delta into file";
   "-dump:delta:minimize", Arg.Unit set_minimize_delta_flags, "\t\tminimize delta";
   "-dump:delta:minimize:more", Arg.Unit set_minimize_delta_more_flags, "\tminimize delta more";
(*   "-dump:delta:rev", Arg.Unit set_dump_rev_delta, "\tgenerate reversible delta";*)
(*   "-dump:delta:irrev", Arg.Unit set_dump_irrev_delta, "\tgenerate irreversible delta";*)
   "-dump:delta:compress", Arg.Unit set_dump_compressed_delta, "\t\tdump compressed AST";

(* cache *)
   "-cache", Arg.String options#set_cache_dir_base,
             sprintf "DIR\tcache dir base (default: %s)" options#cache_dir_base;
   "-getcache", Arg.Set get_cache_dir_only, "\tonly get cache dir";
   "-clearcache", Arg.Unit (fun () -> options#set_clear_cache_flag), "\tclear cache dir";
   "-usecache", Arg.Unit (fun () -> options#clear_clear_cache_flag), "\tuse cache";
   "-fuzzycache", Arg.Unit (fun () -> options#set_fuzzy_cache_flag), "\tsearch cache dir fuzzily";
   "-layeredcache", Arg.Unit (fun () -> options#set_layered_cache_flag),
                    "\tconstruct layered cache dir";
   "-nolayeredcache", Arg.Unit (fun () -> options#clear_layered_cache_flag),
                      "\tconstruct flat cache dir";
   "-localcachename", Arg.String options#set_local_cache_name,
   sprintf "DIR\tlocal cache name (default: %s)" options#local_cache_name;

(* algorithm *)
   "-limit", Arg.Int options#set_tree_size_limit_percent,
             sprintf "N\t\ttree size limit (%%) (default: %d)" options#tree_size_limit_percent;
   "-thresh", Arg.Int options#set_tree_size_threshold,
              sprintf "N\t\ttree size threshold (default: %d)" options#tree_size_threshold;
   "-hardlimit", Arg.Int options#set_hard_tree_size_limit,
                 sprintf "N\t\thard tree size limit (default: %d)" options#hard_tree_size_limit;
(*
   "-multinodematch", Arg.Unit (fun () -> options#set_multi_node_match_flag),
                      "\tmaintain multiple node matches";
*)
   "-nomultinodematch", Arg.Unit (fun () -> options#clear_multi_node_match_flag),
                        "\tdo not maintain multiple node matches";
   "-preprune", Arg.Int options#set_preprune_threshold,
                sprintf "N\tpre-prune size threshold (default: %d)" options#preprune_threshold;
   "-nopreprune", Arg.Unit (fun () -> options#clear_preprune_flag), "\tdisable pre-pruning";
(*
   "-prematch", Arg.Unit (fun () -> options#set_prematch_flag), "\t\tenable pre-matching";
   "-prematch:named", Arg.Unit (fun () -> options#set_prematch_named_flag),
                      "\tenable pre-matching (named nodes only)";
   "-prematch:early", Arg.Unit (fun () -> options#set_prematch_early_resolve_flag),
                      "\tpre-matching multiple pairs early";
   "-prematch:all", Arg.Unit (fun () -> options#clear_prematch_named_flag),
                    "\tpre-match all kinds of nodes";
*)
   "-noprematch", Arg.Unit clear_prematch_flags, "\tdisable pre-matching";
   "-noshrink", Arg.Unit (fun () -> options#clear_shrink_moves_flag), "\tdisable move shrinking";
(*
   "-lock-match", Arg.Unit (fun () -> options#set_lock_matches_flag), "\t\tlock matched subtrees";
*)
   "-nore", Arg.Unit (fun () -> options#set_no_odd_relabel_elim_flag),
            "\tdisable odd relabel elimination";

   "-rrlv", Arg.Int (fun lv ->
                      options#set_rename_rectification_level lv;
                      if lv <= 0 then options#clear_use_binding_info_flag;
                      (*options#set_no_odd_relabel_elim_flag*)
                    ),
          sprintf "\tset rename rectification level (0:none, 1:u, 2:u+d, 3:u+ds) (default: %d)"
          options#rename_rectification_level;

   "-noglue", Arg.Unit (fun () -> options#set_no_glue_flag), "\tdisable delete-insert gluing";
   "-nomoves", Arg.Unit (fun () -> options#set_no_moves_flag), "\tdisable move generation";
   "-nomovrels", Arg.Unit (fun () -> options#set_no_movrels_flag), "\tdisable movrel generation";
   "-nocollapse", Arg.Unit (fun () -> options#set_no_collapse_flag), "\tdisable collapsing";
   "-noee", Arg.Unit (fun () -> options#set_no_enclave_elim_flag), "\tdisable enclave elimination";
   "-ee-match-algo-thresh", Arg.Int options#set_match_algo_threshold,
                            sprintf "N\tthreshold for algorithm selection (default: %d)"
                            options#match_algo_threshold;
   "-ignore-huge-arrays", Arg.Unit (fun () -> options#set_ignore_huge_arrays_flag),
                          sprintf "\t\tignore huge arrays (default:%s)"
                          (if options#ignore_huge_arrays_flag then "ignore" else "scan");
   "-scan-huge-arrays", Arg.Unit (fun () -> options#clear_ignore_huge_arrays_flag),
                        sprintf "\t\tdo not ignore huge arrays (default:%s)"
                        (if options#ignore_huge_arrays_flag then "ignore" else "scan");
   "-huge-array-thresh", Arg.Int options#set_huge_array_threshold,
                         sprintf "N\t\thuge array size threshold (default: %d)"
                         options#huge_array_threshold;
   "-ignore-huge-exprs", Arg.Unit (fun () -> options#set_ignore_huge_exprs_flag),
                         sprintf "\t\tignore huge exprs (default:%s)"
                         (if options#ignore_huge_exprs_flag then "ignore" else "scan");
   "-scan-huge-exprs", Arg.Unit (fun () -> options#clear_ignore_huge_exprs_flag),
                       sprintf "\t\tdo not ignore huge exprs (default:%s)"
                       (if options#ignore_huge_exprs_flag then "ignore" else "scan");
   "-huge-expr-thresh", Arg.Int options#set_huge_expr_threshold,
                        sprintf "N\t\thuge expr size threshold (default: %d)"
                        options#huge_expr_threshold;
   (*"-flatten-if", Arg.Unit (fun () -> options#set_flatten_if_flag),
                  sprintf "\t\tflatten if-statement (default:%s)"
                  (if options#flatten_if_flag then "true" else "false");*)
   (*"-deep-if-thresh", Arg.Int options#set_deep_if_threshold,
                      sprintf "N\t\tdeep nested if-statement threshold (default: %d)"
                      options#deep_if_threshold;*)
   "-moderate-nchildren-thresh", Arg.Int options#set_moderate_nchildren_threshold,
                                 sprintf "N\tmoderate num of children threshold (default: %d)"
                                 options#moderate_nchildren_threshold;
   "-movrel-stability-thresh", Arg.Float options#set_movrel_stability_threshold,
                               sprintf "R\tmovrel stability threshold (default: %f)"
                               options#movrel_stability_threshold;
   "-movrel-ratio-thresh", Arg.Float options#set_movrel_ratio_threshold,
                           sprintf "R\tmovrel ratio threshold (default: %f)"
                           options#movrel_ratio_threshold;
   "-mapped-neighbours-thresh", Arg.Float options#set_mapped_neighbours_difference_threshold,
                                sprintf "R\tmapped neighbours difference threshold (default: %f)"
                                options#mapped_neighbours_difference_threshold;
   "-no-unnamed-node-moves", Arg.Unit (fun () -> options#set_no_unnamed_node_move_flag),
                             "\tsuppress moves of unnamed nodes";
   "-no-binding-trace", Arg.Unit (fun () -> options#set_no_binding_trace_flag),
                        "\t\tdisable binding trace";
   "-weak", Arg.Unit set_weak_flags, "\t\t\tweaken node equation and node permutation detection";
   "-aggressive", Arg.Unit (fun () -> options#clear_conservative_flag),
                  "\t\t\taggressively find moves";
   "-ignore-moves-of-unordered", Arg.Unit (fun () -> options#set_ignore_move_of_unordered_flag),
                                 "\tignore moves of unordered constructs";

(* mode *)
   "-searchonly", Arg.Set_string keyword, "\tKEYWORD\tsearch keyword only";
   "-parseonly",  Arg.Set parseonly_flag, "\tparse only";
   (*"-viewer",     Arg.Unit set_viewer_mode_flags, "\tviewer friendly mode";*)
   "-dist",       Arg.Unit set_dist_mode_flags, "\tdistance computing mode";

(* fact *)
   "-fact", Arg.Unit (fun () -> options#set_fact_flag), "\t\t\tdump fact";
   "-fact:into-virtuoso", Arg.String options#set_fact_into_virtuoso,
                          "URI\toutput fact into graph <URI> in virtuoso";
   "-fact:into-directory", Arg.String options#set_fact_into_directory,
                           "DIR\toutput fact into directory DIR";
   "-fact:project", Arg.String set_fact_proj, "PROJ\t\tset project name to PROJ";
   "-fact:project-root", Arg.String set_fact_proj_root, "PATH\tset project root to PATH";
   "-fact:version", Arg.String set_fact_version,
                    "KIND:VER\tset version of AST to KIND:VER (KIND=REL|SVNREV|GITREV|VARIANT)";
   "-fact:add-versions", Arg.Unit (fun () -> options#set_fact_add_versions_flag),
                         "\tadd version statements to fact";
   "-fact:encoding:FDLC", Arg.Unit set_fact_enc_FDLC, "\tuse FDLC entity encoding";
   "-fact:encoding:FDO", Arg.Unit set_fact_enc_FDO, "\tuse FDO entity encoding";
   "-fact:encoding:FDLO", Arg.Unit set_fact_enc_FDLO, "\tuse FDLO entity encoding";
   "-fact:encoding:FDLCO", Arg.Unit set_fact_enc_FDLCO, "\tuse FDLCO entity encoding";
   "-fact:encoding:PVFLC", Arg.Unit set_fact_enc_PVFLC, "\tuse PVFLC entity encoding";
   "-fact:encoding:PVFO", Arg.Unit set_fact_enc_PVFO, "\tuse PVFO entity encoding";
   "-fact:encoding:PVFLO", Arg.Unit set_fact_enc_PVFLO, "\tuse PVFLO entity encoding";
   "-fact:encoding:PVFLCO", Arg.Unit set_fact_enc_PVFLCO, "use PVFLCO entity encoding";
   "-fact:hash:MD5", Arg.Unit set_fact_algo_MD5, "\tuse MD5 for entity encoding";
   "-fact:hash:SHA1", Arg.Unit set_fact_algo_SHA1, "\tuse SHA1 for entity encoding";
   "-fact:hash:SHA256", Arg.Unit set_fact_algo_SHA256, "\tuse SHA256 for entity encoding";
   "-fact:hash:RIPEMD160", Arg.Unit set_fact_algo_RIPEMD160, "\tuse RIPEMD160 for entity encoding";
   "-fact:hash:GIT", Arg.Unit set_fact_algo_GIT, "\tuse SHA1(Git) for entity encoding";
   "-fact:hash:PATH", Arg.Unit set_fact_algo_PATH,
                      "\tuse SHA1(with path header) for entity encoding";
   "-fact:changes", Arg.Unit (fun () -> options#set_fact_for_changes_flag),
                    "\toutput fact triples for changes";
   "-fact:changes:basic", Arg.Unit set_fact_for_changes_basic,
                          "\toutput restricted change fact triples";
   "-fact:mapping", Arg.Unit (fun () -> options#set_fact_for_mapping_flag),
                    "\t\toutput fact triples for mapping";
   "-fact:mapping:restricted", Arg.Unit set_fact_for_mapping_restricted,
                               "\toutput fact triples for restricted mapping";
   "-fact:restrict", Arg.Unit (fun () -> options#set_fact_restricted_flag),
                                 "\t\trestrict fact generation to specific categories";
   "-fact:ast", Arg.Unit (fun () -> options#set_fact_for_ast_flag),
                "\t\t\toutput fact triples for AST";
   "-fact:delta", Arg.Unit (fun () -> options#set_fact_for_delta_flag),
                  "\t\t\toutput fact triples for delta";
   "-fact:nocompress", Arg.Unit (fun () -> options#clear_fact_compress_flag),
                       "\t\tdisable fact compression";
   "-fact:size-thresh", Arg.Int options#set_fact_size_threshold,
                        sprintf "N\t\tfact buffer size threshold (default: %d)"
                        options#fact_size_threshold;
(*
   "-fact:pruned", Arg.Unit (fun () -> options#set_fact_add_pruned_flag),
                     "\t\toutput fact \"e prunedFrom e'\" for entities";
   "-fact:grafted", Arg.Unit (fun () -> options#set_fact_add_grafted_flag),
                      "\t\toutput fact \"e graftedOnto e'\" for entities";
*)

(* Java *)
   "-java:JLS", Arg.Int (fun lv -> options#set_java_lang_spec lv), "\tset JLS level";

(* Python *)
   "-python:disable-with-stmt", Arg.Unit (fun () -> options#set_python_with_stmt_disabled_flag),
                                "\tdisable with_statement feature";
   "-python:handle-comment", Arg.Unit (fun () -> options#clear_python_ignore_comment_flag),
                             "\thandle comment";

(* Fortran *)
   "-fortran:max-line-length", Arg.Int options#set_fortran_max_line_length,
                               "N\tset max line length to N";
   "-fortran:parse-d-lines",   Arg.Unit (fun () -> options#set_fortran_parse_d_lines_flag),
                               "\tparse d-lines as code";
   "-fortran:ignore-include",  Arg.Unit (fun () -> options#set_fortran_ignore_include_flag),
                               "\tignore include lines";
(*
(* origin *)
   "-origin:nctms", Arg.String options#set_nctms_file,
                    "NCTMS_FILE\tdump origin file using NCTMS_FILE";
   "-origin:revindex", Arg.Int options#set_revindex, "REV_INDEX\tdump origin file of REV_INDEX";
   "-origin:latest", Arg.String options#set_latest_target,
                     "TARGET\t\tset latest version of target to TARGET";
*)
(* others *)
   "-alignfragments", Arg.Unit set_align_fragments_flags, "\tfragments alignment mode";
   "-incompleteinfo", Arg.Unit (fun () -> options#set_incomplete_info_flag),
                      "\tsome parts of info are omitted in AST (for counting nodes only)";

 ]

let _ =
  try
    Arg.parse
      speclist
      (fun s -> filenames := s::!filenames)
      (usage_msg)
  with
  | Entity.Illegal_version_format s -> Xprint.error "illegal version format: %s" s; exit 1


let _ =
  if options#fact_into_virtuoso <> "" && options#fact_into_directory <> "" then begin
    Xprint.error "options -fact:into-virtuoso and -fact:into-directory are mutually exclusive";
    exit 1
  end


let _ =
  if !show_version_flag then begin
    printf "Diff/AST %s\n%s\n" Version.version Version.copyright;
    exit 0
  end


let astapi =
  let _ = Lang.setup_options options in
  new Diffastapi.c options


let _ =
  if !parseonly_flag || options#dump_origin_flag then begin
    begin
      try

        let filename_list = List.rev !filenames in
        let filea =
          match !filenames with
          | [] -> failwith "file(s) not specified"
          | h::_ ->
              if options#dump_src_out <> "" then
                [|h|]
              else
                Array.of_list filename_list
        in
        let nfiles = Array.length filea in
        let nvers = Array.length options#fact_versions in

        let last_proj_root = ref "" in
        let last_version = ref Entity.unknown_version in

        let multi_ver_mode = nfiles = 1 && nvers > 1 in

	Array.iteri
	  (fun i f ->
	    let pr =
	      try
                last_proj_root := options#fact_proj_roots.(i);
                !last_proj_root
	      with
	      | _ -> !last_proj_root
	    in
	    let v =
	      try
		last_version := options#fact_versions.(i);
                !last_version
	      with
	      | _ -> !last_version
	    in
            let file = Fs.file_of_path options f in

            if file#exists then begin

              if file#is_dir then begin
                try
                  astapi#extract_fact_from_dir file#tree
                with
                  Dirtree_base.To_be_skipped -> ()
              end
              else begin
                let show_info =
                  not (options#dump_src_flag && options#dump_src_out = "")
                in
                let version, versions =
                  if multi_ver_mode then
                    Entity.unknown_version, Array.to_list options#fact_versions
                  else
                    v, []
                in
                try
                  let _ =
                    astapi#parse_file
                      ~show_info
	              ~proj_root:pr ~version ~versions
	              ~get_cache_dir_only:!get_cache_dir_only
	              file
                  in
                  ()
                with
                | Lang_base.Parse_error(head, msg)  -> Xprint.warning ~head "%s" msg
                | Xfile.No_such_file_or_directory f -> Xprint.warning "\"%s\": no such file or directory" f
                | Failure msg                       -> Xprint.warning ~head:"[FAILURE]" "%s" msg
                | Lang_base.Error msg               -> Xprint.warning "%s" msg
              end

            end
            else
              Xprint.warning "not found: %s" file#path

	  ) filea
      with
      | Lang_base.Parse_error(head, msg)  -> Xprint.error ~head "%s" msg; exit 1
      | Xfile.No_such_file_or_directory f -> Xprint.error "\"%s\": no such file or directory" f; exit 1
      | Failure msg                       -> Xprint.error ~head:"[FAILURE]" "%s" msg; exit 1
      | Lang_base.Error msg               -> Xprint.error "%s" msg; exit 1
(*      | e                           -> Xprint.error ~head:"[EXCEPTION]" "%s" (Printexc.to_string e); exit 1*)
    end;
    exit 0
  end

let _ =
  if !keyword <> "" then begin
    begin
      try
        match !filenames with
        | p::_ ->
            let f = Fs.file_of_path options p in
            if f#exists then begin
	      let tree = astapi#__parse_file f in
	      if tree#label_match !keyword then
	        printf "found\n"
	      else
	        printf "not found\n"
            end
            else
              failwith (sprintf "not found: %s" f#path)

        | [] -> failwith "file(s) not specified";
      with
      | Lang_base.Parse_error(head, msg) -> Xprint.error ~head "%s" msg; exit 1
      | Failure msg                      -> Xprint.error ~head:"[FAILURE]" "%s" msg; exit 1
    end;
    exit 0
  end

let new_file, old_file =
  try
    match !filenames with
    | n::o::[] -> Fs.file_of_path options n, Fs.file_of_path options o
    | [x] -> begin
        if !get_cache_dir_only then begin
          let f = Fs.file_of_path options x in
	  if f#exists then begin
            if f#is_dir then
              printf "%s\n" (DT.get_cache_path_for_dir1 options f#tree)
            else
              ignore (astapi#parse_file ~get_cache_dir_only:true f);
	    exit 0
          end
          else begin
            Xprint.error ~head:"[FAILURE]" "not found: %s" f#path;
            exit 1
          end
        end
        else begin
	  Xprint.message "If you want to only parse, run with -parseonly flag.";
	  exit 0
        end
    end
    | _ ->
        Arg.usage speclist usage_msg;
        exit 1
  with
  | Xfile.No_such_file_or_directory f -> Xprint.error "\"%s\": no such file or directory" f; exit 1

let _ =
  if new_file = old_file && not !align_fragments_flag && not !get_cache_dir_only then begin
    (*if options#viewer_flag then
      printf "%c%!" Const.viewer_mode_status_SAME
    else*)
      printf "same file or directory\n";
    exit 0
  end


(* main routine *)
let _ =
  if options#dump_delta_flag && not options#conservative_flag then
    Xprint.warning "aggressive mode does not guarantees consistent delta!";
  try
    if not old_file#exists then
      failwith (sprintf "not found: %s" old_file#path);

    if not new_file#exists then
      failwith (sprintf "not found: %s" new_file#path);

    if old_file#is_dir && new_file#is_dir then begin (* directory diff mode *)
      let old_tree = old_file#tree in
      let new_tree = new_file#tree in

      if !get_cache_dir_only then
        printf "%s\n" (DT.get_cache_path_for_dir2 options old_tree new_tree)

      else begin
	verbose_msg "*** entering directory diff mode ***";
        astapi#compare_trees old_tree new_tree
      end
    end (* of directory diff mode *)

    else if !align_fragments_flag then begin
      let cache_path = astapi#get_cache_path2 old_file new_file in
      let gmap_path = Filename.concat cache_path options#clone_map_file_name in
      let ast1 = astapi#__parse_file old_file in
      let ast2 =
	if old_file#digest = new_file#digest then
	  ast1
	else
	  astapi#__parse_file new_file
      in
      let gmap = Sourcecode.load_gmap gmap_path in
      ast1#align_fragments gmap ast2
    end

    else begin (* file diff mode *)
      let cache_path = astapi#get_cache_path2 old_file new_file in
      if !get_cache_dir_only then
	printf "%s\n" cache_path
      else begin
	verbose_msg "*** entering source file diff mode ***";
        let stat_paths = astapi#search_cache_for_stat cache_path in
	if
	  stat_paths <> [] && (not options#clear_cache_flag)
	then begin

	  Xprint.message "read from cache%s:\n%s"
            (if options#local_cache_name = "" then
              ""
            else
              sprintf " (local cache name: %s)" options#local_cache_name)
            (Xlist.to_string (fun x -> x.Cache.sr_cache_path) "\n" stat_paths);

          let handle_file_versions i file =
            let cache_path = astapi#get_cache_path1 file in
            let proj_root =
              try
	        options#fact_proj_roots.(i)
              with
              | _ -> ""
            in
            let version =
              try
	        options#fact_versions.(i)
              with
              | _ -> Entity.unknown_version
            in
            astapi#handle_file_versions ~lock:false None cache_path proj_root file [version]
          in
          handle_file_versions 0 old_file;
          handle_file_versions 1 new_file;

	  try
	    let stat =
              S.File.scan_diff_stat ~max_retry_count:options#max_retry_count
                stat_paths
            in
	    S.File.dump_diff_stat_ch ~short:true stat stdout
	  with
	    S.Stat_not_found ->
	      Xprint.warning "re-computing...";
	      ignore (astapi#compare_files ~cache_path old_file new_file)
	end
	else begin
          let stat = astapi#compare_files ~cache_path old_file new_file in
          if not options#verbose_flag then begin
            Xprint.message "results saved in %s" cache_path;
            S.File.dump_diff_stat_ch ~short:true stat stdout
          end
        end
      end
    end

  with
(*
  | A.No_differences_found            -> printf "\nno differences found\n%!"
*)
  | Astapi.Skip f                    -> Xprint.error "\"%s\": unsupported source file" f; exit 1
  | Xfile.No_such_file_or_directory f -> Xprint.error "\"%s\": no such file or directory" f; exit 1
  | Xfile.No_extension f              -> Xprint.error "have no file extension: \"%s\"" f; exit 1
  | Lang_base.Error msg               -> Xprint.error "%s" msg; exit 1
  | Lang_base.Parse_error(head, msg)  -> Xprint.error ~head "%s" msg; exit 1
(*
  | Failure msg                       -> Xprint.error ~head:"[FAILURE]" "%s" msg; exit 1
  | Sys_error msg                     -> Xprint.error "%s" msg; exit 1
  | Triple.Proj_root_not_set          -> Xprint.error "project root not set"; exit 1
*)

  (*| e -> Xprint.error ~head:"[EXCEPTION]" "%s" (Printexc.to_string e); exit 1*)
