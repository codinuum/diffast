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
(* command line driver for Sim/AST *)

module Xprint = Diffast_misc.Xprint
module Xfile = Diffast_misc.Xfile
module Fs = Diffast_misc.Fs
module Options = Diffast_core.Options
module Lang_base = Diffast_core.Lang_base
module Lang = Diffast_core.Lang
module Version = Diffast_api.Version
module Astapi = Diffast_api.Astapi
module Diffastapi = Diffast_api.Diffastapi

module A  = Diffast_core.Analyzing
module DT = Diffast_core.Dirtree
module S  = Diffast_core.Stat

let sprintf = Printf.sprintf
let printf = Printf.printf

let options = new Options.c

let show_version_flag = ref false
let get_cache_dir_only = ref false
let parseonly_flag = ref false

let filenames = (ref [] : string list ref)
(*let keyword = ref ""*)

(*let _ = options#set_split_hunk_flag!!!!!*)

(* setters *)

let _ =
  options#set_ignore_non_orig_relabel_flag;
  options#set_ignore_move_of_unordered_flag

let set_weak_flags() =
  options#set_partial_typename_resolution_flag;
  options#set_weak_eq_flag;
  options#set_strip_empty_flag;
  options#set_ignore_non_orig_relabel_flag;
  options#set_ignore_move_of_unordered_flag;
  options#clear_recover_orig_ast_flag;
  options#set_sort_unordered_flag

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

let clear_prematch_flags() =
  options#clear_prematch_flag
(*  options#clear_prematch_named_flag *)


let usage_msg = sprintf "usage: %s [OPTIONS] FILE..\nOPTIONS:" Xprint.cmd_name

let speclist =
  [
   "-version", Arg.Set show_version_flag, "\tshow version";
   "-verbose", Arg.Unit (fun () -> options#set_verbose_flag), "\tdisplay verbose messages";
   "-check", Arg.Unit (fun () -> options#set_check_flag), "\tcheck result";
   "-k", Arg.Unit (fun () -> options#set_keep_going_flag), "\t\tcontinue parsing despite errors";

   "-parser:rely-on-naming-convention", Arg.Unit
                                        (fun () -> options#set_rely_on_naming_convention_flag),
                                        "\trely on naming convention";
   "-parser:partial-name-resolution", Arg.Unit (fun () -> options#set_partial_name_resolution_flag),
                                      "\tresolve names partially";
   "-parser:no-implicit-name-resolution",
     Arg.Unit (fun () -> options#set_no_implicit_name_resolution_flag),
     "\tdisable directory-based name resolution";

(* output *)
   "-dump:ast", Arg.Unit set_dump_ast_flags, "\t\tdump AST";
   "-dump:ast:compress", Arg.Unit set_dump_compressed_ast_flags, "\tdump compressed AST";
   "-dump:dot", Arg.Unit (fun () -> options#set_dump_dot_flag), "\t\tdump diff in DOT file";
   "-dump:src", Arg.Unit set_dump_src_flag, "\t\tdump unparsed AST";
   "-dump:src:out", Arg.String set_dump_src_out, "FILE\tdump unparsed AST into file";

(* cache *)
   "-cache", Arg.String options#set_cache_dir_base,
   sprintf "DIR\tcache dir base (default: %s)" options#cache_dir_base;
   "-getcache", Arg.Set get_cache_dir_only, "\tonly get cache dir";
   "-clearcache", Arg.Unit (fun () -> options#set_clear_cache_flag), "\tclear cache dir";
   "-usecache", Arg.Unit (fun () -> options#clear_clear_cache_flag), "\tuse cache";
   "-fuzzycache", Arg.Unit (fun () -> options#set_fuzzy_cache_flag), "\tsearch cache dir fuzzily";
   "-layeredcache", Arg.Unit (fun () -> options#set_layered_cache_flag), "\tconstruct layered cache dir";
   "-nolayeredcache", Arg.Unit (fun () -> options#clear_layered_cache_flag), "\tconstruct flat cache dir";
   "-localcachename", Arg.String options#set_local_cache_name,
                        sprintf "DIR\tlocal cache name (default: %s)" options#local_cache_name;

(* algorithm *)
(*
   "-limit", Arg.Int options#set_tree_size_limit_percent,
   sprintf "N\ttree size limit (%%) (default: %d)" options#tree_size_limit_percent;

   "-thresh", Arg.Int options#set_tree_size_threshold,
   sprintf "N\ttree size threshold (default: %d)" options#tree_size_threshold;

   "-hardlimit", Arg.Int options#set_hard_tree_size_limit,
   sprintf "N\thard tree size limit (default: %d)" options#hard_tree_size_limit;

   "-multinodematch", Arg.Unit (fun () -> options#set_multi_node_match_flag), "\tmaintain multiple node matches";

   "-preprune", Arg.Int options#set_preprune_threshold,
   sprintf "N\tpre-prune size threshold (default: %d)" options#preprune_threshold;
*)
   "-nopreprune", Arg.Unit (fun () -> options#clear_preprune_flag), "\tdisable pre-pruning";

   "-noprematch", Arg.Unit clear_prematch_flags, "\tdisable pre-matching";

   "-noshrink", Arg.Unit (fun () -> options#clear_shrink_moves_flag), "\tdisable move shrinking";

   "-noee", Arg.Unit (fun () -> options#set_no_enclave_elim_flag), "\tdisable enclave elimination";
(*
   "-ee-match-algo-thresh", Arg.Int options#set_match_algo_threshold,
   sprintf "N\tthreshold for algorithm selection (default: %d)" options#match_algo_threshold;
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
   "-nomovrels", Arg.Unit (fun () -> options#set_no_movrels_flag), "\tdisable movrel generation";
   "-nocollapse", Arg.Unit (fun () -> options#set_no_collapse_flag), "\tdisable collapsing";
(*
   "-ignore-huge-arrays", Arg.Unit (fun () -> options#set_ignore_huge_arrays_flag),
   sprintf "\t\tignore huge arrays (default:%s)"
     (if options#ignore_huge_arrays_flag then "ignore" else "scan");
*)
   "-scan-huge-arrays", Arg.Unit (fun () -> options#clear_ignore_huge_arrays_flag),
                          sprintf "\tdo not ignore huge arrays (default:%s)"
                            (if options#ignore_huge_arrays_flag then "ignore" else "scan");
   "-huge-array-thresh", Arg.Int options#set_huge_array_threshold,
                         sprintf "N\thuge array size threshold (default: %d)"
                           options#huge_array_threshold;
   "-no-unnamed-node-moves", Arg.Unit (fun () -> options#set_no_unnamed_node_move_flag),
                             "\tsuppress moves of unnamed nodes";
   "-no-binding-trace", Arg.Unit (fun () -> options#set_no_binding_trace_flag),
                        "\t\tdisable binding trace";
   "-weak", Arg.Unit set_weak_flags, "\t\t\tweaken node equation and node permutation detection";
   "-aggressive", Arg.Unit (fun () -> options#clear_conservative_flag),
                  "\t\t\taggressively find moves";
   "-ignore-moves-of-unordered", Arg.Unit (fun () -> options#set_ignore_move_of_unordered_flag),
                                 "\tignore moves of unordered constructs";

(*
"-moderate-nchildren-thresh", Arg.Int options#set_moderate_nchildren_threshold,
sprintf "N\tmoderate num of children threshold (default: %d)" options#moderate_nchildren_threshold;
*)
(*
"-movrel-stability-thresh", Arg.Float options#set_movrel_stability_threshold,
sprintf "R\tmovrel stability threshold (default: %f)" options#movrel_stability_threshold;

"-movrel-ratio-thresh", Arg.Float options#set_movrel_ratio_threshold,
sprintf "R\tmovrel ratio threshold (default: %f)" options#movrel_ratio_threshold;

"-mapped-neighbours-thresh", Arg.Float options#set_mapped_neighbours_difference_threshold,
sprintf "R\tmapped neighbours difference threshold (default: %f)" options#mapped_neighbours_difference_threshold;
*)

(* mode *)
   "-parseonly",  Arg.Set parseonly_flag, "\tparse only";

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

 ]

let _ =
  Arg.parse
    speclist
    (fun s -> filenames := s::!filenames)
    (usage_msg)

let _ =
  if !show_version_flag then begin
    printf "Sim/AST %s\n%s\n" Version.version Version.copyright;
    exit 0
  end


let astapi =
  let _ = Lang.setup_options options in
  new Diffastapi.c options


let _ =
  if !parseonly_flag then begin
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

	Array.iteri
	  (fun _ f ->
            let file = Fs.file_of_path options f in

            if file#exists then begin

              let show_info =
                not (options#dump_src_flag && options#dump_src_out = "")
              in
              try
                let _ =
                  astapi#parse_file
                    ~show_info
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

let new_file, old_file =
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

let _ =
  if new_file = old_file && not !get_cache_dir_only then begin
    printf "same file or directory\n";
    exit 0
  end


(* main routine *)
let _ =
  try
    if not old_file#exists then
      failwith (sprintf "not found: %s" old_file#path);

    if not new_file#exists then
      failwith (sprintf "not found: %s" new_file#path);

    if old_file#is_dir then
      failwith (sprintf "not a file: %s" old_file#path);

    if new_file#is_dir then
      failwith (sprintf "not a file: %s" new_file#path);

    begin (* file diff mode *)
      let cache_path = astapi#get_cache_path2 old_file new_file in
      if !get_cache_dir_only then
	printf "%s\n" cache_path
      else begin
        let stat_paths = astapi#search_cache_for_stat cache_path in
        let stat =
          if stat_paths = [] || options#clear_cache_flag then
	    astapi#compare_files ~cache_path old_file new_file
          else
            S.File.scan_diff_stat ~max_retry_count:options#max_retry_count stat_paths
        in
	S.File.dump_sim_ch stat stdout
      end
    end

  with
(*
  | A.No_differences_found            -> printf "1.0\n"
*)
  | Astapi.Skip f                    -> Xprint.error "\"%s\": unsupported source file" f; exit 1
  | Xfile.No_such_file_or_directory f -> Xprint.error "\"%s\": no such file or directory" f; exit 1
  | Xfile.No_extension f              -> Xprint.error "have no file extension: \"%s\"" f; exit 1
  | Lang_base.Error msg                    -> Xprint.error "%s" msg; exit 1
  | Failure msg                       -> Xprint.error ~head:"[FAILURE]" "%s" msg; exit 1
(*
  | Sys_error msg                     -> Xprint.error "%s" msg; exit 1
  | Lang_base.Parse_error(head, msg)       -> Xprint.error ~head "%s" msg; exit 1
  | Triple.Proj_root_not_set          -> Xprint.error "project root not set"; exit 1
*)

  (*| e -> Xprint.error ~head:"[EXCEPTION]" "%s" (Printexc.to_string e); exit 1*)
