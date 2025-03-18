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

module Xhash = Diffast_misc.Xhash
module Xprint = Diffast_misc.Xprint
module Xfile = Diffast_misc.Xfile
module Fs = Diffast_misc.Fs
module Parser_options = Diffast_core.Parser_options
module Entity = Diffast_core.Entity
module Lang_base = Diffast_core.Lang_base
module Lang = Diffast_core.Lang
module Dirtree_base = Diffast_core.Dirtree_base
module Version = Diffast_api.Version
module Astapi = Diffast_api.Astapi

let sprintf = Printf.sprintf
let printf  = Printf.printf

let options = new Parser_options.c

(*let verbose_msg = Xprint.verbose options#verbose_flag*)

let show_version_flag = ref false
let get_cache_dir_only = ref false

let filenames = (ref [] : string list ref)
let keyword = ref ""


(* setters *)

let set_external_parser_flags() =
  options#set_external_parser_flag

let set_dump_ast_flags() =
  options#set_dump_ast_flag;
  options#set_no_collapse_flag

let set_dump_compressed_ast_flags() =
  set_dump_ast_flags();
  options#set_compress_ast_flag

let set_dump_src_out s =
  options#set_dump_src_out s;
  options#set_dump_src_flag;
  options#set_no_collapse_flag

let set_dump_src_flag() =
  options#set_dump_src_flag;
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


let usage_msg = sprintf "usage: %s [OPTIONS] FILE..\nOPTIONS:" Xprint.cmd_name

let speclist =
  [
   "-version", Arg.Set show_version_flag, "\tshow version";
   "-verbose", Arg.Unit (fun () -> options#set_verbose_flag), "\tdisplay verbose messages";

   "-I", Arg.String options#add_search_path, "PATH\tadd search path";

   "-k", Arg.Unit (fun () -> options#set_keep_going_flag), "\t\tcontinue parsing in spite of errors";


   "-keep-filtered-temp-file", Arg.Unit (fun () -> options#set_keep_filtered_temp_file_flag),
   "\tkeep filtered temporary file";

   "-parser:external", Arg.Unit set_external_parser_flags, "\t\trely on external parsers";
   "-parser:fortran", Arg.Unit (fun () -> options#designate_parser "fortran"), "\t\tforce to use Fortran parser";
   "-parser:c", Arg.Unit (fun () -> options#designate_parser "c"), "\t\t\tforce to use C parser";
   "-parser:cpp", Arg.Unit (fun () -> options#designate_parser "cpp"), "\t\t\tforce to use C++ parser";
   "-parser:disable", Arg.String options#disable_parser, "PARSER_ID\tdisable parser";

(* output *)
   "-dump:ast", Arg.Unit set_dump_ast_flags, "\tdump AST";
   "-dump:ast:compress", Arg.Unit set_dump_compressed_ast_flags, "\tdump compressed AST";
   "-dump:src", Arg.Unit set_dump_src_flag, "\t\tdump unparsed AST";
   "-dump:src:out", Arg.String set_dump_src_out, "FILE\tdump unparsed AST into file";

(* cache *)
   "-cache", Arg.String options#set_cache_dir_base,
   sprintf "DIR\tcache dir base (default: %s)" options#cache_dir_base;

   "-getcache", Arg.Set get_cache_dir_only, "\tonly get cache dir";
   "-clearcache", Arg.Unit (fun () -> options#set_clear_cache_flag), "\tclear cache dir";
   "-usecache", Arg.Unit (fun () -> options#clear_clear_cache_flag), "\tuse cache";
   "-layeredcache", Arg.Unit (fun () -> options#set_layered_cache_flag), "\tconstruct layered cache dir";
   "-nolayeredcache", Arg.Unit (fun () -> options#clear_layered_cache_flag), "\tconstruct flat cache dir";

   "-localcachename", Arg.String options#set_local_cache_name,
   sprintf "DIR\tlocal cache name (default: %s)" options#local_cache_name;



(* mode *)
   "-searchonly", Arg.Set_string keyword, "\tKEYWORD\tsearch keyword only";

(* fact *)
   "-fact", Arg.Unit (fun () -> options#set_fact_flag), "\tdump fact";
   "-fact:into-virtuoso", Arg.String options#set_fact_into_virtuoso,
                          "URI\t output fact into graph <URI> in virtuoso";
   "-fact:into-directory", Arg.String options#set_fact_into_directory,
                           "DIR\t output fact into directory DIR";
   "-fact:project",      Arg.String set_fact_proj, "PROJ\tset project name to PROJ";
   "-fact:project-root", Arg.String set_fact_proj_root, "PATH\tset project root to PATH";
   "-fact:version",      Arg.String set_fact_version,
                         "KIND:VER\tset version of AST to KIND:VER (KIND=REL|SVNREV|GITREV|VARIANT)";
   "-fact:add-versions", Arg.Unit (fun () -> options#set_fact_add_versions_flag),
                         "\tadd version statements to fact";
   "-fact:encoding:FDLC",   Arg.Unit set_fact_enc_FDLC, "\tuse FDLC entity encoding";
   "-fact:encoding:FDO",    Arg.Unit set_fact_enc_FDO, "\tuse FDO entity encoding";
   "-fact:encoding:FDLO",   Arg.Unit set_fact_enc_FDLO, "\tuse FDLO entity encoding";
   "-fact:encoding:FDLCO",  Arg.Unit set_fact_enc_FDLCO, "\tuse FDLCO entity encoding";
   "-fact:encoding:PVFLC",  Arg.Unit set_fact_enc_PVFLC, "\tuse PVFLC entity encoding";
   "-fact:encoding:PVFO",   Arg.Unit set_fact_enc_PVFO, "\tuse PVFO entity encoding";
   "-fact:encoding:PVFLO",  Arg.Unit set_fact_enc_PVFLO, "\tuse PVFLO entity encoding";
   "-fact:encoding:PVFLCO", Arg.Unit set_fact_enc_PVFLCO, "use PVFLCO entity encoding";
   "-fact:hash:MD5",        Arg.Unit set_fact_algo_MD5, "\tuse MD5 for entity encoding";
   "-fact:hash:SHA1",       Arg.Unit set_fact_algo_SHA1, "\tuse SHA1 for entity encoding";
   "-fact:hash:SHA256",     Arg.Unit set_fact_algo_SHA256, "\tuse SHA256 for entity encoding";
   "-fact:hash:RIPEMD160",  Arg.Unit set_fact_algo_RIPEMD160, "\tuse RIPEMD160 for entity encoding";
   "-fact:hash:GIT",        Arg.Unit set_fact_algo_GIT, "\tuse SHA1(Git) for entity encoding";
   "-fact:hash:PATH",       Arg.Unit set_fact_algo_PATH,
                            "\tuse SHA1(with path header) for entity encoding";
   "-fact:restrict", Arg.Unit (fun () -> options#set_fact_restricted_flag),
                     "\trestrict fact generation to specific categories";
   "-fact:ast",      Arg.Unit (fun () -> options#set_fact_for_ast_flag),
                     "\t\toutput fact triples for AST";

   "-fact:nocompress", Arg.Unit (fun () -> options#clear_fact_compress_flag),
                       "\tdisable fact compression";
   "-fact:size-thresh", Arg.Int options#set_fact_size_threshold,
                        sprintf "N\tfact buffer size threshold (default: %d)"
                                options#fact_size_threshold;

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
   "-fortran:parse-d-lines", Arg.Unit (fun () -> options#set_fortran_parse_d_lines_flag),
                             "\tparse d-lines as code";
   "-fortran:ignore-include", Arg.Unit (fun () -> options#set_fortran_ignore_include_flag),
                              "\tignore include lines";
(*
(* Yacfe *)
   "-yacfe:macros", Arg.String options#set_yacfe_defs_builtins, "FILE\tread yacfe macro FILE";
(*
   "-yacfe:env", Arg.String options#set_yacfe_env, "FILE\tread yacfe env FILE";
*)
   "-yacfe:if0", Arg.Unit (fun () -> options#clear_ignore_if0_flag),
                 "\t\tparse code in '#if 0' block";
*)
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
    printf "Parse/SRC %s\n%s\n" Version.version Version.copyright;
    exit 0
  end


let astapi =
  let _ = Lang_base.setup_options options in
  new Astapi.c options


let _ =
  if !keyword <> "" then begin
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
  end
  else begin
    try
      let filename_list = List.rev !filenames in
      let filea =
        match !filenames with
        | [] -> failwith "file(s) not specified"
        | _ -> Array.of_list filename_list
      in

      let last_proj_root = ref "" in
      let last_version = ref Entity.unknown_version in

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
              (*try*)
                let _ =
                  astapi#parse_file
                    ~show_info:true
	            ~proj_root:pr ~version:v
	            ~get_cache_dir_only:!get_cache_dir_only
	            file
                in
                ()
              (*with
              | Lang_base.Parse_error(head, msg)  -> Xprint.warning ~head "%s" msg
              | Xfile.No_such_file_or_directory f -> Xprint.warning "\"%s\": no such file or directory" f
              | Failure msg                       -> Xprint.warning ~head:"[FAILURE]" "%s" msg
              | Lang_base.Error msg               -> Xprint.warning "%s" msg*)
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
  end
