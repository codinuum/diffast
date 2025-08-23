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
(*
 * A Diff/Patch Tool for Source Code
 *
 * diffastcore.ml
 *
 *)

[%%prepare_logger]

module XML = Diffast_misc.XML
module Fs = Diffast_misc.Fs
module Lang = Diffast_core.Lang
module Const = Diffast_core.Const
module Delta_base = Diffast_core.Delta_base
module Delta_format = Diffast_core.Delta_format

open Printf

open Astapi

module A  = Diffast_core.Analyzing
module DT = Diffast_core.Dirtree

let bar_pat = Str.regexp_string "|"
let get_paths s = Str.split bar_pat s

[%%capture_path
class c options = object (self)
  inherit Astapi.base_c options

  method get_cache_path2 = options#get_cache_path_for_file2

  method __force_to_process =
    options#dump_ast_flag || options#dump_src_flag || options#clear_cache_flag

  method __parse_file ?(proj_root="") ?(version=Entity.unknown_version) file =
    [%debug_log "parsing \"%s\"" file#fullpath];

    let ext = file#get_extension in
    let lang = Lang.search options ext in
    let builder = lang#make_tree_builder options in
    let tree = builder#build_tree file in

    begin
      let extra = builder#extra_source_files in
      match options#fact_versions with
      | [|v1;v2|] ->
          if version = v1 then
            self#add_extra_source_files1 ext extra
          else if version = v2 then
            self#add_extra_source_files2 ext extra
      | [|_|] -> self#add_extra_source_files ext extra
      | _ -> ()
    end;

    if proj_root <> "" then
      tree#set_proj_root proj_root;

    if version <> Entity.unknown_version then begin
      let k, v = version in
      tree#set_vkind k;
      tree#set_version v
    end;

    if options#fact_flag then begin
      let cache_path = self#get_cache_path1 file in
      self#verbose_msg "extracting source fact...";
      lang#extract_fact options cache_path tree;
      self#verbose_msg "done.";
    end;

    tree

  method! _parse_file
      ?(fact_store=None)
      ?(show_info=false)
      ?(proj_root="")
      ?(version=Entity.unknown_version)
      ?(versions=[])
      ?(get_cache_dir_only=false)
      file
      =
    let cache_path = self#get_cache_path1 file in

    [%debug_log "cache_path=\"%s\"" cache_path];

    if get_cache_dir_only then begin
      printf "%s\n" cache_path;
      SF.dummy_info
    end
    else begin
      let info_paths = self#search_cache_for_info cache_path in
      if
        info_paths <> [] &&
        not
          (
           options#dump_ast_flag ||
           options#dump_src_flag ||
           options#dump_origin_flag ||
           options#clear_cache_flag
          )
      then begin

        if show_info then
          self#verbose_msg "using caches%s:\n%s"
            (if options#local_cache_name = "" then
              ""
            else
              sprintf " (local cache name: %s)" options#local_cache_name)
            (Xlist.to_string
               (fun x -> "\""^x.Cache.sr_cache_path^"\"") "\n" info_paths);


        self#handle_file_versions ~lock:false fact_store cache_path proj_root file
          (version :: versions);

        let info = SF.scan_info info_paths in

        if show_info then
          SF.show_info info;

        info

      end
      else begin (* not processed || dump_ast || dump_src || dump_origin || clear_cache *)
        let _ = Cache.prepare_cache_dir options cache_path in
        let tree = self#__parse_file ~proj_root ~version file in

        if options#recover_orig_ast_flag then
          tree#recover_true_children ~initial_only:true ();

        if options#dots_flag then begin
          tree#save_dot "AST" [] (Filename.concat cache_path (file#basename^".dot"))
        end;

        if options#dump_dot_flag then begin
          let fname_dot = file#basename^".dot" in
          let dot = tree#to_dot_initial (*file#basename*) [] in
          Xfile.dump fname_dot
            (fun ch ->
              let buf = Buffer.create 0 in
              Buffer.add_string buf "digraph {";
              Buffer.add_buffer buf dot;
              Buffer.add_string buf "}";
              Buffer.output_buffer ch buf
            );
          self#verbose_msg "AST (in DOT) saved in \"%s\"" fname_dot
        end;

        if options#dump_ast_flag || options#dump_src_flag then begin

          if options#dump_ast_flag then begin
            let fname_astml = file#fullpath^Astml.extension in
            match Misc.find_file_name_with_exts fname_astml Astml.extensions with
            | Some fn -> Xprint.warning "already exists: \"%s\"" fn
            | None ->
                tree#dump_astml ~comp:options#ast_compression fname_astml;
                self#verbose_msg "AST (in ASTML) saved in \"%s\"" fname_astml
          end;

          if options#dump_src_flag then begin
            let opening = options#dump_src_out <> "" in
            let ch =
              if opening then
                open_out options#dump_src_out
              else
                Stdlib.stdout
            in
            tree#unparse_ch (OC.of_pervasives ch);
            if opening then
              close_out ch
          end

        end
        (*else if options#dump_origin_flag then begin (* dump origin related information *)
          let origin_file = Filename.concat cache_path options#origin_file_name in
          let ending_file = Filename.concat cache_path options#ending_file_name in

          [%debug_log "dumping origins: nctms_file=\"%s\" revindex=%d"
            options#nctms_file options#revindex];

          [%debug_log "dumping origins: origin_file=\"%s\" ending_file=\"%s\""
            origin_file ending_file];

          let bufsize = file#size in
          let (nnodes, nknown, cov, nds_tbl, nknown_ending, cov_ending, nds_tbl_ending) =
            tree#dump_origin bufsize options#nctms_file options#revindex origin_file ending_file
          in
          self#verbose_msg "origins saved in \"%s\"" origin_file;
          self#verbose_msg "endings saved in \"%s\"" ending_file;

          let cov_file = Filename.concat cache_path options#coverage_file_name in
          self#dump_coverage cov_file (nknown, nnodes, cov);
          self#verbose_msg "coverage(origin) saved in \"%s\"" cov_file;

          let frag_file =
            self#mkfragfilepath cache_path options#fragment_file_name options#revindex
          in
          self#dump_fragment M_ORIGIN frag_file nds_tbl;
          self#verbose_msg "fragments(origin) saved in \"%s\"" frag_file;

          let cov_file_ending = Filename.concat cache_path options#coverage_file_name_ending in
          self#dump_coverage cov_file_ending (nknown_ending, nnodes, cov_ending);
          self#verbose_msg "coverage(ending) saved in \"%s\"" cov_file_ending;

          let frag_file_ending =
            self#mkfragfilepath cache_path options#fragment_file_name_ending options#revindex
          in
          self#dump_fragment M_ENDING frag_file_ending nds_tbl_ending;
          self#verbose_msg "fragments(ending) saved in \"%s\"" frag_file_ending
        end*); (* if options#dump_origin_flag *)

        S._dump_source cache_path tree;
        S._dump_parser cache_path tree;
        SF.dump_info cache_path tree;

        self#handle_file_versions ~lock:false fact_store cache_path proj_root file
          (version :: versions);

        let info = SF.get_tree_info tree in

        if show_info then begin
          SF.dump_info_ch info stdout;
          flush stdout
        end;

        info

      end (* if not processed *)

    end (* if not get_cache_dir_only *)

  method compare_files ?(cache_path="") file1 file2 =
    let r = self#_compare_files ~cache_path file1 file2 in
    file1#free_local_file;
    file2#free_local_file;
    r

  method _compare_files ?(cache_path="") file1 file2 =
    self#verbose_msg "comparing:\n T1=%s with\n T2=%s" file1#fullpath file2#fullpath;
    let sw = new Misc.stopwatch in

    if options#verbose_flag then
      sw#start;

    options#moveid_generator#reset;

    let is_valid_src, invalid_src =
      if options#parser_designated then
        true, ""
      else if options#check_extension file1#path then
        if options#check_extension file2#path then
          true, ""
        else
          false, file2#path
      else
        false, file1#path
    in

    if is_valid_src then begin

      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_OK;*)

      let comparator = A.get_comparator options ~cache_path file1 file2 in

      let dstat = comparator#compare in

      self#add_extra_source_files1 file1#get_extension comparator#extra_source_files1;
      self#add_extra_source_files2 file2#get_extension comparator#extra_source_files2;

      if options#verbose_flag then begin
        sw#stop;
        self#verbose_msg "execution completed in %f seconds" sw#show
      end;

      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_DONE;*)

      Cache.put_completion_mark cache_path;

      dstat
    end
    else begin
      (*if options#viewer_flag then
        printf "%c%!" Const.viewer_mode_status_EXT_MISMATCH
      else*)
        self#verbose_msg "skipping...";
      raise (Skip invalid_src)
    end

  method! private parse_file_and_handle_info ?(head="") fact_store proj_root version file handler =
    let head =
      if options#fact_proj <> "" then
        head^"["^options#fact_proj^"]"
      else
        head
    in
    try
      let info = self#parse_file ~fact_store ~proj_root ~version file in
      handler info
    with
    | Failure msg                        -> Xprint.warning ~head:(head^"[FAILURE]") "%s" msg
    | Lang_base.Error msg                -> Xprint.warning ~head:(head^"[LANG]") "%s" msg
    | Lang_base.Parse_error(head', msg)  -> Xprint.warning ~head:(head^head') "%s" msg
    | Astml.External_parser_not_found pn -> Xprint.warning ~head "external parser not found: \"%s\"" pn



  method compare_trees old_tree new_tree =
    let old_proj_root =
      try
        options#fact_proj_roots.(0)
      with
      | _ -> ""
    in
    let new_proj_root =
      try
        options#fact_proj_roots.(1)
      with
      | _ -> ""
    in
    let old_version =
      try
        options#fact_versions.(0)
      with
      | _ -> Entity.unknown_version
    in
    let new_version =
      try
        options#fact_versions.(1)
      with
      | _ -> Entity.unknown_version
    in

    let info = DT.compare_trees options old_tree new_tree in
    let modified = info.DT.i_modified in

    if options#viewer_flag then
      List.iter (fun (o, n) -> printf "%s - %s\n" o#fullpath n#fullpath) modified
    else
      printf "cache path: %s\n" info.DT.i_cache_path;

    let stat = SD.empty_diff_stat() in

    if options#recursive_flag then begin

      let fact_store =
        if options#fact_flag then
          let _fact_store =
            new Fact_base.fact_store ~lock:false options info.DT.i_cache_path
          in
          Some _fact_store
        else
          None
      in


      let proc_unmodified (o, n) =
        self#parse_file_and_handle_info ~head:"[unmodified]" fact_store old_proj_root old_version o
          (fun finfo ->
            stat.SD.s_nnodes1          <- stat.SD.s_nnodes1          + finfo.SF.i_nodes;
            stat.SD.s_mapping          <- stat.SD.s_mapping          + finfo.SF.i_nodes;
            stat.SD.s_units            <- stat.SD.s_units            + finfo.SF.i_units;
            stat.SD.s_unmodified_units <- stat.SD.s_unmodified_units + finfo.SF.i_units;
          );
        self#parse_file_and_handle_info ~head:"[unmodified]" fact_store new_proj_root new_version n
          (fun finfo2 ->
            stat.SD.s_nnodes2          <- stat.SD.s_nnodes2          + finfo2.SF.i_nodes;
          )
      in
      let proc_renamed (o, n) =
        self#parse_file_and_handle_info ~head:"[renamed]" fact_store old_proj_root old_version o
          (fun finfo ->
            stat.SD.s_nnodes1          <- stat.SD.s_nnodes1          + finfo.SF.i_nodes;
            stat.SD.s_mapping          <- stat.SD.s_mapping          + finfo.SF.i_nodes;
            stat.SD.s_units            <- stat.SD.s_units            + finfo.SF.i_units;
            stat.SD.s_unmodified_units <- stat.SD.s_unmodified_units + finfo.SF.i_units;
          );
        self#parse_file_and_handle_info ~head:"[renamed]" fact_store new_proj_root new_version n
          (fun finfo2 ->
            stat.SD.s_nnodes2          <- stat.SD.s_nnodes2          + finfo2.SF.i_nodes;
          )
      in
      let proc_moved (o, n) =
        self#parse_file_and_handle_info ~head:"[moved]" fact_store old_proj_root old_version o
          (fun finfo ->
            stat.SD.s_nnodes1          <- stat.SD.s_nnodes1          + finfo.SF.i_nodes;
            stat.SD.s_mapping          <- stat.SD.s_mapping          + finfo.SF.i_nodes;
            stat.SD.s_units            <- stat.SD.s_units            + finfo.SF.i_units;
            stat.SD.s_unmodified_units <- stat.SD.s_unmodified_units + finfo.SF.i_units;
          );
        self#parse_file_and_handle_info ~head:"[moved]" fact_store new_proj_root new_version n
          (fun finfo2 ->
            stat.SD.s_nnodes2          <- stat.SD.s_nnodes2          + finfo2.SF.i_nodes;
          )
      in
      let proc_removed f =
        self#parse_file_and_handle_info ~head:"[removed]" fact_store old_proj_root old_version f
          (fun finfo ->
            stat.SD.s_nnodes1    <- stat.SD.s_nnodes1    + finfo.SF.i_nodes;
            stat.SD.s_deletes    <- stat.SD.s_deletes    + finfo.SF.i_nodes;
            stat.SD.s_deletes_gr <- stat.SD.s_deletes_gr + 1;
            stat.SD.s_units      <- stat.SD.s_units      + finfo.SF.i_units
          )
      in
      let proc_added f =
        self#parse_file_and_handle_info ~head:"[added]" fact_store new_proj_root new_version f
          (fun finfo ->
            stat.SD.s_nnodes2    <- stat.SD.s_nnodes2    + finfo.SF.i_nodes;
            stat.SD.s_inserts    <- stat.SD.s_inserts    + finfo.SF.i_nodes;
            stat.SD.s_inserts_gr <- stat.SD.s_inserts_gr + 1;
            stat.SD.s_units      <- stat.SD.s_units + finfo.SF.i_units
          )
      in
      let proc_copied (_, f2s) = List.iter proc_added f2s in
      let proc_glued (f1s, _) = List.iter proc_removed f1s in

      let proc_modified (o, n) =
        let is_modified = ref true in
        self#verbose_msg "* comparing %s with %s" o#fullpath n#fullpath;
        begin
          let proj_head =
            if options#fact_proj <> "" then
              "["^options#fact_proj^"]"
            else
              ""
          in
          try
            let cache_path = self#get_cache_path2 o n in
            let stat_paths = self#search_cache_for_stat cache_path in
            let dstat =
              if stat_paths <> [] && (not options#clear_cache_flag) then begin
                self#verbose_msg "cache found. skipping...";
                SF.scan_diff_stat ~max_retry_count:options#max_retry_count
                  stat_paths
              end
              else
                self#compare_files ~cache_path o n
            in
            is_modified := dstat.SF.s_total_changes > 0;
            if dstat.SF.s_total_changes < 0 then
              Xprint.warning ~head:"[modified]" "dummy diff info found: %s - %s" o#fullpath n#fullpath;

            self#update_stat stat dstat

          with
          | Failure msg                 -> Xprint.warning ~head:(proj_head^"[FAILURE]") "%s" msg
          | Lang_base.Error msg         -> Xprint.warning ~head:(proj_head^"[LANG]") "%s" msg
          | Lang_base.Parse_error(head, msg) -> Xprint.warning ~head:(proj_head^head) "%s" msg
          | S.Stat_not_found ->
              Xprint.warning ~head:(proj_head^"[modified]") "cache not found: %s - %s" o#fullpath n#fullpath

          | S.Malformed_stat path ->
              Xprint.warning ~head:(proj_head^"[modified]") "malformed cache: %s" path

          | Astml.External_parser_not_found pname ->
              Xprint.warning ~head:(proj_head^"[modified]") "external parser not found: %s" pname
(*
          | A.No_differences_found ->
              Xprint.warning "no differences found";
              proc_unmodified (o, n);
              is_modified := false
*)
        end;
(*            Gc.print_stat stdout *)
        !is_modified
      in

      self#verbose_msg "GATHERING FILE INFO...";

      self#verbose_msg "scanning unmodified files...";
      if not options#ignore_unmodified_flag then
        List.iter proc_unmodified info.DT.i_unmodified;

      self#verbose_msg "scanning renamed files...";
      List.iter proc_renamed info.DT.i_renamed;

      self#verbose_msg "scanning moved files...";
      List.iter proc_moved info.DT.i_moved;

      self#verbose_msg "scanning removed files...";
      List.iter proc_removed info.DT.i_removed;

      self#verbose_msg "scanning added files...";
      List.iter proc_added info.DT.i_added;

      self#verbose_msg "scanning copied files...";
      List.iter proc_copied info.DT.i_copied;

      self#verbose_msg "scanning glued files...";
      List.iter proc_glued info.DT.i_glued;

      self#verbose_msg "COMPUTING DIFFS FOR MODIFIED FILES...";
      let extra_unmodified = ref [] in
      printf "comparing files...\n";
      let total = List.length modified in
      List.iteri
        (fun i p ->
          begin
            try
              if not (proc_modified p) then
                extra_unmodified := p :: !extra_unmodified
            with
              Skip _ -> ()
          end;
          printf " %d/%d (%.2f%%)\r%!" i total ((float (100*i))/.(float total))
        ) modified;

      (* extra source files *)
      let extra_modified, extra_extra_unmodified =

        let extra1 = self#extra_source_files1 in
        let extra2 = self#extra_source_files2 in

        begin %debug_block
          List.iter (fun f -> [%debug_log "extra1: \"%s\"" f#path]) extra1;
          List.iter (fun f -> [%debug_log "extra2: \"%s\"" f#path]) extra2
        end;

        let dtbl1 = Hashtbl.create 0 in
        let dtbl2 = Hashtbl.create 0 in

        let add tbl k v =
          try
            let l = Hashtbl.find tbl k in
            Hashtbl.replace tbl k (v::l)
          with
            Not_found -> Hashtbl.add tbl k [v]
        in

        List.iter (fun f1 -> add dtbl1 f1#digest f1) extra1;
        List.iter (fun f2 -> add dtbl2 f2#digest f2) extra2;

        let deleted_cands  = ref [] in
        let inserted_cands = ref [] in

        let modified   = ref [] in
        let unmodified = ref [] in
        let moved      = ref [] in
        let renamed    = ref [] in
        let copied     = ref [] in
        let glued      = ref [] in

        Hashtbl.iter
          (fun d l1 ->
            try
              let l2 = Hashtbl.find dtbl2 d in

              match l1, l2 with
              | [f1], [f2] ->
                  if f1#path = f2#path then
                    unmodified := (f1, f2) :: !unmodified
                  else if f1#dirname = f2#dirname then
                    renamed := (f1, f2) :: !renamed
                  else if f1#basename = f2#basename then
                    moved := (f1, f2) :: !moved

              | [f1], f2s ->
                  assert (f2s <> []);
                  let p1 = f1#path in
                  let c =
                    List.fold_left
                      (fun l f2 ->
                        if f2#path = p1 then begin
                          unmodified := (f1, f2) :: !unmodified;
                          l
                        end
                        else
                          f2 :: l
                      ) [] f2s
                  in
                  copied := (f1, c) :: !copied

              | f1s, [f2] ->
                  assert (f1s <> []);
                  let p2 = f2#path in
                  let g =
                    List.fold_left
                      (fun l f1 ->
                        if f1#path = p2 then begin
                          unmodified := (f1, f2) :: !unmodified;
                          l
                        end
                        else
                          f1 :: l
                      ) [] f1s
                  in
                  glued := (g, f2) :: !glued

              | f1s, f2s ->
                  assert (f1s <> [] && f2s <> []);

                  let um1 = ref [] in
                  let um2 = ref [] in

                  let ptbl2 = Hashtbl.create 0 in
                  List.iter (fun f2 -> Hashtbl.replace ptbl2 f2#path f2) f2s;

                  let f1s' =
                    List.fold_left
                      (fun l f1 ->
                        try
                          let p1 = f1#path in
                          let f2 = Hashtbl.find ptbl2 p1 in
                          unmodified := (f1, f2) :: !unmodified;
                          um1 := f1 :: !um1;
                          um2 := f2 :: !um2;
                          Hashtbl.remove ptbl2 p1;
                          l
                        with
                          Not_found -> f1 :: l
                      ) [] f1s
                  in
                  let f2s' = Hashtbl.fold (fun _ f2 l -> f2::l) ptbl2 [] in

                  match f1s', f2s' with
                  | [], [] -> ()
                  | [f1], [f2] -> begin
                      if f1#basename = f2#basename then
                        moved := (f1, f2) :: !moved
                      else if f1#dirname = f2#dirname then
                        renamed := (f1, f2) :: !renamed
                  end
                  | f1s, [] -> begin
                      match !um2 with
                      | f2::_ -> glued := (f1s, f2) :: !glued
                      | [] -> assert false
                  end
                  | [], f2s -> begin
                      match !um1 with
                      | f1::_ -> copied := (f1, f2s) :: !copied
                      | [] -> assert false
                  end
                  | f1s, f2s ->
                      let dntbl1 = Hashtbl.create 0 in
                      let dntbl2 = Hashtbl.create 0 in
                      List.iter (fun f1 -> add dntbl1 f1#dirname f1) f1s;
                      List.iter (fun f2 -> add dntbl2 f2#dirname f2) f2s;

                      let rn1 = ref [] in
                      let rn2 = ref [] in

                      let rec balance = function
                        | [], [] -> ()
                        | [], l2 -> begin
                            match !rn1 with
                            | f1::_ -> copied := (f1, l2) :: !copied
                            | [] -> assert false
                        end
                        | l1, [] -> begin
                            match !rn2 with
                            | f2::_ -> glued := (l1, f2) :: !glued
                            | [] -> assert false
                        end
                        | h1::t1, h2::t2 ->
                            renamed := (h1, h2) :: !renamed;
                            rn1 := h1 :: !rn1;
                            rn2 := h2 :: !rn2;
                            balance (t1, t2)
                      in

                      let f1s'' =
                        Hashtbl.fold
                          (fun dn f1s' l ->
                            try
                              let f2s' = Hashtbl.find dntbl2 dn in
                              balance (f1s', f2s');
                              Hashtbl.remove dntbl2 dn;
                              l
                            with
                              Not_found -> f1s' @ l
                          ) dntbl1 []
                      in
                      let f2s'' = Hashtbl.fold (fun _ f2s l -> f2s @ l) dntbl2 [] in

                      let mv1 = ref [] in
                      let mv2 = ref [] in

                      let um1rn1 = !um1 @ !rn1 in
                      let um2rn2 = !um2 @ !rn2 in

                      let rec balance = function
                        | [], [] -> ()
                        | [], l2 -> begin
                            match um1rn1 @ !mv1 with
                            | f1::_ -> copied := (f1, l2) :: !copied
                            | [] -> assert false
                        end
                        | l1, [] -> begin
                            match um2rn2 @ !mv2 with
                            | f2::_ -> glued := (l1, f2) :: !glued
                            | [] -> assert false
                        end
                        | h1::t1, h2::t2 ->
                            moved := (h1, h2) :: !moved;
                            mv1 := h1 :: !mv1;
                            mv2 := h2 :: !mv2;
                            balance (t1, t2)
                      in
                      balance (f1s'', f2s'')

            with
              Not_found -> deleted_cands := l1 @ !deleted_cands
          ) dtbl1;

        Hashtbl.iter
          (fun d l2 ->
            if not (Hashtbl.mem dtbl1 d) then
              inserted_cands := l2 @ !inserted_cands
          ) dtbl2;

        let ptbl1 = Hashtbl.create 0 in
        let ptbl2 = Hashtbl.create 0 in

        List.iter (fun f1 -> Hashtbl.replace ptbl1 f1#path f1) !deleted_cands;
        List.iter (fun f2 -> Hashtbl.replace ptbl2 f2#path f2) !inserted_cands;

        let deleted =
          Hashtbl.fold
            (fun p f1 l ->
              try
                let f2 = Hashtbl.find ptbl2 p in
                modified := (f1, f2) :: !modified;
                Hashtbl.remove ptbl2 p;
                l
              with
                Not_found -> f1::l
            ) ptbl1 []
        in
        let inserted = Hashtbl.fold (fun _ f2 l -> f2::l) ptbl2 [] in

        self#verbose_msg "EXTRA GATHERING FILE INFO...";

        self#verbose_msg "scanning extra unmodified files...";
        if not options#ignore_unmodified_flag then
          List.iter proc_unmodified !unmodified;

        self#verbose_msg "scanning extra renamed files...";
        List.iter proc_renamed !renamed;

        self#verbose_msg "scanning extra moved files...";
        List.iter proc_moved !moved;

        self#verbose_msg "scanning extra removed files...";
        List.iter proc_removed deleted;

        self#verbose_msg "scanning extra added files...";
        List.iter proc_added inserted;

        self#verbose_msg "scanning extra copied files...";
        List.iter proc_copied !copied;

        self#verbose_msg "scanning extra glued files...";
        List.iter proc_glued !glued;

        self#verbose_msg "COMPUTING DIFFS FOR EXTRA MODIFIED FILES...";
        let extra_unmodified = ref [] in
        List.iter
          (fun p ->
            try
              if not (proc_modified p) then
                extra_unmodified := p :: !extra_unmodified
            with
              Skip _ -> ()
          ) !modified;

        (Xlist.subtract !modified !extra_unmodified),
        (!unmodified @ !extra_unmodified)

      in (* let extra_modified, extra_extra_unmodified *)

      begin %debug_block
        List.iter (fun (f1, _) -> [%debug_log "extra_modified: \"%s\"" f1#path]) extra_modified;
        List.iter (fun (f1, _) -> [%debug_log "extra_unmodified: \"%s\"" f1#path]) !extra_unmodified;
        List.iter (fun (f1, _) -> [%debug_log "extra_extra_unmodified: \"%s\"" f1#path]) extra_extra_unmodified
      end;

      info.DT.i_modified   <- (Xlist.subtract info.DT.i_modified !extra_unmodified) @ extra_modified;
      info.DT.i_unmodified <- info.DT.i_unmodified @ !extra_unmodified @ extra_extra_unmodified;

      SD.dump_diff_stat info.DT.i_cache_path stat;

      SD.show_diff_stat ~short:true stat;

      begin
        match fact_store with
        | Some _fact_store -> _fact_store#close
        | None -> ()
      end;

    end; (* if options#recursive_flag *)


    DT.save_extra_result options info;

    if not options#ignore_unmodified_flag then
      List.iter
        (fun (dt, nnodes) ->
          self#_dump_dir_info (DT.get_cache_path1 options dt) dt nnodes
        ) [(info.DT.i_dtree1,stat.SD.s_nnodes1);(info.DT.i_dtree2,stat.SD.s_nnodes2)]


  method update_stat stat s =
    stat.SD.s_nnodes1     <- stat.SD.s_nnodes1     + s.SF.s_nnodes1;
    stat.SD.s_nnodes2     <- stat.SD.s_nnodes2     + s.SF.s_nnodes2;
    stat.SD.s_deletes     <- stat.SD.s_deletes     + s.SF.s_deletes;
    stat.SD.s_deletes_gr  <- stat.SD.s_deletes_gr  + s.SF.s_deletes_gr;
    stat.SD.s_inserts     <- stat.SD.s_inserts     + s.SF.s_inserts;
    stat.SD.s_inserts_gr  <- stat.SD.s_inserts_gr  + s.SF.s_inserts_gr;
    stat.SD.s_relabels    <- stat.SD.s_relabels    + s.SF.s_relabels;
    stat.SD.s_relabels_gr <- stat.SD.s_relabels_gr + s.SF.s_relabels_gr;
    stat.SD.s_movrels     <- stat.SD.s_movrels     + s.SF.s_movrels;
    stat.SD.s_moves       <- stat.SD.s_moves       + s.SF.s_moves;
    stat.SD.s_moves_gr    <- stat.SD.s_moves_gr    + s.SF.s_moves_gr;
    stat.SD.s_mapping     <- stat.SD.s_mapping     + s.SF.s_mapping;
    stat.SD.s_units       <- stat.SD.s_units       + s.SF.s_units;
    stat.SD.s_unmodified_units <- stat.SD.s_unmodified_units + s.SF.s_unmodified_units;


  method patch_file ?(fail_on_error=true) ?(reverse=false) file delta ch =
    [%debug_log "patching \"%s\" with \"%s\"" file#fullpath delta];
    let ext = file#get_extension in
    let lang = Lang.search options ext in
    let tree_patcher = lang#make_tree_patcher options in
    try
      tree_patcher#patch ~fail_on_error ~reverse file delta ch
    with
      Delta_base.Invalid_delta err ->
        Xprint.error
          "[%s %dL,%dC] invalid delta: %s" err.file err.line err.col err.reason

  method patch_dir ?(fail_on_error=true) (dir : Storage.file) bundle =
    let _ = dir in
    [%debug_log "patching \"%s\" with \"%s\"" dir#fullpath bundle];

    let loc_delta_list =
      Delta_base.parse_bundle_file options (new XML.ns_manager) bundle
    in
    let dir_delta_list = ref [] in

    List.iter
      (fun (loc, delta) ->
        [%debug_log "loc=\"%s\"" loc];

        if loc = "" then begin
          (* defer dir patches for resolving the name of the public class in a removed file *)
          dir_delta_list := delta :: !dir_delta_list;
        end
        else begin
          let paths = get_paths loc in

          List.iter
            (fun path ->
              let file =
                new Storage.file (Storage.Tree (Fs.make options ~path:options#root_path ())) path
              in
              let ext = file#get_extension in
              let lang = Lang.search options ext in
              let tree_patcher = lang#make_tree_patcher options in

              self#verbose_msg "patching \"%s\"..." file#fullpath;

              let dumper =
                tree_patcher#_patch ~fail_on_error ~reverse:false file delta false
              in

              let temp = Filename.temp_file "patchast_" "" in

              let pch = Stdlib.open_out temp in
              let ch = OC.of_pervasives pch in

              let apath = file#fullpath in

              try
                dumper ch;

                OC.close ch;

                if not options#nobackup_flag then
                  Sys.rename apath (apath^".orig");

                Xfile.copy_file temp apath;
                Sys.remove temp

              with
              | Delta_format.Skip -> ()
              | exn ->
                  Xprint.error "failed to patch \"%s\"" apath;
                  OC.close ch;
                  Xfile.copy_file temp (apath^".error");
                  raise exn

            ) paths
        end

      ) loc_delta_list;

    List.iter (* deferred dir patches *)
      (fun delta ->
        self#verbose_msg "patching directory...";
        Delta_base.interpret_dir_delta options delta
      ) !dir_delta_list


end (* of class Diffastcore.c *)
]
