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
(* stat.ml *)

module Xfile = Diffast_misc.Xfile
module Xprint = Diffast_misc.Xprint
module C = Diffast_misc.Compression

let printf  = Printf.printf
let fprintf = Printf.fprintf
let sprintf = Printf.sprintf

let fact_file_name = "fact.nt"

let diff_file_name    = "diff"
let info_file_name    = "info"
let summary_file_name = "summary"
let map_file_name     = "map"
let stat_file_name    = "stat"
let sources_file_name = "sources"
let source_file_name  = "source"
let changes_file_name = "changes"
let dot_file_name1    = "old.dot"
let dot_file_name2    = "new.dot"
let parser_file_name  = "parser"




exception Stat_not_found
exception Malformed_stat of string

let fscanf ic =
  let ib = Scanf.Scanning.from_channel ic in
  Scanf.bscanf ib


let scan ?(max_retry_count=10) scanner path =
  let rec _scan n path (scanner : in_channel -> 'a) =
    try
      let ch = open_in path in
      try
        let res = scanner ch in
        begin
          try
            close_in ch
          with
            Sys_error s -> let _ = s in [%warn_log "%s" s]
        end;
        res
      with
      | Scanf.Scan_failure _
      | Failure _
      | End_of_file
      | Invalid_argument _ ->
          (try
            close_in ch;
          with _ -> ());
          raise (Malformed_stat path)
    with
    | Sys_error (*s*)_ -> (*[%warn_log "%s" s]; *)raise Stat_not_found
    | Malformed_stat _ ->
        if n > max_retry_count then
          raise Stat_not_found
        else begin
          Xprint.warning "malformed cache \"%s\": retrying...(%d)" path n;
          Unix.sleep 1;
          _scan (n+1) path scanner
        end
  in
  let x = _scan 1 path scanner in
  x

let scan_paths ?(max_retry_count=10) scanner paths =
  let scan_path = scan ~max_retry_count:1 scanner in
  let rec doit count ps =
    if count < 0 then
      raise Stat_not_found
    else
      match ps with
      | [] -> raise Stat_not_found
      | [x] -> begin
          try
            scan_path x.Cache.sr_path
          with
            _ ->
              Unix.sleep 1;
              doit (count-1) ps
      end
      | x::xs -> begin
          try
            scan_path x.Cache.sr_path
          with
            _ ->
              Unix.sleep 1;
              doit (count-1) xs
      end
  in
  doit max_retry_count paths



module File = struct

  type diff_stat = { s_nnodes1          : int;
                     s_nnodes2          : int;
                     s_deletes          : int; s_deletes_gr  : int;
                     s_inserts          : int; s_inserts_gr  : int;
                     s_relabels         : int; s_relabels_orig : int; s_relabels_gr : int;
                     s_movrels          : int; s_movrels_orig : int;
                     s_moves            : int; s_moves_gr    : int;
                     s_mapping          : int;
                     s_units            : int;
                     s_unmodified_units : int;
                     s_total_changes    : int;
                     s_similarity       : string;
                     s_change_ratio     : string;
                     s_unmodified_rate  : string;
                     s_SPSM             : int;
                     s_SPM              : int;
                     s_MGSM             : int;
                     s_MGM              : int;
                     s_AHS              : string;
                   }

  let make_empty_diff_stat() = { s_nnodes1  = 0;
                                 s_nnodes2  = 0;
                                 s_deletes  = 0; s_deletes_gr  = 0;
                                 s_inserts  = 0; s_inserts_gr  = 0;
                                 s_relabels = 0; s_relabels_orig = 0; s_relabels_gr = 0;
                                 s_movrels  = 0; s_movrels_orig = 0;
                                 s_moves    = 0; s_moves_gr    = 0;
                                 s_mapping  = 0;
                                 s_units    = 0;
                                 s_unmodified_units = 0;
                                 s_total_changes    = 0;
                                 s_similarity       = "0.0";
                                 s_change_ratio     = "0.0";
                                 s_unmodified_rate  = "1.0";
                                 s_SPSM = 0;
                                 s_SPM  = 0;
                                 s_MGSM = 0;
                                 s_MGM  = 0;
                                 s_AHS  = "0.0";
                               }


  let make_diff_stat
      ?(mapping=0)
      ?(units=0)
      ?(unmodified_units=0)
      ()
      = { s_nnodes1  = 0;
          s_nnodes2  = 0;
          s_deletes  = 0; s_deletes_gr  = 0;
          s_inserts  = 0; s_inserts_gr  = 0;
          s_relabels = 0; s_relabels_orig = 0; s_relabels_gr = 0;
          s_movrels  = 0; s_movrels_orig = 0;
          s_moves    = 0; s_moves_gr    = 0;
          s_mapping  = mapping;
          s_units    = units;
          s_unmodified_units = unmodified_units;
          s_total_changes    = 0;
          s_similarity       = "0.0";
          s_change_ratio     = "0.0";
          s_unmodified_rate  = "1.0";
          s_SPSM = 0;
          s_SPM  = 0;
          s_MGSM = 0;
          s_MGM  = 0;
          s_AHS  = "0.0";
        }


  let diff_stat_fmt () =
    "nnodes1 : %d\n" ^^
    "nnodes2 : %d\n\n" ^^
    "deletes(hunks) : %d(%d)\n" ^^
    "inserts(hunks) : %d(%d)\n" ^^
    "relabels : %d(orig:%d)(%d)\n" ^^
    "mov+rels : %d(orig:%d)\n" ^^
    "moves(hunks) : %d(%d)\n\n" ^^
    "total changes : %d\n" ^^
    "mapping size  : %d\n" ^^
    "similarity    : %s\n" ^^
    "CMR           : %s\n\n" ^^
    "units (old)      : %d\n" ^^
    "unmodified units : %d\n" ^^
    "UNMODIFIED RATE  : %s\n\n" ^^
    "SPSM : %d\n" ^^
    "SPM  : %d\n" ^^
    "MGSM : %d\n" ^^
    "MGM  : %d\n" ^^
    "AHS  : %s\n"

  let diff_stat_short_fmt () =
    "nodes : %d -> %d\n" ^^
    "deletes(hunks) : %d(%d)\n" ^^
    "inserts(hunks) : %d(%d)\n" ^^
    "relabels : %d (orig:%d)\n" ^^
    "mov+rels : %d (orig:%d)\n" ^^
    "moves(hunks) : %d(%d)\n" ^^
    "total changes : %d\n" ^^
    "mapping size  : %d\n" ^^
    "similarity    : %s\n"

  let diff_stat_json_fmt () =
    "{" ^^
    "\"nnodes1\":%d,\"nnodes2\":%d," ^^
    "\"deletes\":%d,\"delete_groups\":%d," ^^
    "\"inserts\":%d,\"insert_groups\":%d," ^^
    "\"relabels\":%d,\"orig_relabels\":%d," ^^
    "\"move+relabels\":%d,\"orig_move+relabels\":%d," ^^
    "\"moves\":%d,\"move_groups\":%d," ^^
    "\"edit_cost\":%d," ^^
    "\"nmappings\":%d," ^^
    "\"similarity\":%s" ^^
    "}"

  let dump_diff_stat_json_ch s ch =
    fprintf ch (diff_stat_json_fmt())
      s.s_nnodes1 s.s_nnodes2
      s.s_deletes s.s_deletes_gr
      s.s_inserts s.s_inserts_gr
      s.s_relabels s.s_relabels_orig
      s.s_movrels s.s_movrels_orig
      s.s_moves s.s_moves_gr
      s.s_total_changes
      s.s_mapping
      s.s_similarity

  let dump_diff_stat_ch ?(short=false) s ch =
    if short then
      fprintf ch (diff_stat_short_fmt())
        s.s_nnodes1 s.s_nnodes2
        s.s_deletes s.s_deletes_gr
        s.s_inserts s.s_inserts_gr
        s.s_relabels s.s_relabels_orig(*s.s_relabels_gr*)
        s.s_movrels s.s_movrels_orig
        s.s_moves s.s_moves_gr
        s.s_total_changes
        s.s_mapping
        s.s_similarity
    else
      fprintf ch (diff_stat_fmt())
        s.s_nnodes1 s.s_nnodes2
        s.s_deletes s.s_deletes_gr
        s.s_inserts s.s_inserts_gr
        s.s_relabels s.s_relabels_orig s.s_relabels_gr
        s.s_movrels s.s_movrels_orig
        s.s_moves s.s_moves_gr
        s.s_total_changes
        s.s_mapping
        s.s_similarity
        s.s_change_ratio
        s.s_units
        s.s_unmodified_units
        s.s_unmodified_rate
        s.s_SPSM
        s.s_SPM
        s.s_MGSM
        s.s_MGM
        s.s_AHS

  let dump_diff_stat_json fname s =
    Xfile.dump fname (dump_diff_stat_json_ch s)

  let dump_diff_stat fname s =
    Xfile.dump fname (dump_diff_stat_ch s)

  let dump_sim_ch s ch = fprintf ch "%s\n" s.s_similarity

  type info = {
      i_nodes      : int;
      i_units      : int;
      i_LOC        : int;
      i_missed_LOC : int;
    }

  let dummy_info = {
    i_nodes      = 0;
    i_units      = 0;
    i_LOC        = 0;
    i_missed_LOC = 0;
  }

  let info_fmt () =
    "nodes: %d\n" ^^
    "units: %d\n" ^^
    "LOC: %d\n" ^^
    "missed LOC: %d\n"


  let mkinfo n u l m =
    { i_nodes      = n;
      i_units      = u;
      i_LOC        = l;
      i_missed_LOC = m;
    }

  let dump_info_ch info ch =
    let fmt = info_fmt() in
    fprintf ch fmt info.i_nodes info.i_units info.i_LOC info.i_missed_LOC

  let show_info info = dump_info_ch info stdout

  let get_tree_info tree =
    let units = tree#get_units_to_be_notified in
    mkinfo tree#initial_size (List.length units) tree#total_LOC tree#misparsed_LOC

  let dump_info cache_path tree =
    let path = Filename.concat cache_path info_file_name in
    let info = get_tree_info tree in
    Xfile.dump path (dump_info_ch info)


  let scan_diff_stat ?(max_retry_count=10) paths =
    scan_paths ~max_retry_count
      (fun ch ->
        fscanf ch (diff_stat_fmt())
          (fun n1 n2 d dg i ig r ro rg rm rmo m mg tc map sim cr u uu ur spsm mgsm spm mgm ahs ->
            { s_nnodes1  = n1; s_nnodes2     = n2;
              s_deletes  = d;  s_deletes_gr  = dg;
              s_inserts  = i;  s_inserts_gr  = ig;
              s_relabels = r;  s_relabels_orig = ro; s_relabels_gr = rg;
              s_movrels  = rm; s_movrels_orig = rmo;
              s_moves    = m;  s_moves_gr    = mg;
              s_mapping          = map;
              s_units            = u;
              s_unmodified_units = uu;
              s_total_changes    = tc;
              s_similarity       = sim;
              s_change_ratio     = cr;
              s_unmodified_rate  = ur;
              s_SPSM = spsm;
              s_SPM  = spm;
              s_MGSM = mgsm;
              s_MGM  = mgm;
              s_AHS  = ahs;
            }
          )
      ) paths


  let scan_info paths =
    scan_paths
      (fun ch ->
        fscanf ch (info_fmt())
          (fun nnodes nunits tloc mloc ->
            { i_nodes      = nnodes;
              i_units      = nunits;
              i_LOC        = tloc;
              i_missed_LOC = mloc;
            }
          )
      ) paths


end (* module Stat.File *)



module Dir = struct

  type diff_stat = { mutable s_deletes          : int; mutable s_deletes_gr  : int;
                     mutable s_inserts          : int; mutable s_inserts_gr  : int;
                     mutable s_relabels         : int; mutable s_relabels_gr : int;
                     mutable s_movrels          : int;
                     mutable s_moves            : int; mutable s_moves_gr    : int;
                     mutable s_mapping          : int;
                     mutable s_units            : int;
                     mutable s_unmodified_units : int;
                     mutable s_nnodes1 : int;
                     mutable s_nnodes2 : int;
                   }

  let empty_diff_stat() = { s_deletes  = 0; s_deletes_gr  = 0;
                            s_inserts  = 0; s_inserts_gr  = 0;
                            s_relabels = 0; s_relabels_gr = 0;
                            s_movrels  = 0;
                            s_moves    = 0; s_moves_gr    = 0;
                            s_mapping  = 0;
                            s_units    = 0;
                            s_unmodified_units = 0;
                            s_nnodes1 = 0;
                            s_nnodes2 = 0;
                          }

  let diff_stat_short_fmt () =
    "nodes : %d -> %d\n" ^^
    "deletes(hunks) : %d(%d)\n" ^^
    "inserts(hunks) : %d(%d)\n" ^^
    "relabels : %d\n" ^^
    "mov+rels : %d\n" ^^
    "moves(hunks) : %d(%d)\n" ^^
    "total changes : %d\n" ^^
    "mapping size  : %d\n" ^^
    "similarity    : %s\n"

  let dump_diff_stat_ch ?(short=false) s ch =
    let total = s.s_deletes + s.s_inserts + s.s_relabels + s.s_moves_gr in
    let sim =
      if total = 0 then
        "1.0"
      else
        let spm = s.s_mapping - s.s_moves - s.s_relabels + s.s_movrels in
        let _sim = float (spm * 2) /. float (s.s_nnodes1 + s.s_nnodes2) in
        sprintf "%.6f" _sim
    in
    if short then
      fprintf ch (diff_stat_short_fmt())
        s.s_nnodes1 s.s_nnodes2
        s.s_deletes s.s_deletes_gr
        s.s_inserts s.s_inserts_gr
        s.s_relabels
        s.s_movrels
        s.s_moves s.s_moves_gr
        total
        s.s_mapping
        sim
    else begin
      fprintf ch "nnodes1: %d\n" s.s_nnodes1;
      fprintf ch "nnodes2: %d\n" s.s_nnodes2;
      fprintf ch "deletes  : %d(%d)\n" s.s_deletes s.s_deletes_gr;
      fprintf ch "inserts  : %d(%d)\n" s.s_inserts s.s_inserts_gr;
      fprintf ch "relabels : %d(%d)\n" s.s_relabels s.s_relabels_gr;
      fprintf ch "movrels  : %d\n" s.s_movrels;
      fprintf ch "moves    : %d(%d)\n\n" s.s_moves s.s_moves_gr;
      fprintf ch "total changes : %d\n" total;
      fprintf ch "mapping size  : %d\n" s.s_mapping;
      fprintf ch "similarity    : %s\n" sim;
      fprintf ch "CMR           : %.6f\n\n"
        ((float_of_int total) /. (float_of_int s.s_mapping));
      fprintf ch "units (old)      : %d\n" s.s_units;
      fprintf ch "unmodified units : %d\n" s.s_unmodified_units;
      fprintf ch "UNMODIFIED RATE  : %.6f\n\n"
        ((float_of_int s.s_unmodified_units) /. (float_of_int s.s_units));
      fprintf ch "SPSM : %d\n" (s.s_mapping - s.s_relabels - s.s_moves + s.s_movrels);
      fprintf ch "SPM  : %d\n" (s.s_mapping - s.s_moves);
      fprintf ch "AHS  : %.6f\n"
        ((float_of_int (s.s_deletes + s.s_inserts + s.s_moves))
           /. (float_of_int (s.s_deletes_gr + s.s_inserts_gr + s.s_moves_gr)))
    end

  let show_diff_stat ?(short=false) stat =
    dump_diff_stat_ch ~short stat stdout

  let dump_diff_stat cache_dir stat =
    let path = Filename.concat cache_dir stat_file_name in
    Xfile.dump path (dump_diff_stat_ch stat)


  let info_fmt () =
    "%s\n" ^^
    "nodes:        %d\n" ^^
    "source files: %d\n" ^^
    "AST nodes:    %d\n"

  let dump_info_ch dtree ast_nodes ch =
    let fmt = info_fmt() in
    fprintf ch fmt
      dtree#id
      dtree#initial_size
      (List.length dtree#get_whole_initial_leaves)
      ast_nodes


end (* module Stat.Dir *)


let _get_vkey vkind ver =
  if not (Entity.vkind_is_unknown vkind) && ver <> "" then
    Entity.mkvkey vkind ver
  else
    ""

let get_vkey tree = _get_vkey tree#vkind tree#version

let dump_source_path_ch p ch =
  Printf.fprintf ch "%s\n" p

let _dump_source_path cache_path (k, v) spath =
  let vkey = _get_vkey k v in
  let a = if vkey = "" then "" else "."^vkey in
  let path = (Filename.concat cache_path source_file_name)^a in
  Xfile.dump path (dump_source_path_ch spath)

let dump_source_ch tree = dump_source_path_ch tree#source_path

let _dump_source cache_path tree =
  _dump_source_path cache_path (tree#vkind, tree#version) tree#source_path

let dump_source options file tree =
  let cache_path = options#get_cache_path_for_file1 file in
  _dump_source cache_path tree

let dump_file_info options file tree =
  let cache_path = options#get_cache_path_for_file1 file in
  File.dump_info cache_path tree

let dump_parser_name_ch pname ch =
  Printf.fprintf ch "%s\n" pname

let dump_parser_name file parser_name =
  Xfile.dump file (dump_parser_name_ch parser_name)

let dump_parser_ch tree = dump_parser_name_ch tree#parser_name

let _dump_parser cache_path tree =
  let path = Filename.concat cache_path parser_file_name in
  Xfile.dump path (dump_parser_ch tree)

let dump_parser options file tree =
  let cache_path = options#get_cache_path_for_file1 file in
  _dump_parser cache_path tree

