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

module Astml = Diffast_core.Astml
module Lang_base = Diffast_core.Lang_base

let parser_name = "astml"

let compressors = Astml.compressors

let decomp ext ifile ofile =
  let ipath = ifile#get_local_file in
  try
    let cmd = Printf.sprintf (List.assoc ext compressors) ipath ofile in
    [%debug_log "uncompressing \"%s\"..." ipath];
    [%debug_log "command=\"%s\"" cmd];
    let _ = Sys.command cmd in
    [%debug_log "done."]
  with
    Not_found ->
      failwith (Printf.sprintf "decomp: unsupported compression: %s" ext)


let extensions = Astml.extensions

let _ = Lang_base.register_spec parser_name extensions

let xparser_name_ccx = "ccx"

let external_parser_specs = [ xparser_name_ccx, [".c"; ".cpp"; ".cc"; ".h"; ".hh"; ".hpp"];
                            ]

let _ =
  Lang_base.register_external_specs parser_name external_parser_specs
