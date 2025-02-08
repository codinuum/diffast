(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>
   Copyright 2020-2025 Chiba Institute of Technology

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

(* Author: Masatomo Hashimoto <m.hashimoto@stair.center> *)

module Storage = Diffast_misc.Storage
module Parserlib_base = Langs_common.Parserlib_base

module Aux = Parser_aux
module PB = Parserlib_base
module C = Context

exception Failed_to_parse of Lexing.position

(*type mode = M_NORMAL | M_STMTS*)

class parser_c : object
  method _parse : Ast.c
  method _set_keep_going_flag : bool -> unit
  method _set_verbose_flag : bool -> unit
  method add_search_path : string -> unit
  method clear_keep_going_flag : unit
  method clear_verbose_flag : unit
  method extra_source_files : Storage.file list
  method lines_read : int
  method make_source : Storage.file -> Source.c
  method make_source_stdin : Source.c
  method parse_file : Storage.file -> Ast.c
  method parse_stdin : Ast.c
  method parser_init : unit
  method set_token_hist_flag : unit -> unit
  method set_dump_tokens_flag : unit -> unit
  method set_dump_stats_flag : unit -> unit
  method set_keep_going_flag : unit
  method set_search_path_list : string list -> unit
  method set_verbose_flag : unit
  method clear_parse_macro_defs_flag : unit -> unit
  method stmts_mode : unit -> unit
  method tokens_read : int
end
