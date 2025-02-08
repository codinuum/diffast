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

module Xprint = Diffast_misc.Xprint
module Basic_options = Diffast_misc.Basic_options
module Fs = Diffast_misc.Fs
module Parserlib_base = Langs_common.Parserlib_base
module Ast = Cpp_parsing.Ast
module Parser_aux = Cpp_parsing.Parser_aux
module Lib = Cpp_parsing.Lib

module Aux = Parser_aux

let filename_list = ref []

let dump_ast_flag = ref false
let dump_tokens_flag = ref false
let dump_stats_flag = ref false
let verbose_flag = ref true
let token_hist_flag = ref false
let parse_macro_defs_flag = ref true
let keep_going_flag = ref false

let set_flags p =
  if !verbose_flag then
    p#set_verbose_flag;
  if !token_hist_flag then
    p#set_token_hist_flag();
  if not !parse_macro_defs_flag then
    p#clear_parse_macro_defs_flag();
  if !dump_tokens_flag then
    p#set_dump_tokens_flag();
  p#_set_keep_going_flag !keep_going_flag;
  if !dump_stats_flag then
    p#set_dump_stats_flag()

let options = new Basic_options.c

let _ =
  Arg.parse
    [
     (*"-verbose", Arg.Unit (fun () -> verbose_flag := true), "\tdisplay verbose messages";*)
     "-dump-ast", Arg.Unit (fun () -> dump_ast_flag := true), "\tdump AST(s)";
     "-dump-tokens", Arg.Unit (fun () -> dump_tokens_flag := true), "\tdump token seq(s)";
     "-dump-stats", Arg.Unit (fun () -> dump_stats_flag := true), "\tdump stats";
     "-k", Arg.Unit (fun () -> keep_going_flag := true), "\tparse despite errors";
     "-token-hist", Arg.Unit (fun () -> token_hist_flag := true), "\tshow token histogram";
     "-ignore-macro-defs",
     Arg.Unit (fun () -> parse_macro_defs_flag := false), "ignore macro defs"
    ]
    (fun s -> filename_list := s :: !filename_list)
    ("usage: " ^ Filename.basename (Sys.argv.(0))
     ^ " [OPTIONS] [FILE..]\noptions are:")

let proc filename =
  try
    let parser0 = new Lib.parser_c in
    set_flags parser0;
    let file = Fs.file_of_path options filename in
    let ast = parser0#parse_file file in
    if !dump_ast_flag then
      Ast.dump ast
  with
  | Sys_error msg -> begin
      Xprint.error ~out:stdout "%s" msg;
      exit 1
  end
  | Parserlib_base.Parse_error(head, msg) -> begin
      Xprint.error ~out:stdout ~head "%s" msg;
      exit 1
  end
(*  | Internal_error msg -> Xprint.error ~out:stdout ~head:"[INTERNAL]" "%s" msg*)
(*  | exn -> begin
      Xprint.error "%s" (Printexc.to_string exn);
      exit 1
  end*)

let _ =
  List.iter proc (List.rev !filename_list)
