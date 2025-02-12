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
 * A parser for SystemVerilog
 *
 * main.ml
 *
 *)

module Xfile = Diffast_misc.Xfile
module Basic_options = Diffast_misc.Basic_options
module Fs = Diffast_misc.Fs
module Common = Verilog_parsing.Common
module Printer = Verilog_parsing.Printer
module Parser_aux = Verilog_parsing.Parser_aux
module Lib = Verilog_parsing.Lib

open Common
module Aux = Parser_aux

let compile_mode = ref false
let filename = ref ""
let arg_count = ref 0
let dump_flag = ref false

let read_hint file =
  let _parser = new Lib.parser_c in
  let _ = _parser#parse_file file in
  _parser#macrotbl


let _parser = new Lib.parser_c

let options = new Basic_options.c

let _ =
  Arg.parse
    [
     "-verbose", Arg.Unit (fun () -> _parser#set_verbose_flag), "\tdisplay verbose messages";
     "-I", Arg.String _parser#add_search_path, "PATH\tadd search path";
     "-k", Arg.Unit (fun () -> _parser#set_keep_going_flag), "\tcontinue parsing in spite of errors";
     "-dump", Arg.Unit (fun () -> dump_flag := true), "\tdump AST";
     "-proj-root", Arg.String options#set_root_path, "P\tset project root path to P";
    ]
    (fun s -> incr arg_count; filename := s)
    ("usage: " ^ Filename.basename (Sys.argv.(0))
     ^ " [OPTIONS] [FILE]\noptions are:")

let _ =
  if !arg_count > 1 then begin
    Xprint.error "too many arguments";
    exit 1
  end;

  if !arg_count = 1 then compile_mode := true;
  try
    let macrotbl_opt =
      let path =
        let d =
          Filename.concat
            (Filename.concat
               (Filename.dirname (Filename.dirname (Sys.argv.(0))))
               "etc"
            ) "diffast-langs-verilog-parsing-cli"
        in
        Filename.concat d "standard.v"
      in
      try
        let f = Fs.file_of_path options path in
        Some (read_hint f)
      with
        Xfile.No_such_file_or_directory f -> begin
          Xprint.warning "no such file: \"%s\"" f;
          None
        end
    in
    begin
      match macrotbl_opt with
      | Some tbl -> tbl#set_readonly
      | None -> ()
    end;

    let file = Fs.file_of_path options !filename in

    while true do

      begin
        match macrotbl_opt with
        | Some _ -> _parser#set_predefined_macrotbl macrotbl_opt
        | None -> ()
      end;

      let ast =
	if !compile_mode then
	  _parser#parse_file file
	else
	  _parser#parse_stdin
      in

      if !dump_flag then
	Printer.dump ast#root;

      Printf.printf "*** PARSED! ***\n";

      Printf.printf "AST nodes: %d\n" ast#size;

      _parser#dump_ignored_regions;
      let ignored_LOC = _parser#ignored_LOC in
      if ignored_LOC > 0 then
	Printf.printf "ignored LOC: %d\n" ignored_LOC;

      _parser#dump_missed_regions;
      let missed_LOC = _parser#missed_LOC in
      if missed_LOC > 0 then
	Printf.printf "missed LOC: %d\n" missed_LOC;

      begin %info_block
	Printf.printf "%d lines read\n" _parser#lines_read
      end;

      Printf.printf "\n";

      ignore (exit 0)
    done
  with
  (*| Sys_error msg
  | Failure msg
    ->
      Xprint.error ~out:stdout "%s" msg*)

  | Parse_error(head, msg) -> Xprint.error ~out:stdout ~head "%s" msg
