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
 * command line driver for Patch/AST
 *
 * patchast.ml
 *
 *)

module Xfile = Diffast_misc.Xfile
module Xprint = Diffast_misc.Xprint
module Fs = Diffast_misc.Fs
module Spec_base = Diffast_core.Spec_base
module OutChannel = Spec_base.OutChannel
module Options = Diffast_core.Options
module Lang_base = Diffast_core.Lang_base
module Lang = Diffast_core.Lang
module Misc = Diffast_core.Misc
module Diffastapi = Diffast_api.Diffastapi
module Version = Diffast_api.Version


let sprintf = Printf.sprintf


let options = new Options.c

let verbose_msg fmt = Xprint.verbose options#verbose_flag fmt


let usage_msg =
  sprintf "Usage: %s [OPTIONS] FILE DELTA\nOPTIONS:" Xprint.cmd_name

let set_verbose_mode_flag() =
  options#set_verbose_flag

let set_nobackup_flag() =
  options#set_nobackup_flag

let _ = options#set_no_collapse_flag

let show_version_flag = ref false
let reverse_flag = ref false

let outfile_opt = ref None
let set_outfile path =
  outfile_opt := Some path

let filenames = ref []



let speclist =
  [
   "-version", Arg.Set show_version_flag, "\tshow version";

   "-verbose", Arg.Unit set_verbose_mode_flag, "\tdisplay verbose messages";

   "-o", Arg.String set_outfile, "PATH\tset path of patched file";

   "-nobackup", Arg.Unit set_nobackup_flag, "\tdoes not create backup files";

   "-k", Arg.Unit (fun () -> options#set_keep_going_flag), "\tdo not fail on syntax error";

   "-reverse", Arg.Set reverse_flag, "\tapply reversed delta";
 ]

let _ =
  Arg.parse
    speclist
    (fun s -> filenames := s :: !filenames)
    (usage_msg)

let _ =
  if !show_version_flag then begin
    Printf.printf "Patch/AST %s\n%s\n" Version.version Version.copyright;
    exit 0
  end


let delta, file =
  match !filenames with
  | d::f::[] -> d, f
  | _ -> Arg.usage speclist usage_msg; exit 1


let astapi =
  let _ = Lang.setup_options options in
  new Diffastapi.c options


let patch file delta =

  verbose_msg "patching \"%s\" with \"%s\"" file delta;

  let sw = new Misc.stopwatch in

  if options#verbose_flag then
    sw#start;

  let ext = options#get_extension file in

  if options#is_valid_extension ext then begin
    let f = Fs.file_of_path options file in
    let dumper =
      astapi#patch_file
        ~fail_on_error:(not options#keep_going_flag) ~reverse:!reverse_flag f delta
    in

    let temp = Filename.temp_file "patchast_" "" in

    verbose_msg "temp=%s" temp;

    let pch = Stdlib.open_out temp in
    let ch = OutChannel.of_pervasives pch in
    dumper ch;

    OutChannel.close ch;

    begin
      match !outfile_opt with
      | None ->
          if not options#nobackup_flag then
            Sys.rename file (file^".orig");
          Xfile.copy_file temp file
      | Some path -> Xfile.copy_file temp path
    end;

    Sys.remove temp;

    if options#verbose_flag then begin
      sw#stop;
      verbose_msg "execution completed in %f seconds" sw#show;
    end

  end
  else begin
    Xprint.error "invalid extension: \"%s\"" ext
  end


let patch_dir dir bundle =

  verbose_msg "patching \"%s\" with \"%s\"" dir bundle;

  let sw = new Misc.stopwatch in

  if options#verbose_flag then
    sw#start;

  options#set_root_path dir;

  let d = Fs.file_of_path options dir in

  astapi#patch_dir d bundle;

  if options#verbose_flag then begin
    sw#stop;
    verbose_msg "execution completed in %f seconds" sw#show;
  end



(* main routine *)
let _ =
  try
    if Xfile.is_dir file then
      patch_dir file delta
    else
      patch file delta
  with
  | Xfile.No_such_file_or_directory s -> Xprint.error "%s: no such file or directory" s; exit 1
  | Xfile.No_extension f              -> Xprint.error "have no file extension: \"%s\"" f; exit 1
  | Lang_base.Error msg               -> Xprint.error "%s" msg; exit 1
(*  | Failure s                         -> Xprint.error "%s" s; exit 1*)

(*  | e -> Xprint.error ~head:"[EXCEPTION]" "%s" (Printexc.to_string e); exit 1*)
