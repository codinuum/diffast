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
(* parserlib_base.ml *)

[%%prepare_logger]

module Storage = Diffast_misc.Storage


let cmd_name = Filename.basename(Sys.argv.(0))

exception Parse_error of string * string



type 'rawtoken token = 'rawtoken * Lexing.position * Lexing.position

type 'rawtoken qtoken = 'rawtoken * Astloc.t (* quasi-token *)

(* *)

let is_bom, get_bom_name =
  let bom_tbl = Hashtbl.create 0 in
  let _ = List.iter (fun (bom, name) -> Hashtbl.add bom_tbl bom name)
    [ "\xef\xbb\xbf", "UTF-8";
      "\xfe\xff", "UTF-16 (BE)";
      "\xff\xfe", "UTF-16 (LE)";
      "\x00\x00\xfe\xff", "UTF-32 (BE)";
      "\xff\xfe\x00\x00", "UTF-32 (LE)";
      "\x2b\x2f\x76\x38", "UTF-7";
      "\x2b\x2f\x76\x39", "UTF-7";
      "\x2b\x2f\x76\x2b", "UTF-7";
      "\x2b\x2f\x76\x2f", "UTF-7";
    ]
  in
  (Hashtbl.mem bom_tbl), (Hashtbl.find bom_tbl)

let is_extended_pos pos = Fname.is_extended pos.Lexing.pos_fname

let extend_pos ?cache ext pos =
  let fname = pos.Lexing.pos_fname in
  if ext <> "" && fname <> "" && not (Fname.is_extended fname) then
    { Lexing.pos_fname = Fname.extend ?cache ~force:true fname ext;
      Lexing.pos_lnum  = pos.Lexing.pos_lnum;
      Lexing.pos_bol   = pos.Lexing.pos_bol;
      Lexing.pos_cnum  = pos.Lexing.pos_cnum;
    }
  else
    pos

let extend_poss ?cache ext pos1 pos2 =
  extend_pos ?cache ext pos1, extend_pos ?cache ext pos2
(*
  let fname = pos1.Lexing.pos_fname in
  if fname = pos2.Lexing.pos_fname then begin
    if ext <> "" && fname <> "" && not (Fname.is_extended fname) then
      let extended = Fname.extend ?cache ~force:true fname ext in
      { Lexing.pos_fname = extended;
        Lexing.pos_lnum  = pos1.Lexing.pos_lnum;
        Lexing.pos_bol   = pos1.Lexing.pos_bol;
        Lexing.pos_cnum  = pos1.Lexing.pos_cnum;
      },
      { Lexing.pos_fname = extended;
        Lexing.pos_lnum  = pos2.Lexing.pos_lnum;
        Lexing.pos_bol   = pos2.Lexing.pos_bol;
        Lexing.pos_cnum  = pos2.Lexing.pos_cnum;
      }
    else
      pos1, pos2
  end
  else
    extend_pos ext pos1, extend_pos ext pos2
*)
let get_stripped_pos pos =
  if is_extended_pos pos then
    { Lexing.pos_fname = Fname.strip pos.Lexing.pos_fname;
      Lexing.pos_lnum  = pos.Lexing.pos_lnum;
      Lexing.pos_bol   = pos.Lexing.pos_bol;
      Lexing.pos_cnum  = pos.Lexing.pos_cnum;
    }
  else
    pos

(* *)

let make_token ?cache ?(ext="") rt st ed =
  let xst, xed =
    if ext = "" then
      st, ed
    else
      extend_poss ?cache ext st ed
  in
  ((rt, xst, xed) : 'rawtoken token)

let token_to_rawtoken ((rt, _, _) : 'rt token) = rt

let token_to_lexposs ((_, st, ed) : 'rt token) = st, ed

let decompose_token ((rt, st, ed) : 'rt token) = rt, st, ed

let _token_to_string to_string ((rt, _, _) : 'rt token) = to_string rt


(* *)

let merge_locs ?(cache=None) st ed =
  try
    Astloc.merge st ed
  with
    Failure _ ->
      let lloc =
        Layeredloc.merge (Layeredloc.of_loc st) (Layeredloc.of_loc ed)
      in
      lloc#to_loc ~cache ()


[%%capture_path
let loc_of_lexposs ?(cache=None) st ed =
  try
    Astloc.of_lexposs st ed
  with
    Failure _ ->
      let lloc =
        Layeredloc.merge (Layeredloc.of_lexpos st) (Layeredloc.of_lexpos ed)
      in
      [%debug_log "%s" (lloc#to_string())];
      lloc#to_loc ~cache ()
]

(* *)

let make_qtoken ?cache ?(ext="") rt st ed =
  let xst, xed = extend_poss ?cache ext st ed in
  ((rt, loc_of_lexposs ~cache xst xed) : 'rt qtoken)

let qtoken_to_loc ((_, loc) : 'rt qtoken) = loc

let qtoken_to_rawtoken ((rt, _) : 'rt qtoken) = rt

let qtoken_to_token ((rt, loc) : 'rt qtoken) =
  let st, ed = Astloc.to_lexposs loc in
  make_token rt st ed

let _qtoken_to_string to_string ((rt, loc) : 'rt qtoken) =
  Printf.sprintf "%s[%s]" (to_string rt) (Astloc.to_string loc)




let fail_to_parse ?(head="") msg = raise (Parse_error(head, msg))


let parse_error_loc ?(head="") env mknode loc (fmt : ('a, unit, string, 'b) format4) : 'a =
  let loc_str = Astloc.to_string ~short:false ~prefix:"[" ~suffix:"]" loc in
  Printf.ksprintf
    (fun msg ->
      if env#keep_going_flag then begin
        Printf.fprintf stderr "[%s][WARNING]%s%s %s\n%!" cmd_name head loc_str msg;
        mknode loc
      end
      else
        fail_to_parse ~head:loc_str msg

    ) fmt

let parse_error ?(head="") env mknode spos epos =
  let loc = loc_of_lexposs spos epos in
  parse_error_loc ~head env mknode loc

let parse_warning_loc ?(out=stderr) ?(head="") loc (fmt : ('a, out_channel, unit, 'b) format4) : 'a =
  Printf.kfprintf
    (fun ochan -> Printf.fprintf ochan "\n%!")
    out
    ("[%s][WARNING]%s[%s] "^^fmt) cmd_name head (Astloc.to_string ~short:false loc)

let parse_warning ?(out=stderr) ?(head="") spos epos =
  let loc = loc_of_lexposs spos epos in
  parse_warning_loc ~out ~head loc




let mkparser p = MenhirLib.Convert.Simplified.traditional2revised p


class virtual ['rawtoken] scanner = object
  method virtual get_token : unit -> 'rawtoken token
end


class virtual ['src, 'rawtoken, 'ast] c (env : 'src #Env_base.c) = object (self)

  val env = env

  method virtual _parse             : 'ast

  method virtual make_source        : Storage.file -> #Source_base.c
  method virtual make_source_stdin  : #Source_base.c

  method set_search_path_list l = env#set_search_path_list l
  method add_search_path p = env#add_search_path p

  method _set_verbose_flag b = env#_set_verbose_flag b
  method set_verbose_flag = env#set_verbose_flag
  method clear_verbose_flag = env#clear_verbose_flag

  method _set_keep_going_flag b = env#_set_keep_going_flag b
  method set_keep_going_flag = env#set_keep_going_flag
  method clear_keep_going_flag = env#clear_keep_going_flag

  method extra_source_files = env#extra_source_files

  method parser_init =
    env#init

  method lines_read = env#lines_read


  method parse_file file =
    self#parser_init;
    let _ = env#enter_source (self#make_source file) in
    let ast = self#_parse in
    env#exit_source;
    ast

  method parse_stdin =
    self#parser_init;
    let _ = env#enter_source (self#make_source_stdin) in
    self#_parse

end (* of class Parserlib_base.c *)

class virtual ['rawtoken, 'ast] sb_c (env : 'src #Env_base.c) = object
  inherit [Source_base.c, 'rawtoken, 'ast] c env

  method make_source file  = new Source_base.c file

  method make_source_stdin = new Source_base.c Storage.stdin

end (* of class Parserlib_base.sb_c *)
