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
(* parser_aux.ml *)

[%%prepare_logger]

module Env_base = Langs_common.Env_base
module Source_base = Langs_common.Source_base
module Regions = Langs_common.Regions

(*open Printf*)
open Common
open Ast


[%%capture_path
class env = object (self)
  inherit [Source_base.c] Env_base.c as super

  val mutable with_stmt_enabled = true (* always enabled in v2.6+ *)

  val mutable keep_going_flag = true
  val mutable ignore_comment_flag = false
  val mutable shift_flag = false
  val mutable last_token_opt = (None : Obj.t option)
  val mutable last_range = (Astloc.dummy_lexpos, Astloc.dummy_lexpos)
  val mutable paren_level = 0
  val mutable brace_level = 0
  val mutable bracket_level = 0
  val mutable block_level = 0

  val comment_tbl = (Hashtbl.create 0 : (int, comment) Hashtbl.t)

  method add_comment c = Hashtbl.add comment_tbl c.c_loc.Astloc.start_line c
  method comment_tbl = comment_tbl

  val blank_regions = new Regions.c

  method blank_regions = blank_regions

  method with_stmt_enabled = with_stmt_enabled
  method enable_with_stmt = with_stmt_enabled <- true
  method disable_with_stmt = with_stmt_enabled <- false

  (*method keep_going_flag = keep_going_flag*)
  (*method _set_keep_going_flag b = keep_going_flag <- b*)

  method ignore_comment_flag = ignore_comment_flag
  method _set_ignore_comment_flag b = ignore_comment_flag <- b

  method shift_flag = shift_flag
  method set_shift_flag () =
    [%debug_log "set"];
    shift_flag <- true
  method clear_shift_flag () =
    [%debug_log "clear"];
    shift_flag <- false

  method last_token =
    match last_token_opt with
    | Some o -> o
    | None -> raise Not_found
  method set_last_token o = last_token_opt <- Some o

  method last_range =
    let st, ed = last_range in
    if st != Astloc.dummy_lexpos && ed != Astloc.dummy_lexpos then
      st, ed
    else
      raise Not_found

  method set_last_range x = last_range <- x

  method reset_paren_level () = paren_level <- 0;
  method paren_level = paren_level
  method open_paren () = paren_level <- paren_level + 1
  method close_paren () = paren_level <- paren_level - 1

  method brace_level = brace_level
  method open_brace () = brace_level <- brace_level + 1
  method close_brace () = brace_level <- brace_level - 1

  method bracket_level = bracket_level
  method open_bracket () = bracket_level <- bracket_level + 1
  method close_bracket () = bracket_level <- bracket_level - 1

  method block_level = block_level
  method open_block () = block_level <- block_level + 1
  method close_block () = block_level <- block_level - 1

  method! init =
    super#init;
    blank_regions#clear

  initializer
    self#init

end (* of class Parser_aux.env *)
]

module type STATE_T = sig
  val env     : env
end

let warning_loc loc = PB.parse_warning_loc ~head:"[Python]" loc

[%%capture_path
module F (Stat : STATE_T) = struct

  open Stat

  let get_loc = Astloc.of_lexposs

  let parse_warning start_pos end_pos =
    let loc = get_loc start_pos end_pos in
    warning_loc loc

  let parse_error start_ofs end_ofs (fmt : ('a, unit, string, 'b) format4) : 'a =
    let loc = get_loc start_ofs end_ofs in
    let loc_str = Astloc.to_string ~short:false ~prefix:"[" ~suffix:"]" loc in
    Printf.ksprintf
      (fun msg ->
        if env#keep_going_flag then
          Printf.fprintf stderr "[Python][WARNING]%s%s %s\n%!" PB.cmd_name loc_str msg
        else
          fail_to_parse ~head:loc_str msg
      ) fmt

  let mkstmt sp ep d = { stmt_desc=d; stmt_loc=(get_loc sp ep) }
  let mksstmt sp ep d = { sstmt_desc=d; sstmt_loc=(get_loc sp ep) }
  let mkexpr sp ep d = { expr_desc=d; expr_loc=(get_loc sp ep) }
  let mkprim sp ep d = { prim_desc=d; prim_loc=(get_loc sp ep) }
  let mkprimexpr sp ep d = { expr_desc=(Eprimary (mkprim sp ep d)); expr_loc=(get_loc sp ep) }
  let mkde sp ep d = { delem_desc=d; delem_loc=(get_loc sp ep) }

  let mktestlist ?(comma=false) ?(yield=false) l = { list=l; comma=comma; yield=yield }

  let emptyarglist ?(loc=Ast.Loc.dummy) () = loc, []
  let emptyvarargslist = emptyarglist
  let emptytypedargslist = emptyarglist

  let mkerrexpr sp ep =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    { expr_desc=Eerror; expr_loc=loc }

  let mkerrsstmt sp ep =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    { sstmt_desc=SSerror; sstmt_loc=loc }

  let mkerrstmt sp ep =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    { stmt_desc=Serror; stmt_loc=loc }

  let mkmarkerstmt sp ep s =
    let loc = get_loc sp ep in
    env#missed_regions#add loc;
    { stmt_desc=Smarker s; stmt_loc=loc }

  let chg_loc (_, xl) loc = loc, xl

end (* of functor Parser_aux.F *)
]
