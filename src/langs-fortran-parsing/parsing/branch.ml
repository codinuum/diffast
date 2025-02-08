(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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

(* branch.ml *)

[%%prepare_logger]

module Xstring = Diffast_misc.Xstring
module Astloc = Langs_common.Astloc
module Parserlib_base = Langs_common.Parserlib_base

module Loc = Astloc
module Aux = Parser_aux
module PB = Parserlib_base
module C = Context

open Printf
open Common
open Labels

module PPD = PpDirective

type tag =
  | Tifdef  of string * Loc.t
  | Tifndef of string * Loc.t
  | Tif     of string * Loc.t
  | Telif   of string * Loc.t * Loc.t (* key *)
  | Telse of Loc.t * Loc.t (* key *)
  | Tcontext
  | Tselected
  | Tdummy

let tag_to_string = function
  | Tifdef(s, loc)      -> sprintf "Tifdef:%s[%s]" s (Loc.to_string loc)
  | Tifndef(s, loc)     -> sprintf "Tifndef:%s[%s]" s (Loc.to_string loc)
  | Tif(s, loc)         -> sprintf "Tif:%s[%s]" s (Loc.to_string loc)
  | Telif(s, loc, kloc) -> sprintf "Telif:%s[%s][%s]" s (Loc.to_string loc) (Loc.to_string kloc)
  | Telse(loc, kloc)    -> sprintf "Telse[%s][%s]" (Loc.to_string loc) (Loc.to_string kloc)
  | Tcontext        -> "Tcontext"
  | Tselected       -> "Tselected"
  | Tdummy          -> "Tdummy"

let loc_of_tag = function
  | Tifdef(_, loc)
  | Tifndef(_, loc)
  | Tif(_, loc)
  | Telif(_, loc, _)
  | Telse(loc, _)       -> loc
  | btag -> invalid_arg (sprintf "Branch.loc_of_tag: %s" (tag_to_string btag))

let key_loc_of_tag = function
  | Tifdef(_, loc)
  | Tifndef(_, loc)
  | Tif(_, loc)
  | Telif(_, _, loc)
  | Telse(_, loc)       -> loc
  | btag -> invalid_arg (sprintf "Branch.key_loc_of_tag: %s" (tag_to_string btag))

[%%capture_path
let tag_to_node env c btag _children =
  let loc, sect, ppd =
    match btag with
    | Tifdef(n, loc)   -> loc, Label.PpSectionIfdef n,  PPD.Branch (PPD.Ifdef n)
    | Tifndef(n, loc)  -> loc, Label.PpSectionIfndef n, PPD.Branch (PPD.Ifndef n)
    | Tif(c, loc)      -> loc, Label.PpSectionIf c,     PPD.Branch (PPD.If c)
    | Telif(c, loc, _) -> loc, Label.PpSectionElif c,   PPD.Branch (PPD.Elif c)
    | Telse(loc, _)    -> loc, Label.PpSectionElse,     PPD.Branch PPD.Else
    | _ -> raise Undefined
  in
  let ppd_nd =
    new Ast.node ~lloc:(env#mklloc loc) (Label.PpDirective (PPD.mk ~context:c ppd))
  in
  let children = ppd_nd :: _children in
  [%debug_log "children:\n%s\n" (Xlist.to_string (fun n -> n#to_string) "\n" children)];
  let nd = new Ast.node ~lloc:(Ast.lloc_of_nodes children) ~children sect in
  [%debug_log "node: %s" nd#to_string];
  nd
]


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  module TokenF = Token.F (Stat)

  open Tokens_
  open Stat

  let tag_to_node = tag_to_node Stat.env

  let make_tag iftok id loc kloc =
    match iftok with
    | PP_BRANCH br -> begin
        match br with
        | PPD.Ifdef _  -> Tifdef(id, loc)
        | PPD.Ifndef _ -> Tifndef(id, loc)
        | PPD.If c     -> Tif(Xstring.strip c, loc)
        | PPD.Elif c   -> Telif(Xstring.strip c, loc, kloc)
        | PPD.Else     -> Telse(loc, kloc)
        | PPD.Endif _  -> Telse(loc, kloc) (* virtual #else *)
        (*| _ -> invalid_arg ("Branch.make_tag: invalid iftoken: "^(Token.rawtoken_to_string iftok))*)
    end
    | _ ->
	invalid_arg
	  ("Branch.make_tag: invalid iftoken: "^(Token.rawtoken_to_string iftok))


  class tokensource q = object (self)
    inherit Tokensource.c

    val mutable queue = q

    val mutable last_tok = EOP
    val mutable last_loc = Loc.dummy

    val mutable prev_tok = EOP
    val mutable prev_loc = Loc.dummy

    val mutable eop_flag = false

    method prepend_queue ?(copy=true) q =
      queue#prepend_from (if copy then q#copy else q)

    method prepend qtoken =
      queue#prepend qtoken

    method eop_flag = eop_flag
    method set_eop_flag = eop_flag <- true
    method clear_eop_flag = eop_flag <- false

    method peek_nth_rawtok n =
      try
        let tok, _ = queue#peek_nth n in tok
      with
        Failure _ -> NOTHING

    method peek_nth n =
      try
        queue#peek_nth n
      with
        Failure _ -> NOTHING, Loc.dummy

    method peek_next_rawtok ?(skip_eol=false) () =
      [%debug_log "skip_eol=%B" skip_eol];
      let skip_until_endif_flag = ref false in
      let branch_depth = ref 0 in
      let skip = ref false in
      try
        let t, _ = queue#peek in
        let nxt = ref t in
        try
          queue#iter
            (fun (tok, _) ->
              if !skip then
                skip := false
              else
                match skip_eol, tok with
                | true, EOL -> ()
                | _, _ ->
	            if TokenF.is_pp_directive tok then begin
	              match tok with
	              | PP_IFDEF | PP_IFNDEF ->
                          incr branch_depth;
                          skip := true

	              | PP_UNDEF | PP_BRANCH PPD.Else(*PP_ELSE*) ->
		          if !branch_depth = 0 then
		            skip_until_endif_flag := true

	              | PP_ELIF ->
		          if !branch_depth = 0 then
		            skip_until_endif_flag := true;
                          skip := true

	              | PP_BRANCH (PPD.Endif _)(*PP_ENDIF*) ->
		          if !branch_depth > 0 then
		            decr branch_depth;
		          skip_until_endif_flag := false

	              | _ -> ()
	            end
                    else if !skip_until_endif_flag then
                      ()
                    else begin
                      nxt := tok;
                      raise Exit
                    end
            );
          NOTHING
        with
          Exit -> !nxt
      with
        Xqueue.Empty -> NOTHING


    method get ?(prefetch=true) () =
      ignore prefetch;
      try
        let qtoken = queue#take in
        [%debug_log "%s" (Token.qtoken_to_string qtoken)];
        let tok, _ = qtoken in
        begin
          match tok with
          | LPAREN -> env#enter_paren_context
          | RPAREN | SLASH_RPAREN -> env#exit_paren_context
          | _ -> ()
        end;
        qtoken
      with
        Xqueue.Empty -> raise Tokensource.Empty

    method get_token (handler : Token.qtoken_t -> Token.t) =
      handler (self#get())

    method discard ?(skip_pp_branch) () =
      ignore skip_pp_branch;
      let qtoken = self#get() in
      [%debug_log "discarded: %s" (Token.qtoken_to_string qtoken)];
      qtoken

    method get_last_rawtok = last_tok
    method set_last_rawtok t = last_tok <- t

    method get_last_loc = last_loc
    method set_last_loc l = last_loc <- l

    method get_prev_rawtok = prev_tok
    method set_prev_rawtok t = prev_tok <- t

    method get_prev_loc = prev_loc
    method set_prev_loc l = prev_loc <- l

  end (* of class Branch.tokensource *)


end (* of functor Branch.F *)
]
