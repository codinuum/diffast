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

(*
 * tokenbuffer.ml
 *
 * Buffer for tokens
 *
 *)

[%%prepare_logger]

module Xstring = Diffast_misc.Xstring
module Astloc = Langs_common.Astloc
module Layeredloc = Langs_common.Layeredloc
module Parserlib_base = Langs_common.Parserlib_base

open Common
module Loc = Astloc
module LLoc = Layeredloc
module Aux = Parser_aux
module PB  = Parserlib_base
module C   = Context
module M   = Macro
module PPD = Labels.PpDirective
module Partial = Ast.Partial

open Keyword

let sprintf = Printf.sprintf

(*
let lexposs_to_offsets (st_pos, ed_pos) =
  st_pos.Lexing.pos_cnum, ed_pos.Lexing.pos_cnum
*)

let exponent_pat = Str.regexp "[de][0-9]+$"

type partial_parser = (Token.t, Partial.t) MenhirLib.Convert.revised

type parse_result =
  | Rcomplete of Partial.t
  | Rincomplete
  | Runknown

exception Empty
exception Incomplete


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  module TokenF = Token.F (Stat)

  module A = Aux.F (Stat)
  module P = Parser.Make (Stat)
  module BranchF = Branch.F(Stat)

  open Tokens_
  open Stat


  let tag_to_node = BranchF.tag_to_node

  let loc_of_lexposs = PB.loc_of_lexposs ~cache:(Some env#fname_ext_cache)

  let merge_locs = PB.merge_locs ~cache:(Some env#fname_ext_cache)


  let get_last_cond last tok =
    [%debug_log "last token: %s" (Token.rawtoken_to_string last)];
    match last with
    | CALL _
    | CLASS _
    | CODIMENSION _
    | DATA _
    | DIMENSION _
    | END_ASSOCIATE _
    | END_BLOCK _
    | END_CRITICAL _
(*    | END_FUNCTION _*)
    | END_MODULE _
    | END_PROCEDURE _
    | END_PROGRAM _
    | END_SELECT _
    | END_SUBMODULE _
    | END_SUBPROGRAM _
(*    | END_SUBROUTINE _*)
    | END_TYPE _
    | ENTRY _
    | ENUMERATOR _
(*    | EXTERNAL _*)
    | FUNCTION _
    | INTRINSIC _
    | PROGRAM _
    | RESULT _
    | SAVE _
    | SIMPLE_ATTR _
    | SUBROUTINE _
    | TYPE _
    | USE _

    | EQ
    | PLUS
    | MINUS
    | STAR
    | SLASH
    | SLASH_SLASH
    | STAR_STAR
    | D_EQ
    | D_NE
    | D_GT
    | D_GE
    | D_LT
    | D_LE
    | D_NOT
    | D_AND
    | D_OR
    | D_EQV
    | D_NEQV
      -> true

    | COMMA -> begin
        match tok with
        | TYPE _ | CLASS _ -> true
        | _ -> false
    end

    | MODULE _ -> begin
        match tok with
        | PROCEDURE _ | FUNCTION _ | SUBROUTINE _ -> false

        | KINDED_TYPE_SPEC _ | DOUBLE_PRECISION _ | CHARACTER _ | TYPE _ | CLASS _
        | PREFIX_SPEC _ when env#in_interface_context -> false

        | _ -> true
    end

    | COLON_COLON | INTERFACE _ | END_INTERFACE _ -> begin
        match tok with
        | OPERATOR _ | ASSIGNMENT _ -> false
        | _ -> true
    end

    (*| INTEGER _ | REAL _ | COMPLEX _ | LOGICAL _*) | KINDED_TYPE_SPEC _
    | BYTE _
    | DOUBLE_PRECISION _ | PRECISION _ | CHARACTER _ | PP_MACRO_TYPE_SPEC _
      -> begin
	match tok with
        | PREFIX_SPEC _
	(*| RECURSIVE _ | PURE _ | ELEMENTAL _ | IMPURE _*)
        | FUNCTION _ | SUBROUTINE _ -> false
	| _ -> true
      end

    | EQ_GT -> begin
        match tok with
        | NULL _ | OPERATOR _ -> false
        | _ -> true
    end

    | PRIVATE _ | PUBLIC _ -> begin
        match tok with
        | OPERATOR _ | ASSIGNMENT _ | READ _ | WRITE _ -> false
        | _ -> true
    end

    | _ -> false


  let is_head_of_stmt last =
    [%debug_log "last=%s" (Token.rawtoken_to_string last)];
    let b =
      match last with
      | EOL | EOP | SEMICOLON
      | PP_INCLUDE__FILE _ | PP_DEFINE__IDENT__BODY _ | PP_UNDEF__IDENT _
      | PP_ISSUE__MESG _ (*| PP_ERROR__MESG _ | PP_WARNING__MESG _*)
      | PP_UNKNOWN__REST _
      | INCLUDE__FILE _ | OPTIONS__OPTS _
      | OCL _ | OMP _ | ACC _ | XLF _ | DEC _ | RAW _
      | SPEC_PART_CONSTRUCT _ | EXEC_PART_CONSTRUCT _ | DERIVED_TYPE_DEF_PART _
      | END_FRAGMENT | FUNCTION_HEAD _ | SUBROUTINE_HEAD _ | PU_TAIL _ | STMT _
        -> true
      | RPAREN -> env#in_if_context
      | _ -> false
    in
    [%debug_log "%B" b];
    b


  let get_do_cond tok =
    env#in_do_context &&
    (match tok with
    | WHILE _ | CONCURRENT _ -> false
    | _ -> true
    )

  let get_type_spec_cond tok =
    env#in_type_spec_context &&
    (match tok with
    (*| EXTERNAL _ | PROTECTED _ | VALUE _ | VOLATILE _ *)
    | SIMPLE_ATTR _
    | PARAMETER _ | ALLOCATABLE _ | DIMENSION _ | CODIMENSION _ | INTENT _
    | INTRINSIC _ | OPTIONAL _ | POINTER _ | SAVE _ | TARGET _
    | ASYNCHRONOUS _ | BIND _
    | FUNCTION _
      -> false
    | INTENT_SPEC _ -> not env#in_intent_context
    | _ -> true
    )

  let get_if_action_cond last_tok tok =
    (is_head_of_stmt last_tok) &&
    (match tok with
    | IF _ | END_PROGRAM _(* | END_FUNCTION _ | END_SUBROUTINE _*) | END_SUBPROGRAM _
    | END_PROCEDURE _ -> false
    | _ -> true
    )

  let in_name_context tok next_tok tokensrc =
    let last_tok = tokensrc#get_last_rawtok in

    let in_name_context =
      let last_cond = get_last_cond last_tok tok in
      let next_cond =
	match next_tok with
	| EQ_GT -> true

        | PERCENT -> (not env#in_structure_context) || (not (is_head_of_stmt last_tok))

	| PLUS | MINUS -> begin
            match tok with
            | STOP _ -> false
            | _ -> true
        end

	| EQ -> begin
	    match tok with
	    | KIND _ | LEN _ (*| STAT _*) -> false
            (*| ERRMSG _*) (*| SOURCE _ | MOLD _*)| ALLOC_OPT_EXPR _ -> not env#in_allocate_context
	    | _ -> true
	end

        | LPAREN -> begin
            match tok with
            | LEN _ | KIND _
            | BLOCK _ | CRITICAL _
            | DEFAULT _ | RECORD _ (*| OPTIONS _*)
              -> true
            | _ -> false
        end

	| _ -> false
      in
      let paren_cond =
	env#in_paren_context &&
	(match tok with
	| KIND _ | LEN _ (*| STAT _*) -> begin
	    match next_tok with
	    | EQ -> false
	    | _ -> true
        end
	| INTENT_SPEC _ -> false

        | DOUBLE_PRECISION _ | DOUBLE _
        | DOUBLE_COMPLEX _ | CHARACTER _ | TYPE _ | BYTE _ | CLASS _
        (*| INTEGER _ | REAL _ | COMPLEX _ | LOGICAL _*) | KINDED_TYPE_SPEC _
        | PP_MACRO_TYPE_SPEC _ ->
            not env#in_allocate_context &&
            not env#in_type_guard_context &&
            not env#in_procedure_context &&
            not env#in_type_context

        (*| ERRMSG _*) (*| SOURCE _ | MOLD _*)| ALLOC_OPT_EXPR _ -> begin
            match next_tok with
            | EQ -> not env#in_allocate_context
            | _ -> true
        end

	| _ -> true
	)
      in

      let misc_cond =
	match tok with
	| KIND _ | LEN _ (*| STAT _*) (*| SOURCE _ | MOLD _*)| ALLOC_OPT_EXPR _ (*| ERRMSG _*) ->
            not env#in_paren_context

	| INTENT_SPEC _ -> not env#in_intent_context
        | RESULT _ -> not env#in_result_context
        | DATA_EDIT_DESC _ | POSITION_EDIT_DESC _ -> is_head_of_stmt last_tok
        | OPEN _ | CLOSE _ | WAIT _ -> begin
            match next_tok with
            | LPAREN -> false
            | _ -> true
        end
	| _ -> false
      in

      let character_cond =
        match tok with
        | KIND _ | LEN _
        | PUBLIC _ | PRIVATE _ | ABSTRACT _
        | PASS _ | NOPASS _ | NON_OVERRIDABLE _ | DEFERRED _
        | PARAMETER _ | ALLOCATABLE _ | DIMENSION _ | CODIMENSION _
        | INTENT _ | INTRINSIC _ | OPTIONAL _ | POINTER _ | SAVE _ | TARGET _
        | ASYNCHRONOUS _ | BIND _ | SIMPLE_ATTR _
        (*| EXTERNAL _ | PROTECTED _ | VALUE _ | VOLATILE _ *)
        (*| AUTOMATIC _ | STATIC _*)
        | FUNCTION _
          -> false
        | INTENT_SPEC _ -> not env#in_intent_context
        | _ -> env#in_character_context
      in

      let do_cond = get_do_cond tok in

      let type_spec_cond = get_type_spec_cond tok in

      let access_cond =
        env#in_access_context &&
        (match tok with
        | OPERATOR _ | ASSIGNMENT _ -> false
        | _ -> true
        )
      in

      [%debug_log ("\n"^^
                 "env#in_name_context      :%B\n"^^
                 "env#in_io_control_context:%B\n"^^
                 "env#in_array_ctor_context:%B\n"^^
                 "env#in_only_context      :%B\n"^^
                 "last_cond                :%B\n"^^
                 "next_cond                :%B\n"^^
                 "paren_cond               :%B\n"^^
                 "character_cond           :%B\n"^^
                 "do_cond                  :%B\n"^^
                 "type_spec_cond           :%B\n"^^
                 "access_cond              :%B\n"^^
                 "misc_cond                :%B\n"
                )

        env#in_name_context env#in_io_control_context env#in_array_ctor_context
        env#in_only_context last_cond next_cond paren_cond character_cond do_cond
        type_spec_cond access_cond misc_cond];

      let if_action_cond = get_if_action_cond last_tok tok in

      last_cond ||
      next_cond ||
      ((env#in_name_context || paren_cond) && (not if_action_cond)) ||
      env#in_io_control_context ||
      env#in_array_ctor_context ||
      env#in_only_context ||
      character_cond ||
      do_cond ||
      type_spec_cond ||
      access_cond ||
      misc_cond
    in (* in_name_context *)

    let typeof_cond =
      match tok with
      (*| INTEGER _ | REAL _ | COMPLEX _ | LOGICAL _*) | KINDED_TYPE_SPEC _
      | BYTE _ | CLASS _
      | DOUBLE_PRECISION _ | DOUBLE _ | CHARACTER _ | TYPE _ | PP_MACRO_TYPE_SPEC _
        -> env#in_typeof_context

      | _ -> false
    in

    let b = in_name_context && (not typeof_cond) in
    [%debug_log "%B" b];
    b

 let quotes = ["\"";"'"]

 let data_edit_desc_pat = Str.regexp "\\([abdefgiloz]\\|en\\|es\\)[0-9]+?$"
 let position_edit_desc_pat = Str.regexp "t[lr]?[0-9]+"

 let find_edit_desc str =
   let s = String.lowercase_ascii str in
   if Str.string_match data_edit_desc_pat s 0 then begin
     [%debug_log "%s -> DATA_EDIT_DESC" str];
     DATA_EDIT_DESC str
   end
   else if Str.string_match position_edit_desc_pat s 0 then begin
     [%debug_log "%s -> POSITION_EDIT_DESC" str];
     POSITION_EDIT_DESC str
   end
   else
     raise Not_found

 let toxxx_pat = Str.regexp "to\\([0-9]+\\)$"

 let hack_token (tokensrc : Tokensource.c) ((_tok, _loc) as _qtoken) =
    let loc = ref _loc in
    let tok = ref _tok in

    [%debug_log "%s" (Token.qtoken_to_string _qtoken)];

    let discarded = ref false in

    let discard() =
      discarded := true;
      tokensrc#discard ()
    in

(*    let next_tok = ref (tokensrc#peek_next_rawtok()) in*)
    let next_tok = ref (tokensrc#peek_nth_rawtok 1) in

    let peek_next() =
      if !discarded then begin
        (*next_tok := tokensrc#peek_next_rawtok();*)
        next_tok := tokensrc#peek_nth_rawtok 1;
        discarded := false
      end;
      !next_tok
    in

    let last_tok = tokensrc#get_last_rawtok in

    let is_head_of_stmt_ = is_head_of_stmt last_tok in

    let following_comma =
      match last_tok with
      | COMMA -> true
      | _ -> false
    in

    let is_head_of_stmt_or_following_comma, is_following_rparen =
      match last_tok with
      | COMMA -> true, false
      | RPAREN -> is_head_of_stmt_, true
      | _ -> is_head_of_stmt_, false
    in

(* *)

    begin
      match peek_next() with
      | PP_MACRO_STMT _ -> begin
          let tok2 = tokensrc#peek_nth_rawtok 2 in
          match tok2 with
          | EOL | SEMICOLON -> ()
          | _ -> ignore (discard())
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | DO s -> begin
          let nth = ref 1 in
          let depth = ref 0 in
          let eq_found = ref false in
          try
            while true do
              let nth_tok = tokensrc#peek_nth_rawtok !nth in
              begin
                match nth_tok with
                | LPAREN -> incr depth
                | RPAREN -> decr depth

                | EQ -> eq_found := true

                | COMMA | WHILE _ | CONCURRENT _ -> if !depth = 0 then raise Exit

                | EOL | SEMICOLON | NOTHING | EOF _ ->
                    if !eq_found then begin
                      [%debug_log "DO --> <identifier>"];
                      tok := IDENTIFIER s;
                    end;
                    raise Exit
                | _ -> ()
              end;
              incr nth
            done
          with
            Exit -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | IDENTIFIER s -> begin
          match peek_next() with
          | CONTINUED_IDENTIFIER s' -> begin (* <identifier><continued-identifier> --> <keyword> | <identifier> *)
              [%debug_log "<identifier><continued-identifier> --> <keyword>|<identifier>"];
              tok := Ulexer.find_keyword (s^s');
              let _, loc' = discard() in
	      loc := merge_locs !loc loc'
          end
          | PP_CONCAT -> begin
              [%debug_log "<identifier> '##' <identifier>|<int-literal>|<keyword>|<pp-underscore>|<pp-identifier> --> <keyword>|<identifier>"];
              let sr = ref s in
              try
                while true do
                  let _ = discard() in
                  let s' =
                    match peek_next() with
                    | IDENTIFIER s' | INT_LITERAL s' | PP_UNDERSCORE s' | PP_IDENTIFIER s' -> s'
                    | PP_CONCAT -> begin
                        try
                          while true do
                            let _ = discard() in
                            match peek_next() with
                            | PP_CONCAT -> ()
                            | _ -> raise Exit
                          done;
                          ""
                        with
                          Exit -> begin
                            match peek_next() with
                            | IDENTIFIER s' | INT_LITERAL s' | PP_UNDERSCORE s' | PP_IDENTIFIER s' -> s'
                            | tok -> Token.get_keyword tok
                          end
                    end
                    | tok -> Token.get_keyword tok
                  in
                  sr := !sr ^ s';
                  tok := Ulexer.find_keyword (!sr);
                  let _, loc' = discard() in
	          loc := merge_locs !loc loc';
                  match peek_next() with
                  | PP_CONCAT -> ()
                  | _ -> raise Exit
                done
              with
              | Not_found -> ()
              | Exit -> ()
          end
          | _ -> ()
      end
      | SLASH_SLASH -> begin
          if env#in_format_context then begin
            [%debug_log "'//' --> '/' '/'"];
            let spos, epos = Loc.to_lexposs !loc in
            tok := SLASH;
            loc := loc_of_lexposs spos spos;
            tokensrc#prepend (SLASH, loc_of_lexposs epos epos)
          end
      end
      | _ -> ()
    end;

    begin (* <keyword>|<data-edit-desc>|<position-edit-desc> --> <identifier> *)
      let cond =
        (Token.is_keyword !tok) ||
        (match !tok with
        | DATA_EDIT_DESC _ | POSITION_EDIT_DESC _ -> not env#in_format_context
        | _ -> false
        )
      in
      [%debug_log "cond=%B" cond];
      if cond then begin
	let in_name_context = in_name_context !tok (peek_next()) tokensrc in
        [%debug_log "in_name_context=%B" in_name_context];
	if in_name_context then begin
          match !tok with
          (*| INTEGER s | REAL s | COMPLEX s | LOGICAL s*) | KINDED_TYPE_SPEC s
          | DOUBLE_PRECISION s | DOUBLE s | CHARACTER s | BYTE s
          | CLASS s | TYPE s | PP_MACRO_TYPE_SPEC s
          | LEN s | KIND s
              -> begin
                if is_head_of_stmt_ then begin
                  () (* handled by other rules *)
                end
                else if env#in_array_ctor_context then begin (* search '::' up to '/)' or ']' *)
                  let nth = ref 1 in
                  try
                    while true do
                      let nth_tok = tokensrc#peek_nth_rawtok !nth in
                      match nth_tok with
                      | SLASH | SLASH_RPAREN | RBRACKET | EOL | SEMICOLON | NOTHING | EOF _ -> raise Not_found
                      | COLON_COLON -> raise Exit
                      | _ -> incr nth
                    done
                  with
                  | Not_found -> begin
                      [%debug_log "<keyword>|<data-edit-desc>|<position-edit-desc> --> <identifier>"];
                      tok := IDENTIFIER s
                  end
                  | Exit -> begin
                      match !tok with
                      | LEN s' | KIND s' ->
                          if (peek_next()) = LPAREN then begin
                            [%debug_log "<keyword> --> <identifier>"];
                            tok := IDENTIFIER s'
                          end
                      | _ -> ()
                  end
                end
                else begin
                  [%debug_log "<keyword>|<data-edit-desc>|<position-edit-desc> --> <identifier>"];
                  tok := IDENTIFIER s
                end
              end
          | WRITE _ when begin
              last_tok == RPAREN &&
              peek_next() == LPAREN &&
              env#in_io_control_context
          end -> begin
              [%debug_log "')' WRITE --> ')' ';' WRITE"];
              Common.parse_warning_loc !loc "lack of SEMICOLON";
              let spos, _ = Loc.to_lexposs !loc in
              tokensrc#prepend (!tok, !loc);
              tok := SEMICOLON;
              loc := loc_of_lexposs spos spos
          end
          | OPERATOR s | ASSIGNMENT s | READ s | WRITE s -> begin
              if not env#in_only_context then begin
                [%debug_log "<keyword> --> <identifier>"];
                tok := IDENTIFIER s
              end
          end
          | _ -> begin
              [%debug_log "<keyword>|<data-edit-desc>|<position-edit-desc> --> <identifier>"];
	      tok := IDENTIFIER (Token.rawtoken_to_rep !tok)
          end
	end
      end
    end;

    begin (* <keyword> --> <identifier> *)
      match !tok with
      | IF s -> begin
          match peek_next() with
          | LPAREN -> ()
          | _ -> begin
              [%debug_log "IF --> <identifier>"];
              tok := IDENTIFIER s
          end
      end
      | NULL s -> begin
          match peek_next() with
          | LPAREN -> begin
              match tokensrc#peek_nth_rawtok 2 with
              | RPAREN -> ()
              | _ -> begin
                  match last_tok with
                  | EQ_GT -> ()
                  | _ -> begin
                      [%debug_log "NULL --> <identifier>"];
                      tok := IDENTIFIER s
                  end
              end
          end
          | _ -> begin
              [%debug_log "NULL --> <identifier>"];
              tok := IDENTIFIER s
          end
      end
      | ENTRY s | GENERIC s -> begin
          if not is_head_of_stmt_ then begin
            [%debug_log "ENTRY|GENERIC --> <identifier> : not the head of stmt"];
            tok := IDENTIFIER s
          end
      end
      | PARAMETER s | PRIVATE s | PUBLIC s | ALLOCATABLE s
      | DIMENSION s | CODIMENSION s
      (*| EXTERNAL s | PROTECTED s | VALUE s | VOLATILE s*) | SIMPLE_ATTR s
      | INTENT s | INTRINSIC s | OPTIONAL s | POINTER s | SAVE s | TARGET s
      | ASYNCHRONOUS s  | ASSIGN s | ABSTRACT s | ENUMERATOR s
      | SEQUENCE s | MAP s | PASS s | NOPASS s | DEFERRED s | NON_OVERRIDABLE s
        -> begin
          if not is_head_of_stmt_or_following_comma then begin
            [%debug_log "<keyword> --> <identifier>"];
            tok := IDENTIFIER s
          end
        end
      | BIND s -> begin
          if not is_head_of_stmt_or_following_comma && not is_following_rparen then begin
            [%debug_log "BIND --> <identifier>"];
            tok := IDENTIFIER s
          end
      end
      (*| INTEGER s | REAL s | COMPLEX s | LOGICAL s*) | KINDED_TYPE_SPEC s
      | BYTE s
      | DOUBLE_PRECISION s | DOUBLE s | CHARACTER s -> begin
          if
            not is_head_of_stmt_ &&
            not env#in_array_ctor_context &&
            not env#in_implicit_context &&
            not env#in_allocate_context &&
            not env#in_typeof_context &&
            not env#in_type_guard_context &&
            not env#in_procedure_context &&
            not env#in_type_context
          then begin
            match last_tok with
            | PREFIX_SPEC _ | SUBPROGRAM _ | PROGRAM_UNIT _ | END_FRAGMENT -> ()
            (*| RECURSIVE _ | PURE _ | ELEMENTAL _ | IMPURE _ -> ()*)

            | MODULE _ | KINDED_TYPE_SPEC _ | DOUBLE_PRECISION _ | CHARACTER _ | TYPE _ | CLASS _
              when env#in_interface_context -> ()

            | _ -> begin
                [%debug_log "<keyword> --> <identifier>"];
                tok := IDENTIFIER s
            end
          end
      end
      | _ -> ()
    end;

    begin (* <keyword> --> <identifier> *)
      match !tok with
      | TARGET s | PUBLIC s | PRIVATE s | SAVE s | OPTIONAL s
      (*| EXTERNAL s | PROTECTED s | VALUE s | VOLATILE s*) | SIMPLE_ATTR s
      | ALLOCATABLE s | INTRINSIC s | USE s | STOP s | ASYNCHRONOUS s
      | STRUCTURE s | ENUM s | UNION s | MAP s | ABSTRACT s | END s | ENUMERATOR s
      | SEQUENCE s | ASSIGN s | NOPASS s | NON_OVERRIDABLE s | DEFERRED s
        -> begin (* <keyword> ('='|'(') *)
          [%debug_log "checking if %s is an identifier" (Token.rawtoken_to_string !tok)];
          match peek_next() with
          | LPAREN | EQ -> begin
              [%debug_log "<keyword> --> <identifier> : <keyword> ('='|'(')"];
              tok := IDENTIFIER s
          end
          | _ -> ()
      end
      | PARAMETER s | INTENT s (*| DIMENSION s*) | EXTENDS s
      | PASS s
        -> begin (* <keyword> = *)
          [%debug_log "checking if %s is an identifier" (Token.rawtoken_to_string !tok)];
          match peek_next() with
          | EQ -> begin
              [%debug_log "<keyword> --> <identifier> : <keyword> '='"];
              tok := IDENTIFIER s
          end
          | _ -> ()
      end
      | WHERE s | DATA s | BIND s | TO s | DIMENSION s | CODIMENSION s
      | ASSOCIATE s | BLOCK s | CRITICAL s
      (*| INTEGER s | REAL s | COMPLEX s | LOGICAL s*) | KINDED_TYPE_SPEC s
      | DOUBLE_PRECISION s | DOUBLE s| CHARACTER s | BYTE s
      | ENTRY s | FIND s | DO s | CASE s | POINTER s | IF s | FORMAT s
      | DELETE s | UNLOCK s | ENCODE s | DECODE s | REWRITE s | ACCEPT s
      | FINAL s | GENERIC s | LOCK s | SYNC s | CLASS s | TYPE s
        -> begin (* <keyword> ('('...')')? ('='|'%') *)
          let is_format =
            match !tok with
            | FORMAT _ -> true
            | _ -> false
          in
          match peek_next() with
          | LPAREN -> begin
              if is_format && (not env#in_format_context) then
                env#enter_format_context;

              begin
                let nth = ref 2 in
                let depth = ref 1 in
                try
                  while true do
                    let nth_tok = tokensrc#peek_nth_rawtok !nth in
                    begin
                      match nth_tok with
                      | LPAREN -> incr depth
                      | RPAREN -> begin
                          decr depth;
                          if !depth = 0 then begin
                            begin
                              match tokensrc#peek_nth_rawtok (!nth+1) with
                              | EQ | PERCENT -> begin
                                  [%debug_log "<keyword> --> <identifier> : <keyword> ('('...')')? ('='|'%%')"];
                                  if is_format then
                                    env#exit_format_context;
                                  tok := IDENTIFIER s
                              end
                              | _ -> ()
                            end;
                            raise Exit
                          end
                      end
                      | EOL | SEMICOLON | NOTHING | EOF _ -> raise Exit
                      | _ -> ()
                    end;
                    incr nth
                  done
                with
                  Exit -> ()
              end
          end
          | EQ -> begin
              [%debug_log "<keyword> --> <identifier> : <keyword> ="];
              tok := IDENTIFIER s
          end
          | PERCENT -> begin
              if (not env#in_structure_context) || (not is_head_of_stmt_) then begin
                [%debug_log "<keyword> --> <identifier> : <keyword> %%"];
                tok := IDENTIFIER s
              end
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    if env#current_source#lang_config#is_fixed_source_form then begin
      match !tok with
      | INT_LITERAL _ -> begin
          match peek_next() with
          | HOLLERITH(h, true) -> begin
              [%debug_log "<int-literal><hollerith-partial> --> <hollerith>"];
              tok := HOLLERITH(h, false);
              let _, loc' = discard() in
              loc := merge_locs !loc loc'
          end
          | _ -> ()
      end
      | IDENTIFIER str0 -> begin (* <identifier>(<pp-identifier>|'_'|<int-literal>)+ --> <keyword>|<identifier> *)
	  let str = ref str0 in
	  try
	    while true do
	      match peek_next() with
	      | CONTINUED_IDENTIFIER str1
              | PP_IDENTIFIER str1
              | PP_UNDERSCORE str1
              | INT_LITERAL str1
              (*| IDENTIFIER str1 (* may break pp-macro-id:WRITE rule *)*)
                -> begin
                  [%debug_log "<identifier>(<pp-identifier>|'_'|<int-literal>|<identifier>)+ --> <keyword>|<identifier>"];
                  str := !str^str1;
                  try
		    tok := Ulexer._find_keyword !str;
                    let _, loc' = discard() in
		    loc := merge_locs !loc loc';
                    raise Exit
                  with
                    Not_found ->
                      tok := IDENTIFIER !str;
                      let _, loc' = discard() in
		      loc := merge_locs !loc loc';
	        end
	      | _ -> raise Exit
	    done;
	    assert false
	  with
	    Exit -> ()
      end
      | FUNCTION str0 | SUBROUTINE str0 -> begin (* FUNCTION|SUBROUTINE -> <identifier> *)
	  let str = ref str0 in
          let nth = ref 1 in
	  try
	    while true do
	      match tokensrc#peek_nth_rawtok !nth with
              | COMMA -> raise Exit
              | EOL | SEMICOLON -> begin
                  match !tok with
                  | FUNCTION _ -> raise Exit
                  | SUBROUTINE _ -> raise Not_found (* subroutines may have no arguments *)
                  | _ -> assert false
              end
	      | IDENTIFIER str1 | PP_IDENTIFIER str1 | INT_LITERAL str1 -> begin
                  str := !str^str1;
                  [%debug_log "[FUNCTION|SUBROUTINE -> <identifier>] str=\"%s\"" !str];
                  incr nth
	      end
	      | x ->
                  let _ = x in
                  [%debug_log "[FUNCTION|SUBROUTINE -> <identifier>] %s" (Token.rawtoken_to_string x)];
                  raise Not_found
	    done
	  with
          | Not_found -> ()
	  | Exit ->
              [%debug_log "FUNCTION|SUBROUTINE --> <identifier>"];
              tok := IDENTIFIER !str;
              if !nth > 1 then begin
                for _ = 0 to !nth - 1 do
                  ignore (discard())
                done;
                let _, loc' = discard() in
	        loc := merge_locs !loc loc'
              end
      end
      | SLASH -> begin (* '/' '/' --> '//' *)
          match last_tok with
          | SLASH -> ()
          | _ -> begin
              match peek_next() with
              | SLASH -> begin
                  let tok2 = tokensrc#peek_nth_rawtok 2 in
                  match tok2 with
                  | SLASH -> ()
                  | _ -> begin
                      if not env#in_format_context then begin
                        [%debug_log "'/' '/' --> '//'"];
                        tok := SLASH_SLASH;
                        let _, loc' = discard() in
	                loc := merge_locs !loc loc'
                      end
                  end
              end
              | _ -> ()
          end
      end
      | _ -> ()
    end;

    begin (* <char-literal>+ --> <char-literal> *)
      match !tok with
      | CHAR_LITERAL str0 -> begin
          [%debug_log "<char-literal>+ --> <char-literal>"];
	  let str = ref str0 in
	  try
	    while true do
	      match peek_next() with
	      | CHAR_LITERAL str1 -> begin
                  str := (Xstring.rstrip ~strs:quotes !str)^(Xstring.lstrip ~strs:quotes str1);
		  tok := CHAR_LITERAL !str;
                  let _, loc' = discard() in
		  loc := merge_locs !loc loc'
	      end
	      | _ -> raise Exit
	    done;
	    assert false
	  with
	    Exit -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | PREFIX_SPEC s
      (*| PURE s | ELEMENTAL s | RECURSIVE s | IMPURE s*) -> begin (* <keyword> --> <identifier> *)
          let n = ref 1 in
          try
            while true do
	      let tok', loc' = tokensrc#peek_nth !n in
              let _ = loc' in
	      [%debug_log "peeking %s token: %s[%s]"
                (num_to_ordinal !n) (Token.rawtoken_to_string tok') (Loc.to_string loc')];
	      begin
	        match tok' with
                | EOL | SEMICOLON | NOTHING | EOF _ ->
                    raise Not_found

                | FUNCTION _ | SUBROUTINE _ | EOP ->
                    raise Exit

                | _ -> incr n
              end
            done
          with
          | Exit -> ()
          | Not_found ->
              [%debug_log "PURE|ELEMENTAL|RECURSIVE|IMPURE --> <identifier>"];
              tok := IDENTIFIER s
      end
      | _ -> ()
    end;

    begin (* '$' <keyword>|<identifier>|<pp-identifier> --> <identifier> *)
      match !tok with
      | DOLLAR -> begin
          let next_tok, next_loc = tokensrc#peek_nth 1 in
          if !loc.Loc.end_offset + 1 = next_loc.Loc.start_offset then begin
            try
              let s =
                Token.get_keyword
                  ~elsef:(function IDENTIFIER x | PP_IDENTIFIER x -> x | _ -> raise Not_found)
                  next_tok
              in
              let new_s = "$"^s in
              tok := IDENTIFIER new_s;
              let _ = discard() in
              loc := merge_locs !loc next_loc;
            with
              Not_found -> ()
          end
      end
      | _ -> ()
    end;
    begin (* <identifier> ('$' <keyword>|<identifier>|<pp-identifier>)+ --> <identifier> *)
      match !tok with
      | IDENTIFIER s -> begin
          match peek_next() with
          | DOLLAR -> begin (* some compilers interpret '$' as an extra alphabet *)
              [%debug_log "<identifier> ('$' <keyword>|<identifier>|<pp-identifier>)+ --> <identifier>"];
              let prev_is_dollar = ref false in
              let prev_s = ref s in
              try
                while true do
                  let nth_tok, nth_loc = tokensrc#peek_nth 1 in
                  if !loc.Loc.end_offset + 1 = nth_loc.Loc.start_offset then begin
                    match nth_tok with
                    | DOLLAR -> begin
                        let new_s = !prev_s^"$" in
                        tok := IDENTIFIER new_s;
                        let _ = discard() in
                        loc := merge_locs !loc nth_loc;
                        prev_is_dollar := true;
                        prev_s := new_s
                    end
                    | _ -> begin
                        try
                          let s' =
                            Token.get_keyword
                              ~elsef:(function IDENTIFIER x | PP_IDENTIFIER x -> x | _ -> raise Not_found)
                              nth_tok
                          in
                          if !prev_is_dollar then begin
                            let new_s = !prev_s^s' in
                            tok := IDENTIFIER new_s;
                            let _ = discard() in
                            loc := merge_locs !loc nth_loc;
                            prev_is_dollar := false;
                            prev_s := new_s
                          end
                          else
                            raise Exit
                        with
                          Not_found -> raise Exit
                    end
                  end
                  else
                    raise Exit
                done
              with
                Exit -> ()
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    if is_head_of_stmt_ then begin
      match !tok, peek_next() with
      | IDENTIFIER s0, IDENTIFIER _ -> begin (* <identifier> ... ',' <char-literal> *)
          let nth = ref 2 in
          let depth = ref 0 in
          try
            while true do
              let nth_tok = tokensrc#peek_nth_rawtok !nth in
              begin
                match nth_tok with
                | EOL | SEMICOLON | NOTHING | EOF _ -> raise Exit

                | LPAREN -> incr depth

                | RPAREN -> decr depth

                | COMMA -> begin
                    if !depth = 0 then begin
                      let nth_tok' = tokensrc#peek_nth_rawtok (!nth+1) in
                      match nth_tok' with
                      | CHAR_LITERAL _ -> begin
                          [%debug_log "<identifier> --> <pp-macro-read-print>"];
                          tok := PP_MACRO_READ_PRINT s0;
                          raise Exit
                      end
                      | _ -> ()
                    end
                end
                | _ -> ()
              end;
              incr nth
            done
          with
            Exit -> ()
      end
      | _ -> ()
    end;

    begin (* <identifier>|BLOCK|DOUBLE --> <identifier>|<keyword>|<letter>|<pp-identifier> *)
      match !tok with
      | IDENTIFIER s | BLOCK s | DOUBLE s -> begin
          begin
	    match peek_next() with
            (*| COMPLEX s'*) | KINDED_TYPE_SPEC s'
	    | IDENTIFIER s' | DATA s' | CASE s' | TO s' | PRECISION s' | FILE s'
            | TYPE s'
              -> begin (* <identifier> --> <pp-identifier>|<keyword> *)
	        try
		  tok := find_separated_keyword [s; s'];
                  [%debug_log "(<identifier>|<keyword>) (<identifier>|<keyword>) --> <keyword>"];
                  let _, loc' = discard() in
		  loc := merge_locs !loc loc'
	        with
		  Not_found ->
                    begin
                      match !tok, (peek_next()) with
                      | IDENTIFIER s0, IDENTIFIER s0' ->
                          if env#in_format_context then begin
                            if env#current_source#lang_config#is_fixed_source_form then begin
                              [%debug_log "<identifier>(<identifier>|<int-literal>)+ --> <edit-desc>"];
                              let str = ref s0 in
                              let nth = ref 1 in
                              try
	                        while true do
                                  begin
	                          match tokensrc#peek_nth_rawtok !nth with
	                            | IDENTIFIER str1 | INT_LITERAL str1 -> begin
                                        str := !str^str1;
                                        try
		                          tok := find_edit_desc !str;
                                        with
                                          Not_found -> ()
	                            end
	                            | _ -> raise Exit
                                  end;
                                  incr nth
	                        done
	                      with
	                        Exit ->
                                  let loc' = ref !loc in
                                  for _ = 1 to !nth - 1 do
                                    let _, l = discard() in
                                    loc' := l
                                  done;
                                  loc := merge_locs !loc !loc'
                            end
                          end
                          else begin (* not env#in_format_context *)
                            if is_head_of_stmt_ then begin
                              if
                                env#current_source#lang_config#is_fixed_source_form &&
                                String.lowercase_ascii s0 = "go" &&
                                Str.string_match toxxx_pat (String.lowercase_ascii s0') 0
                              then begin
                                [%debug_log "GO TO<x> --> GO_TO <x>"];
                                let _, l0 = discard() in
                                let l' = Loc.collapse_backward ~len:2 l0 in
                                tokensrc#prepend (INT_LITERAL (Str.matched_group 1 s0'), l');
                                let s_ =
                                  s0^
                                  (String.make (l0.Loc.start_offset-(!loc).Loc.end_offset-1) ' ')^
                                  (String.sub s0' 0 2)
                                in
                                tok := GO_TO s_;
                                loc := merge_locs !loc (Loc.collapse_forward ~len:2 l0)
                              end
                              else begin
                                [%debug_log "<identifier> --> <pp-identifier>"];
                                tok := PP_IDENTIFIER s0
                              end
                            end
                            else begin
                              let is_kind_size =
                                match last_tok with
                                | STAR -> begin
                                    match tokensrc#get_prev_rawtok with
                                      (*| INTEGER _ | REAL _ | COMPLEX _ | LOGICAL _*)
                                    | KINDED_TYPE_SPEC _ -> true
                                    | _ -> false
                                end
                                | _ -> false
                              in
                              [%debug_log "is_kind_size=%B" is_kind_size];

                              if
                                env#current_source#lang_config#is_fixed_source_form &&
                                not is_kind_size
                              then begin
                                [%debug_log "<identifier>(<identifier>|<int-literal>)+ --> <identifier>"];
                                let str = ref (s0^s0') in
                                tok := Ulexer.find_keyword !str;
                                let _, loc' = discard() in
		                loc := merge_locs !loc loc';
                                try
	                          while true do
	                            match peek_next() with
	                            | IDENTIFIER str1 | INT_LITERAL str1 -> begin
                                        str := !str^str1;
                                        try
		                          tok := Ulexer._find_keyword !str;
                                          let _, loc' = discard() in
		                          loc := merge_locs !loc loc';
                                          raise Exit
                                        with
                                          Not_found ->
                                            tok := IDENTIFIER !str;
                                            let _, loc' = discard() in
		                            loc := merge_locs !loc loc'
	                            end
	                            | _ -> raise Exit
	                          done
	                        with
	                          Exit -> ()
                              end (* if env#current... *)
                            end (* if not is_head_of_stmt *)
                          end (* if not env#in_format_context *)
                      | _ -> ()
                    end
	    end
	    | EQ -> begin (* <identifier> --> <connect-spec>|<close-spec>|<position-spec>|<io-control-spec>|<inquire-spec> *)
	        if env#in_open_context then begin
                  [%debug_log "<identifier>|<keyword> --> <connect-spec>"];
		  tok := find_connect_spec_keyword s
	        end
	        else if env#in_close_context then begin
                  [%debug_log "<identifier>|<keyword> --> <close-spec>"];
		  tok := find_close_spec_keyword s
	        end
	        else if env#in_position_context then begin
                  [%debug_log "<identifier>|<keyword> --> <position-spec>"];
		  tok := find_position_spec_keyword s
	        end
	        else if env#in_flush_context then begin
                  [%debug_log "<identifier>|<keyword> --> <flush-spec>"];
		  tok := find_flush_spec_keyword s
	        end
	        else if env#in_io_control_context then begin
                  [%debug_log "<identifier>|<keyword> --> <io-control-spec>"];
		  tok := find_io_control_spec_keyword s
	        end
	        else if env#in_inquire_context then begin
                  [%debug_log "<identifier>|<keyword> --> <inquire-spec>"];
		  tok := find_inquire_spec_keyword s
	        end
	        else if env#in_wait_context then begin
                  [%debug_log "<identifier>|<keyword> --> <wait-spec>"];
		  tok := find_wait_spec_keyword s
	        end
	        else if env#in_bind_context then begin
                  [%debug_log "<identifier>|<keyword> --> <language-binding-spec>"];
		  tok := find_language_binding_spec_keyword s
	        end
	    end
	    | _ -> ()
          end;
	  if env#in_letter_context then begin (* <identifier> --> <letter> *)
            [%debug_log "<identifier>|<keyword> --> <letter>"];
	    tok := LETTER s
	  end;
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | REAL_LITERAL real -> begin
          match peek_next() with
          | INT_LITERAL int -> begin (* <real-literal><int-literal>+ --> <real-literal> *)
              [%debug_log "<real-literal><int-literal>+ --> <real-literal>"];
              let nth = ref 2 in
              let prev_s = ref (real^int) in
              let term() =
                tok := REAL_LITERAL !prev_s;
                let loc' = ref !loc in
                for _ = 1 to (!nth-1) do
                  let _, loc'' = discard() in
                  loc' := loc''
                done;
                loc := merge_locs !loc !loc';
                raise Exit
              in
              try
                while true do
                  [%debug_log "separated real literal detection in progress: \"%s\"" !prev_s];
                  let nth_tok = tokensrc#peek_nth_rawtok !nth in
                  match nth_tok with
                  | INT_LITERAL i -> begin
                      prev_s := (!prev_s)^i;
                      incr nth
                  end
                  | REAL_LITERAL r -> begin
                      if not (String.contains r '.') then begin
                        prev_s := (!prev_s)^r;
                        incr nth
                      end
                      else
                        term()
                  end
                  | _ -> term()
                done
              with
                Exit -> ()
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    let check_exponent ?(discard_n_tokens=0) nth_ini significand next_tok =
      [%debug_log "nth_ini=%d significand=\"%s\" next_tok=%s"
        nth_ini significand (Token.rawtoken_to_string next_tok)];

      match next_tok with
      | IDENTIFIER s -> begin
          let sl = String.lowercase_ascii s in
          if sl = "d" || sl = "e" then begin
            let nth = ref nth_ini in
            let prev_s = ref (significand^s) in
            try
              while true do
                [%debug_log "separated real literal detection in progress: \"%s\" nth=%d" !prev_s !nth];
                let nth_tok, nth_loc = tokensrc#peek_nth !nth in
                match nth_tok with
                | PLUS -> begin
                    prev_s := (!prev_s)^"+";
                    incr nth
                end
                | MINUS -> begin
                    prev_s := (!prev_s)^"-";
                    incr nth
                end
                | INT_LITERAL s' | CONTINUED_IDENTIFIER s' -> begin
                    [%debug_log " --> <real-literal>"];
                    let new_s = !prev_s^s' in
                    tok := REAL_LITERAL new_s;
                    for _ = 1 to !nth+discard_n_tokens do
                      ignore (discard())
                    done;
                    loc := merge_locs !loc nth_loc;
                    raise Exit
                end
                | _ -> raise Exit
              done
            with
              Exit -> ()
          end
          else if Str.string_match exponent_pat sl 0 then begin
            [%debug_log " --> <real-literal>"];
            tok := REAL_LITERAL (significand^s);
            for _ = 1 to discard_n_tokens do
              ignore (discard())
            done;
            let _, loc' = discard() in
            loc := merge_locs !loc loc'
          end
      end
      | PP_IDENTIFIER s -> begin
          let nth = ref nth_ini in
          let prev_s = ref (significand^s) in
          try
            while true do
              [%debug_log "separated real literal detection in progress: \"%s\" nth=%d" !prev_s !nth];
              let nth_tok, nth_loc = tokensrc#peek_nth !nth in
              match nth_tok with
              | PLUS -> begin
                  prev_s := (!prev_s)^"+";
                  incr nth
              end
              | MINUS -> begin
                  prev_s := (!prev_s)^"-";
                  incr nth
              end
              | INT_LITERAL s' | CONTINUED_IDENTIFIER s' -> begin
                  [%debug_log " --> <real-literal>"];
                  let new_s = !prev_s^s' in
                  tok := REAL_LITERAL new_s;
                  for _ = 1 to !nth+discard_n_tokens do
                    ignore (discard())
                  done;
                  loc := merge_locs !loc nth_loc;
                  raise Exit
              end
              | _ -> raise Exit
            done
          with
            Exit -> ()
      end
      | REAL_LITERAL r ->
          [%debug_log " --> <real-literal>"];
          tok := REAL_LITERAL (significand^r);
          for _ = 1 to discard_n_tokens do
            ignore (discard())
          done;
          let _, loc' = discard() in
          loc := merge_locs !loc loc'
      | _ -> ()
    in (* check_exponent *)

    begin
      match !tok with
      | INT_LITERAL int -> begin
          let next_tok = peek_next() in
          match next_tok with
          | INT_LITERAL s -> begin (* <int-literal>+ --> <int-literal> *)
              [%debug_log "<int-literal>+<real-literal>? --> <int-literal>"];
              let nth = ref 2 in
              let prev_s = ref (int^s) in
              try
                while true do
                  [%debug_log "separated int literal detection in progress: \"%s\"" !prev_s];
                  let nth_tok = tokensrc#peek_nth_rawtok !nth in
                  match nth_tok with
                  | INT_LITERAL s' -> begin
                      prev_s := (!prev_s)^s';
                      incr nth
                  end
                  | REAL_LITERAL s' -> begin
                      tok := REAL_LITERAL ((!prev_s)^s');
                      let loc' = ref !loc in
                      for _ = 1 to !nth do
                        let _, loc'' = discard() in
                        loc' := loc''
                      done;
                      loc := merge_locs !loc !loc';
                      raise Exit
                  end
                  | _ -> begin
                      tok := INT_LITERAL !prev_s;
                      let loc' = ref !loc in
                      for _ = 1 to (!nth-1) do
                        let _, loc'' = discard() in
                        loc' := loc''
                      done;
                      loc := merge_locs !loc !loc';
                      raise Exit
                  end
                done
              with
                Exit -> ()
          end
          | DOT -> begin (* <int-literal> '.' <exponent> --> <real-literal> *)
              let tok2 = tokensrc#peek_nth_rawtok 2 in
              match tok2 with
              | INT_LITERAL s -> begin
                  [%debug_log "<int-literal> '.' <int-literal> --> <real-literal>"];
                  tok := REAL_LITERAL (int^"."^s);
                  let _ = discard() in
                  let _, loc' = discard() in
                  loc := merge_locs !loc loc'
              end
              | PLUS | MINUS | STAR | SLASH -> begin
                  [%debug_log "<int-literal>. --> <real-literal>"];
                  tok := REAL_LITERAL (int^".");
                  let _, loc' = discard() in
                  loc := merge_locs !loc loc'
              end
              | _ -> begin
                  [%debug_log "<int-literal> '.' <exponent>"];
                  check_exponent (*~discard_n_tokens:1*) 3 (int^".") tok2
              end
          end
          | REAL_LITERAL r -> begin (* <int-literal> <real-literal> --> <real-literal> *)
              [%debug_log "<int-literal><real-literal> --> <real-literal>"];
              tok := REAL_LITERAL (int^r);
              let _, loc' = discard() in
              loc := merge_locs !loc loc'
          end
          | DATA_EDIT_DESC desc -> begin (* <int-literal><data-edit-desc> --> <data-edit-desc> *)
              [%debug_log "<int-literal><data-edit-desc> --> <data-edit-desc>"];
              tok := DATA_EDIT_DESC (int^desc);
              let _, loc' = discard() in
              loc := merge_locs !loc loc'
          end
          | IDENTIFIER _ -> begin
              let tok2 = tokensrc#peek_nth_rawtok 2 in
              match tok2 with
              | PLUS | MINUS | STAR | SLASH | RPAREN -> begin
                  [%debug_log "<int-literal><identifier>"];
                  check_exponent 2 int next_tok
              end
              | _ -> ()
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    begin (* <real-literal><exponent> --> <real-literal> *)
      match !tok with
      | REAL_LITERAL real -> begin
          [%debug_log "<real-literal>."];
          check_exponent 2 real (peek_next())
      end
      | _ -> ()
    end;

    let get_keyword_or_ident =
      Token.get_keyword ~elsef:(function IDENTIFIER s -> s | _ -> raise Not_found)
    in
    let get_keyword_or_ident_or_continued_ident =
      Token.get_keyword
        ~elsef:
        (function
          | IDENTIFIER s | CONTINUED_IDENTIFIER s -> s
          | _ -> raise Not_found)
    in

    begin
      match !tok with
      | DOT -> begin
          try
            let s = get_keyword_or_ident (peek_next()) in
            [%debug_log "'.' (<identifier>|<keyword>)+ '.' --> <dotted-identifier>"];
            let nth = ref 2 in
            let prev_s = ref ("."^s) in
            try
              while true do
                [%debug_log "separated dotted identifier detection in progress: \"%s\"" !prev_s];
                let nth_tok, nth_loc = tokensrc#peek_nth !nth in
                match nth_tok with
                | DOT -> begin
                    let new_s = !prev_s^"." in
                    tok := Ulexer.find_dotted_keyword new_s;
                    for _ = 1 to !nth do
                      ignore (discard())
                    done;
                    loc := merge_locs !loc nth_loc;
                    raise Exit
                end
                | _ -> begin
                    try
                      let s' = get_keyword_or_ident_or_continued_ident nth_tok in
                      prev_s := (!prev_s)^s';
                      incr nth
                    with
                      Not_found -> raise Exit
                end
              done
            with
              Exit -> ()
          with
            Not_found -> ()
      end
      | _ -> ()
    end;

    if env#current_source#lang_config#is_fixed_source_form then begin
      match !tok with
      | INT_LITERAL i -> begin
          match peek_next() with
          | IDENTIFIER s -> begin
              match tokensrc#peek_nth_rawtok 2 with
              | PLUS | MINUS | STAR | SLASH | RPAREN -> begin
                  let sl = String.lowercase_ascii s in
                  if sl = "b" then begin (* old style octal constant *)
                    [%debug_log "<int-literal>B --> <int-literal>"];
                    tok := INT_LITERAL (i^s);
                    let _, loc' = discard() in
                    loc := merge_locs !loc loc'
                  end
              end
              | _ -> ()
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    begin (* <keyword><keyword> --> <keyword> *)
      match !tok with
      | ELSE s | END s (*| IN s*) | INTENT_SPEC s -> begin
	  match peek_next() with
	  | IF s' | BLOCK_DATA s' | DO s' | FORALL s' | FUNCTION s'
	  | INTERFACE s' | MODULE s' | SUBMODULE s' | PROCEDURE s' | PROGRAM s'
	  | SUBROUTINE s' | TYPE s' | WHERE s' (*| OUT s'*)
          | INTENT_SPEC s' | ASSOCIATE s' | CRITICAL s' | ENUM s'
	  | IDENTIFIER s' | STRUCTURE s' | UNION s' | MAP s' -> begin
	      try
		tok := find_separated_keyword [s; s'];
                [%debug_log "(ELSE|END|IN)<keyword> --> <keyword>"];
                let _, loc' = discard() in
		loc := merge_locs !loc loc'
	      with
		Not_found -> ()
	  end
          | BLOCK s' -> begin
              match !tok with
              | END _ -> begin
                  let second_tok = tokensrc#peek_nth_rawtok 2 in
                  match second_tok with
                  | DATA s'' -> begin
                      [%debug_log "END BLOCK DATA --> <keyword>"];
                      tok := END_BLOCK_DATA (String.concat "" [s; s'; s'']);
                      let _ = discard() in
                      let _, loc' = discard() in
		      loc := merge_locs !loc loc'
                  end
                  | _ -> begin
	              try
		        tok := find_separated_keyword [s; s'];
                        [%debug_log "END BLOCK --> <keyword>"];
                        let _, loc' = discard() in
		        loc := merge_locs !loc loc'
	              with
		        Not_found -> ()
                  end
              end
              | _ -> ()
          end
	  | _ -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | IDENTIFIER s | PP_IDENTIFIER s when begin
          peek_next() == LPAREN &&
          match last_tok with
          | IMPLICIT _ -> true
          | _ -> env#in_implicit_context && not env#in_letter_context
      end -> begin
          [%debug_log "IMPLICIT <identifier>|<pp-identifier> --> IMPLICIT <pp-macro-id:type-spec>"];
          tok := PP_MACRO_ID(M.K_TYPE_SPEC, s)
      end
      | LPAREN -> begin (* '(' --> <lparen-XXX> *)
          if env#in_implicit_context then begin
            let single_lparen = ref true in
            let level = ref 1 in
            let nth = ref 2 in
            begin
              try
                while true do
                  let nth_tok = tokensrc#peek_nth_rawtok !nth in
                  [%debug_log "implicit spec detection in progress: nth_tok=\"%s\""
                    (Token.rawtoken_to_string nth_tok)];
                  match nth_tok with
                  | RPAREN ->
                      decr level;
                      incr nth

                  | LPAREN ->
                      single_lparen := false;
                      raise Exit

                  | COMMA ->
                      if !level = 0 then
                        raise Exit
                      else
                        incr nth

                  | EOL | SEMICOLON | NOTHING | EOF _ -> raise Exit

                  | _ -> incr nth
                done
              with
                Exit -> ()
            end;
            if !single_lparen then begin
              [%debug_log "'(' --> <lparen-implicit>"];
              tok := LPAREN__IMPLICIT;
              env#enter_letter_context
            end
	  end
          else begin
            match last_tok with
            | GO_TO _ -> begin
                [%debug_log "'(' --> <lparen-goto>"];
                tok := LPAREN__GO_TO
            end
            | READ _ | WRITE _ | REWRITE _ | FIND _ | ACCEPT _
            | PP_MACRO_ID_RW(M.K_WRITE, _|M.K_READ_WRITE, _)
            | PP_MACRO_WRITE _ | PP_MACRO_READ_WRITE _
              -> begin
                [%debug_log "'(' --> <lparen-io-control-spec>"];
                tok := LPAREN__io_control_spec
              end
            | REWIND _ | END_FILE _ | BACKSPACE _
            | DELETE _ | UNLOCK _ | ENCODE _ | DECODE _
              -> begin
                [%debug_log "'(' --> <lparen-position-spec>"];
                tok := LPAREN__position_spec
              end
            | FLUSH _ -> begin
                [%debug_log "'(' --> <lparen-flush-spec>"];
                tok := LPAREN__flush_spec
            end

            | _ -> begin
                match peek_next() with
                | SLASH -> begin (* '(' '/' --> '(/' *)
                    match last_tok with
                    | FORMAT _ | IDENTIFIER _ | OPERATOR _ | LINDA_TYPEOF _ -> ()
                    | _ ->
                        if not env#in_format_context then begin
                          [%debug_log "'(' '/' --> '(/'"];
                          tok := LPAREN_SLASH;
                          let _, loc' = discard() in
		          loc := merge_locs !loc loc';
                          env#enter_array_ctor_context
                        end
                end
                | _ -> ()
            end
          end
      end
      | COMMA -> begin (* ',' '/' --> <comma-slash> '/' *)
          match peek_next() with
          | SLASH ->
              if env#in_slash_name_context (* not env#in_format_context *) then begin
                [%debug_log "',' '/' --> <comma-slash> '/'"];
                tok := COMMA__SLASH
              end
          | _ -> ()
      end

      | _ -> ()
    end;

    begin
      match !tok with
      | PERCENT -> begin (* '%'<identifier> --> <identifier> for %VAL, %REF, %LOC, %DESCR, %FILL of Compaq Fortran *)
          [%debug_log "%% (VAL|REF|LOC|DESCR|FILL) --> <identifier>"];
          match last_tok with
          | IDENTIFIER _ | RPAREN -> ()
          | _ ->
              match peek_next() with
              | IDENTIFIER s -> begin
                  tok := IDENTIFIER ("%"^s);
                  let _, loc' = discard() in
		  loc := merge_locs !loc loc'
              end
              | _ -> ()
      end
      | _ -> ()
    end;

    if env#in_format_context then begin
      [%debug_log "in_format_context=true"];
      if env#in_vfe_context then begin
        match !tok with
        | DATA_EDIT_DESC d
        | POSITION_EDIT_DESC d -> begin
            if not (A.startswith_digits d) then begin
              [%debug_log "<data-edit-desc>|<position-edit-desc> --> <identifier>"];
              tok := IDENTIFIER d
            end
        end
        | _ -> ()
      end
      else begin (* not env#in_vfe_context *)
        match !tok with
        | IDENTIFIER s -> begin
            try
              tok := (find_edit_desc s);
              [%debug_log "<identifier> --> <edit-desc>"]
            with
              Not_found -> ()
        end
        | INT_LITERAL i -> begin
            match peek_next() with
            | IDENTIFIER s -> begin
                try
                  let desc = find_edit_desc s in
                  [%debug_log "<int-literal><identifier> --> <edit-desc>"];
                  let desc' =
                    match desc with
                    | DATA_EDIT_DESC d     -> DATA_EDIT_DESC (i^d)
                    | POSITION_EDIT_DESC d -> POSITION_EDIT_DESC (i^d)
                    | _ -> assert false
                  in
                  tok := desc';
                  let _, loc' = discard() in
                  loc := merge_locs !loc loc'
                with
                  Not_found -> ()
            end
            | _ -> ()
        end
        | _ -> ()
      end
    end;

    if env#in_format_context then begin
      [%debug_log "in_format_context=true"];
      match !tok with
      | IDENTIFIER s | REAL_LITERAL s | DATA_EDIT_DESC s -> begin
          match peek_next() with
          | LT -> begin
              [%debug_log "<identifier>|<real-literal> '<' --> <vfe-begin>"];
              tok := (VFE_BEGIN s);
              let _, loc' = discard() in
              loc := merge_locs !loc loc'
          end
          | REAL_LITERAL r -> begin (* <identifier><real-literal> --> <data-edit-desc> *)
              [%debug_log "<identifier><real-literal> --> <data-edit-desc>"];
              tok := DATA_EDIT_DESC (s^r);
              let _, loc' = discard() in
	      loc := merge_locs !loc loc'
          end
          | DOT -> begin (* <identifier>|<real-literal> '.' <int-literal><identifier>? --> <data-edit-desc> *)
              match tokensrc#peek_nth_rawtok 2 with
              | INT_LITERAL i -> begin
                  [%debug_log "<identifier>|<real-literal> '.' <int-literal><identifier>? --> <data-edit-desc>"];
                  let str = s^"."^i in
                  tok := DATA_EDIT_DESC str;
                  let _ = discard() in
                  let _, loc' = discard() in
	          loc := merge_locs !loc loc';
                  match peek_next() with
                  | IDENTIFIER e -> begin
                      if Xstring.startswith e "E" || Xstring.startswith e "e" then begin
                        tok := DATA_EDIT_DESC (str^e);
                        let _, loc' = discard() in
	                loc := merge_locs !loc loc'
                      end
                  end
                  | _ -> ()
              end
              | LT -> begin
                  [%debug_log "<identifier>|<real-literal> '.' '<' --> <vfe-begin>"];
                  tok := (VFE_BEGIN (s^"."));
                  let _ = discard() in
                  let _, loc' = discard() in
                  loc := merge_locs !loc loc'
              end
              | _ -> ()
          end
          | _ -> ()
      end
      | LT -> begin
          [%debug_log "'<' --> <vfe-begin>"];
          tok := VFE_BEGIN ""
      end
      | GT -> begin
          match peek_next() with
          | REAL_LITERAL r -> begin
              [%debug_log "'>' <real-literal> --> <vfe-end>"];
              tok := VFE_END r;
              let _, loc' = discard() in
	      loc := merge_locs !loc loc'
          end
          | DOT -> begin
              match tokensrc#peek_nth_rawtok 2 with
              | INT_LITERAL i -> begin
                  [%debug_log "'>' '.' <int-literal> --> <vfe-end>"];
                  let str = "."^i in
                  tok := VFE_END str;
                  let _ = discard() in
                  let _, loc' = discard() in
	          loc := merge_locs !loc loc';
                  match peek_next() with
                  | IDENTIFIER e -> begin
                      if Xstring.startswith e "E" || Xstring.startswith e "e" then begin
                        tok := VFE_END (str^e);
                        let _, loc' = discard() in
	                loc := merge_locs !loc loc'
                      end
                  end
                  | _ -> ()
              end
              | _ -> begin
                  [%debug_log "'>' --> <vfe-end>"];
                  tok := VFE_END ""
              end
          end
          | _ -> begin
              [%debug_log "'>' --> <vfe-end>"];
              tok := VFE_END ""
          end
      end
      | _ -> ()
    end
    else begin
      match !tok with
      | SLASH -> begin (* '/' ')' --> <slash-rparen> *)
          match peek_next() with
          | RPAREN ->
              if env#in_array_ctor_context then begin
                [%debug_log "'/' ')' --> <slash-rparen>"];
                tok := SLASH_RPAREN;
                let _, loc' = discard() in
		loc := merge_locs !loc loc'
              end
          | _ -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | PASS s -> begin
          match peek_next() with
          | COLON -> begin
              [%debug_log "<keyword> --> <identifier>"];
              tok := IDENTIFIER s
          end
          | _ -> ()
      end
      | ACCEPT s when begin
          is_head_of_stmt_ && peek_next() == COLON ||
          match last_tok with
          | ELSE _ | END_IF _ -> true
          | _ -> false
      end -> begin
        [%debug_log "<keyword> --> <identifier>"];
        tok := IDENTIFIER s
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | IDENTIFIER s -> begin (* <identifier> --> <(do|if|where|forall|case|select-type|associate|block)-construct-name> *)
          match peek_next() with
          | COLON -> begin
              if not env#in_paren_context then begin
                [%debug_log "<identifier> --> <(do|if|where|forall|case|select-type|associate|block)-construct-name>"];
                let second_tok = tokensrc#peek_nth_rawtok 2 in
                match second_tok with
                | DO _ | IF _ | WHERE _ | FORALL _ | SELECT_CASE _ | SELECT_TYPE _
                | ASSOCIATE _ | BLOCK _ | CRITICAL _ ->
                    tok := CONSTRUCT_NAME s

                | IDENTIFIER s' -> begin
                    if (String.lowercase_ascii s') = "select" then begin
                      let third_tok = tokensrc#peek_nth_rawtok 3 in
                      match third_tok with
                      | CASE _ | TYPE _ -> tok := CONSTRUCT_NAME s
                      | _ -> ()
                    end
                end
                | _ -> ()
              end
          end
          | _ -> ()
      end
      | DOT -> begin (* '.' (<int-literal>+|<real-literal>|<identifier>) --> <real-literal> *)
          let rec doit str =
            match peek_next() with
            | INT_LITERAL i -> begin
                [%debug_log "'.' <int-literal> --> <real-literal>"];
                let s = str^i in
                tok := REAL_LITERAL s;
                let _, loc' = discard() in
		loc := merge_locs !loc loc';
                doit s
            end
            | REAL_LITERAL r -> begin
                if not (String.contains r '.') then begin
                  [%debug_log "'.' <real-literal> --> <real-literal>"];
                  tok := REAL_LITERAL (str^r);
                  let _, loc' = discard() in
		  loc := merge_locs !loc loc'
                end
            end
            | IDENTIFIER i -> begin
                let il = String.lowercase_ascii i in
                if Str.string_match exponent_pat il 0 then begin
                  [%debug_log "'.' <identifier> --> <real-literal>"];
                  tok := REAL_LITERAL (str^i);
                  let _, loc' = discard() in
		  loc := merge_locs !loc loc'
                end
                else if il = "d" || il = "e" then begin
                  let second_tok = tokensrc#peek_nth_rawtok 2 in
                  match second_tok with
                  | PLUS | MINUS -> begin
                      let sign =
                        match second_tok with
                        | PLUS -> "+"
                        | MINUS -> "-"
                        | _ -> assert false
                      in
                      let third_tok = tokensrc#peek_nth_rawtok 3 in
                      match third_tok with
                      | INT_LITERAL j -> begin
                          [%debug_log "'.' (D|E)('+'|'-')<int-literal> --> <real-literal>"];
                          let s = str^i^sign^j in
                          tok := REAL_LITERAL s;
                          let _ = discard() in
                          let _ = discard() in
                          let _, loc' = discard() in
		          loc := merge_locs !loc loc'
                      end
                      | _ -> ()
                  end
                  | INT_LITERAL j -> begin
                      [%debug_log "'.' (D|E)<int-literal> --> <real-literal>"];
                      let s = str^i^j in
                      tok := REAL_LITERAL s;
                      let _ = discard() in
                      let _, loc' = discard() in
		      loc := merge_locs !loc loc'
                  end
                  | _ -> ()
                end
            end
            | PP_IDENTIFIER i -> begin
                let second_tok = tokensrc#peek_nth_rawtok 2 in
                match second_tok with
                | PLUS | MINUS -> begin
                    let sign =
                      match second_tok with
                      | PLUS -> "+"
                      | MINUS -> "-"
                      | _ -> assert false
                    in
                    let third_tok = tokensrc#peek_nth_rawtok 3 in
                    match third_tok with
                    | INT_LITERAL j -> begin
                        [%debug_log "'.' (D|E)('+'|'-')<int-literal> --> <real-literal>"];
                        let s = str^i^sign^j in
                        tok := REAL_LITERAL s;
                        let _ = discard() in
                        let _ = discard() in
                        let _, loc' = discard() in
		        loc := merge_locs !loc loc'
                    end
                    | _ -> ()
                end
                | INT_LITERAL j -> begin
                    [%debug_log "'.' (D|E)<int-literal> --> <real-literal>"];
                    let s = str^i^j in
                    tok := REAL_LITERAL s;
                    let _ = discard() in
                    let _, loc' = discard() in
		    loc := merge_locs !loc loc'
                end
                | _ -> ()
            end
            | _ -> ()
          in
          doit "."
      end
      | PLUS -> begin (* unary operator (GNU extension) *)
          if not env#in_data_context then begin
            match last_tok with
            | SLASH | STAR | STAR_STAR | PLUS | MINUS -> begin
                [%debug_log "'+' --> <uplus>"];
                tok := UPLUS
            end
            | _ -> ()
          end
      end
      | MINUS -> begin (* unary operator (GNU extension) *)
          if not env#in_data_context then begin
            match last_tok with
            | SLASH | STAR | STAR_STAR | PLUS | MINUS -> begin
                [%debug_log "'-' --> <uminus>"];
                tok := UMINUS
            end
            | _ -> ()
          end
      end
      | STAR -> begin (* '*' '*' -> '**' *)
          match peek_next() with
          | STAR ->
              [%debug_log "'*' '*' -> '**'"];
              tok := STAR_STAR;
              let _, loc' = discard() in
	      loc := merge_locs !loc loc'
          | _ -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | PP_MACRO_CONST(*_INT*) id -> begin
          match peek_next() with
          | DATA_EDIT_DESC desc -> begin
              [%debug_log "<pp-macro-const-int><data-edit-desc> --> <data-edit-desc>"];
              tok := DATA_EDIT_DESC (id^" "^desc);
              let _, loc' = discard() in
	      loc := merge_locs !loc loc'
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    if is_head_of_stmt_ then begin
      match !tok with
      | SYNC s -> begin
          match peek_next() with
          | IDENTIFIER s' -> begin
              match String.lowercase_ascii s' with
              | "all" | "images" | "memory" -> ()
              | _ ->
                  [%debug_log "SYNC --> <identifier>"];
                  tok := IDENTIFIER s
          end
          | _ ->
              [%debug_log "SYNC --> <identifier>"];
              tok := IDENTIFIER s
      end
      | LEN s | KIND s -> begin
          [%debug_log "<keyword> --> <identifier>"];
          tok := IDENTIFIER s
      end
      | _ -> ()
    end;


    if is_head_of_stmt_ then begin (* <identifier>|<pp-identifier> --> <pp-macro-id> *)
      match !tok with
      | IDENTIFIER s | PP_IDENTIFIER s -> begin
          match peek_next() with
          | COMMA | COLON_COLON -> begin (* <identifier>|<pp-identifier> (','|'::') *)
              [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:type-spec>"];
              tok := PP_MACRO_ID(M.K_TYPE_SPEC, s)
          end
          | CHAR_LITERAL _ -> begin (* <identifier>|<pp-identifier> <char-literal> *)
              [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-read-print>"];
              tok := PP_MACRO_READ_PRINT s
          end
          | FUNCTION _ -> begin (* <identifier> FUNCTION *)
              [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:type-spec>"];
              tok := PP_MACRO_ID(M.K_TYPE_SPEC, s)
          end
          | LPAREN -> begin (* <identifier>|<pp-identifier> '(' <expr> ',' ('*' | <expr> ','...) ')' ... *)
              let nth = ref 2 in
              let depth = ref 1 in
              let comma_count = ref 0 in
              let star_in_second = ref false in
              let char_in_second = ref false in
              try
                while true do
                  let nth_tok = tokensrc#peek_nth_rawtok !nth in
                  begin
                    match nth_tok with
                    | EOL | SEMICOLON | NOTHING | EOF _ -> raise Exit

                    | LPAREN -> incr depth

                    | COMMA -> if !depth = 1 then incr comma_count

                    | STAR -> if !comma_count = 1 then star_in_second := true

                    | CHAR_LITERAL _ -> if !comma_count = 1 then char_in_second := true

                    | RPAREN -> begin
                        decr depth;
                        if !depth = 0 then begin
                          begin
                            incr nth;
                            match tokensrc#peek_nth_rawtok !nth with
                            | SEMICOLON | EOL | NOTHING -> begin
                                match String.lowercase_ascii s with
                                | "out" | "eval" | "in" | "rd" -> () (* Linda operations *)
                                | _ -> begin
                                    [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id>"];
                                    tok := PP_MACRO_ID(M.K_GENERAL, s)
                                end
                            end
                            | CHAR_LITERAL _ -> begin
                                [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:WRITE>"];
                                tok := PP_MACRO_ID_RW(M.K_WRITE, s)
                            end
                            | LPAREN -> begin (* excluding ... '('...')' '('...')' = *)
                                incr nth;
                                incr depth;
                                try
                                  while true do
                                    let nth_tok2 = tokensrc#peek_nth_rawtok !nth in
                                    begin
                                      match nth_tok2 with
                                      | EOL | SEMICOLON | NOTHING | EOF _ -> raise Exit
                                      | LPAREN -> incr depth
                                      | RPAREN -> begin
                                          decr depth;
                                          if !depth = 0 then begin
                                            begin
                                              match tokensrc#peek_nth_rawtok (!nth+1) with
                                              | EQ -> ()
                                              | _ -> begin
                                                  [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:READ|WRITE>"];
                                                  tok := PP_MACRO_ID_RW(M.K_READ_WRITE, s)
                                              end
                                            end;
                                            raise Exit
                                          end
                                      end
                                      | _ -> ()
                                    end;
                                    incr nth
                                  done
                                with
                                  Exit -> ()
                            end
                            | IDENTIFIER _ -> begin (* excluding <type-spec> '('...')' <identifier> *)
                                if !star_in_second || !char_in_second || !comma_count > 1 then begin
                                  [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:READ|WRITE>"];
                                  tok := PP_MACRO_ID_RW(M.K_READ_WRITE, s)
                                end
                                else begin (* search '//' up to EOL or ';' *)
                                  incr nth;
                                  try
                                    while true do
                                      let nth_tok2 = tokensrc#peek_nth_rawtok !nth in
                                      begin
                                        match nth_tok2 with
                                        | EOL | SEMICOLON | NOTHING | EOF _ -> raise Not_found
                                        | SLASH_SLASH -> begin
                                            [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:READ|WRITE>"];
                                            tok := PP_MACRO_ID_RW(M.K_READ_WRITE, s);
                                            raise Exit
                                        end
                                        | _ -> ()
                                      end;
                                      incr nth
                                    done
                                  with
                                  | Not_found -> ()
                                  | Exit -> ()
                                end
                            end
                            | COMMA -> begin
                                match tokensrc#peek_nth_rawtok (!nth+1) with
                                | CHAR_LITERAL _ -> begin
                                    [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:WRITE>"];
                                    tok := PP_MACRO_ID_RW(M.K_WRITE, s)
                                end
                                | LPAREN -> begin
                                    [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:READ|WRITE>"];
                                    tok := PP_MACRO_ID_RW(M.K_READ_WRITE, s)
                                end
                                | IDENTIFIER _ -> begin (* excluding <type-spec>(...) <identifier> *)
                                    if !star_in_second || !char_in_second || !comma_count > 1 then begin
                                      [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-id:READ|WRITE>"];
                                      tok := PP_MACRO_ID_RW(M.K_READ_WRITE, s)
                                    end
                                end
                                | _ -> ()
                            end
                            | _ -> ()
                          end;
                          raise Exit
                        end
                    end
                    | _ -> ()
                  end;
                  incr nth
                done
              with
                Exit -> ()
          end
          | _ -> begin (* <identifier>|<pp-identifier> ... ',' <char-literal> *)
              let nth = ref 2 in
              let depth = ref 1 in
              try
                while true do
                  let nth_tok = tokensrc#peek_nth_rawtok !nth in
                  begin
                    match nth_tok with
                    | EOL | SEMICOLON | NOTHING | EOF _ -> raise Exit

                    | LPAREN -> incr depth

                    | RPAREN -> decr depth

                    | COMMA -> begin
                        if !depth = 0 then begin
                          let nth_tok' = tokensrc#peek_nth_rawtok (!nth+1) in
                          match nth_tok' with
                          | CHAR_LITERAL _ -> begin
                              [%debug_log "<identifier>|<pp-identifier> --> <pp-macro-read-print>"];
                              tok := PP_MACRO_READ_PRINT s;
                              raise Exit
                          end
                          | _ -> ()
                        end
                    end
                    | _ -> ()
                  end;
                  incr nth
                done
              with
                Exit -> ()
          end
      end
      | _ -> ()
    end;


    if is_head_of_stmt_ && env#in_select_type_context then begin
      match !tok with
      | TYPE _ | CLASS _ -> begin
          match peek_next() with
          | IDENTIFIER s' -> begin
              let ls' = String.lowercase_ascii s' in
              match ls' with
              | "is" -> begin
                  [%debug_log "TYPE|CLASS <identifier> --> TYPE_IS|CLASS_IS"];
                  let tok' =
                    match !tok with
                    | TYPE s  -> TYPE_IS (s^" "^s')
                    | CLASS s -> CLASS_IS (s^" "^s')
                    | _ -> assert false
                  in
                  tok := tok';
                  let _, loc' = discard() in
                  loc := merge_locs !loc loc'
              end
              | _ -> ()
          end
          | DEFAULT s' -> begin
              match !tok with
              | CLASS s -> begin
                  [%debug_log "CLASS DEFAULT --> CLASS_DEFAULT"];
                  tok := CLASS_DEFAULT (s^" "^s');
                  let _, loc' = discard() in
                  loc := merge_locs !loc loc'
              end
              | _ -> ()
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | ERROR s -> begin
          let b =
            match peek_next() with
            | STOP _ -> not is_head_of_stmt_
            | _ -> true
          in
          if b then begin
            [%debug_log "ERROR --> <identifier>"];
            tok := IDENTIFIER s
          end
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | SIMPLE_ATTR s -> begin
        if following_comma then begin
          let nth = ref 1 in
          try
            while true do
              let nth_tok = tokensrc#peek_nth_rawtok !nth in
              match nth_tok with
              | EOL | SEMICOLON | NOTHING | EOF _ -> raise Not_found
              | COLON_COLON -> raise Exit
              | _ -> incr nth
            done
          with
          | Not_found -> begin
              [%debug_log "<keyword> --> <identifier>"];
              tok := IDENTIFIER s
          end
          | Exit -> ()
        end
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | PP_IDENTIFIER s -> begin
          let rep = ref s in
          match last_tok with
          | PRIVATE _ | PUBLIC _ | PROCEDURE _ | CALL _ | USE _
          | TYPE _ | END_TYPE _ | SUBROUTINE _ | FUNCTION _(* | END_SUBROUTINE _ | END_FUNCTION _*)
          | END_SUBPROGRAM _ | END_PROCEDURE _
          | INTERFACE _ | END_INTERFACE _ | MODULE _ | END_MODULE _
          | LPAREN | COLON_COLON | PERCENT | COMMA
            -> begin
              match peek_next() with
              | LPAREN -> begin
                  let nth = ref 2 in
                  let depth = ref 1 in
                  let comma_count = ref 0 in
                  let has_pp_underscore = ref false in
                  try
                    while true do
                      let nth_tok = tokensrc#peek_nth_rawtok !nth in
                      begin
                        match nth_tok with
                        | EOL | SEMICOLON | NOTHING | EOF _ -> raise Exit
                        | LPAREN -> incr depth
                        | COMMA -> if !depth = 1 then incr comma_count
                        | PP_UNDERSCORE _ -> has_pp_underscore := true
                        | RPAREN -> begin
                            decr depth;
                            if !depth = 0 then begin
                              if !has_pp_underscore then begin
                                [%debug_log "<pp-identifier> '(' ... '_'+ ... ')' --> <pp-macro-name>"];
                                let loc' = ref !loc in
                                for _ = 1 to !nth do
                                  let t, l = discard() in
                                  rep := !rep ^ (Token.rawtoken_to_rep t);
                                  loc' := l
                                done;
                                tok := PP_MACRO_NAME(!rep, "");
                                loc := merge_locs !loc !loc';

                                let params =
                                  let rec gen (l, n) =
                                    if n = 0 then
                                      (l, 0)
                                    else
                                      gen ((sprintf "X%d" n) :: l, n - 1)
                                  in
                                  let l, _ = gen ([], !comma_count + 1) in
                                  l
                                in
                                let stat = Macro.Resolved (Obj.repr (!tok, !loc)) in
                                let body =
                                  Macro.mk_fun_body ~loc:!loc ~stat params "CONSTRAINED_TO_BE_A_NAME"
                                in
                                env#define_macro s body;
                                env#lex_define_macro s body;

                                raise Exit
                              end
                            end
                        end
                        | _ -> ()
                      end;
                      incr nth
                    done
                  with
                    Exit -> tok := PP_MACRO_NAME(s, "")
              end
              | _ -> begin
                  [%debug_log "<pp-identigfier> --> <pp-macro-name>"];
                  tok := PP_MACRO_NAME(s, "")
              end
            end
          | _ -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | EOL -> begin
          match peek_next() with
          | RPAREN -> begin
              [%debug_log "EOL ')' --> ')'"];
              Common.parse_warning_loc !loc "ignoring EOL followed by ')'";
              let _, l = discard() in
              tok := RPAREN;
              loc := l
          end
          | CHAR_LITERAL _ when env#current_source#lang_config#is_free_source_form -> begin
              match last_tok with
              | COMMA -> begin
                  [%debug_log "',' EOL --> ','"];
                  Common.parse_warning_loc !loc "ignoring EOL after ','";
                  let t, l = discard() in
                  tok := t;
                  loc := l
              end
              | _ -> ()
          end
          | _ -> ()
      end
      | _ -> ()
    end;

    begin
      match !tok with
      | TO s -> begin
          match last_tok with
          | INT_LITERAL _ -> ()
          | _ -> begin
              [%debug_log "<keyword> --> <identifier>"];
              tok := IDENTIFIER s
          end
      end
      | DATA s when not is_head_of_stmt_ -> begin
          [%debug_log "<keyword> --> <identifier>"];
          tok := IDENTIFIER s
      end
      | END s when not is_head_of_stmt_ -> begin
          match last_tok with
          | COLON_COLON -> begin
              [%debug_log "<keyword> --> <identifier>"];
              tok := IDENTIFIER s
          end
          | _ -> begin
              match peek_next() with
              | EQ -> ()
              | _ -> begin
                  [%debug_log "<keyword> --> <identifier>"];
                  tok := IDENTIFIER s
              end
          end
      end
      | FORMAT s | RECORD s | DATA s when not is_head_of_stmt_ -> begin
          match last_tok with
          | COLON_COLON | COMMA -> begin
              [%debug_log "<keyword> --> <identifier>"];
              tok := IDENTIFIER s
          end
          | _ -> begin
              match peek_next() with
              | COMMA -> begin
                  [%debug_log "<keyword> --> <identifier>"];
                  tok := IDENTIFIER s
              end
              | _ -> ()
          end
      end
      | _ -> ()
    end;

    (* * * *)

    begin
      match !tok with
      (*| INTEGER _ | REAL _ | LOGICAL _ | COMPLEX _*) | KINDED_TYPE_SPEC _ -> begin
          if (peek_next()) = STAR then
            if is_head_of_stmt_ then
              env#enter_type_spec_context
      end
      | RPAREN -> begin
          if env#in_implicit_context then
            env#exit_letter_context
      end

      | LBRACKET -> begin
          [%debug_log "entering array constructor context ([)"];
          env#enter_array_ctor_context
      end
      | RBRACKET -> begin
          [%debug_log "exiting array constructor context (])"];
          env#exit_array_ctor_context
      end

      | FORMAT _ -> begin
          [%debug_log "entering format context"];
	  env#enter_format_context
      end

      | PRINT _ | READ _ -> begin
          [%debug_log "entering io-control context (print|read)"];
          env#enter_name_context;
          env#enter_io_control_context
      end

      | PP_MACRO_READ_PRINT _ -> begin
          env#enter_name_context
      end

      | PP_MACRO_ID_RW(M.K_WRITE, _|M.K_READ_WRITE, _)
      | PP_MACRO_WRITE _ | PP_MACRO_READ_WRITE _ -> begin
          [%debug_log "entering io-control context (<pp-macro-id>)"];
          env#enter_name_context;
          env#enter_io_control_context
      end

      | CALL _ -> begin
          [%debug_log "entering name context (call)"];
          env#enter_name_context
      end

      | INTRINSIC _ -> begin
          if is_head_of_stmt_ then begin
            [%debug_log "entering name context (intrinsic)"];
            env#enter_name_context
          end
      end

      | PUBLIC _ | PRIVATE _ -> begin
          if is_head_of_stmt_ then begin
            match peek_next() with
            | IDENTIFIER _ | OPERATOR _ | ASSIGNMENT _ | READ _ | WRITE _
            | COLON_COLON
              -> env#enter_access_context
            | _ -> ()
          end
      end

      | INTERFACE _ -> env#enter_interface_context

      | IMPLICIT _ -> env#enter_implicit_context

      | END_INTERFACE _ -> env#exit_interface_context

      | END _ -> begin
          if not env#in_io_control_context then begin
            [%debug_log "popping context_stack"];
            context_stack#pop
          end
      end

      | END_PROGRAM _ -> begin
          [%debug_log "popping context_stack"];
          context_stack#pop;
      end
      (*| END_FUNCTION _ | END_SUBROUTINE _*) | END_SUBPROGRAM _ | END_PROCEDURE _ -> begin
          if env#in_contains_context || env#in_interface_context then begin
            if not env#partial_parsing_flag then begin
              [%debug_log "popping context_stack"];
              context_stack#pop;
            end
          end
      end
      | END_MODULE _ | END_SUBMODULE _ | END_BLOCK_DATA _ -> begin
          if not env#partial_parsing_flag then begin
            [%debug_log "popping context_stack"];
            context_stack#pop;
          end
      end

      | CONTAINS _ -> begin
          env#enter_contains_context;
          [%debug_log "popping context_stack"];
          context_stack#pop
      end

      | COMMON _ ->
          [%debug_log "entering name context"];
          env#enter_name_context;
          env#enter_slash_name_context

      | VFE_BEGIN _ -> env#enter_vfe_context
      | VFE_END _ -> env#exit_vfe_context

      | ONLY _ -> env#enter_only_context

      | _ -> ()
    end;

    begin
      match !tok with
      | FUNCTION _ | SUBROUTINE _ | MODULE _ | SUBMODULE _ | BLOCK_DATA _ | PROGRAM _ ->
          env#enter_pu_head_context

      | _ -> begin
          if env#at_BOPU then begin
            [%debug_log "clearing BOPU flag: %s" (Token.rawtoken_to_string !tok)];
            env#clear_BOPU
          end
      end
    end;

    begin
      match peek_next() with (* when in pp-branch *)
      | END_FRAGMENT -> begin
          if env#fragment_impossible then
            match tokensrc#peek_nth_rawtok 2 with
            | EOF _ -> ()
            | _ -> ignore (discard())
      end
      | BACKSLASH -> begin (* line continuation? *)
          match tokensrc#peek_nth_rawtok 2 with
          | EOL ->
              ignore (discard());
              ignore (discard())
          | _ -> ()
      end
      | _ -> ()
    end;


    let qtoken = (!tok, !loc) in

    begin %debug_block
      if _tok <> !tok then
        [%debug_log " --> %s" (Token.qtoken_to_string qtoken)];
    end;

    tokensrc#set_prev_rawtok last_tok;
    tokensrc#set_prev_loc tokensrc#get_last_loc;
    tokensrc#set_last_rawtok !tok;
    tokensrc#set_last_loc !loc;

    qtoken
    (* end of hack_token *)



  type token_handler = BranchF.tokensource -> Token.qtoken_t -> Token.t


  class base = object (self : 'self)
    val mutable queue : Token.qtoken_t Xqueue.c = new Xqueue.c
    val mutable ast_cache = Runknown

    val mutable is_regular = true

    method set_irregular = is_regular <- false
    method is_regular = is_regular


    method get_list_rev = queue#fold (fun l x -> x :: l) []

    method get_list = List.rev self#get_list_rev

    method get_stream =
      let q = queue#copy in
      let f _ =
        try
          Some q#take
        with
          Xqueue.Empty -> None
      in
      Stream.from f

    method ast_cache = ast_cache
    method set_ast_cache c = ast_cache <- c

    method to_string =
      let buf = Buffer.create 0 in
      self#iter
	(fun qtok ->
          Buffer.add_string buf
            (sprintf "%s\n" (Token.qtoken_to_string qtok))
        );
      Buffer.contents buf


    method _set_queue q = queue <- q
    method _raw = queue
    method clear = queue#clear

    method _add qtok =
      ast_cache <- Runknown;
      queue#add qtok

    method add qtoken = self#_add qtoken

    method remove_last = queue#remove_last

    method replace_first qtok =
      let _ = queue#take in
      queue#prepend qtok

    method iter f = queue#iter f

    method size = queue#length

    method total_length =
      let sz = ref 0 in
      self#iter
	(fun (tok, _) ->
	  sz := !sz + (TokenF.size tok)
	);
      !sz

    method total_length_no_pp =
      let sz = ref 0 in
      self#iter
	(fun (tok, _) ->
          if not (TokenF.is_pp_directive tok) then
	    sz := !sz + (TokenF.size tok)
	);
      !sz

    method is_empty = queue#is_empty

    method peek =
      try
	queue#peek
      with
	Xqueue.Empty -> raise Empty

    method peek_nth n = queue#peek_nth n

    method take =
      try
	queue#take
      with
	Xqueue.Empty -> raise Empty

    method receive_all : 'self -> unit =
      fun buf ->
	let q = buf#_raw in
	if q#length > 0 then
	  ast_cache <- Runknown;
	q#transfer queue


    method dump =
      [%debug_log "\n%s" self#to_string]

    method get_loc =
      let started = ref false in
      try
        let st = ref Loc.dummy in
        let ed = ref Loc.dummy in
        self#iter
          (fun (tok, loc) ->
            match tok with
            | END_FRAGMENT | EOL -> ()
            | _ ->
                if !started then
                  ed := loc
                else begin
                  st := loc;
                  started := true
                end
          );
        merge_locs !st !ed
      with
	Xqueue.Empty -> raise Empty

    method get_last =
      if self#size > 0 then
	let last = ref (EOF None, Loc.dummy) in
	queue#iter (fun x -> last := x);
	!last
      else
	raise Empty



    method ends_with_EOL =
      match self#get_last_EOL with
      | Some _ -> true
      | None -> false

    method get_last_EOL =
      if self#size > 0 then begin
        let rec scan = function
          | [] -> None
          | ((tok, loc) as t)::rest -> begin
              match tok with
              | PP_BRANCH (PPD.Endif _|PPD.Else) -> scan rest
(*              | PP_ENDIF | PP_ELSE -> scan rest*)

              | END_FRAGMENT -> scan rest

              | EOL -> Some t

              | STMT _
              | SPEC_PART_CONSTRUCT _
              | EXEC_PART_CONSTRUCT _
              | PP_INCLUDE__FILE _
              | PP_ISSUE__MESG _
(*
              | PP_ERROR__MESG _
              | PP_WARNING__MESG _
*)
              | OMP _ | OCL _ | ACC _ | XLF _ | DEC _
                ->
                  let _, _pos = Loc.to_lexposs loc in
                  let pos = Loc.incr_lexpos _pos in
                  let loc' = loc_of_lexposs pos pos in
                  Some (EOL, loc')

              | _ -> None
          end
        in
        scan self#get_list_rev
      end
      else
        None


    method remove_last_EOL =
      if self#size > 0 then
        let rec scan = function
          | [] -> []
          | (((tok, _) as t)::rest as l) -> begin
              match tok with
              | PP_BRANCH (PPD.Endif _|PPD.Else) -> t::(scan rest)
(*              | PP_ENDIF | PP_ELSE -> t::(scan rest)*)
              | EOL -> rest
              | _ -> l
          end
        in
        let l = scan self#get_list_rev in
        queue#clear;
        List.iter
          (fun t -> queue#add t)
          (List.rev l)
      else
        ()

    method remove_first_END_FRAGMENT =
      try
        let t, _ = queue#peek in
        match t with
        | END_FRAGMENT -> ignore queue#take
        | _ -> ()
      with
        Xqueue.Empty -> ()

    method get_tokensrc =
      let copied = queue#copy in (* !!! *)
      let tokensrc = new BranchF.tokensource copied in
      tokensrc


    method _parse_by : ?cache:bool -> token_handler -> partial_parser -> Partial.t =
      fun ?(cache=true) handler _parser ->
	[%debug_log "called"];

	match ast_cache with
	| Rcomplete p ->
	    [%debug_log "using cached value (complete)"];
	    p

	| Rincomplete ->
	    [%debug_log "using cached value (incomplete)"];
	    raise Incomplete

	| Runknown ->
	    [%debug_log "parsing..."];
            self#dump;

            let tokensrc = self#get_tokensrc in

	    let scanner() =
	      try
                let token =
                  tokensrc#get_token (handler tokensrc)
                in
                [%debug_log "---------> %s" (Token.to_string token)];
                token
	      with
	      | Tokensource.Empty ->
		  if tokensrc#eop_flag then begin
                    [%debug_log "raising End_of_file"];
		    raise End_of_file
                  end
		  else begin
		    let _, ed = Loc.to_lexposs tokensrc#get_last_loc in
		    tokensrc#set_eop_flag;

		    begin %debug_block
		      [%debug_log "last token: %s[%s]"
		         (Token.rawtoken_to_string tokensrc#get_last_rawtok)
                         (Loc.to_string tokensrc#get_last_loc)];
		      [%debug_log "EOP[%s]"
		         (Loc.to_string (Astloc.of_lexposs ed ed))];
		    end;

		    PB.make_token EOP ed ed
		  end

	    in (* scanner() *)

	    env#set_partial_parsing_flag;
	    try
	      let p = _parser scanner in
	      env#clear_partial_parsing_flag;
(*
  check_error p;
 *)
	      [%debug_log "result: PARSED"];

              Partial.set_length p self#total_length;

              if cache then
	        ast_cache <- Rcomplete p;
	      p

	    with
	      exn ->
                let _ = exn in
		[%debug_log "result: FAILED (%s)" (Printexc.to_string exn)];
		env#clear_partial_parsing_flag;
                if cache then
		  ast_cache <- Rincomplete;
		raise Incomplete
    (* end of method _parse_by *)


    method parse_by ?(cache=true) p =
      self#_parse_by ~cache
        (fun tokensrc qtoken ->
          let qtoken' = hack_token (tokensrc :> Tokensource.c) qtoken in
          PB.qtoken_to_token qtoken'
        )
        p


  end (* of class Tokenbuffer.base *)


  class c (btag : Branch.tag) = object (self : 'self)

    inherit base as super

    val mutable context = C.unknown()

    method! to_string =
      sprintf "%s@[%s]\n%s"
        (Branch.tag_to_string btag) (C.to_string context) super#to_string

    method! dump =
      [%debug_log "%s" self#to_string]

    method get_copy =
      [%debug_log "called"];
      let copy = new c btag in
      copy#_set_queue queue#copy;
      copy#set_context context;
      copy

    method set_context c =
      [%debug_log "[%s]: %s" (Branch.tag_to_string btag) (C.to_string c)];
      context <- c

    method get_context =
(*      [%debug_log "%s" (C.to_string context)]; *)
      context

    method get_tag = btag

    method! parse_by ?(cache=true) p =
      super#_parse_by ~cache
        (fun tokensrc qtoken ->

          let qtoken' = hack_token (tokensrc :> Tokensource.c) qtoken in
(*
	  context_stack#deactivate_top;
*)
	  if env#context_enter_flag then begin
	    env#clear_context_enter_flag;
	    env#set_last_active_ofss (Loc.to_offsets tokensrc#get_last_loc)
	  end;
	  if env#context_activate_flag then begin
	    env#clear_context_activate_flag;
	    env#set_last_active_ofss (Loc.to_offsets tokensrc#get_prev_loc)
	  end;

          let rt = Token.qtoken_to_rawtoken qtoken' in
          begin
            match rt with
            | END _ | END_BLOCK_DATA _(* | END_FUNCTION _ | END_SUBROUTINE _*) | END_SUBPROGRAM _
            | END_PROCEDURE _
            | END_PROGRAM _ | END_MODULE _ | END_SUBMODULE _
            | CONTAINS _
              -> begin
                [%debug_log "popping context_stack"];
                context_stack#pop
              end
            | _ -> ()
          end;

          PB.qtoken_to_token qtoken'
        )
        p

    method to_partial ?(context_opt=None) partial =
      match partial with
      | Partial.Dummy _ -> ()

      | Partial.Program(spec, nds) -> begin
          [%debug_log "Partial.Program"];
          self#clear;
          try
            self#add (TokenF.of_program_unit spec (tag_to_node C.Ttoplevel btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_program_unit spec nd)) nds
      end
      | Partial.ProgramUnit(spec, nd) -> begin
          [%debug_log "Partial.ProgramUnit"];
          self#clear;
          try
            self#add (TokenF.of_program_unit spec (tag_to_node C.Tprogram_unit btag [nd]))
          with
            Undefined -> self#add (TokenF.of_program_unit spec nd)
      end
      | Partial.Spec_Exec(spec, sp_nd_opt, ep_nd_opt) -> begin
          [%debug_log "Partial.Spec_Exec"];
          self#clear;
          try
            let of_spec_exec, c, l =
              match sp_nd_opt, ep_nd_opt with
              | Some sp_nd, None ->
                  [%debug_log "sp_nd: %s" sp_nd#to_string];
                  Xoption.iter C.resolve_into_spec context_opt;
                  TokenF.of_spec_part_construct, C.Tspecification_part, sp_nd#children

              | None, Some ep_nd ->
                  [%debug_log "ep_nd: %s" ep_nd#to_string];
                  Xoption.iter C.resolve_into_exec context_opt;
                  TokenF.of_exec_part_construct, C.Texecution_part, ep_nd#children

              | Some sp_nd, Some ep_nd ->
                  [%debug_log "sp_nd: %s" sp_nd#to_string];
                  [%debug_log "ep_nd: %s" ep_nd#to_string];
                  Xoption.iter C.resolve_into_exec context_opt;
                  TokenF.of_exec_part_construct, C.Texecution_part, sp_nd#children @ ep_nd#children
              | _ -> raise Not_found
            in
            begin %debug_block
              [%debug_log "l:"];
              List.iter (fun n -> [%debug_log " %s" n#to_string]) l;
            end;
            self#add (of_spec_exec spec (tag_to_node c btag l))
          with
          | Undefined ->
              let specs, execs = Ast.spec_opt_exec_opt_to_children_pair (sp_nd_opt, ep_nd_opt) in
              List.iter (fun nd -> self#add (TokenF.of_spec_part_construct spec nd)) specs;
              List.iter (fun nd -> self#add (TokenF.of_exec_part_construct spec nd)) execs
          | Not_found -> ()
      end
      | Partial.SpecificationPart(spec, nds) -> begin
          [%debug_log "Partial.SpecificationPart"];
          self#clear;
          try
            let c = C.Tspecification_part in
            self#add (TokenF.of_spec_part_construct spec (tag_to_node c btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_spec_part_construct spec nd)) nds
      end
      | Partial.ExecutionPart(spec, nds) -> begin
          [%debug_log "Partial.ExecutionPart"];
          self#clear;
          try
            let c = C.Texecution_part in
            self#add (TokenF.of_exec_part_construct spec (tag_to_node c btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_exec_part_construct spec nd)) nds
      end
      | Partial.Subprograms(spec, nds) -> begin
          [%debug_log "Partial.Subprograms"];
          self#clear;
          try
            self#add (TokenF.of_subprogram spec (tag_to_node C.Tsubprograms btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_subprogram spec nd)) nds
      end
      | Partial.InterfaceSpec(spec, nds) -> begin
          [%debug_log "Partial.InterfaceSpec"];
          self#clear;
          try
            self#add (TokenF.of_interface_spec spec (tag_to_node C.Tinterface_spec btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_interface_spec spec nd)) nds
      end
      | Partial.CaseBlock(spec, nds) -> begin
          [%debug_log "Partial.CaseBlock"];
          self#clear;
          try
            self#add (TokenF.of_case_block spec (tag_to_node C.Tcase_block btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_case_block spec nd)) nds
      end
      | Partial.DataStmtSets(spec, nds) -> begin
          [%debug_log "Partial.DataStmtSets"];
          self#clear;
          try
            self#add (TokenF.of_data_stmt_set spec (tag_to_node C.Tdata_stmt_sets btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_data_stmt_set spec nd)) nds
      end
      | Partial.TypeSpec(spec, nd) -> begin
          [%debug_log "Partial.TypeSpec"];
          self#clear;
          try
            self#add (TokenF.of_type_spec spec (tag_to_node C.Ttype_spec btag [nd]))
          with
            Undefined -> self#add (TokenF.of_type_spec spec nd)
      end
      | Partial.Expr(spec, nd) -> begin
          [%debug_log "Partial.Expr"];
          self#clear;
          try
            self#add (TokenF.of_expr spec (tag_to_node C.Texpr btag [nd]))
          with
            Undefined -> self#add (TokenF.of_expr spec nd)
      end
      | Partial.ActionStmt(spec, nd) -> begin
          [%debug_log "Partial.ActionStmt"];
          let eol =
            let _, p = A.node_to_lexposs nd in
            PB.make_qtoken EOL p p
          in
          self#clear;
          try
            self#add (TokenF.of_action_stmt spec (tag_to_node C.Taction_stmt btag [nd]));
            self#add eol
          with
            Undefined ->
              self#add (TokenF.of_action_stmt spec nd);
              self#add eol
      end
      | Partial.Variable(spec, nd) -> begin
          [%debug_log "Partial.Variable"];
          self#clear;
          try
            self#add (TokenF.of_variable spec (tag_to_node C.Tvariable btag [nd]))
          with
            Undefined -> self#add (TokenF.of_variable spec nd)
      end
      | Partial.Stmts(spec, nds) -> begin
          begin %debug_block
            [%debug_log "Partial.Stmts"];
            List.iter (fun nd -> [%debug_log "%s" nd#to_string]) nds
          end;
          self#clear;
          try
            let conv =
              let select_case_lv =
                List.fold_left
                  (fun select_case_lv nd ->
                    match nd#label with
                    | Label.Stmt stmt -> begin
                        match Labels.Stmt.get_raw_stmt stmt with
                        | Labels.Stmt.SelectCaseStmt _ -> select_case_lv + 1
                        | Labels.Stmt.EndSelectStmt _ -> select_case_lv - 1
                        | _ -> select_case_lv
                    end
                    | _ -> select_case_lv
                  ) 0 nds
              in
              [%debug_log "select_case_lv=%d" select_case_lv];
              if select_case_lv > 0 then
                TokenF.of_select_case_stmt
              else
                TokenF.of_stmt
            in
            self#add (conv spec (tag_to_node C.Tstmts btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_stmt spec nd)) nds
      end
      | Partial.DerivedTypeDefPart(spec, nds) -> begin
          begin %debug_block
            [%debug_log "Partial.DerivedTypeDefPart"];
            List.iter (fun nd -> [%debug_log "%s" nd#to_string]) nds
          end;
          self#clear;
          try
            self#add (TokenF.of_derived_type_def_part spec (tag_to_node C.Tderived_type_def_part btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_derived_type_def_part spec nd)) nds
      end
      | Partial.Onlys(spec, nds) -> begin
          begin %debug_block
            [%debug_log "Partial.Onlys"];
            List.iter (fun nd -> [%debug_log "%s" nd#to_string]) nds
          end;
          self#clear;
          try
            self#add (TokenF.of_only spec (tag_to_node C.Tonlys btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_only spec nd)) nds
      end
      | Partial.FunctionHead(spec, nds) -> begin
          begin %debug_block
            [%debug_log "Partial.FunctionHead"];
            List.iter (fun nd -> [%debug_log "%s" nd#to_string]) nds
          end;
          self#clear;
          try
            self#add (TokenF.of_function_head spec (tag_to_node C.Tfunction_head btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_stmt spec nd)) nds
      end
      | Partial.FunctionStmtHead(spec, nd) -> begin
          begin %debug_block
            [%debug_log "Partial.FunctionStmtHead"];
            [%debug_log "%s" nd#to_string];
          end;
          self#clear;
          try
            self#add (TokenF.of_function_stmt_head spec (tag_to_node C.Tfunction_stmt_head btag [nd]))
          with
            Undefined -> self#add (TokenF.of_stmt spec nd)
      end
      | Partial.SubroutineHead(spec, nds) -> begin
          begin %debug_block
            [%debug_log "Partial.SubroutineHead"];
            List.iter (fun nd -> [%debug_log "%s" nd#to_string]) nds
          end;
          self#clear;
          try
            self#add (TokenF.of_subroutine_head spec (tag_to_node C.Tsubroutine_head btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_stmt spec nd)) nds
      end
      | Partial.SubroutineStmtHead(spec, nd) -> begin
          begin %debug_block
            [%debug_log "Partial.SubroutineStmtHead"];
            [%debug_log "%s" nd#to_string];
          end;
          self#clear;
          try
            self#add (TokenF.of_subroutine_stmt_head spec (tag_to_node C.Tsubroutine_stmt_head btag [nd]))
          with
            Undefined -> self#add (TokenF.of_stmt spec nd)
      end
      | Partial.PuTail(spec, nds) -> begin
          begin %debug_block
            [%debug_log "Partial.PuTail"];
            List.iter (fun nd -> [%debug_log "%s" nd#to_string]) nds
          end;
          self#clear;
          try
            self#add (TokenF.of_pu_tail spec (tag_to_node C.Tpu_tail btag nds))
          with
            Undefined -> List.iter (fun nd -> self#add (TokenF.of_stmt spec nd)) nds
      end

      | p ->
          [%debug_log "not yet: %s" (Partial.to_string p)];
          warning_msg "not yet: %s" (Partial.to_string p);

    (* end of method to_partial *)

  end (* of class Tokenbuffer.c *)


end (* of functor Tokenbuffer.F *)
]
