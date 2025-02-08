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
(* lib.ml *)

[%%prepare_logger]

open Common

module Aux = Parser_aux
module PB = Parserlib_base
module T = Tokens_

let get_lc = Langs_common.Position.get_lc

[%%capture_path
class parser_c = object (self)
  inherit [T.token, Ast.c] PB.sb_c (new Aux.env)

  val mutable keep_going_flag = false
  val mutable ignore_comment_flag = false

  val mutable parser_main = fun _ -> Obj.magic ()
  val mutable scanner     = Obj.magic ()
  val mutable _parse      = fun () -> Obj.magic ()

  method enable_with_stmt = env#enable_with_stmt
  method disable_with_stmt = env#disable_with_stmt

  val mutable rollback_record = []

  method! _set_keep_going_flag b =
    keep_going_flag <- b;
    env#_set_keep_going_flag b

  method _set_ignore_comment_flag b =
    ignore_comment_flag <- b;
    env#_set_ignore_comment_flag b

  method! parser_init =
    scanner#init;
    env#_set_keep_going_flag keep_going_flag;
    env#_set_ignore_comment_flag ignore_comment_flag

  method _parse = _parse()


  method __parse =
(*    self#parser_init; *)
    try
      let root = parser_main ()(*scanner#get_token*) in
      let ast = new Ast.c root in

      ast#set_lines_read env#current_pos_mgr#lines_read;
      ast#set_comment_regions env#comment_regions#get_offsets;
      ast#set_comment_LOC env#comment_regions#get_LOC;
      ast#set_missed_regions env#missed_regions#get_offsets;
      ast#set_missed_LOC env#missed_regions#get_LOC;
      ast#set_blank_regions (env#blank_regions#get_offsets);
      ast#set_blank_LOC (env#blank_regions#get_LOC);

      ast#set_comment_tbl env#comment_tbl;
(*
      ast#set_ignored_regions (env#ignored_regions#get_offsets);
      ast#set_ignored_LOC (env#ignored_regions#get_LOC);
*)
      ast
    with
    | Parsing.Parse_error ->
	let l, c = env#current_pos_mgr#get_current_position in
        fail_to_parse
          ~head:(Printf.sprintf "[%s:%d:%d]" env#current_filename l c)
          "syntax error"


  initializer
    env#_set_keep_going_flag keep_going_flag;
    env#_set_ignore_comment_flag ignore_comment_flag;
    let module S = struct
      let env      = env
    end
    in
    let module U = Ulexer.F (S) in
    let module P = Parser.Make (S) in
    let module I = P.MenhirInterpreter in
    (*let module Scan = Scanner.F (S) in*)
    (*parser_main <- PB.mkparser P.main;*)
    scanner <- new U.scanner;

    let backup_size = 4 in
    let menv_backup_objs = ref [] in
    let error_state = ref (-1) in

    let save_state _menv =
      let sn = I.current_state_number _menv in
      [%debug_log "current state: %d" sn];
      if List.length !menv_backup_objs >= backup_size then begin
        match List.rev !menv_backup_objs with
        | _ :: tl -> menv_backup_objs := List.rev tl
        | _ -> ()
      end;
      menv_backup_objs :=
        (sn, scanner#copy_shadow_queue, (*scanner#copy_shadow_q, *)_menv) :: !menv_backup_objs;
      [%debug_log "\n%s"
        (String.concat "\n"
           (List.map
              (fun (sn, scq, (*soq, *)_) ->
                Printf.sprintf "%d: ^%s$ --- ^%s$"
                  sn (U.token_queue_to_string scq) (U.outline_queue_to_string scq(*soq*))
              ) !menv_backup_objs)
        )];
      scanner#reset_shadow_queue;
      (*scanner#reset_shadow_q*)
    in
    let poss_of_menv _menv =
      match I.get 0 _menv with
      | Some (I.Element (_, _, stp, edp)) -> stp, edp
      | _ -> Lexing.dummy_pos, Lexing.dummy_pos
    in

    let syntax_error menv =
      let stp, edp = poss_of_menv menv in
      let sl, sc = get_lc stp in
      let el, ec = get_lc edp in
      fail_to_parse
        ~head:(Printf.sprintf "[%s:%dL,%dC-%dL,%dC]" env#current_filename sl sc el ec)
        "syntax error"
    in
    let iter_items ?(ith=0) _menv f =
      match I.get ith _menv with
      | Some (I.Element (stat, _, _, _)) -> begin
          let sn = I.number stat in
          let proc o (prod, i) =
            let lhs = I.lhs prod in
            let rhs = I.rhs prod in
            let rhs0 = List.hd rhs in
            let rhsi = List.nth rhs (i-1) in
            match o with
            | Some (s, lh, rh0, rhx, i0) when
                s == sn && lh == lhs && rhx == rhsi && rh0 == rhs0 && i0 = i -> o
            | _ ->
                let x = (sn, lhs, rhs0, rhsi, i) in
                f x;
                Some x
          in
          ignore (List.fold_left proc None (I.items stat))
      end
      | None -> ()
    in
    (*let iter_items_w ?(from_ith=0) ?(to_ith=0) menv_ f =
      try
        for ith = from_ith to to_ith do
          iter_items ~ith menv_ f
        done
      with
        Exit -> ()
    in*)
    let rec rollback _menv sn =
      [%debug_log "sn=%d" sn];
      match I.top _menv with
      | Some _ -> begin
          let cur_sn = I.current_state_number _menv in
          [%debug_log "cur_sn=%d" cur_sn];
          if cur_sn = sn then
            _menv
          else
            match I.pop _menv with
            | Some me -> rollback me sn
            | None -> _menv
      end
      | None -> _menv
    in
    let rec loop ckpt =
      match ckpt with
      | I.InputNeeded _menv -> begin
          [%debug_log "[InputNeeded] %d" (I.current_state_number _menv)];
          let tok = scanner#get_token() in
          let ckpt = I.offer ckpt tok in
          loop ckpt
      end
      | I.Shifting (_menv, menv_, _) -> begin
          [%debug_log "[Shifting] %d" (I.current_state_number _menv)];
          env#set_shift_flag();
          let ckpt = I.resume ckpt in
          let proc_shift (_, l, r0, r, _) =
            match l, r0, r with
            | I.X (I.N N_file_input_), _, I.X (I.T T_NEWLINE) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_suite), _, I.X (I.T T_INDENT) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_if_stmt), _, I.X (I.T T_COLON) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_if_stmt), _, I.X (I.N N_elifs) -> begin
                save_state menv_;
                raise Exit
            end
            (*| I.X (I.N N_simple_stmt), _, I.X (I.T T_NEWLINE) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_eq_testlists), _, I.X (I.T T_EQ) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_arg_comma_list_), _, I.X (I.T T_COMMA) -> begin
                save_state menv_;
                raise Exit
            end
            | I.X (I.N N_trailer), _, I.X (I.T T_LPAREN) -> begin
                save_state menv_;
                raise Exit
            end*)
            (*| I.X (I.N N_expr_stmt), _, x -> begin
                match x with
                | I.X (I.T T_PLUS_EQ)
                | I.X (I.T T_MINUS_EQ)
                | I.X (I.T T_STAR_EQ)
                | I.X (I.T T_SLASH_EQ)
                | I.X (I.T T_PERCENT_EQ)
                | I.X (I.T T_AMP_EQ)
                | I.X (I.T T_PIPE_EQ)
                | I.X (I.T T_HAT_EQ)
                | I.X (I.T T_LT_LT_EQ)
                | I.X (I.T T_GT_GT_EQ)
                | I.X (I.T T_STAR_STAR_EQ)
                | I.X (I.T T_SLASH_SLASH_EQ)
                  -> begin
                    save_state menv_;
                    raise Exit
                  end
                | _ -> ()
            end*)
            | _ -> ()
          in
          begin
            try
              iter_items menv_ proc_shift
            with
              Exit -> ()
          end;
          loop ckpt
      end
      | I.AboutToReduce (_menv, prod) -> begin
          let last_tok = (Obj.obj env#last_token) in
          let last_rawtok = Token.to_rawtoken last_tok in
          [%debug_log "last_rawtoken=%s paren_count=%d"
            (Token.rawtoken_to_string last_rawtok) scanner#scanner_env#paren_count];
          if !error_state > -1 then begin
            match last_rawtok with
            | T.ERROR _ -> ()
            | _ ->
                error_state := -1;
                rollback_record <- []
          end;
          [%debug_log "[AboutToReduce] %d" (I.current_state_number _menv)];
          begin
            let lhs = I.lhs prod in
            match lhs with
            | I.X (I.N N_stmt) -> save_state _menv
            | _ -> ()
          end;
          let ckpt = I.resume ckpt in
          loop ckpt
      end
      | I.HandlingError _menv -> begin
          let sn = I.current_state_number _menv in
          [%debug_log "[HandlingError] %d" sn];

          let last_token = Obj.obj env#last_token in
          let last_rawtoken = Token.to_rawtoken last_token in
          [%debug_log "last_rawtoken=%s" (Token.rawtoken_to_string last_rawtoken)];

          if keep_going_flag && last_rawtoken != T.EOF then begin
            [%debug_log "error_state=%d" !error_state];
            let to_be_popped =
              !error_state > -1 &&
              match !menv_backup_objs with
              | (_, _, (*_, *)menv0)::_ -> begin
                  try
                    iter_items menv0
                      (function
                        | sn, _, _, _, _ -> let _ = sn in [%debug_log "sn=%d" sn]
                      );
                    false
                  with
                    Exit -> true
              end
              | _ -> false
            in
            [%debug_log "to_be_popped=%B" to_be_popped];
            if to_be_popped then begin
              match !menv_backup_objs with
              | (_, scq, (*soq, *)_)::tl -> begin
                  menv_backup_objs := tl;
                  scanner#prepend_shadow_queue scq;
                  (*scanner#prepend_shadow_q soq;*)
              end
              | _ -> ()
            end;
            let stp, edp = poss_of_menv _menv in
            let loc = U.loc_of_poss stp edp in
            let e = scanner#shadow_outline in
            let err = scanner#shadow_contents in
            (*scanner#reset_shadow_q;*)
            scanner#reset_shadow_queue;
            [%debug_log "shadow_queue(outline): %s" e];
            [%debug_log "shadow_queue: %s" err];
            [%debug_log "shift_flag=%B" env#shift_flag];
            begin
              let len = String.length e in
              for i = len - 1 downto 0 do
                match e.[i] with
                | '(' -> env#close_paren()
                | ')' -> env#open_paren()
                | _ -> ()
              done
            end;
            Aux.warning_loc loc "syntax error: %s" err;

            begin
              let to_be_prepended =
                match !menv_backup_objs with
                | (_, scq0, (*soq0, *)_)::_ -> begin
                    try
                      let rt = Token.to_rawtoken scq0#peek in
                      [%debug_log "%s" (Token.rawtoken_to_string rt)];
                      rt != last_rawtoken
                    with _ -> true
                end
                | _ -> true
              in
              [%debug_log "to_be_prepended=%B" to_be_prepended];
              if to_be_prepended then
                scanner#prepend_token last_token
            end;

            let rawtok = T.ERROR err in
            let tok = Token.create rawtok stp edp in
            scanner#prepend_token tok;

            scanner#reset_paren_level();

            error_state := sn;
            let menv =
              match !menv_backup_objs with
              | (sn0, scq0, (*soq0, *)menv0)::_ -> begin
                  let _ = sn0 in
                  let _ = scq0 in
                  [%debug_log "saved state: %d: %s" sn0 (U.token_queue_to_string scq0)];
                  let rrec = (sn, rawtok) in
                  [%debug_log "rrec=(%d,%s)" sn (Token.rawtoken_to_string rawtok)];
                  if not (List.mem rrec rollback_record) then begin
                    rollback_record <- rrec :: rollback_record;
                    rollback menv0 sn0
                  end
                  else
                    syntax_error _menv
              end
              | _ -> syntax_error _menv
            in
            let ckpt = I.input_needed menv in
            loop ckpt
          end
          else
            syntax_error _menv
      end
      | I.Accepted v -> begin
          v
      end
      | I.Rejected -> raise P.Error
    in
    let do_parse () =
      let ini_pos =
        { Lexing.pos_fname = env#current_filename;
          Lexing.pos_lnum  = 1;
          Lexing.pos_bol   = 0;
          Lexing.pos_cnum  = 0
        }
      in
      let ini_ckpt = P.Incremental.main ini_pos in
      loop ini_ckpt
    in
    parser_main <- do_parse;

    _parse <-
      (fun () ->
	try
	  self#__parse
	with
	| P.Error ->
	    let l, c = env#current_pos_mgr#get_current_position in
            fail_to_parse
              ~head:(Printf.sprintf "[%s:%d:%d]" env#current_filename l c)
              "syntax error"
      )


end (* of class Lib.parser_c *)
]

