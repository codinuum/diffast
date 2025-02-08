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

module Xqueue = Diffast_misc.Xqueue
module Xprint = Diffast_misc.Xprint
module Basic_options = Diffast_misc.Basic_options
module Fs = Diffast_misc.Fs
module Parserlib_base = Langs_common.Parserlib_base
module Scanner = Cpp_parsing.Scanner
module Parser_aux = Cpp_parsing.Parser_aux
module Token = Cpp_parsing.Token
module Source = Cpp_parsing.Source
module Token_seq = Cpp_parsing.Token_seq
module Parser = Cpp_parsing.Parser
module Lib = Cpp_parsing.Lib
module Common = Cpp_parsing.Common
module Label = Cpp_parsing.Label
module Ast = Cpp_parsing.Ast
module Tokens_ = Cpp_parsing.Tokens_

module Aux = Parser_aux
module PB = Parserlib_base
module T = Tokens_

let printf = Printf.printf
let sprintf = Printf.sprintf

type token = Scanner.token

let filename_list = ref []

let verbose_flag = ref true
let dump_ast_flag = ref false
let dump_src_only_flag = ref false

let options = new Basic_options.c

let _ =
  Arg.parse
    [
     (*"-verbose", Arg.Unit (fun () -> verbose_flag := true), "\tdisplay verbose messages";*)
     "-dump-ast", Arg.Unit (fun () -> dump_ast_flag := true), "\tdump AST(s)";
     "-dump-source-only", Arg.Unit (fun () -> dump_src_only_flag := true), "\tonly dump source";
    ]
    (fun s -> filename_list := s :: !filename_list)
    ("usage: " ^ Filename.basename (Sys.argv.(0))
     ^ " [OPTIONS] [FILE..]\noptions are:")

let mode_to_string = Aux.parsing_mode_to_string
let mktok rt = rt, Lexing.dummy_pos, Lexing.dummy_pos

class parser_c = object (self)
  val mutable _parse = fun () -> Obj.magic ()
  val mutable tokens_read = 0
  val env = new Aux.env
  val token_queue = Queue.create()

  method tokens_read = tokens_read

  method get_token () =
    let rt = Queue.take token_queue in
    [%debug_log "----- %s" (Token.rawtoken_to_string rt)];
    mktok rt

  method parse_file fname =
    let file = Fs.file_of_path options fname in
    let _ = env#enter_source (new Source.c file) in
    env#set_current_filename fname;
    Token_seq.queue_from_file token_queue fname;
    _parse()

  initializer
    if !verbose_flag then
      env#set_verbose_flag;

    env#set_parse_tokens_flag();

    let module S = struct
      let env = env
    end
    in
    let module P = Parser.Make (S) in
    let module I = P.MenhirInterpreter in

    let lexpos_of_menv _menv =
      match I.get 0 _menv with
      | Some (I.Element (_, _, _, edp)) -> begin
          edp
      end
      | _ -> Lexing.dummy_pos
    in

    let rec loop ?(mode=Aux.M_NORMAL) ?(get_token=self#get_token) ckpt =
      match ckpt with
      | I.InputNeeded _menv -> begin
          let tok = get_token() in
          tokens_read <- tokens_read + 1;
          let ckpt = I.offer ckpt tok in
          loop ~mode ~get_token ckpt
      end
      | I.Shifting (_menv, _, _) -> begin
          let ckpt = I.resume ckpt in
          loop ~mode ~get_token ckpt
      end
      | I.AboutToReduce (_menv, _) -> begin
          let ckpt = I.resume ckpt in
          loop ~mode ~get_token ckpt
      end
      | I.HandlingError _menv -> begin
          raise (Lib.Failed_to_parse (lexpos_of_menv _menv))
      end
      | I.Accepted v -> begin
          begin
            match mode with
            | M_DECLS_SUB s | M_MEM_DECLS_SUB s | M_STMTS_SUB s | M_EXPR_SUB s
            | M_INIT_SUB s | M_TYPE_SUB s | M_SPECS_SUB s | M_DTORS_SUB s | M_ETORS_SUB s
            | M_OBJC_DECLS_SUB s when env#verbose_flag
              -> printf "  macro parsed: %s\n" s
            | _ when env#verbose_flag
              -> printf "PARSED: %s\n" (Common.relpath env#current_filename);
            | _ -> ()
          end;
          v
      end
      | I.Rejected -> assert false
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
      let root = loop ini_ckpt in

      if true then begin

        env#iter_pending_macro
          (fun name (pnd, macro_kind, tok_list_obj) ->
            [%debug_log "pending_macro (%s): %s"
              (match macro_kind with
              | ObjectLike -> "object-like"
              | FunctionLike _ -> "function-like"
              | MK_DUMMY -> "DUMMY"
              ) name];

            if macro_kind == MK_DUMMY then
              ()
            else

            let setup_macro_node nd =
              let mnd =
                let lab =
                  match macro_kind with
                  | ObjectLike -> Label.ObjectLikeMacro
                  | FunctionLike _ -> Label.FunctionLikeMacro macro_kind
                  | _ -> assert false
                in
                new Ast.node ~lloc:(nd#lloc) ~children:[nd] lab
              in
              pnd#set_children [mnd]
            in

            let tok_list = (Obj.obj tok_list_obj : token list) in

            let q0 = new Xqueue.c in
            let has_pp_flag = ref false in
            let _ =
              List.iter
                (fun t ->
                  let rt, _, _ = t in
                  begin
                    match (rt : T.token) with
                    | PP_ERROR | PP_INCLUDE -> has_pp_flag := true
                    | _ -> ()
                  end;
                  [%debug_log "queuing %s" (Token.rawtoken_to_string rt)];
                  q0#add t
                ) tok_list;
              if !has_pp_flag then
                q0#add (mktok T.NEWLINE);
              q0#add (mktok T.EOF)
            in

            let mode =
              let rt, _, _ = q0#take in
              match rt with
              | PMODE m -> m
              | _ ->
                  [%debug_log "%s" (Token.rawtoken_to_string rt)];
                  assert false
            in
            [%debug_log "mode=%s" (mode_to_string mode)];

            let get_token () =
              let rt, _, _ as t = q0#take in
              let _ = rt in
              [%debug_log "----- %s" (Token.rawtoken_to_string rt)];
              t
            in
            try
              let parse_sub =
                match mode with
                | M_DECLS_SUB _ -> P.Incremental.decls_sub
                | M_MEM_DECLS_SUB _ -> P.Incremental.mem_decls_sub
                | M_STMTS_SUB _ -> P.Incremental.stmts_sub
                | M_EXPR_SUB _ -> P.Incremental.expr_sub
                | M_INIT_SUB _ -> P.Incremental.init_sub
                | M_TYPE_SUB _ -> P.Incremental.type_sub
                | M_SPECS_SUB _ -> P.Incremental.specs_sub
                | M_DTORS_SUB _ -> P.Incremental.dtors_sub
                | M_ETORS_SUB _ -> P.Incremental.etors_sub
                | M_OBJC_DECLS_SUB _ -> P.Incremental.objc_decls_sub
                | m ->
                    let _ = m in
                    [%debug_log "%s" (mode_to_string m)];
                    assert false
              in
              [%debug_log "parsing %s with %s" name (mode_to_string mode)];
              let ckpt = parse_sub ini_pos in
              let nd = loop ~mode ~get_token ckpt in
              setup_macro_node nd
            with
              Lib.Failed_to_parse pos -> begin
                [%debug_log "failed to parse %s" name];
                Xprint.warning "failed to parse %s" name;
                raise (Lib.Failed_to_parse pos)
              end
          )
      end;

      new Ast.c root
    in
    _parse <- fun () ->
      try
        do_parse()
      with
        Lib.Failed_to_parse _ ->
          let mes =
            sprintf "failed to parse \"%s\" (%d)"
              (Common.relpath env#current_filename)
              self#tokens_read
          in
          raise (PB.Parse_error("", mes))

end


let proc filename =
  if !dump_src_only_flag then begin
    let q = Queue.create() in
    Token_seq.queue_from_file q filename;
    let prev = ref T.EOF in
    try
      while true do
        let rt = Queue.take q in
        begin
          match rt with
          | PP_IF_ATTR | PP_IFDEF_ATTR | PP_IFNDEF_ATTR
          | PP_IF_COND | PP_IFDEF_COND | PP_IFNDEF_COND
          | PP_IF_COND_ | PP_IFDEF_COND_ | PP_IFNDEF_COND_
          | PP_IF_D | PP_IFDEF_D | PP_IFNDEF_D
          | PP_IF_E | PP_IFDEF_E | PP_IFNDEF_E
          | PP_IF_EH | PP_IFDEF_EH | PP_IFNDEF_EH
          | PP_IF_I | PP_IFDEF_I | PP_IFNDEF_I
          | PP_IF_A | PP_IFDEF_A | PP_IFNDEF_A
          | PP_IF_B | PP_IFDEF_B | PP_IFNDEF_B
          | PP_IF_BROKEN | PP_IFDEF_BROKEN | PP_IFNDEF_BROKEN
          | PP_IF_X | PP_IFDEF_X | PP_IFNDEF_X
          | PP_IF_C | PP_IFDEF_C | PP_IFNDEF_C
          | PP_IF_CB | PP_IFDEF_CB | PP_IFNDEF_CB
          | PP_IF_H | PP_IFDEF_H | PP_IFNDEF_H
          | PP_IF_O | PP_IFDEF_O | PP_IFNDEF_O
          | PP_IF_P | PP_IFDEF_P | PP_IFNDEF_P
          | PP_IF_S | PP_IFDEF_S | PP_IFNDEF_S
          | PP_IF_SHIFT | PP_IFDEF_SHIFT | PP_IFNDEF_SHIFT
          | PP_IF_CLOSING | PP_IFDEF_CLOSING | PP_IFNDEF_CLOSING
          | PP_IF_CLOSE_OPEN | PP_IFDEF_CLOSE_OPEN | PP_IFNDEF_CLOSE_OPEN
          | PP_ODD_IF | PP_ODD_IFDEF | PP_ODD_IFNDEF
          | PP_ODD_ELIF _
          | PP_ODD_ELSE _
          | PP_ODD_ENDIF _
          | PP_INCLUDE
          | PP_DEFINE
          | PP_UNDEF
          | PP_LINE
          | PP_ERROR
          | PP_PRAGMA
          | PP_IMPORT
          | PP_
          | PP_IF | PP_IFDEF | PP_IFNDEF
          | PP_ELIF _
          | PP_ELSE _
          | PP_ENDIF _ | PP_ENDIF_
          | PP_UNKNOWN _ when !prev != NEWLINE -> printf "\n"
          | _ -> ()
        end;
        let repr = Token.rawtoken_to_repr rt in
        printf "%s" repr;
        begin
          match rt with
          | NEWLINE -> ()
          | _ -> printf " "
        end;
        prev := rt
      done
    with
      _ -> printf "\n"
  end
  else begin
    try
      let parser0 = new parser_c in
      let ast = parser0#parse_file filename in
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
          (*| exn -> begin
            Xprint.error "!!! %s" (Printexc.to_string exn);
            exit 1
            end*)
  end

let _ =
  List.iter proc (List.rev !filename_list)
