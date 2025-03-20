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
 * A lexer (utf-8) for the Python programming language
 *
 * ulexer.ml
 *
 *)

[%%prepare_logger]

module Xqueue = Diffast_misc.Xqueue
module Xstring = Diffast_misc.Xstring
module Astloc = Langs_common.Astloc
module Parserlib_base = Langs_common.Parserlib_base

open Printf

open Tokens_
open Common


module PB = Parserlib_base
module Aux = Parser_aux

type longstringmode = LSMfalse | LSMsingle | LSMdouble

exception Illegal_indent

let default_tab_size = 8

let space_only = String.for_all (fun c -> c = ' ')


let lexing_pos_start = Langs_common.Position.lexing_pos_start
let lexing_pos_end = Langs_common.Position.lexing_pos_end
let get_lc = Langs_common.Position.get_lc


let mktok rawtok ulexbuf =
  let st_pos = lexing_pos_start ulexbuf in
  let ed_pos = lexing_pos_end ulexbuf in
  Token.create rawtok st_pos ed_pos


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  open Stat

  let lexeme = Sedlexing.Utf8.lexeme
  let from_string = Sedlexing.Utf8.from_string


  let loc_of_poss = Astloc.of_lexposs


  let lexing_error lexbuf msg =
    let loc = loc_of_poss (lexing_pos_start lexbuf) (lexing_pos_end lexbuf) in
    Common.fail_to_parse ~head:(Astloc.to_string ~prefix:"[" ~suffix:"]" loc) msg


  let find_keyword =
    let keyword_list =
      [
        "and",      AND;
        "assert",   ASSERT;
        "break",    BREAK;
        "class",    CLASS;
        "continue", CONTINUE;
        "def",      DEF;
        "del",      DEL;
        "elif",     ELIF;
        "else",     ELSE;
        "except",   EXCEPT;
        (*"exec",     EXEC;*)
        "finally",  FINALLY;
        "for",      FOR;
        "from",     FROM;
        "global",   GLOBAL;
        "if",       IF;
        "import",   IMPORT;
        "in",       IN;
        "is",       IS;
        "lambda",   LAMBDA;
        "not",      NOT;
        "or",       OR;
        "pass",     PASS;
        (*"print",    PRINT;*)
        "raise",    RAISE;
        "return",   RETURN;
        "try",      TRY;
        "while",    WHILE;
        "yield",    YIELD;

        "await",    AWAIT;
        "async",    ASYNC;
        "nonlocal", NONLOCAL;
      ] in
    let keyword_table = Hashtbl.create (List.length keyword_list) in
    let _ =
      List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
        keyword_list
    in
    let with_keywords = [ "as", AS; "with", WITHx ] in
    let find s =
      try
        Hashtbl.find keyword_table s
      with
        Not_found ->
          if env#with_stmt_enabled then
            try
              List.assoc s with_keywords
            with
              Not_found -> NAMEx s
          else
            NAMEx s
    in
    find

  type token_t = Tokens_.token * Lexing.position * Lexing.position

  class scanner_env = object (self)

    val mutable longstringmode = LSMfalse

    val indent_stack = Stack.create()
    val token_queue = (new Xqueue.c : token_t Xqueue.c)
    val mutable paren_count = 0
    val mutable last_indent = ""
    val mutable last_indent_len = 0
    val mutable newline_flag = false
    val mutable last_ofs = 0
    val mutable tab_size = default_tab_size

    method set_tab_size n =
      [%debug_log "%d -> %d" tab_size n];
      tab_size <- n

    method indent_length ind =
      (*[%debug_log "ind=\"%s\"(%d)" (Xstring.encode ind) (String.length ind)];*)
      let c = ref 0 in
      let add_tab() =
        let n = !c mod tab_size in
        c := !c + tab_size - n
      in
      let n = String.length ind in
      (*[%debug_log "n=%d" n];*)
      if n > 0 then begin
        if ind.[0] = '\012' then
          ()
        else if ind.[0] = '\009' then
          add_tab()
        else if ind.[0] = ' ' then
          incr c
        else
          raise Illegal_indent;
        if n > 1 then
          for i = 1 to n - 1 do
            if ind.[i] = '\009' then
              add_tab()
            else if ind.[i] = ' ' then
              incr c
            else
              raise Illegal_indent
          done
      end;
      (*[%debug_log "length=%d" !c];*)
      !c

    method newline_flag = newline_flag
    method set_newline_flag () = newline_flag <- true
    method clear_newline_flag () = newline_flag <- false

    method last_indent = last_indent
    method set_last_indent ind =
      [%debug_log "%s" (Xstring.encode ind)];
      last_indent <- ind

    method last_indent_len = last_indent_len
    method set_last_indent_len n =
      [%debug_log "%d" n];
      last_indent_len <- n

    method longstringmode = longstringmode
    method set_longstringmode m = longstringmode <- m

    method push_indent n =
      [%debug_log "pushed %d" n];
      Stack.push n indent_stack

    method pop_indent () =
      let n = Stack.pop indent_stack in
      [%debug_log "poped %d" n];
      n

    method top_of_indent_stack = Stack.top indent_stack
    method indent_stack_iter f = Stack.iter f indent_stack
    method indent_stack_len = Stack.length indent_stack
    method is_valid_indent x =
      [%debug_log "%d" x];
      let b =
        try
          Stack.iter
            (fun i ->
              [%debug_log "%d" i];
              if i = x then raise Exit
            ) indent_stack;
          false
        with
          Exit -> true
      in
      [%debug_log "%B" b];
      b

    method init_indent_stack () =
      Stack.clear indent_stack;
      Stack.push 0 indent_stack

    method add_token t =
      [%debug_log "added %s" (Token.to_string t)];
      token_queue#add t

    method take_token () =
      let t = token_queue#take in
      [%debug_log "taken %s" (Token.to_string t)];
      t

    method is_token_queue_empty = token_queue#is_empty
    method init_token_queue () = token_queue#clear

    method paren_in () = paren_count <- paren_count + 1
    method paren_out () = paren_count <- paren_count - 1
    method in_paren = paren_count > 0
    method paren_count = paren_count
    method init_paren () = paren_count <- 0


    method init =
      self#set_longstringmode LSMfalse;
      self#init_indent_stack();
      self#init_token_queue();
      self#init_paren()

    initializer
      self#init

  end (* of Ulexer.scanner_env *)



  let line_terminator = [%sedlex.regexp? Chars "\013\010" | "\013\010"]

  let white_space = [%sedlex.regexp? Chars " \009\012"]

  let indent = [%sedlex.regexp? Opt '\012', Star (Chars " \009")]

  let line_comment = [%sedlex.regexp? '#', Star (Compl (Chars "\013\010"))]

  let null_lines = [%sedlex.regexp? Plus line_terminator, Star (indent, Opt line_comment, Plus line_terminator)]

  let line_join = [%sedlex.regexp? '\\', line_terminator]

  let letter = [%sedlex.regexp?
   'A'..'Z' | 'a'..'z' |
   128 .. 255 | 880 .. 1023 | 1024 .. 1279 | 2304 .. 2431 |
   4352 .. 4607 | 43360 .. 43391 | 44032 .. 55215 | 55216 .. 55295
  ]

  let digit = [%sedlex.regexp? '0'..'9']
  let identifier = [%sedlex.regexp? (letter | '_'), Star (letter | digit | '_')]

  let escapeseq = [%sedlex.regexp? '\\', any]

  let longstring_single_quote = [%sedlex.regexp? "'''"]
  let longstring_double_quote = [%sedlex.regexp? "\"\"\""]
  let longstringchar = [%sedlex.regexp? Compl '\\']
  let shortstringchar_single = [%sedlex.regexp? Compl (Chars "\\\013\010'")]
  let shortstringchar_double = [%sedlex.regexp? Compl (Chars "\\\013\010\"")]

  let longstringitem = [%sedlex.regexp? longstringchar | escapeseq]
  let shortstringitem_single = [%sedlex.regexp? shortstringchar_single | escapeseq]
  let shortstringitem_double = [%sedlex.regexp? shortstringchar_double | escapeseq]

  let shortstring = [%sedlex.regexp?
    '\'', Star shortstringitem_single, '\'' |
    '"', Star shortstringitem_double, '"'
  ]

  let stringprefix = [%sedlex.regexp?
    "r" | "u" | "R" | "U" | "f" | "F" | "fr" | "Fr" | "fR" | "FR" |
    "rf" | "rF" | "Rf" | "RF" | "ur" | "UR" | "Ur" | "uR" |
    "b" | "B" | "br" | "Br" | "bR" | "BR" | "rb" | "rB" | "Rb" | "RB"
  ]

  let string = [%sedlex.regexp? Opt stringprefix, shortstring]

  let longstring_start_single = [%sedlex.regexp? Opt stringprefix, longstring_single_quote]
  let longstring_start_double = [%sedlex.regexp? Opt stringprefix, longstring_double_quote]

  let hexdigit = [%sedlex.regexp? '0'..'9' | 'a'..'f' | 'A'..'F']
  let hexinteger = [%sedlex.regexp? '0', Chars "xX", Plus (Opt '_', hexdigit)]
  let octinteger = [%sedlex.regexp? '0', Chars "oO", Plus (Opt '_', '0'..'7')]
  let bininteger = [%sedlex.regexp? '0', Chars "bB", Plus (Opt '_', '0'..'1')]
  let decimalinteger = [%sedlex.regexp? '0', Star (Opt '_', '0') | '1'..'9', Star (Opt '_', digit)]
  let integer = [%sedlex.regexp? decimalinteger | bininteger | octinteger | hexinteger]
  let longinteger = [%sedlex.regexp? integer, Chars "lL"]

  let exponent = [%sedlex.regexp? Chars "eE", Opt (Chars "+-"), Plus digit]
  let intpart = [%sedlex.regexp? digit, Star (Opt '_', digit)]
  let pointfloat = [%sedlex.regexp? Opt intpart, '.', Plus digit | intpart, '.']
  let exponentfloat = [%sedlex.regexp? (intpart|pointfloat), exponent]
  let floatnumber = [%sedlex.regexp? pointfloat | exponentfloat]
  let imagnumber = [%sedlex.regexp? (floatnumber | Plus digit), Chars "jJ"]

  let conflict_marker = [%sedlex.regexp? null_lines, ("<<<<<<<" | "|||||||" | "=======" | ">>>>>>>")]


  let rec token scanner_env lexbuf =
    match %sedlex lexbuf with

    | line_join -> token scanner_env lexbuf

    | white_space -> token scanner_env lexbuf

    | line_comment -> begin
        let c = lexeme lexbuf in
        [%debug_log "[COMMENT] \"%s\"" c];
        let sp, ep = lexing_pos_start lexbuf, lexing_pos_end lexbuf in
        [%debug_log "[COMMENT] region: %d-%d" sp.Lexing.pos_cnum ep.Lexing.pos_cnum];
        let loc = loc_of_poss sp ep in
        [%debug_log "loc=%s" (Astloc.to_string loc)];
        if env#ignore_comment_flag then
          env#comment_regions#add loc
        else begin
          [%debug_log "c=%s" c];
          env#add_comment (Ast.make_comment loc c);
          [%debug_log "last_range -> %s" (Astloc.to_string loc)];
          let st, ed = Astloc.to_lexposs loc in
          env#set_last_range (st, ed)
        end;

        token scanner_env lexbuf
    end
    | integer                 -> mktok (INTEGER (lexeme lexbuf)) lexbuf
    | longinteger             -> mktok (LONGINTEGER (lexeme lexbuf)) lexbuf
    | floatnumber             -> mktok (FLOATNUMBER (lexeme lexbuf)) lexbuf
    | imagnumber              -> mktok (IMAGNUMBER (lexeme lexbuf)) lexbuf
    | longstring_start_single -> mktok (LONGSTRING_BEGIN_S (lexeme lexbuf)) lexbuf
    | longstring_start_double -> mktok (LONGSTRING_BEGIN_D (lexeme lexbuf)) lexbuf
    | string                  -> mktok (SHORTSTRING (lexeme lexbuf)) lexbuf

    | conflict_marker -> begin
        let m = Xstring.lstrip (lexeme lexbuf) in
        let nl = mktok (NEWLINE scanner_env#top_of_indent_stack) lexbuf in
        marker nl scanner_env (lexing_pos_start lexbuf) m lexbuf
    end
    | null_lines -> begin
        scanner_env#set_newline_flag();
        let sp, ep = lexing_pos_start lexbuf, lexing_pos_end lexbuf in
        let s = lexeme lexbuf in
        [%debug_log "[NULL_LINES] \"%s\": region: %d-%d" s sp.Lexing.pos_cnum ep.Lexing.pos_cnum];
        [%debug_log "encoded: %s" (Xstring.encode s)];

        if env#ignore_comment_flag then begin
          env#blank_regions#add (loc_of_poss sp ep);
          if scanner_env#in_paren then begin
            let ind = indent lexbuf in
            let ind_len = scanner_env#indent_length ind in
            scanner_env#set_last_indent ind;
            scanner_env#set_last_indent_len ind_len;
            token scanner_env lexbuf
          end
          else begin
            [%debug_log "checking indent..."];
            let ind = indent lexbuf in (* next indent *)
            check_indent scanner_env ind lexbuf
          end
        end
        else
          check_null_lines scanner_env sp s lexbuf;
    end
    | "==" -> mktok EQ_EQ lexbuf
    | "<=" -> mktok LT_EQ lexbuf
    | ">=" -> mktok GT_EQ lexbuf
    | "!=" -> mktok EXCLAM_EQ lexbuf
    | "<>" -> mktok LT_GT lexbuf

    | "**" -> mktok STAR_STAR lexbuf
    | "//" -> mktok SLASH_SLASH lexbuf
    | "<<" -> mktok LT_LT lexbuf
    | ">>" -> mktok GT_GT lexbuf

    | "+="  -> mktok PLUS_EQ lexbuf
    | "-="  -> mktok MINUS_EQ lexbuf
    | "*="  -> mktok STAR_EQ lexbuf
    | "/="  -> mktok SLASH_EQ lexbuf
    | "//=" -> mktok SLASH_SLASH_EQ lexbuf
    | "%="  -> mktok PERCENT_EQ lexbuf
    | "&="  -> mktok AMP_EQ lexbuf
    | "|="  -> mktok PIPE_EQ lexbuf
    | "^="  -> mktok HAT_EQ lexbuf
    | ">>=" -> mktok GT_GT_EQ lexbuf
    | "<<=" -> mktok LT_LT_EQ lexbuf
    | "**=" -> mktok STAR_STAR_EQ lexbuf
    | ":="  -> mktok COLON_EQ lexbuf

    | "->"  -> mktok MINUS_GT lexbuf
    | "..." -> mktok ELLIPSIS lexbuf

    | '+' -> mktok PLUS lexbuf
    | '-' -> mktok MINUS lexbuf
    | '*' -> mktok STAR lexbuf
    | '/' -> mktok SLASH lexbuf
    | '%' -> mktok PERCENT lexbuf
    | '&' -> mktok AMP lexbuf
    | '|' -> mktok PIPE lexbuf
    | '^' -> mktok HAT lexbuf
    | '~' -> mktok TILDE lexbuf
    | '>' -> mktok GT lexbuf
    | '<' -> mktok LT lexbuf

    | '(' -> scanner_env#paren_in(); mktok LPAREN lexbuf
    | ')' -> scanner_env#paren_out(); mktok RPAREN lexbuf
    | '{' -> scanner_env#paren_in(); mktok LBRACE lexbuf
    | '}' -> scanner_env#paren_out(); mktok RBRACE lexbuf
    | '[' -> scanner_env#paren_in(); mktok LBRACKET lexbuf
    | ']' -> scanner_env#paren_out(); mktok RBRACKET lexbuf
    | '@' -> mktok AT lexbuf
    | ',' -> mktok COMMA lexbuf
    | ':' -> mktok COLON lexbuf
    | '.' -> mktok DOT lexbuf
    | '`' -> mktok BACKQUOTE lexbuf
    | '=' -> mktok EQ lexbuf
    | ';' -> mktok SEMICOLON lexbuf


    | '$' -> mktok DEDENT lexbuf (* illegal in python! *)

    | identifier -> mktok (find_keyword (lexeme lexbuf)) lexbuf

    | eof -> begin
        let n = scanner_env#indent_stack_len - 1 in
        if n > 0 then begin
          for _ = 1 to n do
            ignore (scanner_env#pop_indent());
            scanner_env#add_token (mktok DEDENT lexbuf)
          done
        end;
        (mktok EOF lexbuf)
    end
    | any -> begin
        let sym = lexeme lexbuf in
        if sym = "\"" then
          lexing_error lexbuf "invalid single-quated string"
        else
          lexing_error lexbuf (sprintf "invalid symbol(%s)" sym)
    end
    | _ -> failwith "Ulexer.token"

(*
  and line_comment lexbuf =
  match %sedlex lexbuf with
  | line_terminator -> ()
  | _ -> line_comment lexbuf
*)

  and handle_indent
      ?(eof_flag=false)
      ?(prepend_opt=None)
      ?(use_last_range=true)
      scanner_env ind_len lexbuf
      =
    [%debug_log "eof_flag=%B use_last_range=%B" eof_flag use_last_range];
    [%debug_log "ind_len=%d" ind_len];
    let tok_consumer =
      match prepend_opt with
      | Some prepend -> prepend
      | None -> scanner_env#add_token
    in
    let top = scanner_env#top_of_indent_stack in
    [%debug_log "top=%d" top];
    if not eof_flag && ind_len = top then
      ()
    else if ind_len > top then begin
      scanner_env#push_indent ind_len;
      tok_consumer (mktok INDENT lexbuf)
    end
    else if eof_flag || ind_len < top then begin
      let ok = ref false in
      scanner_env#indent_stack_iter (fun n -> if n = ind_len then ok := true);
      [%debug_log "ok=%B" !ok];
      if !ok then begin
        let c = ref 0 in
        if eof_flag then
          incr c;
        scanner_env#indent_stack_iter
          (fun n ->
            [%debug_log "n=%d" n];
            if eof_flag || n > ind_len then begin
              let _ = scanner_env#pop_indent() in
              incr c
            end);
        let mkt =
          if use_last_range then
            fun rt ->
              let _, ed = env#last_range in
              Token.create rt ed ed
          else
            fun rt -> (mktok rt lexbuf)
        in
        if !c > 0 then begin
          for i = 1 to !c do
            let _ = i in
            let t = mkt DEDENT in
            [%debug_log "[%d] %s" i (Token.to_string t)];
            tok_consumer t
          done
        end
        else
          raise Illegal_indent
      end
      else
        raise Illegal_indent
    end
    else
      raise Illegal_indent; (* impossible *)

  and check_indent
      ?(token_maker_opt=None)
      scanner_env ind lexbuf
      =
    let token_maker =
      match token_maker_opt with
      | Some f -> f
      | None -> fun rt -> mktok rt lexbuf
    in
    let last_ind = scanner_env#last_indent in
    let last_ind_len = scanner_env#last_indent_len in
    [%debug_log "last_ind=%s last_ind_len=%d" (Xstring.encode last_ind) last_ind_len];
    [%debug_log "ind=%s" (Xstring.encode ind)];
    if
      last_ind <> "" &&
      space_only last_ind &&
      ind = "\t"
    then begin
      [%debug_log "inconsistent use of tab and space in indentation"];
      let st, ed = lexing_pos_start lexbuf, lexing_pos_end lexbuf in
      let loc = loc_of_poss st ed in
      Aux.warning_loc loc "inconsistent use of tab and space in indentation";
      scanner_env#set_tab_size last_ind_len
    end;
    let ind_len = scanner_env#indent_length ind in
    [%debug_log "ind_len=%d" ind_len];
    scanner_env#set_last_indent ind;
    scanner_env#set_last_indent_len ind_len;
    handle_indent scanner_env ind_len lexbuf;
    token_maker (NEWLINE ind_len)

  and check_null_lines scanner_env sp str lexbuf =
    [%debug_log "str=%s" str];
    [%debug_log "%s" (Astloc.to_string (loc_of_poss sp sp))];
    let last_ind_len = scanner_env#last_indent_len in
    [%debug_log "last_ind_len=%d" last_ind_len];
    let next_ind_opt =
      if scanner_env#in_paren then
        None
      else
        let next_ind = indent lexbuf in
        [%debug_log "next_ind=\"%s\"(%d)" (Xstring.encode next_ind) (String.length next_ind)];
        Some next_ind
    in
    let comment_buf = Buffer.create 0 in
    let ind_buf = Buffer.create 0 in
    let in_comment_flag = ref false in
    let comment_start_pos = ref Lexing.dummy_pos in
    let blank_start_pos = ref Lexing.dummy_pos in
    let blank_end_pos = ref Lexing.dummy_pos in

    let rec scan ulb =
      match %sedlex ulb with
      | Chars "\013\010" -> begin
          [%debug_log "@"];
          if !in_comment_flag then begin
            let comment0 = Buffer.contents comment_buf in
            let sp0 = !comment_start_pos in
            let ep0 = lexing_pos_end ulb in
            let loc0 = loc_of_poss sp0 ep0 in
            [%debug_log "loc0=%s comment0=%s" (Astloc.to_string loc0) comment0];
            env#add_comment (Ast.make_comment loc0 comment0);
            if not env#ignore_comment_flag then begin
              [%debug_log "last_range -> %s" (Astloc.to_string loc0)];
              env#set_last_range (sp0, ep0)
            end;
            Buffer.clear comment_buf;
            in_comment_flag := false
          end
          else begin
            Buffer.clear ind_buf;
            if !blank_start_pos != Lexing.dummy_pos && !blank_end_pos != Lexing.dummy_pos then begin
              let loc0 = loc_of_poss !blank_start_pos !blank_end_pos in
              [%debug_log "blank: %s" (Astloc.to_string loc0)];
              env#blank_regions#add loc0;
              blank_start_pos := Lexing.dummy_pos;
              blank_end_pos := Lexing.dummy_pos
            end
          end;
          scan ulb
      end
      | '#' -> begin
          if !in_comment_flag then begin
            let s = lexeme ulb in
            [%debug_log "s=%s" (String.escaped s)];
            Buffer.add_string comment_buf s;
            scan ulb
          end
          else begin
            let s = lexeme ulb in
            [%debug_log "s=%s" (String.escaped s)];
            begin
              let ind = Buffer.contents ind_buf in
              let ind_len = scanner_env#indent_length ind in
              [%debug_log "ind_len=%d" ind_len];
              let ok =
                not scanner_env#in_paren &&
                (
                 match next_ind_opt with
                 | None -> true
                 | Some "" -> true
                 | Some next_ind ->
                     let next_ind_len = scanner_env#indent_length next_ind in
                     [%debug_log "next_ind_len=%d" next_ind_len];
                     scanner_env#is_valid_indent next_ind_len &&
                     next_ind_len <= ind_len
                ) &&
                (
                 ind_len = last_ind_len ||
                 if ind_len < last_ind_len then begin
                   [%debug_log "%d < %d" ind_len last_ind_len];
                   let last_tok = (Obj.obj env#last_token) in
                   let last_rawtok = Token.to_rawtoken last_tok in
                   last_rawtok != COLON
                 end
                 else
                   true
                )
              in
              [%debug_log "ok=%B" ok];
              if ok then begin
                scanner_env#set_last_indent ind;
                scanner_env#set_last_indent_len ind_len;
                handle_indent scanner_env ind_len lexbuf;
              end;
              Buffer.clear ind_buf
            end;
            if !blank_start_pos != Lexing.dummy_pos && !blank_end_pos != Lexing.dummy_pos then begin
              let loc0 = loc_of_poss !blank_start_pos !blank_end_pos in
              [%debug_log "blank: %s" (Astloc.to_string loc0)];
              env#blank_regions#add loc0;
              blank_start_pos := Lexing.dummy_pos;
              blank_end_pos := Lexing.dummy_pos
            end;
            Buffer.add_string comment_buf s;
            comment_start_pos := lexing_pos_start ulb;
            in_comment_flag := true;
            scan ulb
          end
      end
      | Chars "\012 \009" -> begin
          let s = lexeme ulb in
          [%debug_log "s=%s" (String.escaped s)];
          if !in_comment_flag then begin
            Buffer.add_string comment_buf s
          end
          else begin
            Buffer.add_string ind_buf s;
            let pos = lexing_pos_start ulb in
            if !blank_start_pos == Lexing.dummy_pos then begin
              blank_start_pos := pos;
              blank_end_pos := pos
            end
            else if !blank_end_pos != Lexing.dummy_pos then
              blank_end_pos := Astloc.incr_lexpos !blank_end_pos;
          end;
          scan ulb
      end
      | any -> begin
          let s = lexeme ulb in
          [%debug_log "s=%s" (String.escaped s)];
          if !in_comment_flag then
            Buffer.add_string comment_buf s;
          scan ulb
      end
      | eof -> begin
          [%debug_log "eof"]
      end
      | _ -> failwith "Ulexer.F.check_null_lines.scan"
    in
    let ulb = from_string str in
    Sedlexing.set_position ulb sp;
    scan ulb;

    if !blank_start_pos != Lexing.dummy_pos && !blank_end_pos != Lexing.dummy_pos then begin
      let loc0 = loc_of_poss !blank_start_pos !blank_end_pos in
      [%debug_log "blank: %s" (Astloc.to_string loc0)];
      env#blank_regions#add loc0
    end;

    if scanner_env#in_paren then begin
      let ind = indent lexbuf in
      let ind_len = scanner_env#indent_length ind in
      scanner_env#set_last_indent ind;
      scanner_env#set_last_indent_len ind_len;
      token scanner_env lexbuf
    end
    else begin
      [%debug_log "checking next indent..."];
      match next_ind_opt with
      | Some next_ind -> begin
          let ep =
            try
              if str.[0] == '\013' && str.[1] == '\010' then
                Astloc.incr_lexpos sp
              else
                sp
            with
              _ -> sp
          in
          let token_maker rt = Token.create rt sp ep in
          let token_maker_opt = Some token_maker in
          check_indent ~token_maker_opt scanner_env next_ind lexbuf
      end
      | None -> assert false
    end


  and indent lexbuf =
    match %sedlex lexbuf with
    | indent -> begin
        let st, ed = lexing_pos_start lexbuf, lexing_pos_end lexbuf in
        [%debug_log "[INDENT] \"%s\": region: %d-%d"
          (Xstring.encode (lexeme lexbuf)) st.Lexing.pos_cnum ed.Lexing.pos_cnum];
        (*env#blank_regions#add (loc_of_poss st ed);*)
        lexeme lexbuf
    end
    | _ -> failwith "Ulexer.indent"


  and longstring_single s lexbuf =
    match %sedlex lexbuf with
    | longstring_single_quote -> mktok (LONGSTRING_REST (s^(lexeme lexbuf))) lexbuf
    | longstringitem -> longstring_single (s^(lexeme lexbuf)) lexbuf
    | _ -> failwith "Ulexer.longstring_single"


  and longstring_double s lexbuf =
    match %sedlex lexbuf with
    | longstring_double_quote -> mktok (LONGSTRING_REST (s^(lexeme lexbuf))) lexbuf
    | longstringitem -> longstring_double (s^(lexeme lexbuf)) lexbuf
    | _ -> failwith "Ulexer.longstring_double"


  and marker nl scanner_env st s lexbuf =
    match %sedlex lexbuf with
    | null_lines -> begin
        let ind = indent lexbuf in
        let _ = check_indent scanner_env ind lexbuf in
        let mtok = (MARKER s), st, lexing_pos_end lexbuf in
        scanner_env#add_token mtok;
        nl
    end
    | any -> marker nl scanner_env st (s^(lexeme lexbuf)) lexbuf
    | _ -> failwith "Ulexer.marker"


  let peek_nth queue scanner_env ulexbuf nth =
    let t_opt = ref None in
    let count = ref 0 in
    begin
      try
        queue#iter
          (fun t ->
            if !count = nth then
              raise Exit;

            t_opt := Some t;
            incr count
          );

        for _ = 1 to  nth - !count do
          let t = token scanner_env ulexbuf in
          queue#add t;
          t_opt := Some t
        done
      with
        Exit -> ()
    end;
    match !t_opt with
    | Some t ->
        let tok = Token.to_rawtoken t in
        [%debug_log "nth=%d tok=%s" nth (Token.rawtoken_to_string tok)];
        t, tok
    | None -> assert false

  let token_queue_to_string tq =
    let is_alpha_numeric c =
      match c with
      | '0'..'9' | 'a'..'z' | 'A'..'Z' -> true
      | _ -> false
    in
    let buf = Buffer.create 0 in
    tq#iter
      (fun t ->
        let s = Token.to_orig t in
        begin
          match s with
          | "." | ")" | "," | ";" | "}" | "]" -> ()
          | _ -> begin
              let buf_len = Buffer.length buf in
              if buf_len > 0 then
                match Buffer.nth buf (buf_len - 1) with
                | '.' | '(' | '@' | '[' -> ()
                | c when is_alpha_numeric c && s = "(" -> ()
                | _ -> Buffer.add_string buf " "
          end
        end;
        Buffer.add_string buf s
      );
    Buffer.contents buf

  let is_outline_rawtoken = function
    | LPAREN
    | RPAREN
    | LBRACE
    | RBRACE
    | LBRACKET
    | RBRACKET
    | INDENT
    | DEDENT
      -> true
    | _ -> false

  let outline_queue_to_string q =
    let buf = Buffer.create 0 in
    q#iter
      (fun t ->
        let rt = Token.to_rawtoken t in
        if is_outline_rawtoken rt then
          let s = Token.rawtoken_to_orig rt in
          Buffer.add_string buf s
      );
    Buffer.contents buf

  let is_stmt_head = function
    | PRINT | DEL | PASS | BREAK | CONTINUE | RETURN | RAISE(* | YIELD*)
    | IMPORT | GLOBAL | NONLOCAL | EXEC | ASSERT
    (*| IF | ELSE *)| WHILE(* | FOR*) | TRY | WITHx(* | ASYNC*) | DEF | CLASS | AT
      -> true
    | _ -> false

  class scanner = object (self)
    inherit [Tokens_.token] PB.scanner

    val scanner_env = new scanner_env

    val mutable ulexbuf_opt = None

    val queue = new Xqueue.c

    val shadow_queue = new Xqueue.c
    (*val shadow_q = new Xqueue.c*)

    val mutable last_rawtoken = Tokens_.EOF
    val mutable last_rawtoken2 = Tokens_.EOF

    method init =
      scanner_env#init

    initializer
      scanner_env#init;
      env#set_enter_source_callback self#enter_source

    method enter_source src =
      [%debug_log "source=\"%s\"" src#filename];
      let ulexbuf =
        if src#filename = "<stdin>" then begin
          src#get_ulexbuf_from_stdin
        end
        else begin
          src#get_ulexbuf
        end
      in
      ulexbuf_opt <- Some ulexbuf;
      ulexbuf

    method current_indent = scanner_env#top_of_indent_stack

    method scanner_env = scanner_env

    method reset_paren_level () =
      scanner_env#init_paren();
      env#reset_paren_level()

    method prepend_token tok =
      [%debug_log "%s" (Token.rawtoken_to_string (Token.to_rawtoken tok))];
      queue#prepend tok

    method prepend_rawtoken rawtok stp edp =
      let t = Token.create rawtok stp edp in
      self#prepend_token t

    method peek_nth nth =
      match ulexbuf_opt with
      | Some ulexbuf -> begin
          let token, rawtok = peek_nth queue scanner_env ulexbuf nth in
          [%debug_log "%s" (Token.to_string token)];
          token, rawtok
      end
      | None -> failwith "Ulexer.F.scanner#peek_nth"

    method peek_up_to check_rawtok =
      let rec peek l nth =
        try
          let tok, rawtok = self#peek_nth nth in
          if check_rawtok rawtok then
            l, nth
          else
            peek ((tok, rawtok)::l) (nth + 1)
        with
          _ -> l, nth
      in
      peek [] 1

    method peek_nth_rawtoken nth =
      let _, rt = self#peek_nth nth in
      rt

    method shadow_queue = shadow_queue
    method reset_shadow_queue = shadow_queue#clear
    method shadow_contents = token_queue_to_string shadow_queue
    method copy_shadow_queue = shadow_queue#copy
    method prepend_shadow_queue q =
      [%debug_log "shadow_queue=%s" self#shadow_contents];
      [%debug_log "q=%s" (outline_queue_to_string q)];
      shadow_queue#prepend_from q

    method shadow_outline = outline_queue_to_string shadow_queue
(*
    method shadow_q = shadow_q
    method reset_shadow_q = shadow_q#clear
    method shadow_outline = outline_queue_to_string shadow_q
    method copy_shadow_q = shadow_q#copy
    method prepend_shadow_q q =
      [%debug_log "shadow_q=%s" self#shadow_outline];
      [%debug_log "q=%s" (outline_queue_to_string q)];
      shadow_q#prepend_from q
*)

    method has_error () =
      let b =
        try
          shadow_queue#iter
            (fun t ->
              [%debug_log "%s" (Token.to_string t)];
              match Token.decompose t with
              | ERROR _, _, _ -> raise Exit
              | _, stp, edp ->
                  if stp = Lexing.dummy_pos && edp = Lexing.dummy_pos then
                    raise Exit
            );
          false
        with
          Exit -> true
      in
      [%debug_log "%B" b];
      b

    method discard_tokens n =
      match ulexbuf_opt with
      | Some ulexbuf -> begin
          for _ = 1 to n do
            let tok = self#__get_token ulexbuf in
            [%debug_log ">> %s" (Token.to_string tok)];
            ignore tok
          done
      end
      | _ -> ()

    method __get_token ulexbuf =
      let get_token () =
        let tok =
          if scanner_env#is_token_queue_empty then begin
            try
              match scanner_env#longstringmode with
              | LSMsingle -> begin
                  scanner_env#set_longstringmode LSMfalse;
                  longstring_single "" ulexbuf
              end
              | LSMdouble -> begin
                  scanner_env#set_longstringmode LSMfalse;
                  longstring_double "" ulexbuf
              end
              | LSMfalse -> token scanner_env ulexbuf
            with
              Illegal_indent -> lexing_error ulexbuf "illegal indent"
          end
          else
            scanner_env#take_token()
        in
        begin
          match Token.get_rawtoken tok with
          | LONGSTRING_BEGIN_S _ -> scanner_env#set_longstringmode LSMsingle
          | LONGSTRING_BEGIN_D _ -> scanner_env#set_longstringmode LSMdouble
          | _ -> ()
        end;
        tok
      in
      let t =
        if queue#is_empty then
          get_token()
        else
          queue#take
      in
      env#set_last_token (Obj.repr t);
      let _, st, ed = Token.decompose t in
      env#set_last_range (st, ed);
      t

    method _get_token () =
      match ulexbuf_opt with
      | Some ulexbuf -> begin
          let token = self#__get_token ulexbuf in
          (*[%debug_log "--> %s" (Token.to_string token)];*)
          token
      end
      | None -> failwith "Ulexer.scanner#_get_token"

    method get_token () =

      let token = self#_get_token() in

      let rawtok, stp, edp = Token.decompose token in

      let is_print_stmt =
        match rawtok with
        | NAMEx "print" -> begin
            match last_rawtoken with
            | IMPORT -> false
            | _ ->
                match self#peek_nth_rawtoken 1 with
                | LPAREN -> false
                | _ ->
                    [%debug_log "is_print_stmt=true"];
                    true
        end
        | _ -> false
      in
      let is_exec_stmt =
        match rawtok with
        | NAMEx "exec" -> begin
            match self#peek_nth_rawtoken 1 with
            | LPAREN | EQ -> false
            | _ ->
                [%debug_log "is_exec_stmt=true"];
                true
        end
        | _ -> false
      in

      let token, rawtok =
        if is_print_stmt then begin
          let _, s, e = Token.decompose token in
          let t = Token.create PRINT s e in
          t, PRINT
        end
        else if is_exec_stmt then begin
          let _, s, e = Token.decompose token in
          let t = Token.create EXEC s e in
          t, EXEC
        end
        else if env#keep_going_flag && stp <> Lexing.dummy_pos && edp <> Lexing.dummy_pos then begin
          [%debug_log "block_level=%d" env#block_level];
          [%debug_log "paren_level=%d" env#paren_level];
          match rawtok with
          | RPAREN when env#paren_level = 0 -> begin
              let loc = loc_of_poss stp edp in
              [%debug_log "discarding a redundant closing parenthesis"];
              Aux.warning_loc loc "discarding a redundant closing parenthesis";
              self#reset_paren_level();
              let token = self#_get_token() in
              let rawtok = Token.to_rawtoken token in
              token, rawtok
          end
          | INDENT when begin
              match last_rawtoken with
              | NEWLINE _ -> last_rawtoken2 != COLON
              | _ -> false
          end -> begin
            let loc = loc_of_poss stp edp in
            [%debug_log "discarding a redundant indent"];
            Aux.warning_loc loc "discarding a redundant indent";
            let token = self#_get_token() in
            let rawtok = Token.to_rawtoken token in
            token, rawtok
          end
          | DEDENT when env#block_level = 0 -> begin
            let loc = loc_of_poss stp edp in
            let count = ref 1 in
            let t = ref token in
            let rt = ref rawtok in
            begin
              try
                while true do
                  t := self#_get_token();
                  rt := Token.to_rawtoken !t;
                  if !rt != DEDENT then
                    raise Exit
                  else
                    incr count
                done
              with
                Exit -> ()
            end;
            [%debug_log "discarding %d redundant dedent(s)" !count];
            Aux.warning_loc loc "discarding %d redundant dedent(s)" !count;
            !t, !rt
          end
          | DEDENT when begin
              match last_rawtoken with
              | NEWLINE _ -> last_rawtoken2 == COLON
              | _ -> false
          end -> begin
            [%debug_log "last_rawtoken2=%s" (Token.rawtoken_to_string last_rawtoken2)];
            [%debug_log "last_rawtoken=%s" (Token.rawtoken_to_string last_rawtoken)];
            [%debug_log "rawtok=%s" (Token.rawtoken_to_string rawtok)];
            [%debug_log "outline=%s" self#shadow_outline];
            let loc = loc_of_poss stp edp in
            [%debug_log "adding indent and dedent"];
            Aux.warning_loc loc "adding indent and dedent";
            self#prepend_token token;
            (*let ind_len = self#current_indent + 4 in
            self#prepend_token (Token.create (Tokens_.NEWLINE ind_len) stp stp);
            self#prepend_token (Token.create (Tokens_.PASS) stp stp);*)
            self#prepend_token (Token.create (Tokens_.DEDENT) stp stp);
            let token = Token.create (Tokens_.INDENT) stp stp in
            let rawtok = Token.to_rawtoken token in
            token, rawtok
          end
          | rt when begin
              last_rawtoken != COLON && env#paren_level > 0 &&
              (
               is_stmt_head rt || rt == EOF ||
               match rt with
               | NAMEx _ -> begin
                   match last_rawtoken with
                   | RPAREN | NAMEx _
                     -> true
                   | _ -> false
               end
               | _ -> false
              )
          end -> begin
            [%debug_log "newline_flag=%B" scanner_env#newline_flag];
            [%debug_log "last_rawtoken=%s" (Token.rawtoken_to_string last_rawtoken)];
            [%debug_log "rawtok=%s" (Token.rawtoken_to_string rawtok)];
            [%debug_log "outline=%s" self#shadow_outline];
            let n = env#paren_level in
            let loc = loc_of_poss stp edp in

            if scanner_env#newline_flag then begin
              [%debug_log "adding %d closing parentheses" n];
              Aux.warning_loc loc "adding %d closing parentheses" n;
              self#prepend_token token;
              let ind_len = scanner_env#last_indent_len in
              begin
                match ulexbuf_opt with
                | Some ulexbuf ->
                    let prepend_opt = Some self#prepend_token in
                    let eof_flag = rawtok == EOF in
                    handle_indent ~eof_flag scanner_env ~prepend_opt ind_len ulexbuf
                | _ -> ()
              end;
              self#prepend_token (Token.create (Tokens_.NEWLINE ind_len) stp stp);
              let t = Token.create Tokens_.RPAREN stp stp in
              for _ = 1 to n do
                self#prepend_token t;
              done;
              self#reset_paren_level();
              let token = self#_get_token() in
              let rawtok = Token.to_rawtoken token in
              token, rawtok
            end
            else begin
              [%debug_log "adding comma"];
              Aux.warning_loc loc "adding comma";
              self#prepend_token token;
              let token = Token.create (Tokens_.COMMA) stp stp in
              let rawtok = Token.to_rawtoken token in
              token, rawtok
            end

          end
          | _ -> token, rawtok
        end
        else
          token, rawtok
      in

      begin
        match rawtok with
        | LPAREN -> begin
            env#open_paren();
            (*shadow_q#add token*)
        end
        | RPAREN when env#paren_level > 0 -> begin
            env#close_paren();
            (*shadow_q#add token*)
        end
        | LBRACE -> begin
            env#open_brace();
            (*shadow_q#add token*)
        end
        | RBRACE when env#brace_level > 0 -> begin
            env#close_brace();
            (*shadow_q#add token*)
        end
        | LBRACKET -> begin
            env#open_bracket();
            (*shadow_q#add token*)
        end
        | RBRACKET when env#brace_level > 0 -> begin
            env#close_bracket();
            (*shadow_q#add token*)
        end
        | INDENT -> begin
            env#open_block();
            (*shadow_q#add token*)
        end
        | DEDENT when env#block_level > 0 -> begin
            env#close_block();
            (*shadow_q#add token*)
        end
        | _ -> ()
      end;

      shadow_queue#add token;
      [%debug_log "shadow_queue length: %d" shadow_queue#length];
      [%debug_log "---------- %s" (Token.to_string token)];
      env#clear_shift_flag();
      last_rawtoken2 <- last_rawtoken;
      last_rawtoken <- rawtok;
      scanner_env#clear_newline_flag();
      token


  end (* of Ulexer.scanner *)


end (* of functor Ulexer.F *)
]
