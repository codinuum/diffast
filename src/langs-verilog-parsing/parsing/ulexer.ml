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
 * A lexer (utf-8) for SystemVerilog (IEEE-1800-2009)
 *
 * ulexer.ml
 *
 *)

[%%prepare_logger]

module Xfile = Diffast_misc.Xfile
module Astloc = Langs_common.Astloc

module Loc = Astloc
module Ls = Labels

open Tokens_
open Common


let find_pp_keyword =
  let keyword_list =
    [
      "`line",                PP_LINE;
      "`else",                PP_ELSE;
      "`elsif",               PP_ELSIF;
      "`endif",               PP_ENDIF;
      "`ifdef",               PP_IFDEF;
      "`ifndef",              PP_IFNDEF;
      "`include",             PP_INCLUDE "";
      "`undef",               PP_UNDEF;
      "`undefineall",         PP_UNDEFINEALL;
      "`error",               PP_ERROR;
      "`timescale",           PP_TIMESCALE;

      "`default_decay_time",      PP_DEFAULT_DECAY_TIME;
      "`default_trireg_strength", PP_DEFAULT_TRIREG_STRENGTH;
      "`delay_mode_distributed",  PP_DELAY_MODE_DISTRIBUTED;
      "`delay_mode_path",         PP_DELAY_MODE_PATH;
      "`delay_mode_unit",         PP_DELAY_MODE_UNIT;
      "`delay_mode_zero",         PP_DELAY_MODE_ZERO;

      "`resetall",            PP_RESETALL;
      "`default_nettype",     PP_DEFAULT_NETTYPE;
      "`pragma",              PP_PRAGMA;
      "`begin_keywords",      PP_BEGIN_KEYWORDS;
      "`end_keywords",        PP_END_KEYWORDS;
      "`celldefine",          PP_CELLDEFINE;
      "`endcelldefine",       PP_ENDCELLDEFINE;
      "`unconnected_drive",   PP_UNCONNECTED_DRIVE;
      "`nounconnected_drive", PP_NOUNCONNECTED_DRIVE;

(*
  "`protected",           PP_PROTECTED;
  "`endprotected",        PP_ENDPROTECTED;
 *)
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      Hashtbl.find keyword_table s
    with
      Not_found -> PP_IDENTIFIER s
  in
  find



let find_syscall_keyword =
  let keyword_list =
    [
      "$error",     ST_ERROR;   (* SV2005 *)
      "$fatal",     ST_FATAL;   (* SV2005 *)
      "$info",      ST_INFO;    (* SV2005 *)
      "$root",      ST_ROOT;    (* SV2005 *)
      "$unit",      ST_UNIT;    (* SV2005 *)
      "$warning",   ST_WARNING; (* SV2005 *)

      "$setup",     TC_SETUP;
      "$hold",      TC_HOLD;
      "$setuphold", TC_SETUPHOLD;
      "$recovery",  TC_RECOVERY;
      "$removal",   TC_REMOVAL;
      "$recrem",    TC_RECREM;
      "$skew",      TC_SKEW;
      "$timeskew",  TC_TIMESKEW;
      "$fullskew",  TC_FULLSKEW;
      "$period",    TC_PERIOD;
      "$width",     TC_WIDTH;
      "$nochange",  TC_NOCHANGE;
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      Hashtbl.find keyword_table s
    with
      Not_found -> SYSCALL s
  in
  find


let find_keyword =
  let keyword_list =
    [
      "accept_on",           ACCEPT_ON;      (* SV2009 *)
      "alias",               ALIAS;          (* SV2005 *)
      "always",              ALWAYS Ls.AlwaysSpec.NORMAL;
      "always_comb",         ALWAYS Ls.AlwaysSpec.COMB;  (* SV2005 *)
      "always_ff",           ALWAYS Ls.AlwaysSpec.FF;    (* SV2005 *)
      "always_latch",        ALWAYS Ls.AlwaysSpec.LATCH; (* SV2005 *)
      "and",                 AND;
      "assert",              ASSERT;    (* SV2005 *)
      "assume",              ASSUME;    (* SV2005 *)
      "assign",              ASSIGN;
      "automatic",           AUTOMATIC; (* V2001 *)
      "before",              BEFORE;    (* SV2005 *)
      "begin",               BEGIN;
      "bind",                BIND;   (* SV2005 *)
      "bins",                BINS;   (* SV2005 *)
      "binsof",              BINSOF; (* SV2005 *)
      "bit",                 BIT;    (* SV2005 *)
      "break",               BREAK;  (* SV2005 *)
      "buf",                 BUF;

      "bufif0",              GATE Ls.BUFIF0;  (* V1995 *)
      "bufif1",              GATE Ls.BUFIF1;  (* V1995 *)

      "byte",                BYTE;    (* SV2005 *)
      "case",                CASE;
      "casex",               CASEX;
      "casez",               CASEZ;
      "cell",                CELL;       (* V2001 *)
      "chandle",             CHANDLE;    (* SV2005 *)
      "checker",             CHECKER;    (* SV2009 *)
      "class",               CLASS;      (* SV2005 *)
      "clocking",            CLOCKING;   (* SV2005 *)

      "cmos",                GATE Ls.CMOS;       (* V1995 *)

      "config",              CONFIG;     (* V2001 *)
      "const",               CONST;      (* SV2005 *)
      "constraint",          CONSTRAINT; (* SV2005 *)
      "context",             CONTEXT;    (* SV2005 *)
      "continue",            CONTINUE;   (* SV2005 *)
      "cover",               COVER;      (* SV2005 *)
      "covergroup",          COVERGROUP; (* SV2005 *)
      "coverpoint",          COVERPOINT; (* SV2005 *)
      "cross",               CROSS;      (* SV2005 *)
      "deassign",            DEASSIGN;
      "default",             DEFAULT;
      "defparam",            DEFPARAM;
      "design",              DESIGN;     (* V2001 *)
      "disable",             DISABLE;
      "dist",                DIST;       (* SV2005 *)
      "do",                  DO;         (* SV2005 *)
      "edge",                EDGE;
      "else",                ELSE;
      "end",                 END;
      "endcase",             ENDCASE;
      "endchecker",          ENDCHECKER;   (* SV2009 *)
      "endclass",            ENDCLASS;     (* SV2005 *)
      "endclocking",         ENDCLOCKING;  (* SV2005 *)
      "endconfig",           ENDCONFIG;    (* V2001 *)
      "endfunction",         ENDFUNCTION;
      "endgenerate",         ENDGENERATE;  (* V2001 *)
      "endgroup",            ENDGROUP;     (* SV2005 *)
      "endinterface",        ENDINTERFACE; (* SV2005 *)
      "endmodule",           ENDMODULE;
      "endpackage",          ENDPACKAGE;   (* SV2005 *)
      "endprimitive",        ENDPRIMITIVE;
      "endprogram",          ENDPROGRAM;   (* SV2005 *)
      "endproperty",         ENDPROPERTY;  (* SV2005 *)
      "endsequence",         ENDSEQUENCE;  (* SV2005 *)
      "endspecify",          ENDSPECIFY;
      "endtable",            ENDTABLE;
      "endtask",             ENDTASK;
      "enum",                ENUM;        (* SV2005 *)
      "event",               EVENT;
      "expect",              EXPECT;      (* SV2005 *)
      "export",              EXPORT;      (* SV2005 *)
      "extends",             EXTENDS;     (* SV2005 *)
      "extern",              EXTERN;      (* SV2005 *)
      "eventually",          EVENTUALLY;  (* SV2009 *)
      "final",               FINAL;       (* SV2005 *)
      "first_match",         FIRST_MATCH; (* SV2005 *)
      "for",                 FOR;
      "force",               FORCE;
      "foreach",             FOREACH;     (* SV2005 *)
      "forever",             FOREVER;
      "fork",                FORK;
      "forkjoin",            FORKJOIN;    (* SV2005 *)
      "function",            FUNCTION;
      "generate",            GENERATE;    (* V2001 *)
      "genvar",              GENVAR;      (* V2001 *)
      "global",              GLOBAL;      (* SV2009 *)
      "highz0",              STRENGTH Ls.Strength.HIGHZ0;      (* V1995 *)
      "highz1",              STRENGTH Ls.Strength.HIGHZ1;      (* V1995 *)
      "if",                  IF;
      "iff",                 IFF;          (* SV2005 *)
      "ifnone",              IFNONE;       (* V2001 *)
      "ignore_bins",         IGNORE_BINS;  (* SV2005 *)
      "illegal_bins",        ILLEGAL_BINS; (* SV2005 *)
      "implies",             IMPLIES;      (* SV2009 *)
      "import",              IMPORT;       (* SV2005 *)
(*
  "incdir",              INCDIR;       (* V2001 *)
 *)
      "include",             INCLUDE;      (* V2001 *)
      "initial",             INITIAL;
      "inout",               INOUT;
      "input",               INPUT;
      "inside",              INSIDE;     (* SV2005 *)
      "instance",            INSTANCE;   (* V2001 *)
      "int",                 INT;        (* SV2005 *)
      "integer",             INTEGER;
      "interface",           INTERFACE;  (* SV2005 *)
      "intersect",           INTERSECT;  (* SV2005 *)
      "join",                JOIN Ls.JoinSpec.NORMAL;
      "join_any",            JOIN Ls.JoinSpec.ANY;   (* SV2005 *)
      "join_none",           JOIN Ls.JoinSpec.NONE;  (* SV2005 *)
      "large",               STRENGTH Ls.Strength.LARGE;      (* V1995 *)
      "let",                 LET;        (* SV2009 *)
      "liblist",             LIBLIST;    (* V2001 *)
      "library",             LIBRARY;    (* V2001 *)
      "local",               LOCAL;      (* SV2005 *)
      "localparam",          LOCALPARAM; (* V2001 *)
      "logic",               LOGIC;      (* SV2005 *)
      "longint",             LONGINT;    (* SV2005 *)
      "macromodule",         MODULE Ls.ModuleSpec.MACRO;
      "matches",             MATCHES;    (* SV2005 *)
      "medium",              STRENGTH Ls.Strength.MEDIUM;     (* V1995 *)
      "modport",             MODPORT;    (* SV2005 *)
      "module",              MODULE Ls.ModuleSpec.NORMAL;
      "nand",                NAND;
      "negedge",             NEGEDGE;
      "new",                 NEW;       (* SV2005 *)
      "nexttime",            NEXTTIME;  (* SV2009 *)
      "nmos",                GATE Ls.NMOS;      (* V1995 *)
      "nor",                 NOR;
      "noshowcancelled",     NOSHOWCANCELLED; (* V2001 *)
      "not",                 NOT;
      "notif0",              GATE Ls.NOTIF0;          (* V1995 *)
      "notif1",              GATE Ls.NOTIF1;          (* V1995 *)
      "null",                NULL;            (* SV2005 *)
      "or",                  OR;
      "output",              OUTPUT;
      "package",             PACKAGE;         (* SV2005 *)
      "packed",              PACKED;          (* SV2005 *)
      "parameter",           PARAMETER;
      "pmos",                GATE Ls.PMOS;            (* V1995 *)
      "posedge",             POSEDGE;
      "primitive",           PRIMITIVE;
      "priority",            PRIORITY;            (* SV2005 *)
      "program",             PROGRAM;             (* SV2005 *)
      "property",            PROPERTY;            (* SV2005 *)
      "protected",           PROTECTED;           (* SV2005 *)
      "pull0",               STRENGTH Ls.Strength.PULL0;    (* V1995 *)
      "pull1",               STRENGTH Ls.Strength.PULL1;    (* V1995 *)
      "pulldown",            GATE Ls.PULLDOWN;     (* V1995 *)
      "pullup",              GATE Ls.PULLUP;       (* V1995 *)
      "pulsestyle_ondetect", PULSESTYLE_ONDETECT; (* V2001 *)
      "pulsestyle_onevent" , PULSESTYLE_ONEVENT;  (* V2001 *)
      "pure",                PURE;                (* SV2005 *)
      "rand",                RAND;                (* SV2005 *)
      "randc",               RANDC;               (* SV2005 *)
      "randcase",            RANDCASE;            (* SV2005 *)
      "randsequence",        RANDSEQUENCE;        (* SV2005 *)
      "rcmos",               GATE Ls.RCMOS;        (* V1995 *)
      "ref",                 REF;                 (* SV2005 *)
      "return",              RETURN;              (* SV2005 *)
      "rnmos",               GATE Ls.RNMOS;        (* V1995 *)
      "rpmos",               GATE Ls.RPMOS;        (* V1995 *)
      "real",                REAL;
      "realtime",            REALTIME;
      "reg",                 REG;
      "reject_on",           REJECT_ON;    (* SV2009 *)
      "release",             RELEASE;
      "repeat",              REPEAT;
      "restrict",            RESTRICT;     (* SV2009 *)
      "rtran",               GATE Ls.RTRAN;        (* V1995 *)
      "rtranif0",            GATE Ls.RTRANIF0;     (* V1995 *)
      "rtranif1",            GATE Ls.RTRANIF1;     (* V1995 *)
      "s_always",            S_ALWAYS;     (* SV2009 *)
      "s_eventually",        S_EVENTUALLY; (* SV2009 *)
      "s_nexttime",          S_NEXTTIME;   (* SV2009 *)
      "s_until",             S_UNTIL;      (* SV2009 *)
      "s_until_with",        S_UNTIL_WITH; (* SV2009 *)
      "scalared",            SCALARED;
      "sequence",            SEQUENCE;      (* SV2005 *)
      "shortint",            SHORTINT;     (* SV2005 *)
      "shortreal",           SHORTREAL;     (* SV2005 *)
      "showcancelled",       SHOWCANCELLED; (* V2001 *)
      "signed",              SIGNED;        (* V2001 *)
      "small",               STRENGTH Ls.Strength.SMALL;         (* V1995 *)
      "solve",               SOLVE;         (* SV2005 *)
      "specify",             SPECIFY;
      "specparam",           SPECPARAM;
      "static",              STATIC;         (* SV2005 *)
      "string",              STRING;         (* SV2005 *)
      "struct",              STRUCT;         (* SV2005 *)
      "strong",              STRONG;         (* SV2009 *)
      "strong0",             STRENGTH Ls.Strength.STRONG0;        (* V1995 *)
      "strong1",             STRENGTH Ls.Strength.STRONG1;        (* V1995 *)
      "struct",              STRUCT;         (* SV2005 *)
      "sync_accept_on",      SYNC_ACCEPT_ON; (* SV2009 *)
      "sync_reject_on",      SYNC_REJECT_ON; (* SV2009 *)
      "super",               SUPER;          (* SV2005 *)
      "supply0",             SUPPLY0;
      "supply1",             SUPPLY1;
      "table",               TABLE;
      "tagged",              TAGGED;         (* SV2005 *)
      "task",                TASK;
      "this",                THIS;           (* SV2005 *)
      "throughout",          THROUGHOUT;     (* SV2005 *)
      "time",                TIME;
      "timeprecision",       TIMEPRECISION;  (* SV2005 *)
      "timeunit",            TIMEUNIT;       (* SV2005 *)
      "tran",                GATE Ls.TRAN;           (* V1995 *)
      "tranif0",             GATE Ls.TRANIF0;        (* V1995 *)
      "tranif1",             GATE Ls.TRANIF1;        (* V1995 *)
      "tri",                 TRI;
      "tri0",                TRI0;
      "tri1",                TRI1;
      "triand",              TRIAND;
      "trior",               TRIOR;
      "trireg",              TRIREG;
      "type",                TYPE;       (* SV2005 *)
      "typedef",             TYPEDEF;    (* SV2005 *)
      "union",               UNION;      (* SV2005 *)
      "unique",              UNIQUE;     (* SV2005 *)
      "unique0",             UNIQUE0;    (* SV2009 *)
      "unsigned",            UNSIGNED;   (* V2001 *)
      "until",               UNTIL;      (* SV2009 *)
      "until_with",          UNTIL_WITH; (* SV2009 *)
      "untyped",             UNTYPED;    (* SV2009 *)
      "use",                 USE;        (* V2001 *)
      "uwire",               WIRE Ls.WS_UNRESOLVED;      (* V2005 *)
      "var",                 VAR;        (* SV2005 *)
      "vectored",            VECTORED;
      "virtual",             VIRTUAL;    (* SV2005 *)
      "void",                VOID;       (* SV2005 *)
      "wait",                WAIT;
      "wait_order",          WAIT_ORDER; (* SV2005 *)
      "wand",                WAND;
      "weak",                WEAK;       (* SV2009 *)
      "weak0",               STRENGTH Ls.Strength.WEAK0;      (* V1995 *)
      "weak1",               STRENGTH Ls.Strength.WEAK1;      (* V1995 *)
      "while",               WHILE;
      "wildcard",            WILDCARD;   (* SV2005 *)
      "wire",                WIRE Ls.WS_NORMAL;
      "with",                WITHx;      (* SV2005 *)
      "within",              WITHIN;     (* SV2005 *)
      "wor",                 WOR;
      "xnor",                XNOR;
      "xor",                 XOR;

  ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      Hashtbl.find keyword_table s
    with
      Not_found -> IDENTIFIER s
  in
  find


[%%capture_path
module F (Stat : Parser_aux.STATE_T) = struct

  module Loc = Ast.Loc
  module Aux = Parser_aux.F (Stat)
  module T = Token.F (Stat)

  open Stat

  (*let lexeme = Sedlexing.Utf8.lexeme*)
  (*let from_string = Sedlexing.Utf8.from_string*)
  let lexeme = Sedlexing.Latin1.lexeme
  let from_string = Sedlexing.Latin1.from_string

  let lexing_pos_start = Langs_common.Position.lexing_pos_start
  let lexing_pos_end = Langs_common.Position.lexing_pos_end


  let loc_of_poss = Loc.of_lexposs


  let lexing_error lexbuf msg =
    let loc = loc_of_poss (lexing_pos_start lexbuf) (lexing_pos_end lexbuf) in
    fail_to_parse ~head:(Loc.to_string ~prefix:"[" ~suffix:"]" loc) msg



  let white_space = [%sedlex.regexp? Chars " \009\012"]

  let x_digit = [%sedlex.regexp? Chars "xX"]
  let z_digit = [%sedlex.regexp? Chars "zZ?"]

  let binary_digit  = [%sedlex.regexp? '0'..'1' | x_digit | z_digit]
  let octal_digit   = [%sedlex.regexp? '0'..'7' | x_digit | z_digit]
  let decimal_digit = [%sedlex.regexp? '0'..'9']
  let hex_digit     = [%sedlex.regexp? '0'..'9' | 'a'..'f' | 'A'..'F' | x_digit | z_digit]

  let non_zero_decimal_digit = [%sedlex.regexp? '1'..'9']

  let base_prefix = [%sedlex.regexp? '\'', Opt (Chars "sS")]

  let binary_base  = [%sedlex.regexp? base_prefix, Chars "bB"]
  let octal_base   = [%sedlex.regexp? base_prefix, Chars "oO"]
  let decimal_base = [%sedlex.regexp? base_prefix, Chars "dD"]
  let hex_base     = [%sedlex.regexp? base_prefix, Chars "hH"]

  let binary_value  = [%sedlex.regexp? binary_digit, Star ('_' | binary_digit)]
  let octal_value   = [%sedlex.regexp? octal_digit, Star ('_' | octal_digit)]
  let hex_value     = [%sedlex.regexp? hex_digit, Star ('_' | hex_digit)]

  let unsigned_number = [%sedlex.regexp? decimal_digit, Star ('_' | decimal_digit)]

  let non_zero_unsigned_number = [%sedlex.regexp? non_zero_decimal_digit, Star ('_' | decimal_digit)]

  let size = [%sedlex.regexp? (* non_zero_unsigned_number *) unsigned_number]

  let sign = [%sedlex.regexp? Chars "+-"]

  let binary_number = [%sedlex.regexp? Opt size, binary_base, binary_value | '\'', binary_digit]
  let octal_number = [%sedlex.regexp? Opt size, octal_base, octal_value]
  let decimal_number = [%sedlex.regexp? unsigned_number | Opt size, decimal_base, unsigned_number]
  let hex_number = [%sedlex.regexp? Opt size, hex_base, hex_value]

  let exponent = [%sedlex.regexp? Chars "eE"]

  let real_number = [%sedlex.regexp?
    unsigned_number, '.', unsigned_number |
    unsigned_number, Opt ('.', unsigned_number), exponent, Opt sign, unsigned_number
  ]

  let integral_number = [%sedlex.regexp? decimal_number | octal_number | binary_number | hex_number]

  let time_number = [%sedlex.regexp?
    unsigned_number, Opt ('.', Plus ('0'..'9' | '_')), Opt white_space, ("fs"|"ps"|"ns"|"us"|"ms"|'s'|"step")
  ]

  let string_character = [%sedlex.regexp? Compl '"' | "\\\""]
  let string_literal = [%sedlex.regexp? '"', Star string_character, '"']

  let filename_character = [%sedlex.regexp? Compl '"']

  let sys_filename_character = [%sedlex.regexp? Compl '>']


  let line_terminator = [%sedlex.regexp? Chars "\013\010" | "\013\010"]

  let line_concat = [%sedlex.regexp? '\\', line_terminator]


  let not_star_not_slash = [%sedlex.regexp? Compl (Chars "*/") | "\013\010"]
  let not_star = [%sedlex.regexp? Compl '*' | "\013\010"]

  let letter = [%sedlex.regexp? 'a'..'z' | 'A'..'Z']
  let letter_or_digit = [%sedlex.regexp? letter | '0'..'9']
  let identifier_or_keyword = [%sedlex.regexp? (letter | '_'), Star (letter_or_digit | '_' | '$')]

  let escaped_identifier = [%sedlex.regexp? '\\', Plus (Compl (Chars " \009\012\013\010"))]

  let pp_identifier = [%sedlex.regexp? '`', identifier_or_keyword]


  let mkloc ulexbuf =
    let st = lexing_pos_start ulexbuf in
    let ed = lexing_pos_end ulexbuf in
    loc_of_poss st ed


  let make_qtoken rt st_pos ed_pos =
    let ext = env#current_loc_layers_encoded in
    let qt = PB.make_qtoken ~cache:env#fname_ext_cache ~ext rt st_pos ed_pos in
    [%debug_log "%s" (Token.qtoken_to_string qt)];
    qt

  let mktok ?(start_opt=None) ?(end_opt=None) rawtok ulexbuf =
    let st =
      match start_opt with
      | None -> lexing_pos_start ulexbuf
      | Some x -> x
    in
    let ed =
      match end_opt with
      | None -> lexing_pos_end ulexbuf
      | Some x -> x
    in
    make_qtoken rawtok st ed

  type pp_define_stat = D_id | D_params | D_body | D_finished

  let add_comment_region loc =
    (*if env#loc_stack_level = 0 then*)
      env#comment_regions#add loc


  let rec token =
    let in_pragma = ref false in
    fun lexbuf -> match %sedlex lexbuf with
    | white_space -> token lexbuf

    | line_terminator -> begin
        if !in_pragma then begin
          in_pragma := false;
          mktok EOL lexbuf
        end
        else
          token lexbuf
    end
    | "//" -> line_comment (lexing_pos_start lexbuf) lexbuf

    | "/*" -> traditional_comment (lexing_pos_start lexbuf) lexbuf

    | "/**/" -> begin
        let st, ed = lexing_pos_start lexbuf, lexing_pos_end lexbuf in
        env#comment_regions#add (loc_of_poss st ed);
        token lexbuf
    end
    | "`define" -> begin
        let st = lexing_pos_start lexbuf in
        pp_define st "" None "" st D_id lexbuf
    end

    | integral_number -> mktok (INTEGRAL_NUMBER (lexeme lexbuf)) lexbuf
    | real_number     -> mktok (REAL_NUMBER (lexeme lexbuf)) lexbuf
    | time_number     -> mktok (TIME_NUMBER (lexeme lexbuf)) lexbuf
    | string_literal  -> mktok (STRING_LITERAL (lexeme lexbuf)) lexbuf

    | "``"  -> mktok PP_CONCAT lexbuf

    | "&&"  -> mktok AMP_AMP lexbuf
    | "||"  -> mktok PIPE_PIPE lexbuf
    | "<="  -> mktok LT_EQ lexbuf
    | ">="  -> mktok GT_EQ lexbuf
    | "<<"  -> mktok LT_LT lexbuf
    | ">>"  -> mktok GT_GT lexbuf
    | "=="  -> mktok EQ_EQ lexbuf
    | "!="  -> mktok EXCLAM_EQ lexbuf
    | "===" -> mktok EQ_EQ_EQ lexbuf
    | "!==" -> mktok EXCLAM_EQ_EQ lexbuf
    | "^~"  -> mktok HAT_TILDE lexbuf
    | "~^"  -> mktok (* TILDE_HAT *) HAT_TILDE lexbuf
    | "~&"  -> mktok TILDE_AMP lexbuf
    | "~|"  -> mktok TILDE_PIPE lexbuf
    | "->"  -> mktok MINUS_GT lexbuf
    | "=>"  -> mktok EQ_GT lexbuf
    | "*>"  -> mktok STAR_GT lexbuf
    | "&&&" -> mktok AMP_AMP_AMP lexbuf

(* Verilog 2001 operators *)
    | "<<<" ->  mktok (* LT_LT_LT *) LT_LT lexbuf
    | ">>>" ->  mktok GT_GT_GT lexbuf
    | "**"  ->  mktok STAR_STAR lexbuf
    | "+:"  ->  mktok PLUS_COLON lexbuf
    | "-:"  ->  mktok MINUS_COLON lexbuf
    | ".*"  ->  mktok DOT_STAR lexbuf

(* System Verilog 2005 operators *)
    | "'"    -> mktok TICK lexbuf
    | "'{"   -> mktok TICK_LBRACE lexbuf
    | "==?"  -> mktok EQ_EQ_QUESTION lexbuf
    | "!=?"  -> mktok EXCLAM_EQ_QUESTION lexbuf
    | "++"   -> mktok PLUS_PLUS lexbuf
    | "--"   -> mktok MINUS_MINUS lexbuf
    | "+="   -> mktok PLUS_EQ lexbuf
    | "-="   -> mktok MINUS_EQ lexbuf
    | "*="   -> mktok STAR_EQ lexbuf
    | "/="   -> mktok SLASH_EQ lexbuf
    | "%="   -> mktok PERCENT_EQ lexbuf
    | "&="   -> mktok AMP_EQ lexbuf
    | "|="   -> mktok PIPE_EQ lexbuf
    | "^="   -> mktok HAT_EQ lexbuf
    | "<<="  -> mktok LT_LT_EQ lexbuf
    | ">>="  -> mktok GT_GT_EQ lexbuf
    | "<<<=" -> mktok (* LT_LT_LT_EQ *) LT_LT_EQ lexbuf
    | ">>>=" -> mktok GT_GT_GT_EQ lexbuf
    | "->>"  -> mktok MINUS_GT_GT lexbuf
    | "##"   -> mktok SHARP_SHARP lexbuf
    | "@@"   -> mktok AT_AT lexbuf
    | "::"   -> mktok COLON_COLON lexbuf
    | ":="   -> mktok COLON_EQ lexbuf
    | ":/", Compl (Chars "/*")   -> mktok COLON_SLASH lexbuf
    | "|->"  -> mktok PIPE_MINUS_GT lexbuf
    | "|=>"  -> mktok PIPE_EQ_GT lexbuf
    | "[*"   -> mktok LBRACKET_STAR lexbuf
    | "[="   -> mktok LBRACKET_EQ lexbuf
    | "[->"  -> mktok LBRACKET_MINUS_GT lexbuf
    | "[+]"  -> mktok LBRACKET_PLUS_RBRACKET lexbuf

(* System Verilog 2009 operators *)
    | "#-#" -> mktok SHARP_MINUS_SHARP lexbuf
    | "#=#" -> mktok SHARP_EQ_SHARP lexbuf
    | "<->" -> mktok LT_MINUS_GT lexbuf

    | "(*"  -> mktok LPAREN_STAR lexbuf
    | "*)"  -> mktok STAR_RPAREN lexbuf

(* *)

    | '$', identifier_or_keyword -> mktok (find_syscall_keyword (lexeme lexbuf)) lexbuf


    | "{" -> mktok LBRACE lexbuf
    | "}" -> mktok RBRACE lexbuf

    | "!" -> mktok EXCLAM lexbuf
    | "#" -> mktok SHARP lexbuf
    | "$" -> mktok DOLLAR lexbuf
    | "%" -> mktok PERCENT lexbuf
    | "&" -> mktok AMP lexbuf
    | "(" -> mktok LPAREN lexbuf
    | ")" -> mktok RPAREN lexbuf
    | "*" -> mktok STAR lexbuf
    | "+" -> mktok PLUS lexbuf
    | "," -> mktok COMMA lexbuf
    | "-" -> mktok MINUS lexbuf
    | "." -> mktok DOT lexbuf
    | "/" -> mktok SLASH lexbuf
    | ":" -> mktok COLON lexbuf
    | ";" -> mktok SEMICOLON lexbuf
    | "<" -> mktok LT lexbuf
    | "=" -> mktok EQ lexbuf
    | ">" -> mktok GT lexbuf
    | "?" -> mktok QUESTION lexbuf
    | "@" -> mktok AT lexbuf
    | "[" -> mktok LBRACKET lexbuf
    | "]" -> mktok RBRACKET lexbuf
    | "^" -> mktok HAT lexbuf
    | "|" -> mktok PIPE lexbuf
    | "~" -> mktok TILDE lexbuf

    | "_" -> mktok UNDERSCORE lexbuf

    | escaped_identifier -> mktok (IDENTIFIER (lexeme lexbuf)) lexbuf

    | pp_identifier -> begin
        let s = lexeme lexbuf in
        [%debug_log "PP_IDENTIFIER(%s)" s];
        let tok = find_pp_keyword s in
        let get_st_pos () = lexing_pos_start lexbuf in
        begin
          match tok with
          | PP_INCLUDE _ -> pp_include_filename_start (get_st_pos()) lexbuf
          | PP_PRAGMA    -> in_pragma := true; mktok tok lexbuf
          | PP_UNDEF     -> pp_undef (get_st_pos()) "" D_id lexbuf
          | PP_UNDEFINEALL -> begin
              env#lex_macrotbl#clear;
              mktok tok lexbuf
          end
          | _ ->
              let start_opt = Some (lexing_pos_start lexbuf) in
              try
                let body = env#lex_find_macro s in
                match body with
                | Macro.Object line -> begin
                    try
                      mktok (Macro.tok_of_line line) lexbuf
                    with
                      Not_found -> mktok (PP_MACRO_ID s) lexbuf
                end
                | Macro.Function(_, _) ->
                    let is_app = pre_pp_macro_arguments lexbuf in
                    if is_app then
                      let args, ed = pp_macro_arguments 0 [] "" lexbuf in
                      let rt = PP_MACRO_APPL(s, args) in
                      mktok ~start_opt ~end_opt:(Some ed) rt lexbuf
                    else
                      mktok tok lexbuf
              with
                Not_found -> mktok tok lexbuf
        end
    end
    | "-incdir" -> mktok INCDIR lexbuf

    | identifier_or_keyword -> mktok (find_keyword (lexeme lexbuf)) lexbuf

    | eof -> begin
        [%debug_log "EOF[%s]" (Loc.to_string ~short:true (mkloc lexbuf))];
        let st = lexing_pos_start lexbuf in
        let ed = lexing_pos_end lexbuf in
        make_qtoken EOF st ed
    end
    | any -> lexing_error lexbuf (Printf.sprintf "invalid symbol(%s)" (lexeme lexbuf))

    | _ -> failwith "Ulexer.token"


  and traditional_comment st lexbuf =
    match %sedlex lexbuf with
    | "*/" -> begin
        env#comment_regions#add (loc_of_poss st (lexing_pos_end lexbuf));
        token lexbuf
    end
    | any -> traditional_comment st lexbuf

    | _ -> failwith "Ulexer.traditional_comment"


  and line_comment st lexbuf =
    match %sedlex lexbuf with
    | line_terminator -> begin
        env#comment_regions#add (loc_of_poss st (lexing_pos_end lexbuf));
        token lexbuf
    end
    | any -> line_comment st lexbuf

    | _ -> failwith "Ulexer.line_comment"


  and pre_pp_macro_arguments lexbuf =
    match %sedlex lexbuf with
    | '(' -> begin
        Sedlexing.rollback lexbuf;
        true
    end
    | any -> begin
        Sedlexing.rollback lexbuf;
        false
    end
    | _ -> failwith "Ulexer.pre_pp_macro_arguments"


  and pp_macro_arguments paren_lv args arg =
    let _ =
      [%debug_log "paren_lv:%d args=[%s] arg={%s}"
        paren_lv (String.concat "," args) arg]
    in
    fun lexbuf -> match %sedlex lexbuf with
    | '(', Star white_space -> begin
        if paren_lv = 0 then
          pp_macro_arguments (paren_lv+1) args arg lexbuf
        else
          pp_macro_arguments (paren_lv+1) args (arg^"(") lexbuf
    end
    | ')' -> begin
        if paren_lv = 1 then
          let args' =
            if arg <> "" then
              arg::args
            else
              args
          in
          List.rev args', (lexing_pos_end lexbuf)
        else
          pp_macro_arguments (paren_lv-1) args (arg^")") lexbuf
    end
    | ',', Star white_space -> begin
        if paren_lv = 1 then
          pp_macro_arguments paren_lv (arg::args) "" lexbuf
        else
          pp_macro_arguments paren_lv args (arg^",") lexbuf
    end
(*
| char_start_double ->
    let s = lexeme lexbuf in
    pp_char_double paren_lv args (arg^s) lexbuf
*)
    | any -> begin
        let s = lexeme lexbuf in
        pp_macro_arguments paren_lv args (arg^s) lexbuf
    end
    | _ -> failwith "Ulexer.pp_macro_arguments"


  and pp_define st_pos id params_opt body body_st stat =
    let mem_param p =
      match params_opt with
      | Some params -> List.mem p params
      | None -> false
    in
    fun lexbuf -> match %sedlex lexbuf with
    | Star white_space -> begin
        (*let s = lexeme lexbuf in *)
        begin
          match stat with
          | D_id ->
              if id <> "" then
                let body_st' = lexing_pos_end lexbuf in
                pp_define st_pos id params_opt body body_st' D_body lexbuf
              else
                pp_define st_pos id params_opt body body_st stat lexbuf

          | D_body -> pp_define st_pos id params_opt (body^" ") body_st stat lexbuf
          | _ -> pp_define st_pos id params_opt body body_st stat lexbuf
        end
    end
    | line_concat -> pp_define st_pos id params_opt body body_st stat lexbuf

    | line_terminator -> begin
        let ed_pos = Loc.decr_lexpos (lexing_pos_start lexbuf) in
        let body_ =
          let bloc = loc_of_poss body_st ed_pos in
          match params_opt with
          | Some params -> Macro.mk_fun_body ~loc:bloc (List.rev params) body
          | None        -> Macro.mk_obj_body ~loc:bloc body
        in

        begin
          try
            let b = env#find_macro body in
            let ln = Macro.line_of_body b in
            begin
              try
                match Macro.tok_of_line ln with
                | PP_MACRO_CONST_STR _ -> Macro.resolve_body (PP_MACRO_CONST_STR id) body_
                | PP_MACRO_CONST_INT _ -> Macro.resolve_body (PP_MACRO_CONST_INT id) body_
                | _ -> ()
              with
                Not_found -> ()
            end
          with
            Not_found -> [%debug_log "macro not found: %s" body]
        end;

        let pp_qtoken = make_qtoken (PP_DEFINE__IDENT__BODY(id, body_)) st_pos ed_pos in
        [%debug_log "pp_qtoken: %s" (Token.qtoken_to_string pp_qtoken)];
        env#lex_define_macro id body_;
        pp_qtoken
    end
    | identifier_or_keyword -> begin
        let s = lexeme lexbuf in
        begin
          match stat with
          | D_id -> pp_define st_pos s params_opt body body_st stat lexbuf
          | D_params ->
              let params_opt' =
                match params_opt with
                | None -> assert false
                | Some params -> Some (s :: params)
              in
              pp_define st_pos id params_opt' body body_st stat lexbuf

          | D_body ->
              let body' =
                if mem_param s then
                  String.concat "" [body;"{";s;"}"]
                else
                  body^s
              in
              pp_define st_pos id params_opt body' body_st stat lexbuf

          | _ -> pp_define st_pos id params_opt (body^s) body_st stat lexbuf
        end
    end
    | '(' -> begin
        begin
          match stat with
          | D_id -> pp_define st_pos id (Some []) body body_st D_params lexbuf
          | D_body -> pp_define st_pos id params_opt (body^"(") body_st stat lexbuf
          | _ -> pp_define st_pos id params_opt body body_st stat lexbuf
        end
    end
    | ',' -> begin
        begin
          match stat with
          | D_body -> pp_define st_pos id params_opt (body^",") body_st stat lexbuf
          | _ -> pp_define st_pos id params_opt body body_st stat lexbuf
        end
    end
    | ')' -> begin
        begin
          match stat with
          | D_params -> pp_define st_pos id params_opt body body_st D_id lexbuf
          | D_body -> pp_define st_pos id params_opt (body^")") body_st stat lexbuf
          | _ -> pp_define st_pos id params_opt body body_st stat lexbuf
        end
    end
    | any -> begin
        let s = lexeme lexbuf in
        begin
          match stat with
          | D_id -> pp_define st_pos id params_opt body body_st stat lexbuf
          | _ -> pp_define st_pos id params_opt (body^s) body_st stat lexbuf
        end
    end
    | _ -> failwith "Ulexer.pp_define"


  and pp_undef st_pos id stat lexbuf =
    match %sedlex lexbuf with
    | line_concat -> pp_undef st_pos id stat lexbuf

    | line_terminator -> begin
        let ed_pos = Loc.decr_lexpos (lexing_pos_start lexbuf) in
        let pp_qtoken = make_qtoken (PP_UNDEF__IDENT id) st_pos ed_pos in
        [%debug_log "pp_tok: %s" (Token.qtoken_to_string pp_qtoken)];
        env#lex_undefine_macro id;
        pp_qtoken
    end
    | identifier_or_keyword -> begin
        let s = lexeme lexbuf in
        begin
          match stat with
          | D_id -> pp_undef st_pos s D_finished lexbuf
          | _ -> pp_undef st_pos id stat lexbuf
        end
    end
    | any -> begin
        (*let s = lexeme lexbuf in *)
        begin
          match stat with
          | D_id -> pp_undef st_pos id stat lexbuf
          | _ -> pp_undef st_pos id stat lexbuf
        end
    end
    | _ -> failwith "Ulexer.pp_undef"


  and pp_include_filename_start st lexbuf =
    match %sedlex lexbuf with
    | white_space -> pp_include_filename_start st lexbuf
    | '"' -> pp_include_filename st "\"" lexbuf
    | '<' -> pp_include_sys_filename st "<" lexbuf
    | _ -> failwith "Ulexer.pp_include_filename_start"


  and pp_include_filename st str lexbuf =
    match %sedlex lexbuf with
    | filename_character -> pp_include_filename st (str^(lexeme lexbuf)) lexbuf
    | '"' -> begin
        let quoted = str^"\"" in
        handle_include quoted
          (fun () ->
            make_qtoken (PP_INCLUDE quoted)
              st
              (lexing_pos_end lexbuf)
          )
          lexbuf
    end
    | _ -> failwith "Ulexer.pp_include_filename"


  and pp_include_sys_filename st str lexbuf =
    match %sedlex lexbuf with
    | sys_filename_character -> pp_include_sys_filename st (str^(lexeme lexbuf)) lexbuf
    | '>' -> begin
        let quoted = str^">" in
        handle_include quoted
          (fun () ->
            make_qtoken (PP_INCLUDE quoted)
              st
              (lexing_pos_end lexbuf)
          )
          lexbuf
    end
    | _ -> failwith "Ulexer.pp_include_sys_filename"


  and handle_include quoted mkincltok ?(trailing_comment=None) lexbuf =
    match %sedlex lexbuf with
    | line_terminator -> begin
        [%debug_log "quoted=%s" quoted];
        begin
          match trailing_comment with
          | Some st -> begin
              let cloc = loc_of_poss st (lexing_pos_end lexbuf) in
              [%debug_log "comment loc: [%s]" (Loc.to_string ~short:true cloc)];
              add_comment_region cloc
          end
          | None -> ()
        end;

        let feed_incltok() =
          let tok = mkincltok() in
          tok
        in

        if quoted = "" then begin
          feed_incltok()
        end
        else begin
          try
            let unquoted = Ast.get_unquoted quoted in
            let files =
              let fs = env#find_path ~ignore_case:true unquoted in
              match fs with
                (*| [] ->
                  let fpath =
                  if Xfile.has_extension unquoted then
                  unquoted
                  else
                  unquoted^".v"
                  in
                  env#find_path ~ignore_case:true fpath*)
              | _ -> fs
            in

            match files with
            | [file] -> begin
                [%debug_log "checking %s" file#path];
                let is_extra_source_file =
                  try
                    let ext = String.lowercase_ascii file#get_extension in
                    not (List.mem ext extensions)
                  with
                    Xfile.No_extension _ -> true
                in
                if is_extra_source_file then begin
                  env#add_extra_source_file file
                end;

                let src = new Source.c file in
                if src#exists then begin
                  [%debug_log "source exists"];
                  (*env#verbose_msg "found: %s" src#path;*)
                  if env#source_entered src then begin
                    warning_msg "cyclic include: %s" quoted;
                    feed_incltok()
                  end
                  else begin
                    if env#ignore_include_flag then begin
                      feed_incltok()
                    end
                    else begin
                      env#push_loc (Token.qtoken_to_loc (mkincltok()));
                      token (env#enter_source src)
                    end
                  end
                end
                else begin
                  [%debug_log "source does not exist"];
                  warning_msg "not found: %s" quoted;
                  feed_incltok()
                end
            end
            | [] -> begin
                [%debug_log "not found: %s" quoted];
                warning_msg "not found: %s" quoted;
                feed_incltok()
            end
            | _ -> begin
                [%debug_log "multiple files found: %s" quoted];
                warning_msg "multiple files found: %s" quoted;
                List.iter
                  (fun f ->
                    Xprint.println "\"%s\"%!" f#path
                  ) files;
                feed_incltok()
            end
          with
            Invalid_argument _ ->
              warning_msg "invalid quoted file name: %s" quoted;
              feed_incltok()
        end
    end
    | "//" -> begin
        let st = lexing_pos_start lexbuf in
        handle_include quoted mkincltok ~trailing_comment:(Some st) lexbuf
    end
    | any -> handle_include quoted mkincltok ~trailing_comment lexbuf

    | _ -> failwith "Ulexer.handle_include"


end (* of functor Ulexer.F *)
]
