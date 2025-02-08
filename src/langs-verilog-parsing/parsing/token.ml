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
(* token.ml *)

module Parserlib_base = Langs_common.Parserlib_base
module Astloc = Langs_common.Astloc

open Printf

module Loc = Astloc

open Tokens_


let rawtoken_to_string = function
  | DESCRIPTION _            -> "DESCRIPTION"
  | MODULE_ITEM _            -> "MODULE_ITEM"
  | GENERATE_ITEM _          -> "GENERATE_ITEM"
  | BLOCK_ITEM_DECLARATION _ -> "BLOCK_ITEM_DECLARATION"
  | STMT _                   -> "STMT"
  | EXPR _                   -> "EXPR"
  | CASE_ITEM _              -> "CASE_ITEM"
  | CASE_INSIDE_ITEM _       -> "CASE_INSIDE_ITEM"
  | CELLPIN_ITEM _           -> "CELLPIN_ITEM"
  | PORT _                   -> "PORT"

  | IDENTIFIER s  -> "IDENTIFIER:"^s

  | PACKAGE_IDENTIFIER s     -> "PACKAGE_IDENTIFIER:"^s
  | TYPE_IDENTIFIER s        -> "TYPE_IDENTIFIER:"^s
  | CLASS_IDENTIFIER s       -> "CLASS_IDENTIFIER:"^s
(*  | INTERFACE_IDENTIFIER s   -> "INTERFACE_IDENTIFIER:"^s*)
  | COVERGROUP_IDENTIFIER s  -> "COVERGROUP_IDENTIFIER:"^s
(*
  | CLOCKING_IDENTIFIER s   -> "CLOCKING_IDENTIFIER:"^s
  | PROPERTY_IDENTIFIER s   -> "PROPERTY_IDENTIFIER:"^s
 *)
  | PATHPULSE_IDENTIFIER s   -> "PATHPULSE_IDENTIFIER:"^s

  | SYMBOL_xX s       -> "SYMBOL:"^s
  | SYMBOL_bB s       -> "SYMBOL:"^s
  | SYMBOL_rRfFpPnN s -> "SYMBOL:"^s


  | INTEGRAL_NUMBER i -> "INTEGRAL_NUMBER:"^i
  | REAL_NUMBER r     -> "REAL_NUMBER:"^r
  | STRING_LITERAL s  -> "STRING_LITERAL:"^s
  | TIME_NUMBER t     -> "TIME_NUMBER:"^t

  | SYSCALL s  -> "SYSCALL:"^s

  | TC_SETUP     -> "TC_SETUP"
  | TC_HOLD      -> "TC_HOLD"
  | TC_SETUPHOLD -> "TC_SETUPHOLD"
  | TC_RECOVERY  -> "TC_RECOVERY"
  | TC_REMOVAL   -> "TC_REMOVAL"
  | TC_RECREM    -> "TC_RECREM"
  | TC_SKEW      -> "TC_SKEW"
  | TC_TIMESKEW  -> "TC_TIMESKEW"
  | TC_FULLSKEW  -> "TC_FULLSKEW"
  | TC_PERIOD    -> "TC_PERIOD"
  | TC_WIDTH     -> "TC_WIDTH"
  | TC_NOCHANGE  -> "TC_NOCHANGE"


  | PP_IDENTIFIER s      -> "PP_IDENTIFIER:"^s
  | PP_MACRO_NAME s      -> "PP_MACRO_NAME:"^s
  | PP_MACRO_CONST s     -> "PP_MACRO_CONST:"^s
  | PP_MACRO_CONST_STR s -> "PP_MACRO_CONST_STR:"^s
  | PP_MACRO_CONST_INT s -> "PP_MACRO_CONST_INT:"^s
  | PP_MACRO_EXPR s      -> "PP_MACRO_EXPR:"^s
  | PP_MACRO_ID s        -> "PP_MACRO_ID:"^s
  | PP_MACRO_APPL(s, sl) -> sprintf "PP_MACRO_APPL:%s(%s)" s (String.concat "," sl)

  | PP_CONCAT            -> "PP_CONCAT"

  | PP_DEFINE__IDENT__BODY(s, _) -> "PP_DEFINE__IDENT__BODY:"^s
  | PP_UNDEF__IDENT s    -> "PP_UNDEF__IDENT:"^s
  | PP_INCLUDE s         -> "PP_INCLUDE:"^s
  | PP_SYS_INCLUDE s     -> "PP_SYS_INCLUDE:"^s
  | PP_UNDEF             -> "PP_UNDEF"
  | PP_IFDEF             -> "PP_IFDEF"
  | PP_IFNDEF            -> "PP_IFNDEF"
  | PP_ELSE              -> "PP_ELSE"
  | PP_ELSIF             -> "PP_ELSIF"
  | PP_ENDIF             -> "PP_ENDIF"
  | PP_TIMESCALE         -> "PP_TIMESCALE"
  | PP_UNDEFINEALL       -> "PP_UNDEFINEALL"
  | PP_ERROR             -> "PP_ERROR"
  | PP_LINE              -> "PP_LINE"

  | PP_RESETALL          -> "PP_RESETALL"
  | PP_DEFAULT_NETTYPE   -> "PP_DEFAULT_NETTYPE"
  | PP_PRAGMA            -> "PP_PRAGMA"
  | PP_BEGIN_KEYWORDS    -> "PP_BEGIN_KEYWORDS"
  | PP_END_KEYWORDS      -> "PP_END_KEYWORDS"

  | PP_DEFAULT_DECAY_TIME      -> "PP_DEFAULT_DECAY"
  | PP_DEFAULT_TRIREG_STRENGTH -> "PP_DEFAULT_TRIREG_STRENGTH"
  | PP_DELAY_MODE_DISTRIBUTED  -> "PP_DELAY_MODE_DISTRIBUTED"
  | PP_DELAY_MODE_PATH         -> "PP_DELAY_MODE_PATH"
  | PP_DELAY_MODE_UNIT         -> "PP_DELAY_MODE_UNIT"
  | PP_DELAY_MODE_ZERO         -> "PP_DELAY_MODE_ZERO"
  | PP_CELLDEFINE              -> "PP_CELLDEFINE"
  | PP_ENDCELLDEFINE           -> "PP_ENDCELLDEFINE"
  | PP_UNCONNECTED_DRIVE       -> "PP_UNCONNECTED_DRIVE"
  | PP_NOUNCONNECTED_DRIVE     -> "PP_NOUNCONNECTED_DRIVE"


  | UNDERSCORE -> "UNDERSCORE"

  | CONST__R     -> "CONST (REF)"
  | FUNCTION__PV -> "FUNCTION (pure virtual)"
  | LOCAL__CC    -> "LOCAL (COLON_COLON)"
  | LPAREN__S    -> "LPAREN (strength)"
  | NEW__P       -> "NEW (LPAREN)"
  | STATIC__C    -> "STATIC (CONSTANT)"
  | TASK__PV     -> "TASK (pure virtual)"
  | VIRTUAL__C   -> "VIRTUAL (CLASS)"
  | VIRTUAL__I   -> "VIRTUAL (INTERFACE)"
  | VIRTUAL__ID  -> "VIRTUAL (ID)"
  | WITH__B      -> "WITH (LBRACKET)"
  | WITH__C      -> "WITH (LBRACE)"
  | WITH__P      -> "WITH (LPAREN)"
  | COMMA__I     -> "COMMA (ID)"

  | LBRACE    -> "LBRACE"
  | RBRACE    -> "RBRACE"

  | EXCLAM    -> "EXCLAM"
  | SHARP     -> "SHARP"
  | DOLLAR    -> "DOLLAR"
  | PERCENT   -> "PERCENT"
  | AMP       -> "AMP"
  | LPAREN    -> "LPAREN"
  | RPAREN    -> "RPAREN"
  | STAR      -> "STAR"
  | PLUS      -> "PLUS"
  | COMMA     -> "COMMA"
  | MINUS     -> "MINUS"
  | DOT       -> "DOT"
  | SLASH     -> "SLASH"
  | COLON     -> "COLON"
  | SEMICOLON -> "SEMICOLON"
  | LT        -> "LT"
  | EQ        -> "EQ"
  | GT        -> "GT"
  | QUESTION  -> "QUESTION"
  | AT        -> "AT"
  | LBRACKET  -> "LBRACKET"
  | RBRACKET  -> "RBRACKET"
  | HAT       -> "HAT"
  | PIPE      -> "PIPE"
  | TILDE     -> "TILDE"

	(* Verilog 1995 operators *)
  | AMP_AMP      -> "AMP_AMP"
  | PIPE_PIPE    -> "PIPE_PIPE"
  | LT_EQ        -> "LT_EQ"
  | GT_EQ        -> "GT_EQ"
  | LT_LT        -> "LT_LT"
  | GT_GT        -> "GT_GT"
  | EQ_EQ        -> "EQ_EQ"
  | EXCLAM_EQ    -> "EXCLAM_EQ"
  | EQ_EQ_EQ     -> "EQ_EQ_EQ"
  | EXCLAM_EQ_EQ -> "EXCLAM_EQ_EQ"
  | HAT_TILDE    -> "HAT_TILDE"
(*
  | TILDE_HAT    -> "TILDE_HAT"
 *)
  | TILDE_AMP    -> "TILDE_AMP"
  | TILDE_PIPE   -> "TILDE_PIPE"
  | MINUS_GT     -> "MINUS_GT"
  | EQ_GT        -> "EQ_GT"
  | STAR_GT      -> "STAR_GT"
  | AMP_AMP_AMP  -> "AMP_AMP_AMP"

	(* Verilog 2001 operators *)
(*
  | LT_LT_LT     -> "LT_LT_LT"
 *)
  | GT_GT_GT     -> "GT_GT_GT"
  | STAR_STAR    -> "STAR_STAR"
  | PLUS_COLON   -> "PLUS_COLON"
  | MINUS_COLON  -> "MINUS_COLON"
  | DOT_STAR     -> "DOT_STAR"

	(* System Verilog 2005 operators *)
  | TICK               -> "TICK"
  | TICK_LBRACE        -> "TICK_LBRACE"
  | EQ_EQ_QUESTION     -> "EQ_EQ_QUESTION"
  | EXCLAM_EQ_QUESTION -> "EXCLAM_EQ_QUESTION"
  | PLUS_PLUS          -> "PLUS_PLUS"
  | MINUS_MINUS        -> "MINUS_MINUS"
  | PLUS_EQ            -> "PLUS_EQ"
  | MINUS_EQ           -> "MINUS_EQ"
  | STAR_EQ            -> "STAR_EQ"
  | SLASH_EQ           -> "SLASH_EQ"
  | PERCENT_EQ         -> "PERCENT_EQ"
  | AMP_EQ             -> "AMP_EQ"
  | PIPE_EQ            -> "PIPE_EQ"
  | HAT_EQ             -> "HAT_EQ"
  | LT_LT_EQ           -> "LT_LT_EQ"
  | GT_GT_EQ           -> "GT_GT_EQ"
(*
  | LT_LT_LT_EQ        -> "LT_LT_LT_EQ"
 *)
  | GT_GT_GT_EQ        -> "GT_GT_GT_EQ"
  | MINUS_GT_GT        -> "MINUS_GT_GT"
  | SHARP_SHARP        -> "SHARP_SHARP"
  | AT_AT              -> "AT_AT"
  | COLON_COLON        -> "COLON_COLON"
  | COLON_EQ           -> "COLON_EQ"
  | COLON_SLASH        -> "COLON_SLASH"
  | PIPE_MINUS_GT      -> "PIPE_MINUS_GT"
  | PIPE_EQ_GT         -> "PIPE_EQ_GT"
  | LBRACKET_STAR          -> "LBRACKET_STAR"
  | LBRACKET_EQ            -> "LBRACKET_EQ"
  | LBRACKET_MINUS_GT      -> "LBRACKET_MINUS_GT"
  | LBRACKET_PLUS_RBRACKET -> "LBRACKET_PLUS_RBRACKET"

	(* System Verilog 2009 operators *)
  | SHARP_MINUS_SHARP  -> "SHARP_MINUS_SHARP"
  | SHARP_EQ_SHARP     -> "SHARP_EQ_SHARP"
  | LT_MINUS_GT        -> "LT_MINUS_GT"

	(* keywords *)
	(* Verilog 1995 *)
  | ALWAYS  a    -> "ALWAYS:"^(Labels.AlwaysSpec.to_string a)
  | AND          -> "AND"
  | ASSIGN       -> "ASSIGN"
  | BEGIN        -> "BEGIN"
  | BUF          -> "BUF"
  | CASE         -> "CASE"
  | CASEX        -> "CASEX"
  | CASEZ        -> "CASEZ"
  | DEASSIGN     -> "DEASSIGN"
  | DEFAULT      -> "DEFAULT"
  | DEFPARAM     -> "DEFPARAM"
  | DISABLE      -> "DISABLE"
  | EDGE         -> "EDGE"
  | ELSE         -> "ELSE"
  | END          -> "END"
  | ENDCASE      -> "ENDCASE"
  | ENDFUNCTION  -> "ENDFUNCTION"
  | ENDMODULE    -> "ENDMODULE"
  | ENDPRIMITIVE -> "ENDPRIMITIVE"
  | ENDSPECIFY   -> "ENDSPECIFY"
  | ENDTABLE     -> "ENDTABLE"
  | ENDTASK      -> "ENDTASK"
  | EVENT        -> "EVENT"
  | FOR          -> "FOR"
  | FORCE        -> "FORCE"
  | FOREVER      -> "FOREVER"
  | FORK         -> "FORK"
  | FUNCTION     -> "FUNCTION"
  | IF           -> "IF"
  | INITIAL      -> "INITIAL"
  | INOUT        -> "INOUT"
  | INPUT        -> "INPUT"
  | INTEGER      -> "INTEGER"
  | JOIN j       -> "JOIN:"^(Labels.JoinSpec.to_string j)
(*
  | MACROMODULE  -> "MACROMODULE"
 *)
  | MODULE m     -> "MODULE:"^(Labels.ModuleSpec.to_string m)
  | NAND         -> "NAND"
  | NEGEDGE      -> "NEGEDGE"
  | NOR          -> "NOR"
  | NOT          -> "NOT"
  | OR           -> "OR"
  | OUTPUT       -> "OUTPUT"
  | PARAMETER    -> "PARAMETER"
  | POSEDGE      -> "POSEDGE"
  | PRIMITIVE    -> "PRIMITIVE"
  | REAL         -> "REAL"
  | REALTIME     -> "REALTIME"
  | REG          -> "REG"
  | RELEASE      -> "RELEASE"
  | REPEAT       -> "REPEAT"
  | SCALARED     -> "SCALARED"
  | SPECIFY      -> "SPECIFY"
  | SPECPARAM    -> "SPECPARAM"
  | SUPPLY0      -> "SUPPLY0"
  | SUPPLY1      -> "SUPPLY1"
  | TABLE        -> "TABLE"
  | TASK         -> "TASK"
  | TIME         -> "TIME"
  | TRI          -> "TRI"
  | TRI0         -> "TRI0"
  | TRI1         -> "TRI1"
  | TRIAND       -> "TRIAND"
  | TRIOR        -> "TRIOR"
  | TRIREG       -> "TRIREG"
  | VECTORED     -> "VECTORED"
  | WAIT         -> "WAIT"
  | WAND         -> "WAND"
  | WHILE        -> "WHILE"
  | WIRE _       -> "WIRE"
  | WOR          -> "WOR"
  | XNOR         -> "XNOR"
  | XOR          -> "XOR"

  | GATE  g      -> "GATE:"^(Labels.gate_to_string g)
  | STRENGTH s   -> "STRENGTH:"^(Labels.Strength.to_string s)

(*
  | BUFIF0       -> "BUFIF0"
  | BUFIF1       -> "BUFIF1"
  | CMOS         -> "CMOS"
  | HIGHZ0       -> "HIGHZ0"
  | HIGHZ1       -> "HIGHZ1"
  | LARGE        -> "LARGE"
  | MEDIUM       -> "MEDIUM"
  | NMOS         -> "NMOS"
  | NOTIF0       -> "NOTIF0"
  | NOTIF1       -> "NOTIF1"
  | PMOS         -> "PMOS"
  | PULL0        -> "PULL0"
  | PULL1        -> "PULL1"
  | PULLDOWN     -> "PULLDOWN"
  | PULLUP       -> "PULLUP"
  | RCMOS        -> "RCMOS"
  | RNMOS        -> "RNMOS"
  | RPMOS        -> "RPMOS"
  | RTRAN        -> "RTRAN"
  | RTRANIF0     -> "RTRANIF0"
  | RTRANIF1     -> "RTRANIF1"
  | SMALL        -> "SMALL"
  | STRONG0      -> "STRONG0"
  | STRONG1      -> "STRONG1"
  | TRAN         -> "TRAN"
  | TRANIF0      -> "TRANIF0"
  | TRANIF1      -> "TRANIF1"
  | WEAK0        -> "WEAK0"
  | WEAK1        -> "WEAK1"
 *)

				   (* Verilog 2001 *)
  | AUTOMATIC           -> "AUTOMATIC"
  | ENDGENERATE         -> "ENDGENERATE"
  | GENERATE            -> "GENERATE"
  | GENVAR              -> "GENVAR"
  | IFNONE              -> "IFNONE"
  | LOCALPARAM          -> "LOCALPARAM"
  | NOSHOWCANCELLED     -> "NOSHOWCANCELLED"
  | PULSESTYLE_ONDETECT -> "PULSESTYLE_ONDETECT"
  | PULSESTYLE_ONEVENT  -> "PULSESTYLE_ONEVENT"
  | SHOWCANCELLED       -> "SHOWCANCELLED"
  | SIGNED              -> "SIGNED"
  | UNSIGNED            -> "UNSIGNED"

  | CELL      -> "CELL"
  | CONFIG    -> "CONFIG"
  | DESIGN    -> "DESIGN"
  | ENDCONFIG -> "ENDCONFIG"
  | INCDIR    -> "INCDIR"
  | INCLUDE   -> "INCLUDE"
  | INSTANCE  -> "INSTANCE"
  | LIBLIST   -> "LIBLIST"
  | LIBRARY   -> "LIBRARY"
  | USE       -> "USE"

	(* Verilog 2005 *)
(*
  | UWIRE -> "UWIRE"
 *)

	(* System Verilog 2005 *)
(*
  | SYSTASK t     -> "SYSTASK:"^(Labels.system_task_to_string t)
 *)
  | ST_ERROR     -> "ST_ERROR"
  | ST_FATAL     -> "ST_FATAL"
  | ST_INFO      -> "ST_INFO"
  | ST_ROOT      -> "ST_ROOT"
  | ST_UNIT      -> "ST_UNIT"
  | ST_WARNING   -> "ST_WARNING"

  | ALIAS         -> "ALIAS"
(*
  | ALWAYS_COMB   -> "ALWAYS_COMB"
  | ALWAYS_FF     -> "ALWAYS_FF"
  | ALWAYS_LATCH  -> "ALWAYS_LATCH"
 *)
  | ASSERT        -> "ASSERT"
  | ASSUME        -> "ASSUME"
  | BEFORE        -> "BEFORE"
  | BIND          -> "BIND"
  | BINS          -> "BINS"
  | BINSOF        -> "BINSOF"
  | BIT           -> "BIT"
  | BREAK         -> "BREAK"
  | BYTE          -> "BYTE"
  | CHANDLE       -> "CHANDLE"
  | CLASS         -> "CLASS"
  | CLOCKING      -> "CLOCKING"
  | CONST         -> "CONST"
  | CONSTRAINT    -> "CONSTRAINT"
  | CONTEXT       -> "CONTEXT"
  | CONTINUE      -> "CONTINUE"
  | COVER         -> "COVER"
  | COVERGROUP    -> "COVERGROUP"
  | COVERPOINT    -> "COVERPOINT"
  | CROSS         -> "CROSS"
  | DIST          -> "DIST"
  | DO            -> "DO"
  | ENDCLASS      -> "ENDCLASS"
  | ENDCLOCKING   -> "ENDCLOCKING"
  | ENDGROUP      -> "ENDGROUP"
  | ENDINTERFACE  -> "ENDINTERFACE"
  | ENDPACKAGE    -> "ENDPACKAGE"
  | ENDPROGRAM    -> "ENDPROGRAM"
  | ENDPROPERTY   -> "ENDPROPERTY"
  | ENDSEQUENCE   -> "ENDSEQUENCE"
  | ENUM          -> "ENUM"
  | EXPECT        -> "EXPECT"
  | EXPORT        -> "EXPORT"
  | EXTENDS       -> "EXTENDS"
  | EXTERN        -> "EXTERN"
  | FINAL         -> "FINAL"
  | FIRST_MATCH   -> "FIRST_MATCH"
  | FOREACH       -> "FOREACH"
  | FORKJOIN      -> "FORKJOIN"
  | IFF           -> "IFF"
  | IGNORE_BINS   -> "IGNORE_BINS"
  | ILLEGAL_BINS  -> "ILLEGAL_BINS"
  | IMPORT        -> "IMPORT"
  | INSIDE        -> "INSIDE"
  | INT           -> "INT"
  | INTERFACE     -> "INTERFACE"
  | INTERSECT     -> "INTERSECT"
(*
  | JOIN_ANY      -> "JOIN_ANY"
  | JOIN_NONE     -> "JOIN_NONE"
 *)
  | LOCAL         -> "LOCAL"
  | LOGIC         -> "LOGIC"
  | LONGINT       -> "LONGINT"
  | MATCHES       -> "MATCHES"
  | MODPORT       -> "MODPORT"
  | NEW           -> "NEW"
  | NULL          -> "NULL"
  | PACKAGE       -> "PACKAGE"
  | PACKED        -> "PACKED"
  | PRIORITY      -> "PRIORITY"
  | PROGRAM       -> "PROGRAM"
  | PROPERTY      -> "PROPERTY"
  | PROTECTED     -> "PROTECTED"
  | PURE          -> "PURE"
  | RAND          -> "RAND"
  | RANDC         -> "RANDC"
  | RANDCASE      -> "RANDCASE"
  | RANDSEQUENCE  -> "RANDSEQUENCE"
  | REF           -> "REF"
  | RETURN        -> "RETURN"
  | SEQUENCE      -> "SEQUENCE"
  | SHORTINT      -> "SHORTINT"
  | SHORTREAL     -> "SHORTREAL"
  | SOLVE         -> "SOLVE"
  | STATIC        -> "STATIC"
  | STRING        -> "STRING"
  | STRUCT        -> "STRUCT"
  | SUPER         -> "SUPER"
  | TAGGED        -> "TAGGED"
  | THIS          -> "THIS"
  | THROUGHOUT    -> "THOUGHOUT"
  | TIMEPRECISION -> "TIMEPRECISION"
  | TIMEUNIT      -> "TIMEUNIT"
  | TYPE          -> "TYPE"
  | TYPEDEF       -> "TYPEDEF"
  | UNION         -> "UNION"
  | UNIQUE        -> "UNIQUE"
  | VAR           -> "VAR"
  | VIRTUAL       -> "VIRTUAL"
  | VOID          -> "VOID"
  | WAIT_ORDER    -> "WAIT_ORDER"
  | WILDCARD      -> "WILDCARD"
  | WITHx         -> "WITH"
  | WITHIN        -> "WITHIN"

	(* System Verilog 2009 *)
  | ACCEPT_ON      -> "ACCEPT_ON"
  | CHECKER        -> "CHECKER"
  | ENDCHECKER     -> "ENDCHECKER"
  | EVENTUALLY     -> "EVENTUALLY"
  | GLOBAL         -> "GLOBAL"
  | IMPLIES        -> "IMPLIES"
  | LET            -> "LET"
  | NEXTTIME       -> "NEXTTIME"
  | REJECT_ON      -> "REJECT_ON"
  | RESTRICT       -> "RESTRICT"
  | S_ALWAYS       -> "S_ALWAYS"
  | S_EVENTUALLY   -> "S_EVENTUALLY"
  | S_NEXTTIME     -> "S_NEXTTIME"
  | S_UNTIL        -> "S_UNTIL"
  | S_UNTIL_WITH   -> "S_UNTIL_WITH"
  | STRONG         -> "STRONG"
  | SYNC_ACCEPT_ON -> "SYNC_ACCEPT_ON"
  | SYNC_REJECT_ON -> "SYNC_REJECT_ON"
  | UNIQUE0        -> "UNIQUE0"
  | UNTIL          -> "UNTIL"
  | UNTIL_WITH     -> "UNTIL_WITH"
  | UNTYPED        -> "UNTYPED"
  | WEAK           -> "WEAK"

  | LPAREN_STAR    -> "LPAREN_STAR"
  | STAR_RPAREN    -> "STAR_RPAREN"

  | EOL -> "EOL"

  | EOF -> "EOF"

  | EOP -> "EOP"

  | BEGIN_     -> "BEGIN_"
  | END_       -> "END_"
  | FORK_      -> "FORK_"
  | JOIN_      -> "JOIN_"
  | ENDMODULE_ -> "ENDMODULE_"
  | MATCHES_   -> "MATCHES_"
  | INSIDE_    -> "INSIDE_"
  | GENERATE_  -> "GENERATE_"

  | NB_ASSIGN_POSTFIX id -> "NB_ASSIGN_POSTFIX:"^id

  | _ -> "<impossible>"




let rawtoken_to_rep = function
  | DESCRIPTION _              -> "DESCRIPTION"
  | MODULE_ITEM _              -> "MODULE_ITEM"
  | GENERATE_ITEM _            -> "GENERATE_ITEM"
  | BLOCK_ITEM_DECLARATION _   -> "BLOCK_ITEM_DECLARATION"
  | STMT _                     -> "STMT"
  | EXPR _                     -> "EXPR"
  | CASE_ITEM _                -> "CASE_ITEM"
  | CASE_INSIDE_ITEM _         -> "CASE_INSIDE_ITEM"

  | IDENTIFIER s  -> s

  | PACKAGE_IDENTIFIER s     -> s
  | TYPE_IDENTIFIER s        -> s
  | CLASS_IDENTIFIER s       -> s
(*  | INTERFACE_IDENTIFIER s   -> s*)
  | COVERGROUP_IDENTIFIER s  -> s
(*
  | CLOCKING_IDENTIFIER s   -> "CLOCKING_IDENTIFIER:"^s
  | PROPERTY_IDENTIFIER s   -> "PROPERTY_IDENTIFIER:"^s
 *)
  | PATHPULSE_IDENTIFIER s   -> s

  | SYMBOL_xX s       -> s
  | SYMBOL_bB s       -> s
  | SYMBOL_rRfFpPnN s -> s


  | INTEGRAL_NUMBER i -> i
  | REAL_NUMBER r     -> r
  | STRING_LITERAL s  -> s
  | TIME_NUMBER t     -> t

  | SYSCALL s  -> s

  | TC_SETUP     -> "$setup"
  | TC_HOLD      -> "$hold"
  | TC_SETUPHOLD -> "$setuphold"
  | TC_RECOVERY  -> "$recovery"
  | TC_REMOVAL   -> "$removal"
  | TC_RECREM    -> "$recrem"
  | TC_SKEW      -> "$skew"
  | TC_TIMESKEW  -> "$timeskew"
  | TC_FULLSKEW  -> "$fullskew"
  | TC_PERIOD    -> "$period"
  | TC_WIDTH     -> "$width"
  | TC_NOCHANGE  -> "$nochange"


  | PP_IDENTIFIER s      -> s
  | PP_MACRO_NAME s      -> s
  | PP_MACRO_CONST s     -> s
  | PP_MACRO_CONST_STR s -> s
  | PP_MACRO_CONST_INT s -> s
  | PP_MACRO_EXPR s      -> s
  | PP_MACRO_ID s        -> s
  | PP_MACRO_APPL(s, sl) -> sprintf "%s(%s)" s (String.concat "," sl)

  | PP_CONCAT            -> "``"

  | PP_DEFINE__IDENT__BODY(s, _) -> "`define "^s
  | PP_UNDEF__IDENT s    -> "`undef "^s
  | PP_INCLUDE s         -> s
  | PP_SYS_INCLUDE s     -> s
  | PP_UNDEF             -> "`undef"
  | PP_IFDEF             -> "`ifdef"
  | PP_IFNDEF            -> "`ifndef"
  | PP_ELSE              -> "`else"
  | PP_ELSIF             -> "`elsif"
  | PP_ENDIF             -> "`endif"
  | PP_TIMESCALE         -> "`timescale"
  | PP_UNDEFINEALL       -> "`undefineall"
  | PP_ERROR             -> "`error"
  | PP_LINE              -> "`line"

  | PP_RESETALL          -> "`resetall"
  | PP_DEFAULT_NETTYPE   -> "`default_nettype"
  | PP_PRAGMA            -> "`pragma"
  | PP_BEGIN_KEYWORDS    -> "`begin_keywords"
  | PP_END_KEYWORDS      -> "`end_keywords"

  | PP_DEFAULT_DECAY_TIME      -> "`default_decay"
  | PP_DEFAULT_TRIREG_STRENGTH -> "`default_trireg_strength"
  | PP_DELAY_MODE_DISTRIBUTED  -> "`delay_mode_distributed"
  | PP_DELAY_MODE_PATH         -> "`delay_mode_path"
  | PP_DELAY_MODE_UNIT         -> "`delay_mode_unit"
  | PP_DELAY_MODE_ZERO         -> "`delay_mode_zero"
  | PP_CELLDEFINE              -> "`celldefine"
  | PP_ENDCELLDEFINE           -> "`endcelldefine"
  | PP_UNCONNECTED_DRIVE       -> "`unconnected_drive"
  | PP_NOUNCONNECTED_DRIVE     -> "`nounconnected_drive"


  | UNDERSCORE -> "_"

  | CONST__R     -> "const"
  | FUNCTION__PV -> "function"
  | LOCAL__CC    -> "local"
  | LPAREN__S    -> "("
  | NEW__P       -> "new"
  | STATIC__C    -> "static"
  | TASK__PV     -> "task"
  | VIRTUAL__C   -> "virtual"
  | VIRTUAL__I   -> "virtual"
  | VIRTUAL__ID  -> "virtual"
  | WITH__B      -> "with"
  | WITH__C      -> "with"
  | WITH__P      -> "with"
  | COMMA__I     -> ","

  | LBRACE    -> "{"
  | RBRACE    -> "}"

  | EXCLAM    -> "!"
  | SHARP     -> "#"
  | DOLLAR    -> "$"
  | PERCENT   -> "%"
  | AMP       -> "&"
  | LPAREN    -> "("
  | RPAREN    -> ")"
  | STAR      -> "*"
  | PLUS      -> "+"
  | COMMA     -> ","
  | MINUS     -> "-"
  | DOT       -> "."
  | SLASH     -> "/"
  | COLON     -> ":"
  | SEMICOLON -> ";"
  | LT        -> "<"
  | EQ        -> "="
  | GT        -> ">"
  | QUESTION  -> "?"
  | AT        -> "@"
  | LBRACKET  -> "["
  | RBRACKET  -> "]"
  | HAT       -> "^"
  | PIPE      -> "|"
  | TILDE     -> "~"

	(* Verilog 1995 operators *)
  | AMP_AMP      -> "&&"
  | PIPE_PIPE    -> "||"
  | LT_EQ        -> "<="
  | GT_EQ        -> ">="
  | LT_LT        -> "<<"
  | GT_GT        -> ">>"
  | EQ_EQ        -> "=="
  | EXCLAM_EQ    -> "!="
  | EQ_EQ_EQ     -> "===="
  | EXCLAM_EQ_EQ -> "!=="
  | HAT_TILDE    -> "^~"
(*
  | TILDE_HAT    -> "~^"
 *)
  | TILDE_AMP    -> "~&"
  | TILDE_PIPE   -> "~|"
  | MINUS_GT     -> "->"
  | EQ_GT        -> "=>"
  | STAR_GT      -> "*>"
  | AMP_AMP_AMP  -> "&&&"

	(* Verilog 2001 operators *)
(*
  | LT_LT_LT     -> "<<<"
 *)
  | GT_GT_GT     -> ">>>"
  | STAR_STAR    -> "**"
  | PLUS_COLON   -> "+:"
  | MINUS_COLON  -> "-:"
  | DOT_STAR     -> ".*"

	(* System Verilog 2005 operators *)
  | TICK               -> "'"
  | TICK_LBRACE        -> "'{"
  | EQ_EQ_QUESTION     -> "==?"
  | EXCLAM_EQ_QUESTION -> "!=?"
  | PLUS_PLUS          -> "++"
  | MINUS_MINUS        -> "--"
  | PLUS_EQ            -> "+="
  | MINUS_EQ           -> "-="
  | STAR_EQ            -> "*="
  | SLASH_EQ           -> "/="
  | PERCENT_EQ         -> "%="
  | AMP_EQ             -> "&="
  | PIPE_EQ            -> "|="
  | HAT_EQ             -> "^="
  | LT_LT_EQ           -> "<<="
  | GT_GT_EQ           -> ">>="
(*
  | LT_LT_LT_EQ        -> "<<<="
 *)
  | GT_GT_GT_EQ        -> ">>>="
  | MINUS_GT_GT        -> "->>"
  | SHARP_SHARP        -> "##"
  | AT_AT              -> "@@"
  | COLON_COLON        -> "::"
  | COLON_EQ           -> ":="
  | COLON_SLASH        -> ":/"
  | PIPE_MINUS_GT      -> "|->"
  | PIPE_EQ_GT         -> "|=>"
  | LBRACKET_STAR          -> "[*"
  | LBRACKET_EQ            -> "[="
  | LBRACKET_MINUS_GT      -> "[->"
  | LBRACKET_PLUS_RBRACKET -> "[+]"

	(* System Verilog 2009 operators *)
  | SHARP_MINUS_SHARP  -> "#-#"
  | SHARP_EQ_SHARP     -> "#=#"
  | LT_MINUS_GT        -> "<->"

	(* keywords *)
	(* Verilog 1995 *)
  | ALWAYS  a   -> Labels.AlwaysSpec.to_rep a
  | AND         -> "and"
  | ASSIGN      -> "assign"
  | BEGIN       -> "begin"
  | BUF         -> "buf"
  | CASE        -> "case"
  | CASEX       -> "casex"
  | CASEZ       -> "casez"
  | DEASSIGN    -> "deassign"
  | DEFAULT     -> "default"
  | DEFPARAM    -> "defparam"
  | DISABLE     -> "disable"
  | EDGE        -> "edge"
  | ELSE        -> "else"
  | END         -> "end"
  | ENDCASE     -> "endcase"
  | ENDFUNCTION -> "endfunction"
  | ENDMODULE   -> "endmodule"
  | ENDPRIMITIVE -> "endprimitive"
  | ENDSPECIFY   -> "endspecify"
  | ENDTABLE     -> "endtable"
  | ENDTASK      -> "endtask"
  | EVENT        -> "event"
  | FOR          -> "for"
  | FORCE        -> "force"
  | FOREVER      -> "forever"
  | FORK         -> "fork"
  | FUNCTION     -> "function"
  | IF           -> "if"
  | INITIAL      -> "initial"
  | INOUT        -> "inout"
  | INPUT        -> "input"
  | INTEGER      -> "integer"
  | JOIN j       -> Labels.JoinSpec.to_rep j
(*
  | MACROMODULE  -> "macromodule"
 *)
  | MODULE m     -> Labels.ModuleSpec.to_rep m
  | NAND         -> "nand"
  | NEGEDGE      -> "negedge"
  | NOR          -> "nor"
  | NOT          -> "not"
  | OR           -> "or"
  | OUTPUT       -> "output"
  | PARAMETER    -> "parameter"
  | POSEDGE      -> "posedge"
  | PRIMITIVE    -> "primitive"
  | REAL         -> "real"
  | REALTIME     -> "realtime"
  | REG          -> "reg"
  | RELEASE      -> "release"
  | REPEAT       -> "repeat"
  | SCALARED     -> "scalared"
  | SPECIFY      -> "specify"
  | SPECPARAM    -> "specparam"
  | SUPPLY0      -> "supply0"
  | SUPPLY1      -> "supply1"
  | TABLE        -> "table"
  | TASK         -> "task"
  | TIME         -> "time"
  | TRI          -> "tri"
  | TRI0         -> "tri0"
  | TRI1         -> "tri1"
  | TRIAND       -> "triand"
  | TRIOR        -> "trior"
  | TRIREG       -> "trireg"
  | VECTORED     -> "vectored"
  | WAIT         -> "wait"
  | WAND         -> "wand"
  | WHILE        -> "while"
  | WIRE _       -> "wire"
  | WOR          -> "wor"
  | XNOR         -> "xnor"
  | XOR          -> "xor"

  | GATE  g      -> Labels.gate_to_rep g
  | STRENGTH s   -> Labels.Strength.to_rep s

(*
  | BUFIF0       -> "BUFIF0"
  | BUFIF1       -> "BUFIF1"
  | CMOS         -> "CMOS"
  | HIGHZ0       -> "HIGHZ0"
  | HIGHZ1       -> "HIGHZ1"
  | LARGE        -> "LARGE"
  | MEDIUM       -> "MEDIUM"
  | NMOS         -> "NMOS"
  | NOTIF0       -> "NOTIF0"
  | NOTIF1       -> "NOTIF1"
  | PMOS         -> "PMOS"
  | PULL0        -> "PULL0"
  | PULL1        -> "PULL1"
  | PULLDOWN     -> "PULLDOWN"
  | PULLUP       -> "PULLUP"
  | RCMOS        -> "RCMOS"
  | RNMOS        -> "RNMOS"
  | RPMOS        -> "RPMOS"
  | RTRAN        -> "RTRAN"
  | RTRANIF0     -> "RTRANIF0"
  | RTRANIF1     -> "RTRANIF1"
  | SMALL        -> "SMALL"
  | STRONG0      -> "STRONG0"
  | STRONG1      -> "STRONG1"
  | TRAN         -> "TRAN"
  | TRANIF0      -> "TRANIF0"
  | TRANIF1      -> "TRANIF1"
  | WEAK0        -> "WEAK0"
  | WEAK1        -> "WEAK1"
 *)

	(* Verilog 2001 *)
  | AUTOMATIC           -> "automatic"
  | ENDGENERATE         -> "endgenerate"
  | GENERATE            -> "generate"
  | GENVAR              -> "genvar"
  | IFNONE              -> "ifnone"
  | LOCALPARAM          -> "localparam"
  | NOSHOWCANCELLED     -> "noshowcancelled"
  | PULSESTYLE_ONDETECT -> "pulsestype_ondetect"
  | PULSESTYLE_ONEVENT  -> "pulsestype_onevent"
  | SHOWCANCELLED       -> "showcancelled"
  | SIGNED              -> "signed"
  | UNSIGNED            -> "unsigned"

  | CELL      -> "cell"
  | CONFIG    -> "config"
  | DESIGN    -> "design"
  | ENDCONFIG -> "endconfig"
  | INCDIR    -> "-incdir"
  | INCLUDE   -> "include"
  | INSTANCE  -> "instance"
  | LIBLIST   -> "liblist"
  | LIBRARY   -> "library"
  | USE       -> "use"

	(* Verilog 2005 *)
(*
  | UWIRE -> "UWIRE"
 *)

	(* System Verilog 2005 *)
(*
  | SYSTASK t     -> Labels.system_task_to_rep t
 *)
  | ST_ERROR     -> "$error"
  | ST_FATAL     -> "$fatal"
  | ST_INFO      -> "$info"
  | ST_ROOT      -> "$root"
  | ST_UNIT      -> "$unit"
  | ST_WARNING   -> "$warning"

  | ALIAS         -> "alias"
(*
  | ALWAYS_COMB   -> "ALWAYS_COMB"
  | ALWAYS_FF     -> "ALWAYS_FF"
  | ALWAYS_LATCH  -> "ALWAYS_LATCH"
 *)
  | ASSERT        -> "assert"
  | ASSUME        -> "assume"
  | BEFORE        -> "before"
  | BIND          -> "bind"
  | BINS          -> "bins"
  | BINSOF        -> "binsof"
  | BIT           -> "bit"
  | BREAK         -> "break"
  | BYTE          -> "byte"
  | CHANDLE       -> "chandle"
  | CLASS         -> "class"
  | CLOCKING      -> "clocking"
  | CONST         -> "const"
  | CONSTRAINT    -> "constraint"
  | CONTEXT       -> "context"
  | CONTINUE      -> "continue"
  | COVER         -> "cover"
  | COVERGROUP    -> "covergroup"
  | COVERPOINT    -> "coverpoint"
  | CROSS         -> "cross"
  | DIST          -> "dist"
  | DO            -> "do"
  | ENDCLASS      -> "endclass"
  | ENDCLOCKING   -> "endclocking"
  | ENDGROUP      -> "endgroup"
  | ENDINTERFACE  -> "endinterface"
  | ENDPACKAGE    -> "endpackage"
  | ENDPROGRAM    -> "endprogram"
  | ENDPROPERTY   -> "endproperty"
  | ENDSEQUENCE   -> "endsequence"
  | ENUM          -> "enum"
  | EXPECT        -> "expect"
  | EXPORT        -> "export"
  | EXTENDS       -> "extends"
  | EXTERN        -> "extern"
  | FINAL         -> "final"
  | FIRST_MATCH   -> "first_match"
  | FOREACH       -> "foreach"
  | FORKJOIN      -> "forkjoin"
  | IFF           -> "iff"
  | IGNORE_BINS   -> "ignore_bins"
  | ILLEGAL_BINS  -> "illegal_bins"
  | IMPORT        -> "import"
  | INSIDE        -> "inside"
  | INT           -> "int"
  | INTERFACE     -> "interface"
  | INTERSECT     -> "intersect"
(*
  | JOIN_ANY      -> "JOIN_ANY"
  | JOIN_NONE     -> "JOIN_NONE"
 *)
  | LOCAL         -> "local"
  | LOGIC         -> "logic"
  | LONGINT       -> "longint"
  | MATCHES       -> "matches"
  | MODPORT       -> "modport"
  | NEW           -> "new"
  | NULL          -> "null"
  | PACKAGE       -> "package"
  | PACKED        -> "packed"
  | PRIORITY      -> "priority"
  | PROGRAM       -> "program"
  | PROPERTY      -> "property"
  | PROTECTED     -> "protected"
  | PURE          -> "pure"
  | RAND          -> "rand"
  | RANDC         -> "randc"
  | RANDCASE      -> "randcase"
  | RANDSEQUENCE  -> "randsequence"
  | REF           -> "ref"
  | RETURN        -> "return"
  | SEQUENCE      -> "sequence"
  | SHORTINT      -> "shortint"
  | SHORTREAL     -> "shortreal"
  | SOLVE         -> "solve"
  | STATIC        -> "static"
  | STRING        -> "string"
  | STRUCT        -> "struct"
  | SUPER         -> "super"
  | TAGGED        -> "tagged"
  | THIS          -> "this"
  | THROUGHOUT    -> "throughout"
  | TIMEPRECISION -> "timeprecision"
  | TIMEUNIT      -> "timeunit"
  | TYPE          -> "type"
  | TYPEDEF       -> "typedef"
  | UNION         -> "union"
  | UNIQUE        -> "unique"
  | VAR           -> "var"
  | VIRTUAL       -> "virtual"
  | VOID          -> "void"
  | WAIT_ORDER    -> "wait_order"
  | WILDCARD      -> "wildcard"
  | WITHx         -> "with"
  | WITHIN        -> "within"

	(* System Verilog 2009 *)
  | ACCEPT_ON      -> "accept_on"
  | CHECKER        -> "checker"
  | ENDCHECKER     -> "endchecker"
  | EVENTUALLY     -> "eventually"
  | GLOBAL         -> "global"
  | IMPLIES        -> "implies"
  | LET            -> "let"
  | NEXTTIME       -> "nexttime"
  | REJECT_ON      -> "reject_on"
  | RESTRICT       -> "restrict"
  | S_ALWAYS       -> "s_always"
  | S_EVENTUALLY   -> "s_eventually"
  | S_NEXTTIME     -> "s_nexttime"
  | S_UNTIL        -> "s_until"
  | S_UNTIL_WITH   -> "s_until_with"
  | STRONG         -> "strontg"
  | SYNC_ACCEPT_ON -> "sync_accept_on"
  | SYNC_REJECT_ON -> "sync_reject_on"
  | UNIQUE0        -> "unique0"
  | UNTIL          -> "until"
  | UNTIL_WITH     -> "until_with"
  | UNTYPED        -> "untyped"
  | WEAK           -> "weak"

  | LPAREN_STAR    -> "(*"
  | STAR_RPAREN    -> "*)"

  | EOL -> "EOL"

  | EOF -> "EOF"

  | EOP -> "EOP"

  | BEGIN_     -> "BEGIN_"
  | END_       -> "END_"
  | FORK_      -> "FORK_"
  | JOIN_      -> "JOIN_"
  | ENDMODULE_ -> "ENDMODULE_"
  | MATCHES_   -> "MATCHES_"
  | INSIDE_    -> "INSIDE_"
  | GENERATE_  -> "GENERATE_"

  | NB_ASSIGN_POSTFIX id -> id

  | _ -> "<impossible>"


module PB = Parserlib_base

type t = token PB.token

let to_rawtoken = PB.token_to_rawtoken
let to_lexposs = PB.token_to_lexposs

let _to_string = PB._token_to_string rawtoken_to_string

let to_loc ?(cache=None) (token : t) =
  let st, ed = to_lexposs token in
  PB.loc_of_lexposs ~cache st ed

let to_qtoken ?(cache=None) (token : t) =
  let rt, st, ed = PB.decompose_token token in
  rt, PB.loc_of_lexposs ~cache st ed

let to_string ?(cache=None) ?(show_ext=false) ?(short=true) (token : t) =
  let tok, st, ed = PB.decompose_token token in
  let loc = PB.loc_of_lexposs ~cache st ed in
  sprintf "%s[%s]" (rawtoken_to_string tok) (Loc.to_string ~show_ext ~short loc)


type qtoken_t = token PB.qtoken

let qtoken_to_rawtoken = PB.qtoken_to_rawtoken
let qtoken_to_loc = PB.qtoken_to_loc

let _qtoken_to_string = PB._qtoken_to_string rawtoken_to_string

let qtoken_to_string ?(short=true) (qtoken : qtoken_t) =
  let tok, loc = qtoken in
  let mark = if Loc.is_extended loc then "*" else "" in
  sprintf "%s[%s]%s" (rawtoken_to_string tok) (Loc.to_string ~short loc) mark


module F (Stat : Parser_aux.STATE_T) = struct

  open Stat


  let to_rawtoken (rt, _, _) = rt
  let to_lexposs (_, st, ed) = st, ed


  let loc_of_nd nd =
    nd#lloc#to_loc ?cache:(Some (Some env#fname_ext_cache)) ()

  let of_description d =
    (DESCRIPTION d, loc_of_nd d)

  let of_module_item mi =
    (MODULE_ITEM mi, loc_of_nd mi)

  let of_generate_item gi =
    (GENERATE_ITEM gi, loc_of_nd gi)

  let of_block_item_declaration bid =
    (BLOCK_ITEM_DECLARATION bid, loc_of_nd bid)

  let of_stmt s =
    (STMT s, loc_of_nd s)

  let of_case_item ci =
    (CASE_ITEM ci, loc_of_nd ci)

  let of_case_inside_item cii =
    (CASE_INSIDE_ITEM cii, loc_of_nd cii)

  let of_cellpin_item cpi =
    (CELLPIN_ITEM cpi, loc_of_nd cpi)

  let of_port p =
    (PORT p, loc_of_nd p)

  let of_expr e =
    (EXPR e, loc_of_nd e)


  let is_compiler_directive = function
    | PP_INCLUDE _
    | PP_SYS_INCLUDE _
    | PP_UNDEF
    | PP_IFDEF
    | PP_IFNDEF
    | PP_ELSE
    | PP_ELSIF
    | PP_ENDIF
    | PP_TIMESCALE
    | PP_UNDEFINEALL
    | PP_ERROR
    | PP_LINE
    | PP_RESETALL
    | PP_DEFAULT_NETTYPE
    | PP_PRAGMA
    | PP_BEGIN_KEYWORDS
    | PP_END_KEYWORDS
    | PP_DEFAULT_DECAY_TIME
    | PP_DEFAULT_TRIREG_STRENGTH
    | PP_DELAY_MODE_DISTRIBUTED
    | PP_DELAY_MODE_PATH
    | PP_DELAY_MODE_UNIT
    | PP_DELAY_MODE_ZERO
    | PP_CELLDEFINE
    | PP_ENDCELLDEFINE
    | PP_UNCONNECTED_DRIVE
    | PP_NOUNCONNECTED_DRIVE
      -> true
    | _ -> false


  let is_sv2005_keyword = function
    | ALIAS | ASSERT | ASSUME | BEFORE | BIND | BINS | BINSOF | BIT | BREAK | BYTE
    | CHANDLE | CLASS | CLOCKING | CONST | CONSTRAINT | CONTEXT | CONTINUE | COVER
    | COVERGROUP | COVERPOINT | CROSS | DIST | DO | ENDCLASS | ENDCLOCKING | ENDGROUP
    | ENDINTERFACE | ENDPACKAGE | ENDPROGRAM | ENDPROPERTY | ENDSEQUENCE | ENUM
    | EXPECT | EXPORT | EXTENDS | EXTERN | FINAL | FIRST_MATCH | FOREACH | FORKJOIN
    | IFF | IGNORE_BINS | ILLEGAL_BINS | IMPORT | INSIDE | INT | INTERFACE | INTERSECT
    | JOIN Labels.JoinSpec.ANY | JOIN Labels.JoinSpec.NONE | LOCAL | LOGIC | LONGINT | MATCHES | MODPORT
    | NEW | NULL | PACKAGE | PACKED | PRIORITY | PROGRAM | PROPERTY | PROTECTED | PURE
    | RAND | RANDC | RANDCASE | RANDSEQUENCE | REF | RETURN | SEQUENCE | SHORTINT
    | SHORTREAL | SOLVE | STATIC | STRING | STRUCT | ST_ERROR | ST_FATAL | ST_INFO
    | ST_ROOT | ST_UNIT | ST_WARNING | SUPER | TAGGED | THIS | THROUGHOUT | TIMEPRECISION
    | TIMEUNIT | TYPE | TYPEDEF | UNION | UNIQUE | VAR | VIRTUAL | VOID | WAIT_ORDER
    | WILDCARD | WITHx | WITHIN
      -> true
    | _ -> false

  let is_sv2009_keyword = function
    | ACCEPT_ON | CHECKER | ENDCHECKER | EVENTUALLY | GLOBAL | IMPLIES | LET | NEXTTIME
    | REJECT_ON | RESTRICT | S_ALWAYS | S_EVENTUALLY | S_NEXTTIME | S_UNTIL | S_UNTIL_WITH
    | STRONG | SYNC_ACCEPT_ON | SYNC_REJECT_ON | UNIQUE0 | UNTIL | UNTIL_WITH | UNTYPED | WEAK
      -> true
    | _ -> false

  let is_sv_keyword tok = is_sv2005_keyword tok || is_sv2009_keyword tok

  let size = function
    | DESCRIPTION d              -> Ast.size d
    | MODULE_ITEM mi             -> Ast.size mi
    | GENERATE_ITEM gi           -> Ast.size gi
    | BLOCK_ITEM_DECLARATION bid -> Ast.size bid
    | STMT s                     -> Ast.size s
    | CASE_ITEM ci               -> Ast.size ci
    | CASE_INSIDE_ITEM cii       -> Ast.size cii
    | CELLPIN_ITEM cpi           -> Ast.size cpi
    | PORT p                     -> Ast.size p
    | _                          -> 1


  let to_string (tok, st, ed) =
    let loc = Ast.Loc.of_lexposs st ed in
    Printf.sprintf "%s[%s]" (rawtoken_to_string tok) (Ast.Loc.to_string loc)

  let to_loc (_, st, ed) =
    let loc = Ast.Loc.of_lexposs st ed in
    loc

end (* of functor Token.F *)
