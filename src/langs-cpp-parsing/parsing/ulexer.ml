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

[%%prepare_logger]

module Xhash = Diffast_misc.Xhash
module Xprint = Diffast_misc.Xprint
module Parserlib_base = Langs_common.Parserlib_base
module Astloc = Langs_common.Astloc

module C = Context
module PB = Parserlib_base
open Tokens_


let white_space = [%sedlex.regexp? Chars " \009\012\005"]
let line_terminator = [%sedlex.regexp? Chars "\013\010" | "\013\010"]

let h_char = [%sedlex.regexp? Compl (Chars ">\013\010")]
let q_char = [%sedlex.regexp? Compl (Chars "\"\013\010")]

let header_name = [%sedlex.regexp? '<', Plus h_char, '>' | '"', Plus q_char, '"']

let digit = [%sedlex.regexp? '0'..'9']

let nondigit = [%sedlex.regexp? 'a'..'z' | 'A'..'Z' | Chars "_$" | "##"]

let hexadecimal_digit = [%sedlex.regexp? '0'..'9' | 'a'..'f' | 'A'..'F']

let hex_quad = [%sedlex.regexp?
  hexadecimal_digit, hexadecimal_digit, hexadecimal_digit, hexadecimal_digit
]

let universal_character_name = [%sedlex.regexp? 'u', hex_quad | 'U', hex_quad, hex_quad]

let shell_var = [%sedlex.regexp? "${", nondigit, Star (nondigit|digit|Chars ":-"), '}']

let identifier_nondigit = [%sedlex.regexp?
   nondigit | universal_character_name | shell_var | '?', '?', Plus '?'
]

let identifier = [%sedlex.regexp? identifier_nondigit, Star (identifier_nondigit|digit)]

let sign = [%sedlex.regexp? Chars "+-"]

let pp_number = [%sedlex.regexp?
  Opt '.', digit, Star (digit|identifier_nondigit|'\'', digit|'\'', nondigit|Chars "eEpP", sign|'.')
]

let unsigned_suffix = [%sedlex.regexp? Chars "uU"]
let long_suffix = [%sedlex.regexp? Chars "lL"]
let long_long_suffix = [%sedlex.regexp? "ll" | "LL"]

let integer_suffix = [%sedlex.regexp?
  unsigned_suffix, Opt long_suffix |
  unsigned_suffix, Opt long_long_suffix |
  long_suffix, Opt unsigned_suffix |
  long_long_suffix, Opt unsigned_suffix
]

let binary_digit = [%sedlex.regexp? '0'..'1']
let octal_digit = [%sedlex.regexp? '0'..'7']
let nonzero_digit = [%sedlex.regexp? '1'..'9']


let hexadecimal_prefix = [%sedlex.regexp? '0', Chars "xX"]

let hexadecimal_digit_sequence = [%sedlex.regexp?
  Star (Plus hexadecimal_digit, '\''), Plus hexadecimal_digit
]

let binary_literal = [%sedlex.regexp?
  '0', Chars "bB", Star (Plus binary_digit, '\''), Plus binary_digit
]
let octal_literal = [%sedlex.regexp?
  '0', Star (Star octal_digit, '\'', octal_digit), Star octal_digit
]
let decimal_literal = [%sedlex.regexp? nonzero_digit, Star (Star digit, '\'', digit), Star digit]
let hexadecimal_literal = [%sedlex.regexp? hexadecimal_prefix, hexadecimal_digit_sequence]

let integer_literal = [%sedlex.regexp?
  binary_literal, Opt integer_suffix |
  octal_literal, Opt integer_suffix |
  decimal_literal, Opt integer_suffix |
  hexadecimal_literal, Opt integer_suffix
]

(*let escape_sequence = [%sedlex.regexp?
 '\\',
 (
  Chars "'\"?\\abfnrtv" |
  octal_digit, Opt (octal_digit, Opt octal_digit) |
  'x', Plus hexadecimal_digit
 )
]*)

let escape_sequence = [%sedlex.regexp?
  '\\',
  (
    Chars "'\"?\\%" | 'a'..'z'  | (* !!! to handle "\con" for instance *)
    octal_digit, Opt (octal_digit, Opt octal_digit) |
    Chars "xU", Plus hexadecimal_digit (* to handle non-standard \U *)
  )
]

let c_char = [%sedlex.regexp?
  Compl (Chars "'\\\013\010") | escape_sequence | universal_character_name
]

let encoding_prefix = [%sedlex.regexp? "u8" | Chars "uUL"]

let character_literal = [%sedlex.regexp? Opt encoding_prefix, '\'', Plus c_char, '\'' | "'\\'"]

let digit_sequence = [%sedlex.regexp? Star (Plus digit, '\''), Plus digit]

let fractional_constant = [%sedlex.regexp?
  Opt digit_sequence, '.', digit_sequence | digit_sequence, '.'
]
let hexadecimal_fractional_constant = [%sedlex.regexp? 
  Opt hexadecimal_digit_sequence, '.', hexadecimal_digit_sequence | hexadecimal_digit_sequence, '.'
]

let exponent_part = [%sedlex.regexp? Chars "eE", Opt sign, digit_sequence]
let binary_exponent_part = [%sedlex.regexp? Chars "pP", Opt sign, digit_sequence]
let floating_suffix = [%sedlex.regexp? Chars "flFL"]

let decimal_floating_literal = [%sedlex.regexp?
  fractional_constant, Opt exponent_part, Opt floating_suffix |
  digit_sequence, exponent_part, Opt floating_suffix
]

let hexadecimal_floating_literal = [%sedlex.regexp?
  hexadecimal_prefix, hexadecimal_fractional_constant, binary_exponent_part, Opt floating_suffix |
  hexadecimal_prefix, hexadecimal_digit_sequence, binary_exponent_part, Opt floating_suffix
]

let floating_literal = [%sedlex.regexp? decimal_floating_literal | hexadecimal_floating_literal]

let s_char = [%sedlex.regexp?
  Compl (Chars "\"\\\013\010") | escape_sequence | universal_character_name
]
let s_char_no_bq = [%sedlex.regexp? Compl (Chars "`\"\\\013\010")]
let d_char = [%sedlex.regexp? Compl (Chars " ()\\\009\011\012\013\010")]
let r_char = [%sedlex.regexp? '.'] (* !!! *)

(*let s_char_sequence = [%sedlex.regexp?
  Plus (s_char|'\\', (identifier|line_terminator|'('|')'|'/'|','|']'|'>')|line_terminator, Compl '#')
]*)

let s_char_sequence = [%sedlex.regexp?
  Plus (s_char|'\\', (identifier|line_terminator|Chars "()/,]>"))
]
let s_char_sequence_no_bq = [%sedlex.regexp? Plus s_char_no_bq]
let d_char_sequence = [%sedlex.regexp? Plus d_char]
let r_char_sequence = [%sedlex.regexp? Plus r_char]

let raw_string_head = [%sedlex.regexp? Opt encoding_prefix, 'R', '"', Opt d_char_sequence, '(']
let raw_string_tail = [%sedlex.regexp? ')', Opt d_char_sequence, '"']

let string_literal = [%sedlex.regexp?
  Opt encoding_prefix, '"', Opt s_char_sequence, '"' |
  '@', '"', Opt s_char_sequence, '"' |
  '`', s_char_sequence_no_bq, '`'
]

let boolean_literal = [%sedlex.regexp? "false" | "true"]

(*let pointer_literal = [%sedlex.regexp? "nullptr"]*)

let user_defined_integer_literal = [%sedlex.regexp? integer_literal, identifier]
let user_defined_floating_literal = [%sedlex.regexp? floating_literal, identifier]
let user_defined_string_literal = [%sedlex.regexp? string_literal, identifier]
let user_defined_character_literal = [%sedlex.regexp? character_literal, identifier]

let user_defined_literal = [%sedlex.regexp?
  user_defined_integer_literal | user_defined_floating_literal |
  user_defined_string_literal | user_defined_character_literal
]

(*let literal = [%sedlex.regexp?
  integer_literal | character_literal | floating_literal | string_literal |
  boolean_literal (*| pointer_literal*) | user_defined_literal
]*)


let pp_keyword = [%sedlex.regexp? '#', Star white_space, identifier]
let ws_or_lt = [%sedlex.regexp? white_space | '\\', line_terminator]
let ident_or_symbol = [%sedlex.regexp? identifier | '.' | '=' | Plus ('0'..'9'), Opt identifier]
let pp_concatenated_identifier = [%sedlex.regexp?
  Plus (identifier, Star ws_or_lt, "##", Star ws_or_lt),
    Star (ident_or_symbol, Star ws_or_lt, "##", Star ws_or_lt), ident_or_symbol |
  Plus (identifier, "#"), Opt identifier
]

let garbage = [%sedlex.regexp? '%', Star sign, Plus ('0'..'9'), Star sign, '%']

(* *)

let ws_pat = Str.regexp "[ \009\012\013\010\\]+"

let normalize_pp_keyword k =
  let s = Str.global_replace ws_pat "" k in
  String.lowercase_ascii s

let normalize_pp_concatenated_ident k =
  IDENT (Str.global_replace ws_pat "" k)

let raw_string_head_pat =
  Str.regexp "^\\(u8\\|u\\|U\\|L\\)?R\"\\([^' ' '(' ')' '\\' '\009' '\011' '\012' '\013' '\010']*\\)($"

let get_marker s =
  let b = Str.string_match raw_string_head_pat s 0 in
  if b then
    Str.matched_group 2 s
  else
    ""

module StringHash = struct
  type t = string
  let equal s0 s1 = String.equal s0 s1
  let hash s = Hashtbl.hash_param 5 8 s
end

module StringHashtbl = Hashtbl.Make (StringHash)

(*module StringMap = Map.Make (String)*)


let _find_objc_keyword =
  let keyword_list =
    [
      "@class",        OBJC_CLASS;
      "@interface",    OBJC_INTERFACE;
      "@end",          OBJC_END;
      "@property",     OBJC_PROPERTY;
      "@private",      OBJC_PRIVATE;
      "@public",       OBJC_PUBLIC;
      "@protected",    OBJC_PROTECTED;
      "@package",      OBJC_PACKAGE;
      "@protocol",     OBJC_PROTOCOL;
      "@encode",       OBJC_ENCODE;
      "@synchronized", OBJC_SYNCHRONIZED;
      "@selector",     OBJC_SELECTOR;
      "@defs",         OBJC_DEFS;
      "@try",          OBJC_TRY;
      "@throw",        OBJC_THROW;
      "@catch",        OBJC_CATCH;
      "@finally",      OBJC_FINALLY;
      "@synthesize",   OBJC_SYNTHESIZE;
      "@dynamic",      OBJC_DYNAMIC;
      "@optional",     OBJC_OPTIONAL;
      "@required",     OBJC_REQUIRED;
      "@autoreleasepool", OBJC_AUTORELEASEPOOL;
      "@available",    OBJC_AVAILABLE;
    ] in
  let keyword_table = StringHashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> StringHashtbl.add keyword_table kwd tok)
      keyword_list
  in
  fun s -> StringHashtbl.find keyword_table s

let find_objc_keyword s =
  try
    _find_objc_keyword s
  with
    Not_found -> (*OBJC_UNKNOWN*)IDENT s


let _find_pp_keyword =
  let keyword_list =
    [
     "#include", (fun () -> PP_INCLUDE);
     "#define",  (fun () -> PP_DEFINE);
     "#undef",   (fun () -> PP_UNDEF);
     "#line",    (fun () -> PP_LINE);
     "#error",   (fun () -> PP_ERROR);
     "#pragma",  (fun () -> PP_PRAGMA);
     "#if",      (fun () -> PP_IF);
     "#ifdef",   (fun () -> PP_IFDEF);
     "#ifndef",  (fun () -> PP_IFNDEF);
     "#elif",    (fun () -> PP_ELIF (ref ""));
     "#else",    (fun () -> PP_ELSE (ref ""));
     "#endif",   (fun () -> PP_ENDIF (ref ""));
     "#import",  (fun () -> PP_IMPORT);
    ] in
  let keyword_table = StringHashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> StringHashtbl.add keyword_table kwd tok)
      keyword_list
  in
  fun s -> (StringHashtbl.find keyword_table (normalize_pp_keyword s))()
  (*let keyword_map =
    List.fold_left (fun m (kwd, tok) -> StringMap.add kwd tok m) StringMap.empty keyword_list
  in
  fun s -> StringMap.find (normalize_pp_keyword s) keyword_map*)

let find_pp_keyword s =
  try
    _find_pp_keyword s
  with
    Not_found -> PP_UNKNOWN s


let _find_keyword =
  let keyword_list =
    [
     "alignas"          , ALIGNAS;
     "alignof"          , ALIGNOF;
     "asm"              , ASM;
     "auto"             , AUTO;
     "bool"             , BOOL;
     "break"            , BREAK;
     "case"             , CASE;
     "catch"            , CATCH;
     "char"             , CHAR;
     "char8_t"          , CHAR8_T;
     "char16_t"         , CHAR16_T;
     "char32_t"         , CHAR32_T;
     "class"            , CLASS;
     "concept"          , CONCEPT;
     "const"            , CONST;
     "consteval"        , CONSTEVAL;
     "constexpr"        , CONSTEXPR;
     "constinit"        , CONSTINIT;
     "const_cast"       , CONST_CAST;
     "continue"         , CONTINUE;
     "decltype"         , DECLTYPE;
     "default"          , DEFAULT;
     "delete"           , DELETE;
     "double"           , DOUBLE;
     "do"               , DO;
     "dynamic_cast"     , DYNAMIC_CAST;
     "else"             , ELSE;
     "enum"             , ENUM;
     "explicit"         , EXPLICIT;
     "export"           , EXPORT;
     "extern"           , EXTERN;
     "false"            , FALSE;
     "float"            , FLOAT;
     "for"              , FOR;
     "friend"           , FRIEND;
     "goto"             , GOTO;
     "if"               , IF;
     "inline"           , INLINE;
     "int"              , INT;
     "long"             , LONG;
     "mutable"          , MUTABLE;
     "namespace"        , NAMESPACE;
     "new"              , NEW;
     "noexcept"         , NOEXCEPT;
     "nullptr"          , NULLPTR;
     "operator"         , OPERATOR;
     "private"          , PRIVATE;
     "protected"        , PROTECTED;
     "public"           , PUBLIC;
     "register"         , REGISTER;
     "reinterpret_cast" , REINTERPRET_CAST;
     "requires"         , REQUIRES;
     "return"           , RETURN;
     "short"            , SHORT;
     "signed"           , SIGNED;
     "sizeof"           , SIZEOF;
     "static"           , STATIC;
     "static_assert"    , STATIC_ASSERT;
     "static_cast"      , STATIC_CAST;
     "struct"           , STRUCT;
     "switch"           , SWITCH;
     "template"         , TEMPLATE;
     "this"             , THIS;
     "thread_local"     , THREAD_LOCAL;
     "throw"            , THROW;
     "true"             , TRUE;
     "try"              , TRY;
     "typedef"          , TYPEDEF;
     "typeid"           , TYPEID;
     "typename"         , TYPENAME;
     "union"            , UNION;
     "unsigned"         , UNSIGNED;
     "using"            , USING;
     "virtual"          , VIRTUAL;
     "void"             , VOID;
     "volatile"         , VOLATILE;
     "wchar_t"          , WCHAR_T;
     "while"            , WHILE;

     "and"              , AMP_AMP "and";
     "or"               , BAR_BAR "or";
     "xor"              , HAT "xor";
     "not"              , EXCLAM "not";
     "bitand"           , AMP "bitand";
     "bitor"            , BAR "bitor";
     "compl"            , TILDE "compl";
     "and_eq"           , AMP_EQ "and_eq";
     "or_eq"            , BAR_EQ "or_eq";
     "xor_eq"           , HAT_EQ "xor_eq";
     "not_eq"           , EXCLAM_EQ "not_eq";

     "audit"            , AUDIT;
     "axiom"            , AXIOM;
     "final"            , FINAL;
     "override"         , OVERRIDE;

     "defined"          , DEFINED;
     "__has_include"    , HAS_INCLUDE;
     "__has_cpp_attribute", HAS_CPP_ATTRIBUTE;

     "restrict"         , RESTRICT "restrict"; (* C99 *)
     "__restrict__"     , RESTRICT "__restrict__";

     "__asm__"          , GNU_ASM "__asm__";
     "__attribute__"    , GNU_ATTR "__attribute__";
     "__attribute"      , GNU_ATTR "__attribute";

     "__stdcall"        , MS_STDCALL "__stdcall";
     "WINAPI"           , MS_STDCALL "WINAPI";
     "APIENTRY"         , MS_STDCALL "APIENTRY";
     "__cdecl"          , MS_CDECL "__cdecl";
     "__asm"            , MS_ASM "__asm";
     "_asm"             , MS_ASM "_asm";
   ] in
  let keyword_table = StringHashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> StringHashtbl.add keyword_table kwd tok)  keyword_list
  in
  StringHashtbl.find keyword_table
  (*let keyword_map =
    List.fold_left (fun m (kwd, tok) -> StringMap.add kwd tok m) StringMap.empty keyword_list
  in
  fun s -> StringMap.find s keyword_map*)

let find_keyword s =
  try
    _find_keyword s
  with
    Not_found -> IDENT s


[%%capture_path
module F (Stat : Parser_aux.STATE_T) = struct

  open Stat

  let lexeme = Sedlexing.Utf8.lexeme
  let from_string = Sedlexing.Utf8.from_string
  (*let lexeme = Sedlexing.Latin1.lexeme*)
  (*let from_string = Sedlexing.Latin1.from_string*)


  let lexing_pos_start = Langs_common.Position.lexing_pos_start
  let lexing_pos_end = Langs_common.Position.lexing_pos_end
  let get_lc = Langs_common.Position.get_lc


  let mktok ?(st_opt=None) rawtok ulexbuf =
    let st_pos =
      match st_opt with
      | Some x -> x
      | None -> lexing_pos_start ulexbuf
    in
    [%debug_log "%s" (Token.rawtoken_to_string rawtok)];
    env#clear_lex_line_head_flag();
    let ed_pos = lexing_pos_end ulexbuf in
    rawtok, st_pos, ed_pos

  let mktok_nl rawtok ulexbuf =
    let len = Sedlexing.lexeme_length ulexbuf in
    let st_pos = lexing_pos_start ulexbuf in
    [%debug_log "%s" (Token.rawtoken_to_string rawtok)];
    env#clear_lex_line_head_flag();
    let ed_pos =
      if len <= 1 then
        st_pos
      else
        Astloc.incr_n_lexpos (len - 1) st_pos
    in
    rawtok, st_pos, ed_pos


  let add_comment_region (*loc*)_ =
    ()



  let rec _token lexbuf =
    match %sedlex lexbuf with
    | Plus white_space -> begin
        begin %debug_block
          let s = lexeme lexbuf in
          [%debug_log "\"%s\"" (String.escaped s)];
        end;
        _token lexbuf
    end
    | line_terminator -> begin
        [%debug_log "@"];
        if env#lex_pp_line_flag then begin
          env#exit_lex_pp_line();
          env#exit_lex_ms_asm_line();
          let tok = mktok_nl NEWLINE lexbuf in
          env#set_lex_line_head_flag();
          tok
        end
        else if env#lex_ms_asm_line_flag then begin
          env#exit_lex_ms_asm_line();
          let tok = mktok END_ASM lexbuf in
          env#set_lex_line_head_flag();
          tok
        end
        else begin
          env#set_lex_line_head_flag();
          _token lexbuf
        end
    end
    | '\\', Star white_space, line_terminator -> begin
        begin %debug_block
          let s = lexeme lexbuf in
          [%debug_log "\"%s\"" (String.escaped s)];
        end;
        _token lexbuf
    end
    | "//" -> begin
        let st = lexing_pos_start lexbuf in
        line_comment st lexbuf
    end
    | "/*" -> begin
        let st_pos = lexing_pos_start lexbuf in
        begin
          try
            block_comment st_pos lexbuf
          with
            _ -> begin
              let pos = lexing_pos_start lexbuf in
              let l, c = get_lc pos in
              let mes = Printf.sprintf "failed to handle block comment (%dL,%dC)" l c in
              raise (PB.Parse_error("", mes))
            end
        end
    end
    | "/**/" -> begin
        let st, ed = lexing_pos_start lexbuf, lexing_pos_end lexbuf in
        add_comment_region (Astloc.of_lexposs st ed);
        _token lexbuf
    end
    | pp_keyword -> begin
        let kwd = lexeme lexbuf in
        [%debug_log "kwd=%s" kwd];
        if env#lex_pp_line_flag || env#lex_ms_asm_line_flag || env#lex_line_head_flag then
          let r = find_pp_keyword kwd in
          let r =
            match r with
            | PP_UNKNOWN s when env#asm_flag -> IDENT s
            | _ -> env#enter_lex_pp_line(); r
          in
          mktok r lexbuf
        else
          mktok (IDENT kwd) lexbuf
    end

    | integer_literal -> begin
        let s = lexeme lexbuf in
        mktok (INT_LITERAL s) lexbuf
    end
    | character_literal -> begin
        let s = lexeme lexbuf in
        mktok (CHAR_LITERAL s) lexbuf
    end
    | floating_literal -> begin
        let s = lexeme lexbuf in
        mktok (FLOAT_LITERAL s) lexbuf
    end
    | string_literal -> begin
        let s = lexeme lexbuf in
        mktok (STR_LITERAL s) lexbuf
    end
    | boolean_literal -> begin
        let s = lexeme lexbuf in
        mktok (BOOL_LITERAL s) lexbuf
    end
(*| pointer_literal -> begin
    let s = lexeme lexbuf in
    mktok (PTR_LITERAL s) lexbuf
  end*)
    | user_defined_integer_literal -> begin
        let s = lexeme lexbuf in
        mktok (USER_INT_LITERAL s) lexbuf
    end
    | user_defined_floating_literal -> begin
        let s = lexeme lexbuf in
        mktok (USER_FLOAT_LITERAL s) lexbuf
    end
(*| user_defined_string_literal -> begin
    let s = lexeme lexbuf in
    mktok (USER_STR_LITERAL s) lexbuf
  end*)

    | user_defined_character_literal -> begin
        let s = lexeme lexbuf in
        mktok (USER_CHAR_LITERAL s) lexbuf
    end

    | ">>>>>>>" -> mktok (GT_7 (ref false)) lexbuf
    | "=======" -> conflict_marker (lexing_pos_start lexbuf) (lexeme lexbuf) lexbuf
    | "|||||||" -> conflict_marker (lexing_pos_start lexbuf) (lexeme lexbuf) lexbuf
    | "<<<<<<<" -> conflict_marker (lexing_pos_start lexbuf) (lexeme lexbuf) lexbuf

    | garbage -> _token lexbuf

    | "%:%:" -> mktok SHARP_SHARP(*PERC_COLON_PERC_COLON*) lexbuf
    | "..." -> mktok ELLIPSIS lexbuf
    | "->*" -> mktok MINUS_GT_STAR lexbuf
    | "<=>" -> mktok LT_EQ_GT lexbuf
    | "<<=" -> mktok LT_LT_EQ lexbuf
    | ">>=" -> mktok GT_GT_EQ lexbuf
    | "<<<" -> mktok CUDA_LT_LT_LT lexbuf
    | "##" -> mktok SHARP_SHARP lexbuf
(*| "<:" -> mktok LBRACKET(*LT_COLON*) lexbuf*)
    | ":>" -> mktok RBRACKET(*COLON_GT*) lexbuf
    | "<%" -> mktok LBRACE(*LT_PERC*) lexbuf
    | "%>" -> mktok RBRACE(*PERC_GT*) lexbuf
    | "%:" -> mktok SHARP(*PERC_COLON*) lexbuf
    | "::" -> mktok COLON_COLON lexbuf
    | ".*" -> mktok DOT_STAR lexbuf
    | "->" -> mktok MINUS_GT lexbuf
    | "+=" -> mktok PLUS_EQ lexbuf
    | "-=" -> mktok MINUS_EQ lexbuf
    | "*=" -> mktok STAR_EQ lexbuf
    | "/=" -> mktok SLASH_EQ lexbuf
    | "%=" -> mktok PERC_EQ lexbuf
    | "^=" -> mktok (HAT_EQ "^=") lexbuf
    | "&=" -> mktok (AMP_EQ "&=") lexbuf
    | "|=" -> mktok (BAR_EQ "|=") lexbuf
    | "==" -> mktok EQ_EQ lexbuf
    | "!=" -> mktok (EXCLAM_EQ "!=") lexbuf
    | "<=" -> mktok LT_EQ lexbuf
    | ">=" -> mktok GT_EQ lexbuf
    | "&&" -> mktok PTR_AMP_AMP lexbuf
    | "||" -> mktok (BAR_BAR "||") lexbuf
    | "<<" -> mktok LT_LT lexbuf
    | ">>" -> mktok GT_GT lexbuf
    | "++" -> mktok PLUS_PLUS lexbuf
    | "--" -> mktok MINUS_MINUS lexbuf
    | "{" -> begin
        if env#lex_ms_asm_line_flag then
          env#exit_lex_ms_asm_line();
        mktok LBRACE lexbuf
    end
    | "}" -> mktok RBRACE lexbuf
    | "[" -> mktok LBRACKET lexbuf
    | "]" -> mktok RBRACKET lexbuf
    | "#" -> begin
        if env#lex_pp_line_flag || env#asm_flag then
          mktok SHARP lexbuf
        else begin
          env#enter_lex_pp_line();
          mktok PP_ lexbuf
        end
    end
    | "(" -> mktok TY_LPAREN lexbuf
    | ")" -> mktok RPAREN lexbuf
    | ";" -> mktok (SEMICOLON true) lexbuf
    | ":" -> mktok COLON lexbuf
    | "?" -> mktok QUEST lexbuf
    | "." -> mktok DOT lexbuf
    | "~" -> mktok (TILDE "~") lexbuf
    | "!" -> mktok (EXCLAM "!") lexbuf
    | "+" -> mktok PLUS lexbuf
    | "-" -> mktok MINUS lexbuf
    | "*" -> mktok PTR_STAR lexbuf
    | "/" -> mktok SLASH lexbuf
    | "%" -> mktok PERC lexbuf
    | "^" -> mktok (HAT "^") lexbuf
    | "&" -> mktok PTR_AMP lexbuf
    | "|" -> mktok (BAR "|") lexbuf
    | "=" -> mktok EQ lexbuf
    | "<" -> mktok TEMPL_LT lexbuf
    | ">" -> mktok TY_TEMPL_GT lexbuf
    | "," -> mktok COMMA lexbuf


    | pp_concatenated_identifier -> begin
        let s = lexeme lexbuf in
        mktok (normalize_pp_concatenated_ident s) lexbuf
    end
    | identifier -> begin
        let s = lexeme lexbuf in
        [%debug_log "%s" s];
        let kw = find_keyword s in
        begin
          match kw with
          | MS_ASM _ -> env#enter_lex_ms_asm_line()
          | _ -> ()
        end;
        mktok kw lexbuf
    end
    | raw_string_head -> begin
        let s = lexeme lexbuf in
        [%debug_log "raw_string_head: %s" s];
        let m = get_marker s in
        [%debug_log "marker=\"%s\"" m];
        let buf = Buffer.create 0 in
        Buffer.add_string buf s;
        raw_string m (lexing_pos_start lexbuf) buf lexbuf
    end
    | '\\', identifier -> begin
        let s = lexeme lexbuf in
        mktok (BS_IDENT s) lexbuf
    end

    | "@@" -> begin
        let st, ed = lexing_pos_start lexbuf, lexing_pos_end lexbuf in
        add_comment_region (Astloc.of_lexposs st ed);
        let l, c = get_lc st in
        Xprint.warning "unknown token \"@@\" found at (%dL,%dC)" l c;
        _token lexbuf
    end
    | '@', identifier -> begin
        let s = lexeme lexbuf in
        let kw = find_objc_keyword s in
        mktok kw lexbuf
    end
    | '@' -> begin
        if env#asm_flag then
          line_comment (lexing_pos_start lexbuf) lexbuf
        else
          mktok AT lexbuf
    end
    | '\\' -> mktok BS lexbuf

    | eof -> begin
        if env#lex_pp_line_flag then begin
          env#exit_lex_pp_line();
          mktok_nl NEWLINE lexbuf
        end
        else
          mktok EOF lexbuf
    end
    | '"' -> mktok DQ lexbuf

    | any -> begin
        let s = lexeme lexbuf in
        if PB.is_bom s then
          Xprint.warning "BOM (0x%s:%s) found" (Xhash.to_hex s) (PB.get_bom_name s)
        else begin
          let l, c = get_lc (lexing_pos_start lexbuf) in
          Xprint.warning "unknown token \"%s\" found at (%dL,%dC)" s l c
        end;
        _token lexbuf
    end
    | _ -> failwith "Ulexer._token"


  and line_comment st lexbuf =
    match %sedlex lexbuf with
    | line_terminator -> begin
        if env#lex_pp_line_flag then begin
          env#exit_lex_pp_line();
          let tok = mktok_nl NEWLINE lexbuf in
          env#set_lex_line_head_flag();
          tok
        end
        else begin
          let cloc = Astloc.of_lexposs st (lexing_pos_end lexbuf) in
          add_comment_region cloc;
          env#set_lex_line_head_flag();
          _token lexbuf
        end
    end
    | '\\', line_terminator -> line_comment st lexbuf

    | any -> line_comment st lexbuf

    | _ -> failwith "Ulexer.line_comment"


  and block_comment st_pos lexbuf =
    match %sedlex lexbuf with
    | "*/" -> begin
        let ed_pos = lexing_pos_end lexbuf in
        add_comment_region (Astloc.of_lexposs st_pos ed_pos);
        _token lexbuf
    end
    | any -> block_comment st_pos lexbuf

    | _ -> failwith "Ulexer.block_comment"


  and _string st buf lexbuf =
    match %sedlex lexbuf with
    | '"' -> begin
        let s = lexeme lexbuf in
        [%debug_log "string_tail: %s" s];
        Buffer.add_string buf s;
        mktok ~st_opt:(Some st) (STR_LITERAL (Buffer.contents buf)) lexbuf
    end
    | escape_sequence -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        _string st buf lexbuf
    end
    | universal_character_name -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        _string st buf lexbuf
    end
    | '\\', identifier -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        _string st buf lexbuf
    end
    | '\\', line_terminator -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" (String.escaped s)];
        Buffer.add_string buf s;
        _string st buf lexbuf
    end
    | '\\', Chars "()/,]>" -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        _string st buf lexbuf
    end
    | any -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        _string st buf lexbuf
    end
    | _ -> failwith "Ulexer._string"


  and raw_string marker st buf lexbuf =
    match %sedlex lexbuf with
    | raw_string_tail -> begin
        let s = lexeme lexbuf in
        [%debug_log "raw_string_tail: %s" s];
        let m = String.sub s 1 ((String.length s) - 2) in
        [%debug_log "m=\"%s\" marker=\"%s\"" m marker];
        if m = marker then begin
          Buffer.add_string buf s;
          mktok ~st_opt:(Some st) (STR_LITERAL (Buffer.contents buf)) lexbuf
        end
        else begin
          Buffer.add_string buf s;
          raw_string marker st buf lexbuf
        end
    end
    | identifier -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        raw_string marker st buf lexbuf
    end
    | Plus ' ' -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        raw_string marker st buf lexbuf
    end
    | line_terminator -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" (String.escaped s)];
        Buffer.add_string buf s;
        raw_string marker st buf lexbuf
    end
    | any -> begin
        let s = lexeme lexbuf in
        [%debug_log "s=\"%s\"" s];
        Buffer.add_string buf s;
        raw_string marker st buf lexbuf
    end
    | _ -> failwith "Ulexer.raw_string"


  and conflict_marker st s lexbuf =
    match %sedlex lexbuf with
    | line_terminator -> begin
        (CONFLICT_MARKER(ref false, s)), st, lexing_pos_end lexbuf
    end
    | any -> conflict_marker st (s^(lexeme lexbuf)) lexbuf

    | _ -> failwith "Ulexer.conflict_marker"


end (* Ulexer.F *)
]
