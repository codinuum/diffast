(*
   Copyright 2023-2025 Chiba Institute of Technology

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

module Xfile = Diffast_misc.Xfile
module Xprint = Diffast_misc.Xprint

module Aux = Parser_aux
module T = Tokens_

type mode = Aux.parsing_mode

let mode_to_string = Aux.parsing_mode_to_string

type macro_body = MB_NONE | MB_SOME of mode * T.token Queue.t

[%%capture_path
class c = object (self)
  val main_queue = (Queue.create() : T.token Queue.t)
  val sub_queue = (Queue.create() : T.token Queue.t)
  val mutable macro_queue = (Queue.create() : T.token Queue.t)
  val macro_body_tbl = (Hashtbl.create 0 : (string, macro_body) Hashtbl.t)

  val mutable sub_flag = false
  val mutable macro_flag = false
  val mutable macro_name = ""
  val mutable macro_mode = (M_NORMAL : mode)

  val mutable func_body_flag = false

  method func_body_flag = func_body_flag
  method set_func_body_flag () = func_body_flag <- true
  method clear_func_body_flag () = func_body_flag <- false

  method skip_until_newline () =
    match Queue.peek main_queue with
    | NEWLINE -> ()
    | _ ->
        let _ = Queue.take main_queue in
        self#skip_until_newline()

  method dump fname =
    [%debug_log "\"%s\"" fname];
    let dump_ch ch =
      let dump_rt rt = Printf.fprintf ch "%s\n" (Token.rawtoken_to_string rt) in
      let dump_rtq q =
        let sz = Queue.length q in
        let count = ref 0 in
        Queue.iter
          (fun x ->
            incr count;
            if !count = sz && x == T.NEWLINE then
              ()
            else
              dump_rt x;
          ) q
      in
      let dump_mode m = Printf.fprintf ch "PMODE:%s\n" (mode_to_string m) in
      try
        while true do
          let rt = Queue.take main_queue in
          [%debug_log "%s" (Token.rawtoken_to_string rt)];
          match rt with
          | PP_DEFINE -> begin
              let rt1 = Queue.take main_queue in
              [%debug_log "  %s" (Token.rawtoken_to_string rt1)];
              let rt2 = Queue.peek main_queue in
              dump_rt rt; dump_rt rt1;
              match rt1 with
              | IDENT x when rt2 == PP_LPAREN -> begin
                  try
                    let mb = Hashtbl.find macro_body_tbl x in
                    Hashtbl.remove macro_body_tbl x;
                    match mb with
                    | MB_NONE -> begin
                        [%debug_log "MB_NONE"]
                    end
                    | MB_SOME(mode, q) -> begin
                        [%debug_log "%s" (mode_to_string macro_mode)];
                        try
                          while true do
                            let rt_ = Queue.take main_queue in
                            dump_rt rt_; 
                            match rt_ with
                            | RPAREN -> raise Exit
                            | _ -> ()
                          done
                        with
                          Exit ->
                            dump_mode mode;
                            dump_rtq q;
                            self#skip_until_newline()
                    end
                  with
                    Not_found -> ()
              end
              | IDENT x -> begin
                  try
                    let mb = Hashtbl.find macro_body_tbl x in
                    Hashtbl.remove macro_body_tbl x;
                    match mb with
                    | MB_NONE -> begin
                        [%debug_log "mb=MB_NONE"]
                    end
                    | MB_SOME(mode, q) -> begin
                        [%debug_log "%s" (mode_to_string macro_mode)];
                        self#skip_until_newline();
                        dump_mode mode;
                        dump_rtq q;
                        self#skip_until_newline()
                    end
                  with
                    Not_found -> ()
              end
              | _ -> ()
          end
          | _ -> dump_rt rt
        done
      with
        Queue.Empty -> ()
    in
    Xfile.dump fname dump_ch

  method enter_sub () =
    [%debug_log "sub_flag=%B" sub_flag];
    if not sub_flag then begin
      sub_flag <- true;
      self#clear_sub()
    end

  method exit_sub () =
    [%debug_log "sub_flag=%B" sub_flag];
    if sub_flag then begin
      begin %debug_block
      if macro_flag then
        Queue.iter
          (fun rt ->
            [%debug_log "macro_queue: %s" (Token.rawtoken_to_string rt)]
          ) macro_queue
      else
        [%debug_log "main_queue"]
      end;
      let q = if macro_flag then macro_queue else main_queue in
      Queue.iter
        (fun rt ->
          [%debug_log "%s" (Token.rawtoken_to_string rt)];
          Queue.add rt q
        ) sub_queue;
      self#clear_sub();
      sub_flag <- false
    end

  method clear_sub () =
    [%debug_log "@"];
    if sub_flag then
      Queue.clear sub_queue

  method enter_macro name mode =
    [%debug_log "%s (%s)" name (mode_to_string mode)];
    macro_flag <- true;
    macro_name <- name;
    macro_mode <- mode;
    self#clear_macro()

  method reg_dummy_macro macro_name =
    [%debug_log "%s" macro_name];
    Hashtbl.add macro_body_tbl macro_name MB_NONE

  method exit_macro () =
    [%debug_log "%s (%s)" macro_name (mode_to_string macro_mode)];
    Queue.iter
      (fun rt ->
        let _ = rt in
        [%debug_log "macro_queue: %s" (Token.rawtoken_to_string rt)]
      ) macro_queue;
    Hashtbl.add macro_body_tbl macro_name (MB_SOME (macro_mode, macro_queue));
    macro_queue <- Queue.create();
    macro_flag <- false;
    macro_name <- "";
    macro_mode <- M_NORMAL

  method clear_macro () =
    [%debug_log "@"];
    if macro_flag then
      Queue.clear macro_queue

  method add_token rt =
    [%debug_log "sub_flag=%B macro_flag=%B func_body_flag=%B rt=%s"
      sub_flag macro_flag func_body_flag (Token.rawtoken_to_string rt)];

    if not func_body_flag then
      ()
    else

    if sub_flag then begin
      Queue.add rt sub_queue
    end
    else if macro_flag then begin
      if rt != EOF then begin
        Queue.add rt macro_queue;
        Queue.iter (fun x -> let _ = x in [%debug_log "  %s" (Token.rawtoken_to_string x)]) macro_queue
      end
    end
    else begin
      Queue.add rt main_queue
    end

end
]

let split_word word =
  try
    let i0 = String.index_from word 0 ':' in
    let k0 = String.sub word 0 i0 in
    try
      begin
        match k0 with
        | "DOXYGEN_LINE"
        | "PP_ELIF" | "PP_ELSE" | "PP_ENDIF"
          -> raise Not_found
        | _ -> ()
      end;
      let i1 = String.index_from word (i0+1) ':' in
      let c0 = word.[i0+1] in
      if c0 = '\'' && word.[i0+2] = ':' then
        raise Not_found
      else
        let c1 = word.[i0+2] in
        if c0 = '\\' && c1 = '"' then
          raise Not_found
        else if
          (c0 = 'L' || c0 = 'u' || c0 = 'U' || c0 = 'R' || c0 = '@') &&
          (c1 = '\\' && word.[i0+3] = '"' || c1 = '\'')
        then
          raise Not_found
        else if
          (c0 = 'u' && (c1 = '8' || c1 = 'R') || c0 = 'L' && c1 = 'R') &&
          let c2 = word.[i0+3] in
          c2 = '\\' && word.[i0+4] = '"' || c2 = '\''
        then
          raise Not_found
        else if
          c0 = 'u' && c1 = '8' && word.[i0+3] = 'R' &&
          let c3 = word.[i0+4] in
          c3 = '\\' && word.[i0+5] = '"' || c3 = '\''
        then
          raise Not_found
        else if c0 = '$' && c1 = '{' then
          raise Not_found;

        let k1 = String.sub word (i0+1) (i1-i0-1) in
        let k2 = String.sub word (i1+1) (String.length word - i1 - 1) in
        [k0; k1; k2]
    with
      (*Not_found*)_ ->
        let k1 = String.sub word (i0+1) (String.length word - i0 - 1) in
        [k0; k1]
  with
  | Not_found -> [word]
  | _ -> invalid_arg "split_word"

let mode_of_string mode s : mode =
  match mode with
  | "M_NORMAL" -> M_NORMAL
  | "M_STMTS" -> M_STMTS
  | "M_DECLS_SUB" -> M_DECLS_SUB s
  | "M_MEM_DECLS_SUB" -> M_MEM_DECLS_SUB s
  | "M_STMTS_SUB" -> M_STMTS_SUB s
  | "M_EXPR_SUB" -> M_EXPR_SUB s
  | "M_INIT_SUB" -> M_INIT_SUB s
  | "M_TYPE_SUB" -> M_TYPE_SUB s
  | "M_SPECS_SUB" -> M_SPECS_SUB s
  | "M_DTORS_SUB" -> M_DTORS_SUB s
  | "M_ETORS_SUB" -> M_ETORS_SUB s
  | "M_OBJC_DECLS_SUB" -> M_OBJC_DECLS_SUB s
  | _ -> assert false

let word_to_token word : T.token =
  match split_word word with
  | [w] -> begin
      match w with
      | "ALIGNAS" -> ALIGNAS
      | "ALIGNOF" -> ALIGNOF
      | "AND" -> AND
      | "AND_EQ" -> AND_EQ
      | "ASM" -> ASM
      | "ASM_SHADER" -> ASM_SHADER
      | "ASSERT" -> ASSERT
      | "AT" -> AT
      | "ATTR_LBRACKET" -> ATTR_LBRACKET
      | "AUDIT" -> AUDIT
      | "AUTO" -> AUTO
      | "AXIOM" -> AXIOM
      | "BASE_COLON" -> BASE_COLON
      | "BEGIN_ASM" -> BEGIN_ASM
      | "BEGIN_ETORS" -> BEGIN_ETORS
      | "BEGIN_QPROP" -> BEGIN_QPROP
      | "BEGIN_STMTS" -> BEGIN_STMTS
      | "BITAND" -> BITAND
      | "BITOR" -> BITOR
      | "BOOL" -> BOOL
      | "BRACE_PAREN_MARKER" -> BRACE_PAREN_MARKER
      | "BREAK" -> BREAK
      | "BS" -> BS
      | "CASE" -> CASE
      | "CATCH" -> CATCH
      | "CHAR" -> CHAR
      | "CHAR16_T" -> CHAR16_T
      | "CHAR32_T" -> CHAR32_T
      | "CHAR8_T" -> CHAR8_T
      | "CLASS" -> CLASS
      | "CLASS_LBRACE" -> CLASS_LBRACE
      | "COLON" -> COLON
      | "COLON_COLON" -> COLON_COLON
      | "COLON_GT" -> COLON_GT
      | "COMMA" -> COMMA
      | "COMMA_BROKEN" -> COMMA_BROKEN
      | "COMPL" -> COMPL
      | "CONCEPT" -> CONCEPT
      | "COND_MARKER" -> COND_MARKER
      | "CONST" -> CONST
      | "CONSTEVAL" -> CONSTEVAL
      | "CONSTEXPR" -> CONSTEXPR
      | "CONSTINIT" -> CONSTINIT
      | "CONST_CAST" -> CONST_CAST
      | "CONTINUE" -> CONTINUE
      | "CO_AWAIT" -> CO_AWAIT
      | "CO_RETURN" -> CO_RETURN
      | "CO_YIELD" -> CO_YIELD
      | "CUDA_GT_GT_GT" -> CUDA_GT_GT_GT
      | "CUDA_LT_LT_LT" -> CUDA_LT_LT_LT
      | "DECLTYPE" -> DECLTYPE
      | "DEFAULT" -> DEFAULT
      | "DEFINED" -> DEFINED
      | "DELETE" -> DELETE
      | "DO" -> DO
      | "DOT" -> DOT
      | "DOT_STAR" -> DOT_STAR
      | "DOUBLE" -> DOUBLE
      | "DUMMY_BODY" -> DUMMY_BODY
      | "DUMMY_DTOR" -> DUMMY_DTOR
      | "DUMMY_EXPR" -> DUMMY_EXPR
      | "DUMMY_STMT" -> DUMMY_STMT
      | "DUMMY_TYPE" -> DUMMY_TYPE
      | "DYNAMIC_CAST" -> DYNAMIC_CAST
      | "ELAB_CLASS" -> ELAB_CLASS
      | "ELAB_ENUM" -> ELAB_ENUM
      | "ELLIPSIS" -> ELLIPSIS
      | "ELLIPSIS_" -> ELLIPSIS_
      | "ELSE" -> ELSE
      | "END_ASM" -> END_ASM
      | "END_ETORS" -> END_ETORS
      | "END_QPROP" -> END_QPROP
      | "END_STMTS" -> END_STMTS
      | "ENSURES" -> ENSURES
      | "ENUM" -> ENUM
      | "EOF" -> EOF
      | "EQ" -> EQ
      | "EQ_EQ" -> EQ_EQ
      | "EQ_EQ_EQ" -> EQ_EQ_EQ
      | "EXPECTS" -> EXPECTS
      | "EXPLICIT" -> EXPLICIT
      | "EXPORT" -> EXPORT
      | "EXTERN" -> EXTERN
      | "FALSE" -> FALSE
      | "FINAL" -> FINAL
      | "FLOAT" -> FLOAT
      | "FOLD_LPAREN" -> FOLD_LPAREN
      | "FOR" -> FOR
      | "FRIEND" -> FRIEND
      | "GOTO" -> GOTO
      | "GT" -> GT
      | "GT_EQ" -> GT_EQ
      | "GT_GT" -> GT_GT
      | "GT_GT_EQ" -> GT_GT_EQ
      | "GT_GT_GT" -> GT_GT_GT
      | "HAS_CPP_ATTRIBUTE" -> HAS_CPP_ATTRIBUTE
      | "HAS_INCLUDE" -> HAS_INCLUDE
      | "HEAD_COLON_COLON" -> HEAD_COLON_COLON
      | "IF" -> IF
      | "IMPORT" -> IMPORT
      | "IN" -> IN
      | "INI_LBRACE" -> INI_LBRACE
      | "INLINE" -> INLINE
      | "INT" -> INT
      | "LAM_LBRACKET" -> LAM_LBRACKET
      | "LAM_MARKER" -> LAM_MARKER
      | "LBRACE" -> LBRACE
      | "LBRACKET" -> LBRACKET
      | "LONG" -> LONG
      | "LPAREN" -> LPAREN
      | "LT" -> LT
      | "LT_COLON" -> LT_COLON
      | "LT_EQ" -> LT_EQ
      | "LT_EQ_GT" -> LT_EQ_GT
      | "LT_LT" -> LT_LT
      | "LT_LT_EQ" -> LT_LT_EQ
      | "LT_PERC" -> LT_PERC
      | "MARKER" -> MARKER
      | "MINUS" -> MINUS
      | "MINUS_EQ" -> MINUS_EQ
      | "MINUS_GT" -> MINUS_GT
      | "MINUS_GT_STAR" -> MINUS_GT_STAR
      | "MINUS_MINUS" -> MINUS_MINUS
      | "MOCK_MARKER" -> MOCK_MARKER
      | "MS_ATTR_LBRACKET" -> MS_ATTR_LBRACKET
      | "MS_PROPERTY" -> MS_PROPERTY
      | "MS_REF" -> MS_REF
      | "MS_SEALED" -> MS_SEALED
      | "MUTABLE" -> MUTABLE
      | "NAMESPACE" -> NAMESPACE
      | "NEW" -> NEW
      | "NEWLINE" -> NEWLINE
      | "NOEXCEPT" -> NOEXCEPT
      | "NOT" -> NOT
      | "NOT_EQ" -> NOT_EQ
      | "NULLPTR" -> NULLPTR
      | "OBJC_ABAILABLE" -> OBJC_AVAILABLE
      | "OBJC_AUTORELEASEPOOL" -> OBJC_AUTORELEASEPOOL
      | "OBJC_CATCH" -> OBJC_CATCH
      | "OBJC_CLASS" -> OBJC_CLASS
      | "OBJC_DEFS" -> OBJC_DEFS
      | "OBJC_DYNAMIC" -> OBJC_DYNAMIC
      | "OBJC_ENCODE" -> OBJC_ENCODE
      | "OBJC_END" -> OBJC_END
      | "OBJC_FINALLY" -> OBJC_FINALLY
      | "OBJC_INTERFACE" -> OBJC_INTERFACE
      | "OBJC_LBRACKET" -> OBJC_LBRACKET
      | "OBJC_MINUS" -> OBJC_MINUS
      | "OBJC_OPTIONAL" -> OBJC_OPTIONAL
      | "OBJC_PACKAGE" -> OBJC_PACKAGE
      | "OBJC_PLUS" -> OBJC_PLUS
      | "OBJC_PRIVATE" -> OBJC_PRIVATE
      | "OBJC_PROPERTY" -> OBJC_PROPERTY
      | "OBJC_PROTECTED" -> OBJC_PROTECTED
      | "OBJC_PROTOCOL" -> OBJC_PROTOCOL
      | "OBJC_PUBLIC" -> OBJC_PUBLIC
      | "OBJC_REQUIRED" -> OBJC_REQUIRED
      | "OBJC_SELECTOR" -> OBJC_SELECTOR
      | "OBJC_SYNCHRONIZED" -> OBJC_SYNCHRONIZED
      | "OBJC_SYNTHESIZE" -> OBJC_SYNTHESIZE
      | "OBJC_THROW" -> OBJC_THROW
      | "OBJC_TRY" -> OBJC_TRY
      | "ODD_ELSE" -> ODD_ELSE
      | "ODD_FOR" -> ODD_FOR
      | "ODD_LBRACE" -> ODD_LBRACE
      | "ODD_RBRACE" -> ODD_RBRACE
      | "OPERATOR" -> OPERATOR
      | "OR" -> OR
      | "OR_EQ" -> OR_EQ
      | "OVERRIDE" -> OVERRIDE
      | "PERC" -> PERC
      | "PERC_COLON" -> PERC_COLON
      | "PERC_COLON_PERC_COLON" -> PERC_COLON_PERC_COLON
      | "PERC_EQ" -> PERC_EQ
      | "PERC_GT" -> PERC_GT
      | "PLUS" -> PLUS
      | "PLUS_EQ" -> PLUS_EQ
      | "PLUS_PLUS" -> PLUS_PLUS
      | "PP_" -> PP_
      | "PP_DEFINE" -> PP_DEFINE
      | "PP_ENDIF_" -> PP_ENDIF_
      | "PP_ERROR" -> PP_ERROR
      | "PP_IF" -> PP_IF
      | "PP_IFDEF" -> PP_IFDEF
      | "PP_IFDEF_A" -> PP_IFDEF_A
      | "PP_IFDEF_ATTR" -> PP_IFDEF_ATTR
      | "PP_IFDEF_B" -> PP_IFDEF_B
      | "PP_IFDEF_BROKEN" -> PP_IFDEF_BROKEN
      | "PP_IFDEF_C" -> PP_IFDEF_C
      | "PP_IFDEF_CB" -> PP_IFDEF_CB
      | "PP_IFDEF_CLOSE_OPEN" -> PP_IFDEF_CLOSE_OPEN
      | "PP_IFDEF_CLOSING" -> PP_IFDEF_CLOSING
      | "PP_IFDEF_COND" -> PP_IFDEF_COND
      | "PP_IFDEF_COND_" -> PP_IFDEF_COND_
      | "PP_IFDEF_D" -> PP_IFDEF_D
      | "PP_IFDEF_E" -> PP_IFDEF_E
      | "PP_IFDEF_EH" -> PP_IFDEF_EH
      | "PP_IFDEF_H" -> PP_IFDEF_H
      | "PP_IFDEF_I" -> PP_IFDEF_I
      | "PP_IFDEF_O" -> PP_IFDEF_O
      | "PP_IFDEF_P" -> PP_IFDEF_P
      | "PP_IFDEF_S" -> PP_IFDEF_S
      | "PP_IFDEF_SHIFT" -> PP_IFDEF_SHIFT
      | "PP_IFDEF_X" -> PP_IFDEF_X
      | "PP_IFNDEF" -> PP_IFNDEF
      | "PP_IFNDEF_A" -> PP_IFNDEF_A
      | "PP_IFNDEF_ATTR" -> PP_IFNDEF_ATTR
      | "PP_IFNDEF_B" -> PP_IFNDEF_B
      | "PP_IFNDEF_BROKEN" -> PP_IFNDEF_BROKEN
      | "PP_IFNDEF_C" -> PP_IFNDEF_C
      | "PP_IFNDEF_CB" -> PP_IFNDEF_CB
      | "PP_IFNDEF_CLOSE_OPEN" -> PP_IFNDEF_CLOSE_OPEN
      | "PP_IFNDEF_CLOSING" -> PP_IFNDEF_CLOSING
      | "PP_IFNDEF_COND" -> PP_IFNDEF_COND
      | "PP_IFNDEF_COND_" -> PP_IFNDEF_COND_
      | "PP_IFNDEF_D" -> PP_IFNDEF_D
      | "PP_IFNDEF_E" -> PP_IFNDEF_E
      | "PP_IFNDEF_EH" -> PP_IFNDEF_EH
      | "PP_IFNDEF_H" -> PP_IFNDEF_H
      | "PP_IFNDEF_I" -> PP_IFNDEF_I
      | "PP_IFNDEF_O" -> PP_IFNDEF_O
      | "PP_IFNDEF_P" -> PP_IFNDEF_P
      | "PP_IFNDEF_S" -> PP_IFNDEF_S
      | "PP_IFNDEF_SHIFT" -> PP_IFNDEF_SHIFT
      | "PP_IFNDEF_X" -> PP_IFNDEF_X
      | "PP_IF_A" -> PP_IF_A
      | "PP_IF_ATTR" -> PP_IF_ATTR
      | "PP_IF_B" -> PP_IF_B
      | "PP_IF_BROKEN" -> PP_IF_BROKEN
      | "PP_IF_C" -> PP_IF_C
      | "PP_IF_CB" -> PP_IF_CB
      | "PP_IF_CLOSE_OPEN" -> PP_IF_CLOSE_OPEN
      | "PP_IF_CLOSING" -> PP_IF_CLOSING
      | "PP_IF_COND" -> PP_IF_COND
      | "PP_IF_COND_" -> PP_IF_COND_
      | "PP_IF_D" -> PP_IF_D
      | "PP_IF_E" -> PP_IF_E
      | "PP_IF_EH" -> PP_IF_EH
      | "PP_IF_H" -> PP_IF_H
      | "PP_IF_I" -> PP_IF_I
      | "PP_IF_O" -> PP_IF_O
      | "PP_IF_P" -> PP_IF_P
      | "PP_IF_S" -> PP_IF_S
      | "PP_IF_SHIFT" -> PP_IF_SHIFT
      | "PP_IF_X" -> PP_IF_X
      | "PP_IMPORT" -> PP_IMPORT
      | "PP_INCLUDE" -> PP_INCLUDE
      | "PP_LINE" -> PP_LINE
      | "PP_LPAREN" -> PP_LPAREN
      | "PP_MARKER" -> PP_MARKER
      | "PP_ODD_IF" -> PP_ODD_IF
      | "PP_ODD_IFDEF" -> PP_ODD_IFDEF
      | "PP_ODD_IFNDEF" -> PP_ODD_IFNDEF
      | "PP_PRAGMA" -> PP_PRAGMA
      | "PP_UNDEF" -> PP_UNDEF
      | "PRIVATE" -> PRIVATE
      | "PROTECTED" -> PROTECTED
      | "PS_LPAREN" -> PS_LPAREN
      | "PTR_AMP" -> PTR_AMP
      | "PTR_AMP_AMP" -> PTR_AMP_AMP
      | "PTR_HAT" -> PTR_HAT
      | "PTR_STAR" -> PTR_STAR
      | "PUBLIC" -> PUBLIC
      | "PURE_ZERO" -> PURE_ZERO
      | "QUEST" -> QUEST
      | "RBRACE" -> RBRACE
      | "RBRACKET" -> RBRACKET
      | "REGISTER" -> REGISTER
      | "REINTERPRET_CAST" -> REINTERPRET_CAST
      | "REQUIRES" -> REQUIRES
      | "RETURN" -> RETURN
      | "RPAREN" -> RPAREN
      | "SECTION_MARKER" -> SECTION_MARKER
      | "SEMICOLON_" -> SEMICOLON_
      | "SHARP" -> SHARP
      | "SHARP_SHARP" -> SHARP_SHARP
      | "SHORT" -> SHORT
      | "SIGNED" -> SIGNED
      | "SIZEOF" -> SIZEOF
      | "SLASH" -> SLASH
      | "SLASH_EQ" -> SLASH_EQ
      | "SS_LPAREN" -> SS_LPAREN
      | "STAR" -> STAR
      | "STAR_EQ" -> STAR_EQ
      | "STATIC" -> STATIC
      | "STATIC_ASSERT" -> STATIC_ASSERT
      | "STATIC_CAST" -> STATIC_CAST
      | "STRUCT" -> STRUCT
      | "STR_MARKER" -> STR_MARKER
      | "SUB_REQUIRES" -> SUB_REQUIRES
      | "SUFFIX_MARKER" -> SUFFIX_MARKER
      | "SWITCH" -> SWITCH
      | "S_LPAREN" -> S_LPAREN
      | "S_RPAREN" -> S_RPAREN
      | "TEMPLATE" -> TEMPLATE
      | "TEMPL_GT" -> TEMPL_GT
      | "TEMPL_LT" -> TEMPL_LT
      | "TEMPL_LT_" -> TEMPL_LT_
      | "THIS" -> THIS
      | "THREAD_LOCAL" -> THREAD_LOCAL
      | "THROW" -> THROW
      | "THROW_" -> THROW_
      | "TRUE" -> TRUE
      | "TRY" -> TRY
      | "TYPEDEF" -> TYPEDEF
      | "TYPEID" -> TYPEID
      | "TYPENAME" -> TYPENAME
      | "TY_HAT" -> TY_HAT
      | "TY_LPAREN" -> TY_LPAREN
      | "TY_LPAREN_" -> TY_LPAREN_
      | "TY_TEMPL_GT" -> TY_TEMPL_GT
      | "TY_TEMPL_GT_" -> TY_TEMPL_GT_
      | "TY_TILDE" -> TY_TILDE
      | "UNION" -> UNION
      | "UNSIGNED" -> UNSIGNED
      | "USING" -> USING
      | "VAX_GLOBALDEF" -> VAX_GLOBALDEF
      | "VIRTUAL" -> VIRTUAL
      | "VOID" -> VOID
      | "VOLATILE" -> VOLATILE
      | "WCHAR_T" -> WCHAR_T
      | "WHILE" -> WHILE
      | "XOR" -> XOR
      | "XOR_EQ" -> XOR_EQ
      | _ -> assert false
  end
  | [w; x] -> begin
      match w, x with
      | "PMODE", m -> PMODE (mode_of_string m "")
      | "GT_7", b -> GT_7 (ref (bool_of_string b))
      | "STR_MACRO", s -> STR_MACRO s
      | "INT_MACRO", s -> INT_MACRO s
      | "DECL_MACRO", s -> DECL_MACRO s
      | "PRAGMA_MACRO", s -> PRAGMA_MACRO s
      | "STMT_MACRO", s -> STMT_MACRO s
      | "VIRT_SPEC_MACRO", s -> VIRT_SPEC_MACRO s
      | "OP_MACRO", s -> OP_MACRO s
      | "PARAM_DECL_MACRO", s -> PARAM_DECL_MACRO s
      | "PARAMS_MACRO", s -> PARAMS_MACRO s
      | "PARAMS_BODY_MACRO", s -> PARAMS_BODY_MACRO s
      | "ARG_MACRO", s -> ARG_MACRO s
      | "ARGS_MACRO", s -> ARGS_MACRO s
      | "NEW_INIT_MACRO", s -> NEW_INIT_MACRO s
      | "ATTR_MACRO", s -> ATTR_MACRO s
      | "ACC_SPEC_MACRO", s -> ACC_SPEC_MACRO s
      | "DECL_SPEC_MACRO", s -> DECL_SPEC_MACRO s
      | "CC_MACRO", s -> CC_MACRO s
      | "LAM_MACRO", s -> LAM_MACRO s
      | "CV_MACRO", s -> CV_MACRO s
      | "NOEXCEPT_MACRO", s -> NOEXCEPT_MACRO s
      | "NS_MACRO", s -> NS_MACRO s
      | "EMPTY_MACRO", s -> EMPTY_MACRO s
      | "DELIM_MACRO", s -> DELIM_MACRO s
      | "BLOCK_HEAD_MACRO", s -> BLOCK_HEAD_MACRO s
      | "BLOCK_END_MACRO", s -> BLOCK_END_MACRO s
      | "TYPE_MACRO", s -> TYPE_MACRO s
      | "BASE_MACRO", s -> BASE_MACRO s
      | "BASE_SPEC_MACRO", s -> BASE_SPEC_MACRO s
      | "SUFFIX_MACRO", s -> SUFFIX_MACRO s
      | "PTR_MACRO", s -> PTR_MACRO s
      | "BODY_MACRO", s -> BODY_MACRO s
      | "DTOR_MACRO", s -> DTOR_MACRO s
      | "CLASS_HEAD_MACRO", s -> CLASS_HEAD_MACRO s
      | "FUNC_HEAD_MACRO", s -> FUNC_HEAD_MACRO s
      | "CAST_HEAD_MACRO", s -> CAST_HEAD_MACRO s
      | "OBJC_PROTOCOL_REF_LIST_MACRO", s -> OBJC_PROTOCOL_REF_LIST_MACRO s
      | "OBJC_SEL_MACRO", s -> OBJC_SEL_MACRO s
      | "CLASS_BODY_HEAD_MACRO", s -> CLASS_BODY_HEAD_MACRO s
      | "CLASS_BODY_END_MACRO", s -> CLASS_BODY_END_MACRO s
      | "IDENT", s -> IDENT s
      | "IDENT_", s -> IDENT_ s
      | "IDENT_V", s -> IDENT_V s
      | "IDENT_B", s -> IDENT_B s
      | "IDENT_C", s -> IDENT_C s
      | "IDENT_E", s -> IDENT_E s
      | "IDENT_BM", s -> IDENT_BM s
      | "IDENT_DM", s -> IDENT_DM s
      | "IDENT_EM", s -> IDENT_EM s
      | "IDENT_SM", s -> IDENT_SM s
      | "IDENT_TM", s -> IDENT_TM s
      | "IDENT_IM", s -> IDENT_IM s
      | "IDENT_PM", s -> IDENT_PM s
      | "IDENT_PBM", s -> IDENT_PBM s
      | "IDENT_PGM", s -> IDENT_PGM s
      | "IDENT_CM", s -> IDENT_CM s
      | "IDENT_LM", s -> IDENT_LM s
      | "IDENT_LPAREN", s -> IDENT_LPAREN s
      | "IDENT_AM", s -> IDENT_AM s
      | "IDENT_OM", s -> IDENT_OM s
      | "IDENT_TPM", s -> IDENT_TPM s
      | "IDENT_NSM", s -> IDENT_NSM s
      | "IDENT_DSM", s -> IDENT_DSM s
      | "IDENT_BHM", s -> IDENT_BHM s
      | "IDENT_BIM", s -> IDENT_BIM s
      | "IDENT_BEM", s -> IDENT_BEM s
      | "IDENT_BFM", s -> IDENT_BFM s
      | "IDENT_BSM", s -> IDENT_BSM s
      | "IDENT_CHM", s -> IDENT_CHM s
      | "IDENT_CTM", s -> IDENT_CTM s
      | "IDENT_AGM", s -> IDENT_AGM s
      | "IDENT_AGSM", s -> IDENT_AGSM s
      | "IDENT_LOM", s -> IDENT_LOM s
      | "IDENT_PDM", s -> IDENT_PDM s
      | "IDENT_VM", s -> IDENT_VM s
      | "IDENT_SXM", s -> IDENT_SXM s
      | "IDENT_DSL", s -> IDENT_DSL s
      | "IDENT_DLM", s -> IDENT_DLM s
      | "IDENT_CBHM", s -> IDENT_CBHM s
      | "IDENT_CBEM", s -> IDENT_CBEM s
      | "IDENT_IHM", s -> IDENT_IHM s
      | "IDENT_IEM", s -> IDENT_IEM s
      | "EXTERN_X", s -> EXTERN_X s
      | "BAR_BAR_BROKEN", i -> BAR_BAR_BROKEN i
      | "AMP_AMP_BROKEN", i -> AMP_AMP_BROKEN i
      | "PP_ODD_ENDIF", x -> PP_ODD_ENDIF x
      | "PP_ODD_ELIF", x -> PP_ODD_ELIF x
      | "PP_ODD_ELSE", x -> PP_ODD_ELSE x
      | "PP_STRINGIZED", s -> PP_STRINGIZED s
      | "INT_LITERAL", s -> INT_LITERAL s
      | "CHAR_LITERAL", s -> CHAR_LITERAL s
      | "FLOAT_LITERAL", s -> FLOAT_LITERAL s
      | "STR_LITERAL", s -> STR_LITERAL (Scanf.unescaped s)
      | "BOOL_LITERAL", s -> BOOL_LITERAL s
      | "USER_INT_LITERAL", s -> USER_INT_LITERAL s
      | "USER_FLOAT_LITERAL", s -> USER_FLOAT_LITERAL s
      | "USER_STR_LITERAL", s -> USER_STR_LITERAL s
      | "USER_CHAR_LITERAL", s -> USER_CHAR_LITERAL s
      | "RESTRICT", s -> RESTRICT s
      | "MS_ASM", s -> MS_ASM s
      | "MS_PRAGMA", s -> MS_PRAGMA s
      | "MS_CDECL", s -> MS_CDECL s
      | "MS_STDCALL", s -> MS_STDCALL s
      | "GNU_ASM", s -> GNU_ASM s
      | "GNU_ATTR", s -> GNU_ATTR s
      | "SEMICOLON", b -> SEMICOLON (bool_of_string b)
      | "TILDE", s -> TILDE s
      | "EXCLAM", s -> EXCLAM s
      | "HAT", s -> HAT s
      | "AMP", s -> AMP s
      | "BAR", s -> BAR s
      | "HAT_EQ", s -> HAT_EQ s
      | "AMP_EQ", s -> AMP_EQ s
      | "BAR_EQ", s -> BAR_EQ s
      | "EXCLAM_EQ", s -> EXCLAM_EQ s
      | "AMP_AMP", s -> AMP_AMP s
      | "BAR_BAR", s -> BAR_BAR s
      | "PP_ELIF", x -> PP_ELIF (ref x)
      | "PP_ELSE", x -> PP_ELSE (ref x)
      | "PP_ENDIF", x -> PP_ENDIF (ref x)
      | "PP_UNKNOWN", s -> PP_UNKNOWN s
      | "BS_IDENT", s -> BS_IDENT s
      | "DOXYGEN_CMD", s -> DOXYGEN_CMD s
      | "DOXYGEN_LINE", s -> DOXYGEN_LINE s
      | "OBJC_UNKNOWN", s -> OBJC_UNKNOWN s
      | _ -> assert false
  end
  | [w; x; y] -> begin
      match w, x, y with
      | "PMODE", m, s -> PMODE (mode_of_string m s)
      | "CONFLICT_MARKER", b, s -> CONFLICT_MARKER(ref (bool_of_string b), s)
      | "BRACE_LEVEL", lv, b -> BRACE_LEVEL(int_of_string lv, bool_of_string b)
      | _ -> assert false
  end
  | _ -> assert false


[%%capture_path
let queue_from_file q fpath =
  let ch = open_in fpath in
  let count = ref 0 in
  try
    while true do
      let w = input_line ch in
      [%debug_log "%s" w];
      let rt = word_to_token w in
      [%debug_log "[%d] ----- %s" !count (Token.rawtoken_to_string rt)];
      Queue.add rt q;
      incr count
    done
  with
  | End_of_file -> close_in ch
  | exn -> begin
      Xprint.error "!!! %s" (Printexc.to_string exn);
      close_in ch;
      exit 1
  end
]
