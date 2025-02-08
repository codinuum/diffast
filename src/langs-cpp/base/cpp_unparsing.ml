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

(*
 * An unparser for C/C++
 *
 * cpp_unparsing.ml
 *
 *)

module Sourcecode = Diffast_core.Sourcecode
module Unparsing_base = Langs_common.Unparsing_base
module Ast = Cpp_parsing.Ast

module L = Cpp_label
module Tree = Sourcecode.Tree (L)

module Fmtr = struct
  let formatter = Format.std_formatter
end

module UPB = Unparsing_base.Make(Fmtr)

open UPB

(*******)
let _pr_semicolon() = pr_string ";"
let pr_semicolon() = _pr_semicolon(); pr_space()
let pr_colon_colon() = pr_string "::"
let pr_lt() = pr_string "<"
let pr_gt() = pr_string ">"

let pr_if_newline = Format.print_if_newline

class ppbox_ = object (self)
  inherit ppbox

  val mutable block_style = BSshort

  method pr_block_head() =
    match block_style with
    | BStall  -> pr_cut(); pr_lbrace(); self#open_vbox self#indent; pr_cut()
    | BSshort -> pr_lbrace(); pr_space(); self#open_vbox self#indent; pr_if_newline(); pad self#indent

  method! pr_block_end() = self#close_box(); pr_space(); pr_rbrace()

  method pr_else() =
    match block_style with
    | BStall  -> pr_space(); pr_string "else"; pr_space()
    | BSshort -> pr_string " else "

end
(*******)

let pb = new ppbox_

let error_symbol = "###"

let getlab nd =
  match nd#data#orig_lab_opt with
  | Some o -> (Obj.obj o : L.t)
  | None -> (Obj.obj nd#data#_label : L.t)

let has_orig_lab nd =
  match nd#data#orig_lab_opt with
  | Some o -> (Obj.obj o : L.t) <> (Obj.obj nd#data#_label : L.t)
  | None -> false


let get_nth_children = Sourcecode._get_logical_nth_child


let rec pr_node ?(fail_on_error=true) ?(va=false) ?(prec=0) node =
  ignore va;
  ignore prec;
  let pr_node_ = pr_node ~fail_on_error in
  let children = node#initial_children in
  let nchildren = Array.length children in
  let pr_nth_child =
    if fail_on_error then
      fun ?(va=false) ?(prec=0) nth ->
        pr_node ~fail_on_error:true ~va ~prec children.(nth)
    else
      fun ?(va=false) ?(prec=0) nth ->
        try
          pr_node ~fail_on_error:false ~va ~prec children.(nth)
        with
          _ -> pr_string error_symbol
  in
  let nth_children = get_nth_children node in
  let pr_nth_children ?(head=pr_none) ?(tail=pr_none) =
    if fail_on_error then begin
      fun ?(va=false) ?(prec=0) nth ->
        let ca = nth_children nth in
        let non_empty = ca <> [||] in
        if non_empty then head();
        pb#pr_a pad1 (pr_node ~fail_on_error:true ~va ~prec) ca;
        if non_empty then tail()
    end
    else
      fun ?(va=false) ?(prec=0) nth ->
        try
          let ca = get_nth_children node nth in
          let non_empty = ca <> [||] in
          if non_empty then head();
          pb#pr_a pad1 (pr_node ~fail_on_error:false ~va ~prec) ca;
          if non_empty then tail()
        with
          _ -> pr_string error_symbol
  in
  let pr_macro_invocation i = pr_string i; pr_lparen(); pb#pr_a pr_comma pr_node_ children; pr_rparen() in

  let pr_seq ?(head=pr_none) ?(sep=pad1) ?(tail=pr_none) () = pb#pr_a ~head ~tail sep pr_node_ children in

  let prefix = node#data#get_prefix in
  if prefix <> "" then
    pr_string prefix;

  begin
  match getlab node with
  | DUMMY -> ()
  | EMPTY -> ()
  | AMBIGUOUS_CONSTRUCT -> pr_seq()
  | PARTIAL_CONSTRUCT   -> pr_seq()
  | DECLS               -> pr_seq ~sep:pr_cut ()
  | MEM_DECLS           -> pr_seq ~sep:pr_cut ()
  | STMTS               -> pb#open_vbox 0; pr_seq ~sep:pr_cut (); pb#close_box()
  | EXPRS               -> pr_seq ~sep:pr_comma ()
  | INITS               -> pr_seq ~sep:pr_comma ()
  | LABELS              -> pr_seq()
  | SPECS               -> pr_seq()
  | ETORS               -> pr_seq ~sep:pr_comma ()
  | OBJC_DECLS          -> pr_seq ~sep:pr_cut ()
  | TEMPL_PARAMS        -> pr_seq ~sep:pr_comma ()
  | TEMPL_ARGS          -> pr_seq ~sep:pr_comma ()
  | DELIM_MACRO_ i      -> pr_macro_invocation i
  | DELIM_MACRO i -> begin
      for i = 0 to nchildren - 2 do
        if i > 0 then pr_comma();
        pr_node ~fail_on_error children.(i)
      done;
      pr_id i;
      pr_node ~fail_on_error children.(nchildren-1)
  end
  | Q_PROPERTY -> begin
      pr_id "Q_PROPERTY";
      pr_lparen(); pb#pr_a pad1 pr_node_ children; pr_rparen()
  end

  | ERROR s -> pr_string s

  | TranslationUnit -> pb#open_vbox 0; pb#pr_a pr_cut pr_node_ children; pb#close_box()

(* PpDirective *)
  | PpInclude s -> pr_string "#include "; pr_string s
  | PpDefine i -> begin
      pb#enable_backslash_newline();
      pr_string "#define "; pr_id i;
      if nchildren > 0 then
        pr_nth_child 0;
      pb#disable_backslash_newline()
  end
  | PpUndef i     -> pr_string "#undef " ; pr_id i
  | PpLine (j, s) -> pr_string "#line "; pr_int j; pad1(); pr_string s
  | PpError s     -> pr_string "#error "; pr_string s
  | PpPragma s    -> pr_string "#pragma "; pr_string s
  | PpNull        -> pr_string "#"
  | PpMarker(j, s, jl) -> begin
      pr_string "# "; pr_int j; pad1(); pr_string s;
      pr_string (String.concat " " (List.map string_of_int jl))
  end
  | PpIf _      -> pr_string "#if "; pb#pr_a pad1 pr_node_ children
  | PpIfdef i   -> pr_string "#ifdef "; pr_id i
  | PpIfndef i  -> pr_string "#ifndef "; pr_id i
  | PpElif _    -> pr_string "#elif "; pb#pr_a pad1 pr_node_ children
  | PpElse _    -> pr_string "#else"
  | PpEndif _   -> pr_string "#endif"
  | PpUnknown s -> pr_string "#"; pr_string s
  | PpImport s  -> pr_string "#import "; pr_string s

  | OmpDirective s -> pr_string "#pragma omp ";pr_string s
  | AccDirective s -> pr_string "#pragma acc ";pr_string s

  | PpIfSection _
  | PpIfSectionFuncDef _
  | PpIfSectionAltFuncDef
  | PpIfSectionBroken
  | PpIfSectionBrokenIf
  | PpIfSectionBrokenFuncDef
  | PpIfSectionBrokenDtorFunc
  | PpIfSectionCondExpr
  | PpIfSectionLogicalAnd
  | PpIfSectionLogicalOr
  | PpIfSectionTemplDecl
  | PpIfSectionHandler
  | PpIfSectionTryBlock
    -> begin
      force_newline();
      pb#open_vbox 0;
      pb#pr_a pr_cut pr_node_ children;
      pb#close_box();
      force_newline()
    end

  | PpIfGroup _    -> pb#pr_a pr_cut pr_node_ children
  | PpElifGroup _  -> pb#pr_a pr_cut pr_node_ children
  | PpElseGroup _  -> pb#pr_a pr_cut pr_node_ children
  | PpStringized s -> pr_string s
  | PpMacroParam s -> pr_string s

(* Declaration *)
  | InitDeclaration                      -> pb#pr_a pr_cut pr_node_ children
  | SimpleDeclaration                    -> pb#open_hbox(); pr_seq(); pb#close_box()
  | AsmDefinition _                      -> pr_nth_children 0; pr_string "asm"; pr_nth_children 1
  | NamespaceAliasDefinition i -> begin
      pr_string "namespace "; pr_id i; pr_eq(); pr_nth_child 0
  end
  | UsingDeclaration                     -> pr_string "using "; pr_seq ~sep:pr_comma ()
  | UsingEnumDeclaration                 -> pr_string "using enum "; pr_nth_children 0
  | UsingDirective _ -> begin
      pr_nth_children 0; pr_string "using namespace "; pr_nth_children 1
  end
  | Static_assertDeclaration -> begin
      pr_string "static_assert";
      pr_lparen(); pr_nth_children 0; pr_nth_children ~head:pr_comma 1; pr_rparen()
  end
  | AliasDeclaration i -> begin
      pr_string "using "; pr_id i; pr_nth_children 0; pr_eq(); pr_nth_children 1
  end
  | OpaqueEnumDeclaration                -> pr_string "enum "; pr_seq()
  | OpaqueEnumDeclarationClass           -> pr_string "enum class "; pr_seq()
  | OpaqueEnumDeclarationStruct          -> pr_string "enum struct "; pr_seq()
  | OpaqueEnumDeclarationMacro i         -> pr_id i; pad1(); pr_seq()

  | NodeclspecFunctionDeclaration        -> pr_seq()
  | FunctionDefinition _                 -> pr_seq()
  | NestedFunctionDefinition _           -> pr_seq()
  | TemplateDeclaration                  -> pr_nth_child 0; pr_space(); pr_nth_child 1
  | DeductionGuide n -> begin
      pr_id n; pr_lparen(); pr_nth_children 1; pr_rparen(); pr_string " -> "; pr_nth_children 2; _pr_semicolon()
  end
  | ExplicitInstantiation  -> pr_nth_children 0; pr_string "template "; pr_nth_children 1
  | ExplicitSpecialization -> pr_string "template<>"; pr_nth_child 0;
  | ExportDeclaration when nchildren = 0 -> pr_string "export {}"
  | ExportDeclaration when nchildren = 1 -> pr_string "export "; pr_nth_children 0
  | ExportDeclaration -> begin
      pr_string "export"; pad1();
      pb#pr_block_head();
      pb#pr_a pr_cut pr_node_ children;
      pb#pr_block_end()
  end
  | LinkageSpecification s -> begin
      pr_string "extern "; pr_string s; pad1();
      pb#pr_block_head();
      pb#pr_a pr_cut pr_node_ children;
      pb#pr_block_end()
  end
  | NamedNamespaceDefinition i -> begin
      let has_ns =
        try
          not (L.is_namespace_head (getlab (nth_children 0).(0)))
        with _ -> true
      in
      pr_nth_children 0;
      if has_ns then
        pr_string "namespace ";
      pr_nth_children 1;
      pr_id i;
      pr_nth_children 2;
      if nth_children 3 <> [||] then begin
        pad1();
        pb#pr_block_head();
        pb#pr_a pr_cut pr_node_ (nth_children 3);
        pb#pr_block_end()
      end
  end
  | UnnamedNamespaceDefinition -> begin
      pr_nth_children 0;
      pr_string "namespace ";
      pr_nth_children 1;
      pad1();
      pb#pr_block_head();
      pb#pr_a pr_cut pr_node_ (nth_children 2);
      pb#pr_block_end()
  end
  | NestedNamespaceDefinition _ -> begin
      pr_string "namespace ";
      pr_nth_child 0;
      pr_colon_colon();
      pr_nth_children 1;
      pad1();
      pb#pr_block_head();
      pb#pr_a pr_cut pr_node_ (nth_children 2);
      pb#pr_block_end()
  end
  | NamespaceDefinitionMacro i           -> pr_id i
  | EmptyDeclaration                     -> _pr_semicolon()
  | AttributeDeclaration                 -> pr_seq()
  | DeclarationMacro i                   -> pr_id i
  | DeclarationMacroInvocation i         -> pr_macro_invocation i
  | DeclarationMacroInvocationInvocation -> begin
      pr_nth_child 0; pr_lparen(); pb#pr_a pr_comma pr_node_ (nth_children 1); pr_rparen()
  end
  | PragmaMacro i                        -> pr_id i
  | PragmaMacroInvocation i              -> pr_macro_invocation i
  | MockQualifier i                      -> pr_id i
  | DeclarationMacroInvocationArrow      -> pr_nth_child 0; pr_string "->"; pr_nth_children 1; pr_nth_children 2
  | DeclarationMacroInvocationDot        -> pr_nth_child 0; pr_string "."; pr_nth_children 1; pr_nth_children 2
  | ImportDeclaration s                  -> pr_string "import "; pr_string s
  | RefMacro i                           -> pr_id i
  | RefMacroInvocation i                 -> pr_macro_invocation i

(* Statement *)
  | Statement            -> pr_string "<statement>"
  | ExpressionStatement  -> pr_nth_children ~tail:pad1 0; pr_nth_children 1
  | DeclarationStatement -> pb#open_hbox(); pr_seq(); pb#close_box()
  | TryBlock             -> pr_string "try "; pr_nth_child 0
  | LabeledStatement     -> pr_seq()
  | SelectionStatement   -> pr_string "<selection-statement>"
  | IfStatement -> begin
      let has_paren =
        try
          let lab = getlab (nth_children 2).(0) in
          not (L.is_expr_macro_ivk lab) && not (L.is_stmt_macro_ivk lab)
        with _ -> true
      in
      pr_string "if ";
      pr_nth_children 0;
      if has_paren then pr_lparen();
      pr_nth_children 1; pr_nth_children 2;
      if has_paren then pr_rparen();
      pad1();
      pr_nth_children 3;
      pr_nth_children ~head:pb#pr_else 4
  end
  | ElseStatement   -> pr_string "else"; pr_seq ~head:pad1 ()
  | SwitchStatement -> pr_string "switch "; pr_seq()
  (*| EmptyStatement  -> _pr_semicolon()*)
  | CompoundStatement -> begin
      if nchildren = 0 then
        pr_string "{}"
      else begin
        pb#pr_block_head();
        pr_seq ~sep:pr_cut ();
        pb#pr_block_end()
      end
  end
  | IterationStatement -> pr_string "<iteration-statement>"
  | WhileStatement     -> pr_string "while "; pr_lparen(); pr_nth_children 0; pr_rparen(); pr_nth_children 1
  | DoStatement -> begin
      pr_string "do "; pr_nth_children 0;
      if nth_children 1 <> [||] then begin
        pr_string "while ";
        pr_lparen();
        pr_nth_children 1;
        pr_rparen();
        _pr_semicolon()
      end
  end
  | ForStatement -> begin
      pb#open_hbox();
      pr_string "for ";
      pr_lparen(); pr_nth_child 0; pad1(); pr_nth_children 1; pr_semicolon(); pr_nth_children 2; pr_rparen();
      pad1();
      pb#close_box();
      pr_nth_children 3
  end
  | ForInStatement -> begin
      pr_string "for ";
      pr_lparen(); pr_nth_children 0; pr_string " in "; pr_nth_children 1; pr_rparen();
      pr_nth_children 2
  end
  | RangeBasedForStatement -> begin
      pr_string "for ";
      pr_lparen(); pr_nth_children 0; pr_nth_children 1; pr_colon(); pr_nth_children 2; pr_rparen();
      pr_nth_children 3
  end
  | JumpStatement          -> pr_string "<jump-statement>"
  | BreakStatement         -> pr_string "break"
  | ContinueStatement      -> pr_string "continue"
  | ReturnStatement -> begin
      pr_string "return";
      if nchildren > 0 then begin
        pad1();
        pr_nth_child 0;
      end
  end
  | GotoStatement i            -> pr_string "goto "; pr_string i
  | ComputedGotoStatement      -> pr_string "goto"
  | CoroutineReturnStatement   -> pr_string "co_return"; pr_nth_children ~head:pad1 0

  | StatementMacroInvocation i -> pr_macro_invocation i
  | StatementMacro i           -> pr_id i
  | IterationMacroInvocation i -> pr_macro_invocation i
  | IterationMacro i           -> pr_id i

(* Expression *)
  | This                         -> pr_string "this"
  | ParenthesizedExpression      -> pr_lparen(); pr_nth_child 0; pr_rparen()
  | RequiresExpression           -> pr_string "requires "; pr_seq()
  | FoldExpression -> begin
      pr_lparen();
      pr_nth_children 0; pr_nth_children 1; pr_ellipsis();
      pr_nth_children 2; pr_nth_children 3;
      pr_rparen()
  end
  | LambdaExpression -> begin
      pr_nth_child 0;
      pr_nth_children ~head:pr_lt ~tail:pr_gt 1;
      pr_nth_children 2;
      pr_nth_children 3;
      pr_nth_children 4;
      pr_nth_children 5
  end
  | LogicalOrExpression i   -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_child 1
  | LogicalAndExpression i  -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_child 1
  | InclusiveOrExpression i -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_child 1
  | ExclusiveOrExpression i -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_child 1
  | AndExpression i         -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_child 1

  | EqualityExpression         -> pr_string "<equality-expression>"
  | EqualityExpressionEq       -> pr_nth_child 0; pr_string " == "; pr_nth_child 1
  | EqualityExpressionStrictEq -> pr_nth_child 0; pr_string " === "; pr_nth_child 1
  | EqualityExpressionNeq i    -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_child 1

  | RelationalExpression   -> pr_string "<relational-expression>"
  | RelationalExpressionLt -> pr_nth_child 0; pr_string " < "; pr_nth_child 1
  | RelationalExpressionGt -> pr_nth_child 0; pr_string " > "; pr_nth_child 1
  | RelationalExpressionLe -> pr_nth_child 0; pr_string " <= "; pr_nth_child 1
  | RelationalExpressionGe -> pr_nth_child 0; pr_string " >= "; pr_nth_child 1

  | CompareExpression -> pr_string "<=>"

  | ShiftExpression       -> pr_string "<shift-expression>"
  | ShiftExpressionLeft   -> pr_nth_child 0; pr_string " << "; pr_nth_child 1
  | ShiftExpressionRight  -> pr_nth_child 0; pr_string " >> "; pr_nth_child 1
  | ShiftExpressionRightU -> pr_nth_child 0; pr_string " >>> "; pr_nth_child 1

  | AdditiveExpression     -> pr_string "<additive-expression>"
  | AdditiveExpressionAdd  -> pr_nth_child 0; pr_string " + "; pr_nth_child 1
  | AdditiveExpressionSubt -> pr_nth_child 0; pr_string " - "; pr_nth_child 1

  | MultiplicativeExpression     -> pr_string "<multiplicative-expression>"
  | MultiplicativeExpressionMult -> pr_nth_child 0; pr_string " * "; pr_nth_child 1
  | MultiplicativeExpressionDiv  -> pr_nth_child 0; pr_string " / "; pr_nth_child 1
  | MultiplicativeExpressionMod  -> pr_nth_child 0; pr_string " % "; pr_nth_child 1

  | PmExpression      -> pr_string "<pm-expression>"
  | PmExpressionClass -> pr_nth_child 0; pr_string ".*"; pr_nth_child 1
  | PmExpressionPtr   -> pr_nth_child 0; pr_string "->*"; pr_nth_child 1

  | CastExpression -> begin
      let has_head =
        try
          L.is_type_macro_ivk (getlab children.(0))
        with _ -> false
      in
      if has_head then
        pr_seq()
      else begin
        pr_lparen();
        pr_nth_children 0;
        pr_nth_children 1;
        pr_rparen();
        pr_nth_children 2;
      end
  end

  | CompoundLiteralExpression -> pr_lparen(); pr_nth_child 0; pr_rparen(); pr_nth_child 1

  | UnaryExpression             -> pr_string "<unary-expression>"
  | UnaryExpressionIncr         -> pr_string "++"; pr_nth_child 0
  | UnaryExpressionDecr         -> pr_string "--"; pr_nth_child 0
  | UnaryExpressionInd          -> pr_string "*"; pr_nth_child 0
  | UnaryExpressionAddr         -> pr_string "&"; pr_nth_child 0
  | UnaryExpressionLabelAddr    -> pr_string "&&"; pr_nth_child 0
  | UnaryExpressionPlus         -> pr_string "+"; pr_nth_child 0
  | UnaryExpressionMinus        -> pr_string "-"; pr_nth_child 0
  | UnaryExpressionNeg i        -> pr_string i; pr_nth_child 0
  | UnaryExpressionCompl i      -> pr_string i; pr_nth_child 0
  | UnaryExpressionSizeof       -> pr_string "sizeof "; pr_nth_child 0
  | UnaryExpressionSizeofPack i -> pr_string (sprintf "sizeof ... (%s)" i)
  | UnaryExpressionAlignof      -> pr_string "alignof"; pr_lparen(); pr_nth_child 0; pr_rparen()

  | NoexceptExpression          -> pr_string "noexcept"; pr_lparen(); pr_nth_child 0; pr_rparen()

  | PostfixExpression           -> pr_string "<postfix-expression>"
  | PostfixExpressionSubscr     -> pr_nth_child 0; pr_lbracket(); pr_nth_child 1; pr_rbracket()
  | PostfixExpressionFunCall -> begin
      pb#open_hbox();
      pr_nth_child 0;
      pr_nth_children 1;
      pb#close_box()
  end
  | PostfixExpressionFunCallGuarded i       -> pr_nth_child 0; pr_id i; pr_lparen(); pr_nth_children 1; pr_rparen()
  | PostfixExpressionFunCallMacro i         -> pr_id i
  | PostfixExpressionExplicitTypeConv       -> pr_string "<explicit-type-conversion>"
  | PostfixExpressionExplicitTypeConvExpr   -> pr_nth_children 0; pr_lparen(); pr_nth_children 1; pr_rparen()
  | PostfixExpressionExplicitTypeConvBraced -> pr_seq()
  | PostfixExpressionDot -> begin
      pr_nth_child 0;
      pr_string ".";
      pr_nth_children ~tail:pad1 1;
      pr_nth_children 2
  end
  | PostfixExpressionArrow -> begin
      pr_nth_child 0;
      pr_string "->";
      pr_nth_children ~tail:pad1 1;
      pr_nth_children 2
  end
  | PostfixExpressionIncr       -> pr_nth_child 0; pr_string "++"
  | PostfixExpressionDecr       -> pr_nth_child 0; pr_string "--"
  | PostfixExpressionTypeid     -> pr_string "typeid"
  | PostfixExpressionTypeidExpr -> pr_string "typeid"; pr_lparen(); pr_nth_child 0; pr_rparen()
  | PostfixExpressionTypeidTy   -> pr_string "typeid"; pr_lparen(); pr_nth_child 0; pr_rparen()
  | PostfixExpressionDynamic_cast -> begin
      pr_string "dynamic_cast<"; pr_nth_child 0; pr_string ">";
      if L.is_ident (getlab children.(1)) then
        pr_nth_child 1
      else begin
        pr_lparen();
        pr_nth_child 1;
        pr_rparen()
      end
  end
  | PostfixExpressionStatic_cast -> begin
      pr_string "static_cast"; pr_lt(); pr_nth_child 0; pr_gt();
      pr_nth_child 1
  end
  | PostfixExpressionReinterpret_cast -> begin
      pr_string "reinterpret_cast"; pr_lt(); pr_nth_child 0; pr_gt();
      pr_nth_child 1
  end
  | PostfixExpressionConst_cast -> begin
      pr_string "const_cast"; pr_lt(); pr_nth_child 0; pr_gt();
      pr_nth_child 1
  end

  | SwiftArg i -> begin
      pr_id i; pr_colon();
      if nchildren > 0 then begin
        pad1();
        pr_nth_child 0
      end
  end
  | SwiftFunCall -> begin
      pb#open_hbox();
      pr_nth_child 0;
      pr_nth_children 1;
      pb#close_box()
  end

  | AssignmentExpression              -> pr_string "<assignment-expression>"
  | AssignmentExpressionOverloaded i  -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_children 1
  | AssignmentExpressionEq            -> pr_nth_child 0; pr_eq(); pr_nth_children 1
  | AssignmentExpressionPlus          -> pr_nth_child 0; pr_string " += "; pr_nth_children 1
  | AssignmentExpressionMinus         -> pr_nth_child 0; pr_string " -= "; pr_nth_children 1
  | AssignmentExpressionMult          -> pr_nth_child 0; pr_string " *= "; pr_nth_children 1
  | AssignmentExpressionDiv           -> pr_nth_child 0; pr_string " /= "; pr_nth_children 1
  | AssignmentExpressionMod           -> pr_nth_child 0; pr_string " %= "; pr_nth_children 1
  | AssignmentExpressionShiftLeft     -> pr_nth_child 0; pr_string " <<= "; pr_nth_children 1
  | AssignmentExpressionShiftRight    -> pr_nth_child 0; pr_string " >>= "; pr_nth_children 1
  | AssignmentExpressionAnd i
  | AssignmentExpressionXor i
  | AssignmentExpressionOr i          -> pr_nth_child 0; pad1(); pr_string i; pad1(); pr_nth_children 1

  | ThrowExpression                   -> pr_string "throw"; pr_nth_children ~head:pad1 0
  | ExpressionPair                    -> pr_seq ~sep:pr_comma ()
  | ConditionalExpression             -> pr_seq()
  | NewExpression -> begin
      let is_type_id =
        try
          L.is_type_id (getlab (nth_children 2).(0))
        with _ -> false
      in
      pr_nth_children 0; pr_string "new "; pr_nth_children 1;
      if is_type_id then pr_lparen();
      pr_nth_children 2;
      if is_type_id then pr_rparen();
      pr_nth_children 3
  end
  | RefNewExpression -> begin
      pr_string "ref ";
      pr_nth_children 0;
      pr_string "new ";
      pr_nth_children 1;
      pr_nth_children 2;
      pr_nth_children 3
  end
  | DeleteExpression                  -> pr_nth_children 0; pr_string "delete "; pr_nth_children 1
  | DeleteExpressionBracket           -> pr_nth_children 0; pr_string "delete[] "; pr_nth_children 1
  | YieldExpression                   -> pr_string "co_yield "; pr_nth_child 0
  | AwaitExpression                   -> pr_string "co_await "; pr_nth_child 0
  | BlockLiteralExpression            -> pr_string "^"; pr_seq()

  | ExpressionMacroInvocation i       -> pr_macro_invocation i
  | LogicalOrMacroInvocation i        -> pr_macro_invocation i
  | DefinedMacroExpression i          -> pr_string (sprintf "defined(%s)" i)
  | HasIncludeExpression s            -> pr_string (sprintf "__has_include(%s)" s)
  | HasAttributeExpression            -> pr_string "__has_cpp_attribute"; pr_seq ~sep:pr_none ()

(* Literal *)
  | Literal                       -> pr_string "<literal>"
  | IntegerLiteral v              -> pr_string v
  | CharacterLiteral v            -> pr_string v
  | FloatingLiteral v             -> pr_string v
  | StringLiteral v               -> pr_string v
  | StringMacro i                 -> pr_id i
  | BooleanLiteral v              -> pr_string v
  | Nullptr                       -> pr_string "nullptr"
  | ConcatenatedString            -> pr_seq()
  | UserDefinedCharacterLiteral v -> pr_string v
  | UserDefinedStringLiteral v    -> pr_string v
  | UserDefinedFloatingLiteral v  -> pr_string v
  | UserDefinedIntegerLiteral v   -> pr_string v
  | LiteralMacro i                -> pr_id i
  | LiteralMacroInvocation i      -> pr_macro_invocation i

(* UnqualifiedId *)
  | UnqualifiedId        -> pr_string "<unqualified-id>"
  | OperatorFunctionId   -> pr_string "operator"; pr_nth_child 0
  | ConversionFunctionId -> pr_string "operator "; pr_nth_child 0
  | LiteralOperatorId i  -> pr_string "operator "; pr_nth_children 0; pr_id i
  | Destructor           -> pr_string "~"; pr_nth_child 0
  | TemplateId           -> pr_string "<template-id>"
  | TemplateIdOp         -> pr_nth_child 0; pr_nth_children ~head:pr_lt ~tail:pr_gt 1
  | TemplateIdLit        -> pr_nth_child 0; pr_nth_children ~head:pr_lt ~tail:pr_gt 1

(* Operator *)
  | Operator      -> pr_string "<operator>"
  | New           -> pr_string "new"
  | Delete        -> pr_string "delete"
  | NewBracket    -> pr_string "new[]"
  | DeleteBracket -> pr_string "delete[]"
  | Parentheses   -> pr_string "()"
  | Brackets      -> pr_string "[]"
  | MinusGt       -> pr_string "->"
  | MinusGtStar   -> pr_string "->*"
  | Tilde i       -> pr_string i
  | Exclam i      -> pr_string i
  | Plus          -> pr_string "+"
  | Minus         -> pr_string "-"
  | Star          -> pr_string "*"
  | Slash         -> pr_string "/"
  | Perc          -> pr_string "%"
  | Hat i         -> pr_string i
  | Amp i         -> pr_string i
  | Bar i         -> pr_string i
  | Eq            -> pr_string "="
  | PlusEq        -> pr_string "+="
  | MinusEq       -> pr_string "-="
  | StarEq        -> pr_string "*="
  | SlashEq       -> pr_string "/="
  | PercEq        -> pr_string "%="
  | HatEq i       -> pr_string i
  | AmpEq i       -> pr_string i
  | BarEq i       -> pr_string i
  | EqEq          -> pr_string "=="
  | ExclamEq i    -> pr_string i
  | Lt            -> pr_string "<"
  | Gt            -> pr_string ">"
  | LtEq          -> pr_string "<="
  | GtEq          -> pr_string ">="
  | LtEqGt        -> pr_string "<=>"
  | AmpAmp i      -> pr_string i
  | BarBar i      -> pr_string i
  | LtLt          -> pr_string "<<"
  | GtGt          -> pr_string ">>"
  | LtLtEq        -> pr_string "<<="
  | GtGtEq        -> pr_string ">>="
  | PlusPlus      -> pr_string "++"
  | MinusMinus    -> pr_string "--"
  | Comma         -> pr_string ","
  | Semicolon     -> pr_string ";"
  | Colon         -> pr_string ":"
  | Co_await      -> pr_string "co_await"

  | DotStar       -> pr_string ".*"
  | Dot           -> pr_string "."

(* DefiningTypeSpecifier *)
  | DefiningTypeSpecifier -> pr_seq()
  | SimpleTypeSpecifier i -> begin
      let ca2 = nth_children 2 in
      if ca2 = [||] then begin
        pr_nth_children 0; pr_string (Ast.decode_ident i)
      end
      else
        pr_seq ~sep:pr_none ()
  end
  | ElaboratedTypeSpecifier         -> pr_string "<elaborated-type-specifier>"
  | ElaboratedTypeSpecifierClass i  -> begin
      pr_string "class "; pr_nth_children ~tail:pad1 0; pr_nth_children 1;
      if nth_children 2 = [||] then
        pr_id (Ast.decode_ident i)
      else
        pr_nth_children 2
  end
  | ElaboratedTypeSpecifierStruct i -> pr_string "struct "; pr_id (Ast.decode_ident i)
  | ElaboratedTypeSpecifierUnion i  -> pr_string "union "; pr_id (Ast.decode_ident i)
  | ElaboratedTypeSpecifierEnum i   -> pr_string "enum "; pr_id (Ast.decode_ident i)
  | TypenameSpecifier _             -> pr_string "typename "; pr_seq ~sep:pr_none ()
  | CvQualifier                     -> pr_string "<cv-qualifier>"
  | TypeMacro i                     -> pr_id i
  | Const                           -> pr_string "const"
  | Volatile                        -> pr_string "volatile"
  | Restrict i                      -> pr_string i

  | MsAsmBlock(a, s)                -> pr_string (sprintf "%s {%s}" a s)
  | MsCdecl i                       -> pr_string i
  | MsStdcall i                     -> pr_string i
  | MsPragma i                      -> pr_string i
  | MsWarningSpecifier i            -> pr_string i

  | CallingConvention i             -> pr_string i
  | GnuAsmBlock(a, s)               -> pr_string (sprintf "%s %s" a s)
  | GnuAttribute i                  -> pr_string i; pr_seq()
  | GnuStatementExpression          -> pr_lparen(); pr_nth_child 0; pr_rparen()
  | AsmOperand
    ->
      pr_lbracket(); pr_nth_child 0; pr_rbracket(); pr_nth_child 1;
      pr_lparen(); pr_nth_child 2; pr_rparen()

  | ClassSpecifier -> begin
      let mema = nth_children 1 in
      if mema = [||] then begin
        pr_nth_child 0; pad1(); pr_string "{}"
      end
      else begin
        pb#open_vbox 0;
        pr_nth_child 0;
        pad1();
        pb#pr_block_head();
        pb#pr_a pr_cut pr_node_ mema;
        pb#pr_block_end();
        pb#close_box()
      end
  end
  | EnumSpecifier -> begin
      let mema = nth_children 1 in
      if mema = [||] then begin
        pr_nth_child 0; pad1(); pr_string "{}"
      end
      else begin
        pb#open_vbox 0;
        pr_nth_child 0;
        pad1();
        pb#pr_block_head();
        pb#pr_a pr_cut pr_node_ (nth_children 1);
        pb#pr_block_end();
        pb#close_box()
      end
  end

(* BasicType *)
  | BasicType -> pr_string "<basic-type>"
  | Char      -> pr_string "char"
  | Char8_t   -> pr_string "char8_t"
  | Char16_t  -> pr_string "char16_t"
  | Char32_t  -> pr_string "char32_t"
  | Wchar_t   -> pr_string "wchar_t"
  | Bool      -> pr_string "bool"
  | Short     -> pr_string "short"
  | Int       -> pr_string "int"
  | Long      -> pr_string "long"
  | Signed    -> pr_string "signed"
  | Unsigned  -> pr_string "unsigned"
  | Float     -> pr_string "float"
  | Double    -> pr_string "double"
  | Void      -> pr_string "void"
  | UnsignedInt   -> pr_string "unsigned int"
  | UnsignedLong  -> pr_string "unsigned long"

(* AccessSpecifier *)
  | AccessSpecifier   -> pr_string "<access-specifier>"
  | Private           -> pr_string "private"; pr_nth_children ~head:pad1 0
  | Protected         -> pr_string "protected"; pr_nth_children ~head:pad1 0
  | Public            -> pr_string "public"; pr_nth_children ~head:pad1 0
  | AccessSpecMacro i -> pr_id i; pr_nth_children ~head:pad1 0

(* AttributeSpecifier *)
  | AttributeSpecifier                  -> pr_string "<attribute-specifier>"
  | StandardAttributeSpecifier          -> pr_string "[["; pr_seq(); pr_string "]]"
  | ContractAttributeSpecifier          -> pr_string "<contract-attribute-specifier>"
  | ContractAttributeSpecifierExpects -> begin
      pr_string "[[expects "; pr_nth_children 0; pr_colon(); pr_nth_children 1; pr_string "]]"
  end
  | ContractAttributeSpecifierEnsures i -> begin
      pr_string "[[ensures "; pr_nth_children 0;
      if i <> "" then begin
        pad1();
        pr_id i;
      end;
      pr_colon(); pr_nth_children 1; pr_string "]]"
  end
  | ContractAttributeSpecifierAssert -> begin
      pr_string "[[assert "; pr_nth_children 0; pr_colon(); pr_nth_children 1; pr_string "]]"
  end
  | AlignmentAttributeSpecifier b -> begin
      pr_string "alignas";
      pr_lparen();
      pr_nth_child 0;
      if b then pr_ellipsis();
      pr_rparen()
  end
  | AttributeMacro i -> pr_id i
  | MsAttributeSpecifier -> pr_string "["; pr_seq(); pr_string "]"

(* RefQualifier *)
  | RefQualifier       -> pr_string "<ref-qualifier>"
  | RefQualifierAmp    -> pr_string "&"
  | RefQualifierAmpAmp -> pr_string "&&"

(* PlaceholderTypeSpecifier *)
  | PlaceholderTypeSpecifier         -> pr_string "<placeholder-type-specifier>"
  | PlaceholderTypeSpecifierAuto     -> pr_string "auto"
  | PlaceholderTypeSpecifierDecltype -> pr_string "decltype(auto)"

(* PtrOperator *)
  | PtrOperator        -> pr_string "<ptr-operator>"
  | PtrOperatorStar    -> pr_nth_children 0; pr_string "*"; pr_nth_children ~head:pad1 1; pr_nth_children ~head:pad1 2
  | PtrOperatorAmp     -> pr_string "&"; pr_seq()
  | PtrOperatorAmpAmp  -> pr_string "&&"; pr_seq()
  | PtrOperatorHat     -> pr_string "^"
  | PtrOperatorMacro i -> pr_id i

(* Declarator *)
  | Declarator             -> pr_string "<declarator>"
  | DeclaratorFunc         -> pr_seq()
  | PtrDeclarator          -> pr_string "<ptr-declarator>"
  | PtrDeclaratorPtr       -> pr_seq()
  | NoptrDeclarator        -> pr_seq()
  | NoptrDeclaratorId      -> pr_seq()
  | NoptrDeclaratorParen   -> pr_lparen(); pr_nth_child 0; pr_rparen()
  | NoptrDeclaratorFunc    -> pr_nth_children 0; pr_nth_children 1
  | NoptrDeclaratorOldFunc -> begin
      pr_nth_child 0;
      pr_lparen();
      pr_nth_children 1;
      pr_rparen();
      pr_nth_children ~head:pr_space 2
  end
  | NoptrDeclaratorArray -> begin
      pr_nth_child 0;
      pr_lbracket();
      pr_nth_children 1;
      pr_nth_children 2;
      pr_rbracket();
      pr_nth_children ~head:pad1 3;
  end
  | DtorMacro i -> pr_id i

(* NoexceptSpecifier *)
  | NoexceptSpecifier         -> pr_string "noexcept"; pr_nth_children ~head:pr_lparen ~tail:pr_rparen 0
  | NoexceptSpecifierThrow    -> pr_string "throw"; pr_lparen(); pr_seq ~sep:pr_comma (); pr_rparen()
  | NoexceptSpecifierThrowAny -> pr_string "throw(...)"
  | NoexceptSpecifierMacro i  -> pr_id i

(* VirtSpecifier *)
  | VirtSpecifier                  -> pr_string "<virt-specifier>"
  | VirtSpecifierFinal             -> pr_string "final"
  | VirtSpecifierOverride          -> pr_string "override"
  | VirtSpecifierMacro i           -> pr_id i
  | VirtSpecifierMacroInvocation i -> pr_macro_invocation i

(* StorageClassSpecifier *)
  | StorageClassSpecifier             -> pr_string "<storage-class-specifier>"
  | StorageClassSpecifierStatic       -> pr_string "static"
  | StorageClassSpecifierThread_local -> pr_string "thread_local"
  | StorageClassSpecifierExtern       -> pr_string "extern"
  | StorageClassSpecifierMutable      -> pr_string "mutable"
  | StorageClassSpecifierRegister     -> pr_string "register"
  | StorageClassSpecifierVaxGlobaldef -> pr_string "globaldef"

(* FunctionSpecifier *)
  | FunctionSpecifier        -> pr_string "<function-specifier>"
  | FunctionSpecifierVirtual -> pr_string "virtual"
  | ExplicitSpecifier        -> pr_string "explicit"

(* ClassHead *)
  | ClassHead                  -> pr_string "<class-head>"
  | ClassHeadClass             -> pr_string "class "; pr_seq()
  | ClassHeadStruct            -> pr_string "struct "; pr_seq()
  | ClassHeadUnion             -> pr_string "union "; pr_seq()
  | ClassHeadMsRefClass        -> pr_string "ref class"; pr_seq()
  | ClassHeadMacro i           -> pr_id i
  | ClassHeadMacroInvocation i -> pr_macro_invocation i

(* EnumHead *)
  | EnumHead            -> pr_string "<enum-head>"
  | EnumHeadEnum        -> pr_string "enum "; pr_seq()
  | EnumHeadEnumClass   -> pr_string "enum class "; pr_seq()
  | EnumHeadEnumStruct  -> pr_string "enum struct "; pr_seq()
  | EnumHeadEnumMacro i -> pr_id i

(* TypeParameterKey *)
  | TypeParameterKey         -> pr_string "<type-parameter-key>"
  | TypeParameterKeyClass    -> pr_string "class"
  | TypeParameterKeyTypename -> pr_string "typename"

(* FunctionBody *)
  | FunctionBody _                -> pb#pr_a pad1 pr_node_ children
  | FunctionBodyDefault           -> pr_string "= default;"
  | FunctionBodyDelete            -> pr_string "= delete;"
  | FunctionTryBlock _            -> pr_string "try "; pr_nth_children ~tail:pad1 0; pr_nth_children 1; pr_nth_children 2
  | FunctionBodyMacro i           -> pr_id i
  | FunctionBodyMacroInvocation i -> pr_macro_invocation i

(* DeclSpecifier *)
  | DeclSpecifier                  -> pr_string "<decl-specifier>"
  | DeclSpecifierInline            -> pr_string "inline"
  | DeclSpecifierConstexpr         -> pr_string "constexpr"
  | DeclSpecifierConsteval         -> pr_string "consteval"
  | DeclSpecifierConstinit         -> pr_string "constinit"
  | DeclSpecifierTypedef           -> pr_string "typedef"
  | DeclSpecifierFriend            -> pr_string "friend"
  | DeclSpecifierMacro i           -> pr_id i
  | DeclSpecifierMacroInvocation i -> pr_macro_invocation i

(* Requirement *)
  | Requirement           -> pr_string "<requirement>"
  | SimpleRequirement     -> pr_nth_child 0; _pr_semicolon()
  | TypeRequirement       -> pr_string "typename "; pr_seq(); _pr_semicolon()
  | CompoundRequirement   -> pr_lbrace(); pr_nth_child 0; pr_rbrace(); pr_nth_children 1; pr_nth_children ~head:pad1 2
  | ReturnTypeRequirement -> pr_string "->"; pr_nth_child 0
  | NestedRequirement     -> pr_string "requires "; pr_nth_child 0; _pr_semicolon()

(* AbstractDeclarator *)
  | AbstractDeclarator           -> pr_string "<abstract-declarator>"
  | AbstractDeclaratorFunc       -> pr_seq()
  | PtrAbstractDeclarator        -> pr_string "<ptr-abstract-declarator>"
  | PtrAbstractDeclaratorPtr     -> pr_seq()
  | NoptrAbstractDeclarator      -> pr_string "<noptr-abstract-declarator>"
  | NoptrAbstractDeclaratorFunc  -> pr_seq()
  | NoptrAbstractDeclaratorArray -> pr_nth_children 0; pr_lbracket(); pr_nth_children 1; pr_rbracket(); pr_nth_children 2
  | NoptrAbstractDeclaratorParen -> pr_lparen(); pr_nth_child 0; pr_rparen()

(* NoptrAbstractPackDeclarator *)
  | NoptrAbstractPackDeclaratorFunc  -> pr_seq()
  | NoptrAbstractPackDeclaratorArray ->
      pr_nth_child 0; pr_lbracket(); pr_nth_children 1; pr_rbracket(); pr_nth_children 2

(* SimpleCapture *)
  | SimpleCapture i       -> pr_string i
  | SimpleCaptureAmp i    -> pr_string ("&"^i)
  | SimpleCaptureThis     -> pr_string "this"
  | SimpleCaptureStarThis -> pr_string "*this"

(* InitCapture *)
  | InitCapture i    -> pr_string i; pr_nth_child 0
  | InitCaptureAmp i -> pr_amp(); pr_id i; pr_nth_child 0

(* LambdaCapture *)
  | LambdaCapture -> begin
      if nth_children 0 <> [||] && nth_children 1 <> [||] then begin
        pr_nth_children 0; pr_comma(); pr_nth_children 1
      end
      else
        pr_seq()
  end
  | LambdaCaptureDefaultEq         -> pr_string "="
  | LambdaCaptureDefaultAmp        -> pr_string "&"
  | LambdaCaptureMacroInvocation i -> pr_macro_invocation i

(* MemberDeclarator *)
  | MemberDeclarator           -> pr_string "<member-declarator>"
  | MemberDeclaratorDecl       -> pb#pr_a pad1 pr_node_ children
  | MemberDeclaratorBitField i -> begin
      pr_string i;
      pr_nth_children 0;
      pr_colon();
      pr_nth_children 1;
      pr_nth_children 2
  end

(* Label *)
  | Label i                -> pr_seq(); pr_id i; pr_colon()
  | CaseLabel              -> pr_nth_children 0; pr_string "case "; pr_nth_children 1; pr_colon()
  | RangedCaseLabel -> begin
      pr_nth_children 0; pr_string "case "; pr_nth_children 1; pr_ellipsis(); pr_nth_children 2; pr_colon()
  end
  | DefaultLabel           -> pr_seq(); pr_string "default:"
  | LabelMacroInvocation i -> pr_macro_invocation i; pr_colon()

(* ContractLevel *)
  | ContractLevel        -> pr_string "<contract-level>"
  | ContractLevelDefault -> pr_string "default"
  | ContractLevelAudit   -> pr_string "audit"
  | ContractLevelAxiom   -> pr_string "axiom"

(* Member *)
  | MemberSpecification   -> pr_seq ~sep:pr_cut ()
  | MemberDeclarationDecl -> pb#open_hbox(); pr_seq(); pb#close_box()

  | MsProperty i ->
      pr_string "property "; pr_nth_child 0; pad1(); pr_id i;
      if nchildren > 1 then begin
        pb#pr_block_head();
        pr_nth_child 1;
        pb#pr_block_end()
      end

(* *)
  | Explicit                         -> pr_string "explicit"
  | Virtual                          -> pr_string "virtual"
  | Template                         -> pr_string "template"
  | Noexcept                         -> pr_string "noexcept"
  | Extern                           -> pr_string "extern"
  | Inline                           -> pr_string "inline"
  | Default                          -> pr_string "default"
  | Constexpr                        -> pr_string "constexpr"
  | Typename                         -> pr_string "typename"
  | ColonColon                       -> pr_colon_colon()
  | Ellipsis                         -> pr_ellipsis()

  | PureSpecifier                    -> pr_string "= 0"
  | BaseSpecifier                    -> pr_seq()
  | BaseClause                       -> pr_seq()
  | BaseMacro i                      -> pr_id i
  | BaseSpecMacro i                  -> pr_id i
  | BaseSpecMacroInvocation i        -> pr_macro_invocation i
  | SuffixMacro i                    -> pr_id i
  | SuffixMacroInvocation i          -> pr_macro_invocation i
  | DslMacroArgument                 -> pr_lparen(); pr_seq(); pr_rparen()
  | ClassVirtSpecifierFinal          -> pr_string "final"
  | ClassVirtSpecifierMsSealed       -> pr_string "sealed"
  | ClassName i when nchildren = 0   -> pr_id (Ast.decode_ident i)
  | ClassName _                      -> pr_nth_child 0
  | ClassHeadName _                  -> pr_seq ~sep:pr_none ()
  | LambdaIntroducerMacro i          -> pr_id i
  | MacroArgument                    -> pr_seq()
  | NoptrNewDeclarator -> begin
      pr_nth_children 0; pr_lbracket(); pr_nth_children 1; pr_rbracket(); pr_nth_children 2
  end
  | NewInitializer -> begin
      let has_rparen =
        try
          not (L.is_pp_if_section (getlab (nth_children 1).(0)))
        with _ -> true
      in
      pr_lparen(); pr_nth_children 0;
      if has_rparen then pr_rparen()
  end
  | NewInitializerMacro i            -> pr_id i
  | ArgumentsMacro i                 -> pr_id i
  | ArgumentsMacroInvocation i       -> pr_macro_invocation i
  | NewDeclaratorPtr                 -> pr_seq()
  | NewDeclarator                    -> pr_string "<new-declarator>"
  | NewTypeId                        -> pr_seq()
  | NewPlacement                     -> pr_lparen(); pr_seq(); pr_rparen()
  | LambdaDeclarator -> begin
      pr_lparen(); pr_nth_child 0; pr_rparen();
      pr_nth_children 1;
      pr_nth_children 2;
      pr_nth_children 3;
      pr_nth_children 4;
      pr_nth_children 5
  end
  | ParenthesizedInitList            -> pr_lparen(); pr_seq(); pr_rparen()
  | LambdaIntroducer                 -> pr_lbracket(); pr_seq(); pr_rbracket()
  | AbstractPackDeclarator           -> pr_seq()
  | AbstractPack                     -> pr_ellipsis()
  | RequirementBody                  -> pr_lbrace(); pr_seq(); pr_rbrace()
  | RequirementParameterList         -> pr_lparen(); pr_nth_child 0; pr_rparen()
  | MemInitializer -> begin
      pr_nth_child 0;
      pr_nth_children 1
  end
  | MemInitMacroInvocation i         -> pr_macro_invocation i
  | QualifiedTypeName                -> pr_seq ~sep:pr_none ()
  | InitDeclarator _                 -> pb#pr_a pad1 pr_node_ children
  | ConceptDefinition n              -> pr_string "concept "; pr_id n; pr_eq(); pr_nth_child 0; _pr_semicolon()
  | CtorInitializer                  -> pb#open_hvbox 0; pr_seq ~sep:pr_space (); pb#close_box()
  | ConstraintLogicalOrExpression _  -> pr_nth_child 0; pr_string " || "; pr_nth_child 1
  | ConstraintLogicalAndExpression _ -> pr_nth_child 0; pr_string " && "; pr_nth_child 1
  | RequiresClause                   -> pr_string "requires "; pr_nth_child 0
  | TypeParameter i -> begin
      pr_nth_children ~tail:pad1 0;
      pr_nth_children ~tail:pad1 1;
      pr_nth_children ~tail:pad1 2;
      pr_id i;
      pr_nth_children ~head:pr_eq 3;
  end
  | TemplateHead -> begin
      pb#open_hvbox 0;
      pr_string "template"; pr_lt(); pb#pr_a pr_space pr_node_ (nth_children 0); pr_gt();
      pr_nth_children ~head:pad1 1;
      pb#close_box();
  end
  | EnclosingNamespaceSpecifier i    -> pr_nth_children ~tail:pr_colon_colon 0; pr_nth_children 1; pr_id i
  | Enumerator i                     -> pr_string i; pr_seq()
  | EnumeratorDefinition             -> pr_nth_child 0; pr_eq(); pr_nth_children ~tail:pad1 1; pr_nth_children 2
  | EnumeratorDefinitionMacro i      -> pr_id i
  | TypeMacroInvocation i            -> pr_macro_invocation i
  | Condition                        -> pr_seq()
  | ParameterDeclaration _           -> pr_seq()
  | ParameterDeclarationClause _ -> begin
      pb#open_hbox();
      pr_seq ~sep:pr_space ();
      pb#close_box()
  end
  | ParametersAndQualifiers -> begin
      pb#open_hbox();
      pr_lparen();
      pr_nth_children 0;
      pr_rparen();
      pr_nth_children ~head:pad1 1;
      pr_nth_children ~head:pad1 2;
      pr_nth_children ~head:pad1 3;
      pr_nth_children ~head:pad1 4;
      pb#close_box()
  end
  | ParametersAndQualifiersList -> pr_lparen(); pr_seq ~sep:pr_comma (); pr_rparen()
  | ParamDeclMacro i                  -> pr_id i
  | ParamDeclMacroInvocation i        -> pr_macro_invocation i
  | ParametersMacro i                 -> pr_id i
  | ParametersMacroInvocation i       -> pr_macro_invocation i
  | Handler                           -> pr_string "catch "; pr_lparen(); pr_nth_child 0; pr_rparen(); pr_nth_children 1
  | ExceptionDeclaration              -> pr_seq()
  | ExpressionList                    -> pr_lparen(); pr_seq(); pr_rparen(); pr_nth_children 1
  | EqualInitializer                  -> pr_string "= "; pr_nth_child 0
  | DesignatedInitializerClause -> begin
      if L.is_desig_old (getlab children.(0)) then begin
        pr_nth_child 0; pr_colon(); pr_nth_child 1
      end
      else begin
        pr_seq()
      end
  end
  | DesignatorField i                 -> pr_string ("."^i)
  | DesignatorIndex                   -> pr_lbracket(); pr_seq(); pr_rbracket()
  | DesignatorRange                   -> pr_lbracket(); pr_seq ~sep:pr_ellipsis (); pr_rbracket()
  | TrailingReturnType                -> pr_string " -> "; pr_nth_child 0
  | BracedInitList                    -> pr_lbrace(); pr_seq(); pr_rbrace()
  | ForRangeDeclaration -> begin
      pr_nth_children 0;
      pr_nth_children 1;
      pr_nth_children 2;
      pr_nth_children 3;
      pr_nth_children ~head:pr_lbracket ~tail:pr_rbracket 4
  end
  | DefiningTypeId                    -> pr_seq()
  | EnumHeadName i                    -> pr_nth_children 0; pr_id (Ast.decode_ident i)
  | EnumBase                          -> pr_colon(); pr_seq()
  | QualifiedId                       -> pr_seq ~sep:pr_none ()
  | QualifiedNamespaceSpecifier i     -> if nchildren > 0 then pr_nth_child 0; pr_id i
  | TypeName i                        -> pr_id i
  | ConversionDeclarator              -> pr_seq()
  | ConversionTypeId                  -> pr_seq()
  | UsingDeclarator                   -> pr_seq()
  | UsingEnumDeclarator               -> pr_seq()
  | TypeConstraint i -> begin
      pr_nth_children 0; pr_id (Ast.decode_ident i); pr_nth_children ~head:pr_lt ~tail:pr_gt 1
  end
  | TypeId                            -> pr_seq()
  | DecltypeSpecifier                 -> pr_string "decltype"; pr_lparen(); pr_nth_child 0; pr_rparen()
  | SimpleTemplateId n -> begin
      pb#open_hvbox 0;
      pr_string n; pr_lt(); pr_seq ~sep:pr_space (); pr_gt();
      pb#close_box()
  end
  | SimpleTemplateIdM -> begin
      pb#open_hvbox 0;
      pr_nth_child 0; pr_lt(); pr_nth_children 1; pr_gt();
      pb#close_box()
  end
  | TemplateArguments -> pr_lt(); pr_seq(); pr_gt();
  | Identifier i                      -> pr_id i
  | IdentifierMacroInvocation i       -> pr_macro_invocation i
  | PpConcatenatedIdentifier          -> pr_nth_child 0; pr_string "##"; pr_nth_child 1
  | NestedNameSpecifier               -> pr_string "<nested-name-specifier>"
  | NestedNameSpecifierHead           -> pr_colon_colon()
  | NestedNameSpecifierIdent _        -> pr_nth_children 0; pr_nth_children 1; pr_colon_colon()
  | NestedNameSpecifierTempl _        -> pr_nth_children 0; pr_nth_children 1; pr_colon_colon()
  | NestedNameSpecifierDeclty         -> pr_nth_child 0; pr_colon_colon()
  | PackExpansion                     -> pr_nth_child 0
  | AttributeUsingPrefix              -> pr_string "using "; pr_nth_child 0; pr_colon()
  | Attribute                         -> pr_seq()
  | AttributeToken i                  -> pr_id i
  | AttributeScopedToken i            -> pr_nth_child 0; pr_colon_colon(); pr_string i
  | AttributeNamespace i              -> pr_id i
  | AttributeArgumentClause           -> pr_lparen(); pr_seq(); pr_rparen()
  | AttributeArgumentClauseMacro i    -> pr_id i
  | BalancedToken                     -> pr_string "<balanced-token>"
  | BalancedTokenParen                -> pr_lparen(); pr_seq(); pr_rparen()
  | BalancedTokenBracket              -> pr_lbracket(); pr_seq(); pr_rbracket()
  | BalancedTokenBrace                -> pr_lbrace(); pr_seq(); pr_rbrace()
  | BalancedTokenSingle s             -> pr_string s
  | TokenSeq s                        -> pr_string s
  | ObjectLikeMacro                   -> pad1(); pr_seq()
  | FunctionLikeMacro mk -> begin
      pr_lparen(); pr_string (L.macro_kind_to_rep mk); pr_rparen(); pad1();
      pr_seq();
  end
  | OperatorMacro i                   -> pr_id i
  | OperatorMacroInvocation i         -> pr_macro_invocation i
  | DefiningTypeSpecifierSeq          -> pr_string "<defining-type-specifier-seq>"
  | DeclSpecifierSeq                  -> pr_string "<decl-specifier-seq>"
  | TypeSpecifierSeq                  -> pr_seq()
  | FunctionHead _ -> begin
      let has_rparen =
        try
          L.is_pp_if_section_broken (getlab (nth_children 2).(0))
        with _ -> false
      in
      pr_seq();
      if has_rparen then pr_rparen()
  end
  | FunctionHeadMacro i               -> pr_id i
  | AccessSpecAnnot i                 -> pr_id i
  | EnumeratorMacroInvocation i       -> pr_macro_invocation i
  | CvMacro i                         -> pr_id i
  | CvMacroInvocation i               -> pr_macro_invocation i
  | OpeningBrace                      -> pr_lbrace()
  | ClosingBrace                      -> pr_rbrace()
  | OpeningBracket                    -> pr_lbracket()
  | ClosingBracket                    -> pr_rbracket()
  | DummyBody                         -> ()
  | DummyDecl                         -> ()
  | DummyStmt                         -> ()
  | DummyExpr                         -> ()
  | DummyOp                           -> ()
  | DummyDtor                         -> ()
  | GnuAsmBlockFragmented a           -> pr_string a; pad1(); pr_seq()
  | GnuAsmFragment s                  -> pr_string s
  | DesignatorFieldOld i              -> pr_string (i^":")
  | DoxygenLine s                     -> pr_string s
  | AttributeMacroInvocation i        -> pr_macro_invocation i
  | CudaExecutionConfiguration        -> pr_string "<<<"; pr_seq(); pr_string ">>>";
  | CudaKernelCall -> begin
      pr_nth_child 0; pad1(); pr_nth_children 1; pr_lparen(); pr_nth_children 2; pr_rparen()
  end
  | NamespaceHead i                   -> pr_id i
  | NamedNamespaceDefinitionHead i -> begin
      pr_nth_children 0;
      if try not (L.is_namespace_head (getlab (nth_children 0).(0))) with _ -> true then
        pr_string "namespace ";
      pr_nth_children 1;
      if nth_children 2 <> [||] then
        pr_nth_children 2
      else
        pr_id i
  end
  | BlockHeadMacro i                  -> pr_id i
  | BlockEndMacro i                   -> pr_id i
  | PtrMacro i                        -> pr_id i
  | InitializerClause                 -> pr_seq()
  | TemplParamMacroInvocation i       -> pr_macro_invocation i
  | Try                               -> pr_string "try"
  | DeclStmtBlock                     -> pr_seq()
  | AsmShader s                       -> pr_string s
  | AsmName i                         -> pr_string (sprintf "%%[%s]" i)
  | AsmDirective i                    -> pr_string ("."^i)
  | VaArgs s                          -> pr_string s
  | ClassBody -> begin
      pb#pr_block_head(); pb#pr_a pr_cut pr_node_ (nth_children 1); pb#pr_block_end()
  end
  | ClassBodyHeadMacro i              -> pr_id i
  | ClassBodyEndMacro i               -> pr_id i
  | ClassBodyHeadMacroInvocation i    -> pr_macro_invocation i
  | ClassBodyEndMacroInvocation i     -> pr_macro_invocation i
  | InitHeadMacroInvocation i         -> pr_macro_invocation i
  | InitEndMacroInvocation i          -> pr_macro_invocation i
  | LiteralMacroArgument s            -> pr_string s
  | At                                -> pr_string "@"
  | Lparen                            -> pr_lparen()
  | Rparen                            -> pr_rparen()
  | Asm                               -> pr_string "asm"; pr_lparen(); pr_seq(); pr_rparen()
  | HugeArray(_, c)                   -> pr_string c

(* Objective C *)
  | ObjcThrow                                -> pr_string "@throw"
  | ObjcSynchronized                         -> pr_string "@synchronized"
  | ObjcClassDeclarationList                 -> pr_string "@class"
  | ObjcProtocolDeclarationList              -> pr_string "@protocol"
  | ObjcProtocolDeclaration i                -> pr_string ("@protocol "^i)
  | ObjcClassInterface i                     -> pr_string ("@interface "^i)
  | ObjcCategoryInterface(i, c)              -> pr_string (sprintf "@interface %s (%s)" i c)
  | ObjcSuperclass i                         -> pr_string (": "^i)
  | ObjcProtocolReferenceList                -> pr_string "<objc-protocol-reference-list>"
  | ObjcInstanceVariables                    -> pr_string "<objc-instance-variables>"
  | ObjcInstanceVariableDeclaration          -> pr_string "<objc-instance-variable-declaration>"
  | ObjcInterfaceDeclaration                 -> pr_string "<objc-interface-declaration>"
  | ObjcPrivate                              -> pr_string "@private"
  | ObjcPublic                               -> pr_string "@public"
  | ObjcPackage                              -> pr_string "@package"
  | ObjcProtected                            -> pr_string "@protected"
  | ObjcStructDeclaration                    -> pr_string "<objc-struct-declaration>"
  | ObjcStructDeclarator                     -> pr_string "<objc-struct-declarator>"
  | ObjcPropertyDeclaration                  -> pr_string "<objc-property-declaration>"
  | ObjcPropertyAttributesDeclaration        -> pr_string "<objc-property-attributes-declaration>"
  | ObjcClassMethodDeclaration               -> pr_string "<objc-class-method-declaration>"
  | ObjcInstanceMethodDeclaration            -> pr_string "<objc-instance-method-declaration>"
  | ObjcMethodMacroInvocation i              -> pr_macro_invocation i
  | ObjcMethodType                           -> pr_string "<objc-method-type"
  | ObjcMethodSelector                       -> pr_string "<objc-method-selector>"
  | ObjcMethodSelectorPack                   -> pr_string "<objc-method-selector-pack>"
  | ObjcSelector i                           -> pr_string i
  | ObjcSelectorMacro i                      -> pr_string i
  | ObjcKeywordSelector                      -> pr_string "<objc-keyword-selector>"
  | ObjcKeywordDeclarator i                  -> pr_string i
  | ObjcSpecifierQualifier i                 -> pr_string i
  | ObjcProtocolName i                       -> pr_string i
  | ObjcClassName i                          -> pr_string i
  | ObjcPropertyAttribute i                  -> pr_string i
  | ObjcMessageExpression                    -> pr_string "<objc-message-expression>"
  | ObjcMessageSelector                      -> pr_string "<objc-message-selector>"
  | ObjcKeywordArgument i                    -> pr_string i
  | ObjcProtocolInterfaceDeclarationOptional -> pr_string "@optional"
  | ObjcProtocolInterfaceDeclarationRequired -> pr_string "@required"
  | ObjcAutoreleasepool                      -> pr_string "@autoreleasepool"
  | ObjcAvailable                            -> pr_string "@available"
  | ObjcSelectorExpression i                 -> pr_string ("@selector "^i)
  | ObjcEncodeExpression                     -> pr_string "@encode"
  | ObjcTryBlock                             -> pr_string "<try-block>"
  | ObjcTry                                  -> pr_string "@try"
  | ObjcCatchClause                          -> pr_string "@catch"
  | ObjcFinally                              -> pr_string "@finally"
  | ObjcKeywordName ""                       -> pr_colon()
  | ObjcKeywordName i                        -> pr_string i; pr_colon()
  | ObjcProtocolReferenceListMacro i         -> pr_string i
  | ObjcProtocolExpression                   -> pr_string "<objc-protocol-expression>"
  | ObjcLiteral    -> pr_string "@"
  | ObjcDictionary -> pr_string "@{}"
  | ObjcArray      -> pr_string "@[]"
  | ObjcKeyValue   -> pr_string "<objc-key-value>"
  | ObjcClass      -> pr_string "@class"
  end;

  let suffix = node#data#get_suffix in
  if suffix <> "" then
    pr_string suffix



let unparse ?(no_boxing=false) ?(no_header=false) ?(fail_on_error=true) t =
  let prev_boxing_flag = pb#boxing_flag in
  if no_boxing && prev_boxing_flag then begin
    Format.open_hbox();
    pb#disable_boxing()
  end;

  pb#open_vbox 0;
  if not no_header then begin
    pr_string "// generated by Diff/AST C/C++ Unparser"; pr_cut();
  end;
  if not fail_on_error && no_header then begin
    pr_string (Printf.sprintf "// error_symbol=\"%s\"" error_symbol); pr_cut();
  end;
  pr_node ~fail_on_error t;
  pb#close_box();
  pr_cut();
  pr_flush();

  if no_boxing && prev_boxing_flag then begin
    pb#enable_boxing();
    Format.close_box()
  end
