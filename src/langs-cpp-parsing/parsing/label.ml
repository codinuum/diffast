(*
   Copyright 2012-2023 Codinuum Software Lab <https://codinuum.com>
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

(* cpp/label.ml *)

module XML = Diffast_misc.XML

open Common

let lang_prefix = "cpp"

let xmlenc = XML.encode_string

let np () n = if n = "" then "" else "("^n^")"

type function_like_macro_spec = {
    fm_params : string list;
    fm_va : string;
    mutable fm_param_occur_count : int list;
  }

type macro_kind =
  | ObjectLike
  | FunctionLike of function_like_macro_spec
  | MK_DUMMY

let make_func_like pl va =
  FunctionLike
    { fm_params=pl;
      fm_va=va;
      fm_param_occur_count=[];
    }

let macro_kind_to_string = function
  | ObjectLike -> "OBJ"
  | FunctionLike {fm_params=sl;fm_va=s;fm_param_occur_count=cl;} ->
      sprintf "FUNC(%s%s; occur:%s)"
        (String.concat "," sl)
        (if s = "" then "" else sprintf ",%s..." s)
        (String.concat "," (List.map string_of_int cl))
  | MK_DUMMY -> "MK_DUMMY"

let macro_kind_to_rep = function
  | ObjectLike -> ""
  | FunctionLike {fm_params=sl;fm_va=s;_} ->
      (String.concat ", " sl)^(if s = "" then "" else "...")
  | MK_DUMMY -> "MK_DUMMY"

let macro_kind_to_attrs = function
  | ObjectLike -> []
  | FunctionLike {fm_params=sl;fm_va=s;fm_param_occur_count=(*cl*)_} ->
      ["params",(String.concat "," sl);"va_args",s;
       (*"param_occurrences",(String.concat "," (List.map string_of_int cl))*)]
  | MK_DUMMY -> []

type t =
  | DUMMY
  | EMPTY
  | AMBIGUOUS_CONSTRUCT
  | PARTIAL_CONSTRUCT
  | DECLS
  | MEM_DECLS
  | EXPRS
  | STMTS
  | INITS
  | LABELS
  | SPECS
  | ETORS
  | OBJC_DECLS
  | TEMPL_PARAMS
  | TEMPL_ARGS
  | DELIM_MACRO of ident
  | DELIM_MACRO_ of ident
  | Q_PROPERTY

  | ERROR of string

  | TranslationUnit

(* PpDirective *)
  | PpInclude of string
  | PpDefine of ident
  | PpUndef of ident
  | PpLine of int * string
  | PpError of string
  | PpPragma of string
  | PpNull
  | PpMarker of int * string * int list
  | PpIf of string
  | PpIfdef of ident
  | PpIfndef of ident
  | PpElif of string
  | PpElse of string
  | PpEndif of string
  | PpUnknown of string
  | PpIfSection of int * string
  | PpIfSectionFuncDef of ident
  | PpIfSectionAltFuncDef
  | PpIfSectionBroken
  | PpIfSectionBrokenIf
  | PpIfSectionBrokenFuncDef
  | PpIfSectionBrokenDtorFunc
  | PpIfSectionCondExpr
  | PpIfSectionLogicalAnd
  | PpIfSectionLogicalOr
  | PpIfGroup of string
  | PpElifGroup of string
  | PpElseGroup of string
  | PpStringized of string
  | PpMacroParam of ident
  | PpImport of string

  | OmpDirective of string
  | AccDirective of string

(* Declaration *)
  | SimpleDeclaration                 (* BlockDeclaration *)
  | AsmDefinition of string           (* BlockDeclaration *)
  | NamespaceAliasDefinition of ident (* BlockDeclaration *)
  | UsingDeclaration                  (* BlockDeclaration *)
  | UsingEnumDeclaration              (* BlockDeclaration *)
  | UsingDirective of ident           (* BlockDeclaration *)
  | Static_assertDeclaration          (* BlockDeclaration *)
  | AliasDeclaration of ident         (* BlockDeclaration *)
  | OpaqueEnumDeclaration             (* BlockDeclaration *)
  | OpaqueEnumDeclarationClass        (* BlockDeclaration *)
  | OpaqueEnumDeclarationStruct       (* BlockDeclaration *)
  | OpaqueEnumDeclarationMacro of ident (* BlockDeclaration *)
  | NodeclspecFunctionDeclaration
  | FunctionDefinition of name
  | TemplateDeclaration
  | DeductionGuide of name
  | ExplicitInstantiation
  | ExplicitSpecialization
  | ExportDeclaration
  | LinkageSpecification of string
  | NamedNamespaceDefinition of ident  (* NamespaceDefinition *)
  | UnnamedNamespaceDefinition         (* NamespaceDefinition *)
  | NestedNamespaceDefinition of ident (* NamespaceDefinition *)
  | NamespaceDefinitionMacro of ident  (* NamespaceDefinition *)
  | EmptyDeclaration
  | AttributeDeclaration
  | DeclarationMacro of ident
  | DeclarationMacroInvocation of ident
  | DeclarationMacroInvocationInvocation
  | DeclarationMacroInvocationArrow
  | DeclarationMacroInvocationDot
  | ImportDeclaration of string

(* Statement *)
  | Statement
  | ExpressionStatement
  | DeclarationStatement
  (*| EmptyStatement*)
  | CompoundStatement
  | TryBlock

  | LabeledStatement
  (*| CaseStatement
  | DefaultStatement*)

  | SelectionStatement
  | IfStatement
  | ElseStatement
  | SwitchStatement

  | IterationStatement
  | WhileStatement
  | DoStatement
  | ForStatement
  | ForInStatement (* Objective-C *)
  | RangeBasedForStatement

  | JumpStatement
  | BreakStatement
  | ContinueStatement
  | ReturnStatement
  | GotoStatement of ident
  | ComputedGotoStatement
  | CoroutineReturnStatement

  | StatementMacroInvocation of ident
  | StatementMacro of ident
  | IterationMacroInvocation of ident
  | IterationMacro of ident

(* Expression *)
  | This
  | ParenthesizedExpression
  | RequiresExpression
  | FoldExpression
  | LambdaExpression

  | LogicalOrExpression of ident
  | LogicalAndExpression of ident
  | InclusiveOrExpression of ident
  | ExclusiveOrExpression of ident
  | AndExpression of ident
  | EqualityExpression    (* EqualityExpression *)
  | EqualityExpressionEq  (* EqualityExpression *)
  | EqualityExpressionStrictEq
  | EqualityExpressionNeq of ident (* EqualityExpression *)
  | RelationalExpression   (* RelationalExpression *)
  | RelationalExpressionLt (* RelationalExpression *)
  | RelationalExpressionGt (* RelationalExpression *)
  | RelationalExpressionLe (* RelationalExpression *)
  | RelationalExpressionGe (* RelationalExpression *)
  | CompareExpression
  | ShiftExpression      (* ShiftExpression *)
  | ShiftExpressionLeft  (* ShiftExpression *)
  | ShiftExpressionRight (* ShiftExpression *)
  | ShiftExpressionRightU (* ShiftExpression *)
  | AdditiveExpression     (* AdditiveExpression *)
  | AdditiveExpressionAdd  (* AdditiveExpression *)
  | AdditiveExpressionSubt (* AdditiveExpression *)
  | MultiplicativeExpression     (* MultiplicativeExpression *)
  | MultiplicativeExpressionMult (* MultiplicativeExpression *)
  | MultiplicativeExpressionDiv  (* MultiplicativeExpression *)
  | MultiplicativeExpressionMod  (* MultiplicativeExpression *)
  | PmExpression      (* PmExpression *)
  | PmExpressionClass (* PmExpression *)
  | PmExpressionPtr   (* PmExpression *)
  | CastExpression
  | CompoundLiteralExpression
  | UnaryExpression                    (* UnaryExpression *)
  | UnaryExpressionIncr                (* UnaryExpression *)
  | UnaryExpressionDecr                (* UnaryExpression *)
  | UnaryExpressionInd                 (* UnaryExpression *)
  | UnaryExpressionAddr                (* UnaryExpression *)
  | UnaryExpressionLabelAddr           (* UnaryExpression *)
  | UnaryExpressionPlus                (* UnaryExpression *)
  | UnaryExpressionMinus               (* UnaryExpression *)
  | UnaryExpressionNeg of ident        (* UnaryExpression *)
  | UnaryExpressionCompl of ident      (* UnaryExpression *)
  | UnaryExpressionSizeof              (* UnaryExpression *)
  | UnaryExpressionSizeofPack of ident (* UnaryExpression *)
  | UnaryExpressionAlignof             (* UnaryExpression *)
  | NoexceptExpression                 (* UnaryExpression *)
  | NewExpression                      (* UnaryExpression *)
  | RefNewExpression                   (* UnaryExpression *)
  | DeleteExpression                   (* UnaryExpression *)
  | PostfixExpression                 (* PostfixExpression *)
  | PostfixExpressionSubscr           (* PostfixExpression *)
  | PostfixExpressionFunCall          (* PostfixExpression *)
  | PostfixExpressionFunCallMacro of ident (* PostfixExpression *)
  | PostfixExpressionExplicitTypeConv (* PostfixExpression *)
  | PostfixExpressionExplicitTypeConvExpr   (* PostfixExpression *)
  | PostfixExpressionExplicitTypeConvBraced (* PostfixExpression *)
  | PostfixExpressionDot              (* PostfixExpression *)
  | PostfixExpressionArrow            (* PostfixExpression *)
  | PostfixExpressionIncr             (* PostfixExpression *)
  | PostfixExpressionDecr             (* PostfixExpression *)
  | PostfixExpressionTypeid           (* PostfixExpression *)
  | PostfixExpressionTypeidExpr       (* PostfixExpression *)
  | PostfixExpressionTypeidTy         (* PostfixExpression *)
  | PostfixExpressionDynamic_cast     (* PostfixExpression *)
  | PostfixExpressionStatic_cast      (* PostfixExpression *)
  | PostfixExpressionReinterpret_cast (* PostfixExpression *)
  | PostfixExpressionConst_cast       (* PostfixExpression *)
  | AssignmentExpression           (* AssignmentExpression *)
  | AssignmentExpressionOverloaded of ident (* AssignmentExpression *)
  | AssignmentExpressionEq         (* AssignmentExpression *)
  | AssignmentExpressionPlus       (* AssignmentExpression *)
  | AssignmentExpressionMinus      (* AssignmentExpression *)
  | AssignmentExpressionMult       (* AssignmentExpression *)
  | AssignmentExpressionDiv        (* AssignmentExpression *)
  | AssignmentExpressionMod        (* AssignmentExpression *)
  | AssignmentExpressionShiftLeft  (* AssignmentExpression *)
  | AssignmentExpressionShiftRight (* AssignmentExpression *)
  | AssignmentExpressionAnd of ident (* AssignmentExpression *)
  | AssignmentExpressionXor of ident (* AssignmentExpression *)
  | AssignmentExpressionOr of ident  (* AssignmentExpression *)
  | ThrowExpression
  | ExpressionPair (* Expression *)
  | ConditionalExpression
  | DeleteExpressionBracket
  | YieldExpression
  | AwaitExpression
  | BlockLiteralExpression

  | ExpressionMacroInvocation of ident (* PostfixExpression *)
  | LogicalOrMacroInvocation of ident
  | DefinedMacroExpression of ident
  | HasIncludeExpression of string
  | HasAttributeExpression

(* Literal *)
  | Literal
  | IntegerLiteral of value
  | CharacterLiteral of value
  | FloatingLiteral of value
  | StringLiteral of value
  | StringMacro of ident
  | BooleanLiteral of value
  | Nullptr
  | ConcatenatedString
  | UserDefinedCharacterLiteral of value
  | UserDefinedStringLiteral of value
  | UserDefinedFloatingLiteral of value
  | UserDefinedIntegerLiteral of value

  | LiteralMacro of ident
  | LiteralMacroInvocation of ident

(* UnqualifiedId *)
  | UnqualifiedId
  | OperatorFunctionId
  | ConversionFunctionId
  | LiteralOperatorId of string
  | Destructor
  | TemplateId
  | TemplateIdOp
  | TemplateIdLit

(* Operator *)
  | Operator
  | New
  | Delete
  | NewBracket
  | DeleteBracket
  | Parentheses
  | Brackets
  | MinusGt
  | MinusGtStar
  | Tilde of ident
  | Exclam of ident
  | Plus
  | Minus
  | Star
  | Slash
  | Perc
  | Hat of ident
  | Amp of ident
  | Bar of ident
  | Eq
  | PlusEq
  | MinusEq
  | StarEq
  | SlashEq
  | PercEq
  | HatEq of ident
  | AmpEq of ident
  | BarEq of ident
  | EqEq
  | ExclamEq of ident
  | Lt
  | Gt
  | LtEq
  | GtEq
  | LtEqGt
  | AmpAmp of ident
  | BarBar of ident
  | LtLt
  | GtGt
  | LtLtEq
  | GtGtEq
  | PlusPlus
  | MinusMinus
  | Comma
  | Semicolon
  | Colon
  | Co_await

  | DotStar
  | Dot

(* DefiningTypeSpecifier *)
  | DefiningTypeSpecifier
  | SimpleTypeSpecifier of ident (* TypeSpecifier *)
  | TypenameSpecifier of ident   (* TypeSpecifier *)
  | CvQualifier                  (* TypeSpecifier *)
  | TypeMacro of ident
  | Const    (* CvQualifier *)
  | Volatile (* CvQualifier *)
  | Restrict of ident (* CvQualifier *)


  | MsAsmBlock of ident * string (* MS *)
  | MsCdecl of ident   (* MS calling convention *)
  | MsStdcall of ident (* MS calling convention *)
  | MsPragma of ident
  | MsWarningSpecifier of ident
  | MsProperty of ident
  | MsAttributeSpecifier

  | CallingConvention of ident

  | GnuAsmBlock of string * string (* GNU *)
  | GnuAttribute of ident (* GNU *)
  | GnuStatementExpression (* GNU *)

  | ElaboratedTypeSpecifier      (* TypeSpecifier *)
  | ElaboratedTypeSpecifierClass of ident  (* ElaboratedTypeSpecifier *)
  | ElaboratedTypeSpecifierStruct of ident (* ElaboratedTypeSpecifier *)
  | ElaboratedTypeSpecifierUnion of ident  (* ElaboratedTypeSpecifier *)
  | ElaboratedTypeSpecifierEnum of ident   (* ElaboratedTypeSpecifier *)
  | ClassSpecifier
  | EnumSpecifier

(* BasicType *)
  | BasicType
  | Char
  | Char8_t
  | Char16_t
  | Char32_t
  | Wchar_t
  | Bool
  | Short
  | Int
  | Long
  | Signed
  | Unsigned
  | Float
  | Double
  | Void
  | UnsignedInt
  | UnsignedLong

(* AccessSpecifier *)
  | AccessSpecifier
  | Private
  | Protected
  | Public

(* AttributeSpecifier *)
  | AttributeSpecifier
  | StandardAttributeSpecifier
  | ContractAttributeSpecifier
  | ContractAttributeSpecifierExpects
  | ContractAttributeSpecifierEnsures of ident
  | ContractAttributeSpecifierAssert
  | AlignmentAttributeSpecifier of bool

  | AttributeMacro of ident

(* RefQualifier *)
  | RefQualifier
  | RefQualifierAmp
  | RefQualifierAmpAmp

(* PlaceholderTypeSpecifier *)
  | PlaceholderTypeSpecifier
  | PlaceholderTypeSpecifierAuto
  | PlaceholderTypeSpecifierDecltype

(* PtrOperator *)
  | PtrOperator
  | PtrOperatorStar
  | PtrOperatorAmp
  | PtrOperatorAmpAmp
  | PtrOperatorHat
  | PtrOperatorMacro of ident

(* Declarator *)
  | Declarator
  | DeclaratorFunc
  | PtrDeclarator (* PtrDeclarator *)
  | PtrDeclaratorPtr (* PtrDeclarator *)
  | NoptrDeclarator      (* NoptrDeclarator *)
  | NoptrDeclaratorId    (* NoptrDeclarator *)
  | NoptrDeclaratorParen (* NoptrDeclarator *)
  | NoptrDeclaratorFunc  (* NoptrDeclarator *)
  | NoptrDeclaratorOldFunc (* NoptrDeclarator *)
  | NoptrDeclaratorArray (* NoptrDeclarator *)
  | DtorMacro of ident

(* NoexceptSpecifier *)
  | NoexceptSpecifier
  | NoexceptSpecifierThrow
  | NoexceptSpecifierThrowAny

(* VirtSpecifier *)
  | VirtSpecifier
  | VirtSpecifierFinal
  | VirtSpecifierOverride
  | VirtSpecifierMacro of ident
  | VirtSpecifierMacroInvocation of ident

(* StorageClassSpecifier *)
  | StorageClassSpecifier
  | StorageClassSpecifierStatic
  | StorageClassSpecifierThread_local
  | StorageClassSpecifierExtern
  | StorageClassSpecifierMutable
  | StorageClassSpecifierRegister
  | StorageClassSpecifierVaxGlobaldef

(* FunctionSpecifier *)
  | FunctionSpecifier
  | FunctionSpecifierVirtual
  | ExplicitSpecifier

(* ClassHead *)
  | ClassHead
  | ClassHeadClass
  | ClassHeadStruct
  | ClassHeadUnion
  | ClassHeadMacro of ident
  | ClassHeadMacroInvocation of ident
  | ClassHeadMsRefClass

(* EnumHead *)
  | EnumHead
  | EnumHeadEnum
  | EnumHeadEnumClass
  | EnumHeadEnumStruct
  | EnumHeadEnumMacro of ident

(* TypeParameterKey *)
  | TypeParameterKey
  | TypeParameterKeyClass
  | TypeParameterKeyTypename

(* FunctionBody *)
  | FunctionBody of name
  | FunctionBodyDefault
  | FunctionBodyDelete
  | FunctionTryBlock of name
  | FunctionBodyMacro of ident
  | FunctionBodyMacroInvocation of ident

(* DeclSpecifier *)
  | DeclSpecifier
  | DeclSpecifierInline
  | DeclSpecifierConstexpr
  | DeclSpecifierConsteval
  | DeclSpecifierConstinit
  | DeclSpecifierTypedef
  | DeclSpecifierFriend
  | DeclSpecifierMacro of ident
  | DeclSpecifierMacroInvocation of ident

(* Requirement *)
  | Requirement
  | SimpleRequirement
  | TypeRequirement
  | CompoundRequirement
  | ReturnTypeRequirement
  | NestedRequirement

(* AbstractDeclarator *)
  | AbstractDeclarator
  | AbstractDeclaratorFunc
  | PtrAbstractDeclarator (* AbstractDeclarator *)
  | PtrAbstractDeclaratorPtr (* AbstractDeclarator *)
  | NoptrAbstractDeclarator (* AbstractDeclarator *)
  | NoptrAbstractDeclaratorFunc
  | NoptrAbstractDeclaratorArray
  | NoptrAbstractDeclaratorParen

(* NoptrAbstractPackDeclarator *)
  | NoptrAbstractPackDeclaratorFunc
  | NoptrAbstractPackDeclaratorArray

(* SimpleCapture *)
  | SimpleCapture of ident
  | SimpleCaptureAmp of ident
  | SimpleCaptureThis
  | SimpleCaptureStarThis

(* InitCapture *)
  | InitCapture of ident
  | InitCaptureAmp of ident

(* LambdaCapture *)
  | LambdaCapture
  | LambdaCaptureDefaultEq
  | LambdaCaptureDefaultAmp
  | LambdaCaptureMacroInvocation of ident

(* MemberDeclarator *)
  | MemberDeclarator
  | MemberDeclaratorDecl
  | MemberDeclaratorBitField of ident

(* Label *)
  | Label of ident
  | CaseLabel
  | RangedCaseLabel
  | DefaultLabel
  | LabelMacroInvocation of ident

(* ContractLevel *)
  | ContractLevel
  | ContractLevelDefault
  | ContractLevelAudit
  | ContractLevelAxiom

(* BalancedToken *)
  | BalancedToken
  | BalancedTokenSingle of string(*Obj.t*)
  | BalancedTokenParen
  | BalancedTokenBracket
  | BalancedTokenBrace

  | MemberSpecification

  | MemberDeclarationDecl

(* *)
  | Explicit
  | Virtual
  | Template
  | Noexcept
  | Extern
  | Inline
  | Default
  | ColonColon
  | Ellipsis
  | Constexpr
  | Typename

  | PureSpecifier
  | BaseSpecifier
  | BaseClause
  | BaseMacro of ident
  | BaseSpecMacro of ident
  | BaseSpecMacroInvocation of ident
  | SuffixMacro of ident
  | ClassVirtSpecifierFinal
  | ClassVirtSpecifierMsSealed
  | ClassName of ident
  | ClassHeadName of name
  | MacroArgument
  | NoptrNewDeclarator
  | NewInitializer
  | NewInitializerMacro of ident
  | ArgumentsMacro of ident
  | ArgumentsMacroInvocation of ident
  | NewDeclaratorPtr
  | NewDeclarator
  | NewTypeId
  | NewPlacement
  | LambdaDeclarator
  | ParenthesizedInitList
  | LambdaIntroducer
  | LambdaIntroducerMacro of ident
  | AbstractPackDeclarator
  | AbstractPack
  | RequirementBody
  | RequirementParameterList
  | MemInitializer
  | MemInitMacroInvocation of ident
  | QualifiedTypeName
  | InitDeclarator of name
  | ConceptDefinition of name
  | CtorInitializer
  | ConstraintLogicalOrExpression of ident
  | ConstraintLogicalAndExpression of ident
  | RequiresClause
  | TypeParameter of ident
  | TemplateHead
  | EnclosingNamespaceSpecifier of ident
  | Enumerator of ident
  | EnumeratorDefinition
  | EnumeratorDefinitionMacro of ident
  | TypeMacroInvocation of ident
  | Condition
  | ParameterDeclaration of name
  | ParameterDeclarationClause of bool
  | ParametersAndQualifiers
  | ParamDeclMacro of ident
  | ParamDeclMacroInvocation of ident
  | ParametersMacro of ident
  | ParametersMacroInvocation of ident
  | Handler
  | ExceptionDeclaration
  | ExpressionList
  | EqualInitializer
  | DesignatedInitializerClause
  | DesignatorField of ident
  | DesignatorIndex
  | DesignatorRange
  | TrailingReturnType
  | BracedInitList
  | ForRangeDeclaration
  | DefiningTypeId
  | EnumHeadName of ident
  | EnumBase
  | QualifiedId
  | QualifiedNamespaceSpecifier of name
  | TypeName of name
  | ConversionDeclarator
  | ConversionTypeId
  | UsingDeclarator
  | UsingEnumDeclarator
  | TypeConstraint of name
  | TypeId
  | DecltypeSpecifier
  | SimpleTemplateId of name
  | Identifier of ident
  | IdentifierMacroInvocation of ident
  | PpConcatenatedIdentifier
  | NestedNameSpecifier
  | NestedNameSpecifierHead
  | NestedNameSpecifierIdent of ident
  | NestedNameSpecifierTempl of ident
  | NestedNameSpecifierDeclty
  | PackExpansion
  | AttributeUsingPrefix
  | Attribute
  | AttributeToken of ident
  | AttributeScopedToken of ident
  | AttributeNamespace of ident
  | AttributeArgumentClause
  | AttributeArgumentClauseMacro of ident
  | TokenSeq of string
  | ObjectLikeMacro
  | FunctionLikeMacro of macro_kind
  | OperatorMacro of ident
  | OperatorMacroInvocation of ident
  | DefiningTypeSpecifierSeq
  | DeclSpecifierSeq
  | TypeSpecifierSeq
  | FunctionHead of name
  | FunctionHeadMacro of ident
  | AccessSpecAnnot of ident
  | EnumeratorMacroInvocation of ident
  | AccessSpecMacro of ident
  | CvMacro of ident
  | CvMacroInvocation of ident
  | RefMacro of ident
  | RefMacroInvocation of ident
  | OpeningBrace
  | ClosingBrace
  | OpeningBracket
  | ClosingBracket
  | DummyBody
  | DummyDecl
  | DummyStmt
  | DummyExpr
  | DummyOp
  | DummyDtor
  | GnuAsmBlockFragmented of string
  | GnuAsmFragment of string
  (*| GnuAsmQualifier of ident*)
  | DesignatorFieldOld of ident
  | DoxygenLine of string
  | NoexceptSpecifierMacro of ident
  | AttributeMacroInvocation of ident
  | CudaExecutionConfiguration
  | CudaKernelCall
  | SimpleTemplateIdM
  | NamespaceHead of ident
  | NamedNamespaceDefinitionHead of ident
  | InitializerClause
  | TemplParamMacroInvocation of ident
  | PostfixExpressionFunCallGuarded of ident
  | PpIfSectionTemplDecl
  | PpIfSectionTryBlock
  | Try
  | PpIfSectionHandler
  | BlockHeadMacro of ident
  | BlockEndMacro of ident
  | DeclStmtBlock
  | AsmShader of string
  | AsmName of ident
  | AsmOperand
  | AsmDirective of ident
  | VaArgs of string
  | PtrMacro of ident
  | At
  | ClassBody
  | Lparen
  | Rparen
  | Asm
  | TemplateArguments
  | SuffixMacroInvocation of ident

  | ObjcThrow
  | ObjcSynchronized
  | ObjcClassDeclarationList
  | ObjcProtocolDeclarationList
  | ObjcProtocolDeclaration of ident
  | ObjcClassInterface of ident
  | ObjcCategoryInterface of ident * ident
  | ObjcSuperclass of ident
  | ObjcProtocolReferenceList
  | ObjcProtocolReferenceListMacro of ident
  | ObjcInstanceVariables
  | ObjcInstanceVariableDeclaration
  | ObjcInterfaceDeclaration
  | ObjcPrivate
  | ObjcPublic
  | ObjcPackage
  | ObjcProtected
  | ObjcStructDeclaration
  | ObjcStructDeclarator
  | ObjcPropertyDeclaration
  | ObjcPropertyAttributesDeclaration
  | ObjcClassMethodDeclaration
  | ObjcInstanceMethodDeclaration
  | ObjcMethodType
  | ObjcMethodSelector
  | ObjcMethodSelectorPack
  | ObjcSelector of ident
  | ObjcSelectorMacro of ident
  | ObjcKeywordSelector
  | ObjcKeywordDeclarator of ident
  | ObjcSpecifierQualifier of ident
  | ObjcProtocolName of ident
  | ObjcClassName of ident
  | ObjcPropertyAttribute of ident
  | ObjcMessageExpression
  | ObjcMessageSelector
  | ObjcProtocolExpression
  | ObjcKeywordArgument of ident
  | ObjcProtocolInterfaceDeclarationOptional
  | ObjcProtocolInterfaceDeclarationRequired
  | ObjcAutoreleasepool
  | ObjcAvailable
  | ObjcSelectorExpression of ident
  | ObjcEncodeExpression
  | ObjcTryBlock
  | ObjcTry
  | ObjcCatchClause
  | ObjcFinally
  | ObjcMethodMacroInvocation of ident
  | ObjcKeywordName of ident
  | ObjcLiteral
  | ObjcArray
  | ObjcDictionary
  | ObjcKeyValue
  | ObjcClass

  | SwiftArg of ident
  | SwiftFunCall

  | HugeArray of int * string
  | DslMacroArgument
  | ParametersAndQualifiersList
  | NestedFunctionDefinition of name
  | PragmaMacro of ident
  | PragmaMacroInvocation of ident
  | MockQualifier of ident

  | ClassBodyHeadMacro of ident
  | ClassBodyEndMacro of ident
  | ClassBodyHeadMacroInvocation of ident
  | ClassBodyEndMacroInvocation of ident
  | InitHeadMacroInvocation of ident
  | InitEndMacroInvocation of ident
  | InitDeclaration
  | LiteralMacroArgument of string

let to_string = function
  | DUMMY -> "DUMMY"
  | EMPTY -> "EMPTY"
  | AMBIGUOUS_CONSTRUCT -> "AMBIGUOUS_CONSTRUCT"
  | PARTIAL_CONSTRUCT   -> "PARTIAL_CONSTRUCT"
  | DECLS               -> "DECLS"
  | MEM_DECLS           -> "MEM_DECLS"
  | EXPRS               -> "EXPRS"
  | STMTS               -> "STMTS"
  | INITS               -> "INITS"
  | LABELS              -> "LABELS"
  | SPECS               -> "SPECS"
  | ETORS               -> "ETORS"
  | OBJC_DECLS          -> "OBJC_DECLS"
  | TEMPL_PARAMS        -> "TEMPL_PARAMS"
  | TEMPL_ARGS          -> "TEMPL_ARGS"
  | DELIM_MACRO i       -> "DELIM_MACRO:"^i
  | DELIM_MACRO_ i      -> "DELIM_MACRO_:"^i
  | Q_PROPERTY          -> "Q_PROPERTY"
  | ERROR s             -> "ERROR:"^s

  | TranslationUnit -> "TranslationUnit"

(* PpDirective *)
  | PpInclude s              -> "PpInclude:"^s
  | PpDefine i               -> "PpDefine:"^i
  | PpUndef i                -> "PpUndef:"^i
  | PpLine (j, s)            -> sprintf "PpLine:%d:%s" j s
  | PpError s                -> "PpError:"^s
  | PpPragma s               -> "PpPragma:"^s
  | PpNull                   -> "PpNull"
  | PpMarker(j, s, jl)       -> sprintf "PpMarker:%d:%s:%s" j s
        (String.concat ":" (List.map string_of_int jl))
  | PpIf x                   -> "PpIf:"^x
  | PpIfdef i                -> "PpIfdef:"^i
  | PpIfndef i               -> "PpIfndef:"^i
  | PpElif x                 -> "PpElif:"^x
  | PpElse x                 -> "PpElse:"^x
  | PpEndif x                -> "PpEndif:"^x
  | PpUnknown s              -> "PpUnknown:"^s
  | PpIfSection(j, s)        -> sprintf "PpIfSection:%d:%s" j s
  | PpIfSectionFuncDef i     -> "PpIfSectionFuncDef:"^i
  | PpIfSectionAltFuncDef    -> "PpIfSectionAltFuncDef"
  | PpIfSectionBroken        -> "PpIfSectionBroken"
  | PpIfSectionBrokenIf      -> "PpIfSectionBrokenIf"
  | PpIfSectionBrokenFuncDef -> "PpIfSectionBrokenFuncDef"
  | PpIfSectionBrokenDtorFunc -> "PpIfSectionBrokenDtorFunc"
  | PpIfSectionCondExpr      -> "PpIfSectionCondExpr"
  | PpIfSectionLogicalAnd    -> "PpIfSectionLogicalAnd"
  | PpIfSectionLogicalOr     -> "PpIfSectionLogicalOr"
  | PpIfGroup x              -> "PpIfGroup:"^x
  | PpElifGroup x            -> "PpElifGroup:"^x
  | PpElseGroup x            -> "PpElseGroup:"^x
  | PpStringized s           -> "PpStringized:"^s
  | PpMacroParam s           -> "PpMacroParam:"^s
  | PpImport s               -> "PpImport:"^s

  | OmpDirective s           -> "OmpDirective:"^s
  | AccDirective s           -> "AccDirective:"^s

(* Declaration *)
  | SimpleDeclaration             -> "SimpleDeclaration"
  | AsmDefinition s               -> sprintf "AsmDefinition(%s)" s
  | NamespaceAliasDefinition i    -> "NamespaceAliasDefinition:"^i
  | UsingDeclaration              -> "UsingDeclaration"
  | UsingEnumDeclaration          -> "UsingEnumDeclaration"
  | UsingDirective i              -> "UsingDirective:"^i
  | Static_assertDeclaration      -> "Static_assertDeclaration"
  | AliasDeclaration i            -> "AliasDeclaration:"^i
  | OpaqueEnumDeclaration         -> "OpaqueEnumDeclaration"
  | OpaqueEnumDeclarationClass    -> "OpaqueEnumDeclarationClass"
  | OpaqueEnumDeclarationStruct   -> "OpaqueEnumDeclarationStruct"
  | OpaqueEnumDeclarationMacro i  -> "OpaqueEnumDeclarationMacro:"^i
  | NodeclspecFunctionDeclaration -> "NodeclspecFunctionDeclaration"
  | FunctionDefinition n          -> "FunctionDefinition:"^n
  | TemplateDeclaration           -> "TemplateDeclaration"
  | DeductionGuide n              -> "DeductionGuide:"^n
  | ExplicitInstantiation         -> "ExplicitInstantiation"
  | ExplicitSpecialization        -> "ExplicitSpecialization"
  | ExportDeclaration             -> "ExportDeclaration"
  | LinkageSpecification s        -> "LinkageSpecification:"^s
  | NamedNamespaceDefinition i    -> "NamedNamespaceDefinition:"^i
  | UnnamedNamespaceDefinition    -> "UnnamedNamespaceDefinition"
  | NestedNamespaceDefinition i   -> "NestedNamespaceDefinition:"^i
  | NamespaceDefinitionMacro i    -> "NamespaceDefinitionMacro:"^i
  | EmptyDeclaration              -> "EmptyDeclaration"
  | AttributeDeclaration          -> "AttributeDeclaration"
  | DeclarationMacro i            -> "DeclarationMacro:"^i
  | DeclarationMacroInvocation i  -> "DeclarationMacroInvocation:"^i
  | DeclarationMacroInvocationInvocation -> "DeclarationMacroInvocationInvocation"
  | DeclarationMacroInvocationArrow -> "DeclarationMacroInvocationArrow"
  | DeclarationMacroInvocationDot -> "DeclarationMacroInvocationDot"
  | ImportDeclaration s           -> "ImportDeclaration:"^s

(* Statement *)
  | Statement                  -> "Statement"
  | ExpressionStatement        -> "ExpressionStatement"
  | DeclarationStatement       -> "DeclarationStatement"
  | TryBlock                   -> "TryBlock"
  | LabeledStatement           -> "LabeledStatement"
  | SelectionStatement         -> "SelectionStatement"
  | IfStatement                -> "IfStatement"
  | ElseStatement              -> "ElseStatement"
  | SwitchStatement            -> "SwitchStatement"
  (*| EmptyStatement             -> "EmptyStatement"*)
  | CompoundStatement          -> "CompoundStatement"
  | IterationStatement         -> "IterationStatement"
  | WhileStatement             -> "WhileStatement"
  | DoStatement                -> "DoStatement"
  | ForStatement               -> "ForStatement"
  | ForInStatement             -> "ForInStatement"
  | RangeBasedForStatement     -> "RangeBasedForStatement"
  | JumpStatement              -> "JumpStatement"
  | BreakStatement             -> "BreakStatement"
  | ContinueStatement          -> "ContinueStatement"
  | ReturnStatement            -> "ReturnStatement"
  | GotoStatement i            -> "GotoStatement:"^i
  | ComputedGotoStatement      -> "ComputedGotoStatement"
  | CoroutineReturnStatement   -> "CoroutineReturnStatement"
  | StatementMacroInvocation i -> "StatementMacroInvocation:"^i
  | StatementMacro i           -> "StatementMacro:"^i
  | IterationMacroInvocation i -> "IterationMacroInvocation:"^i
  | IterationMacro i           -> "IterationMacro:"^i

(* Expression *)
  | This                              -> "This"
  | ParenthesizedExpression           -> "ParenthesizedExpression"
  | RequiresExpression                -> "RequiresExpression"
  | FoldExpression                    -> "FoldExpression"
  | LambdaExpression                  -> "LambdaExpression"
  | LogicalOrExpression i             -> "LogicalOrExpression:"^i
  | LogicalAndExpression i            -> "LogicalAndExpression:"^i
  | InclusiveOrExpression i           -> "InclusiveOrExpression:"^i
  | ExclusiveOrExpression i           -> "ExclusiveOrExpression:"^i
  | AndExpression i                   -> "AndExpression:"^i
  | EqualityExpression                -> "EqualityExpression"
  | EqualityExpressionEq              -> "EqualityExpressionEq"
  | EqualityExpressionStrictEq        -> "EqualityExpressionStrictEq"
  | EqualityExpressionNeq i           -> "EqualityExpressionNeq:"^i
  | RelationalExpression              -> "RelationalExpression"
  | RelationalExpressionLt            -> "RelationalExpressionLt"
  | RelationalExpressionGt            -> "RelationalExpressionGt"
  | RelationalExpressionLe            -> "RelationalExpressionLe"
  | RelationalExpressionGe            -> "RelationalExpressionGe"
  | CompareExpression                 -> "CompareExpression"
  | ShiftExpression                   -> "ShiftExpression"
  | ShiftExpressionLeft               -> "ShiftExpressionLeft"
  | ShiftExpressionRight              -> "ShiftExpressionRight"
  | ShiftExpressionRightU             -> "ShiftExpressionRightU"
  | AdditiveExpression                -> "AdditiveExpression"
  | AdditiveExpressionAdd             -> "AdditiveExpressionAdd"
  | AdditiveExpressionSubt            -> "AdditiveExpressionSubt"
  | MultiplicativeExpression          -> "MultiplicativeExpression"
  | MultiplicativeExpressionMult      -> "MultiplicativeExpressionMult"
  | MultiplicativeExpressionDiv       -> "MultiplicativeExpressionDiv"
  | MultiplicativeExpressionMod       -> "MultiplicativeExpressionMod"
  | PmExpression                      -> "PmExpression"
  | PmExpressionClass                 -> "PmExpressionClass"
  | PmExpressionPtr                   -> "PmExpressionPtr"
  | CastExpression                    -> "CastExpression"
  | CompoundLiteralExpression         -> "CompoundLiteralExpression"
  | UnaryExpression                   -> "UnaryExpression"
  | UnaryExpressionIncr               -> "UnaryExpressionIncr"
  | UnaryExpressionDecr               -> "UnaryExpressionDecr"
  | UnaryExpressionInd                -> "UnaryExpressionInd"
  | UnaryExpressionAddr               -> "UnaryExpressionAddr"
  | UnaryExpressionLabelAddr          -> "UnaryExpressionLabelAddr"
  | UnaryExpressionPlus               -> "UnaryExpressionPlus"
  | UnaryExpressionMinus              -> "UnaryExpressionMinus"
  | UnaryExpressionNeg i              -> "UnaryExpressionNeg:"^i
  | UnaryExpressionCompl i            -> "UnaryExpressionCompl:"^i
  | UnaryExpressionSizeof             -> "UnaryExpressionSizeof"
  | UnaryExpressionSizeofPack i       -> "UnaryExpressionSizeofPack:"^i
  | UnaryExpressionAlignof            -> "UnaryExpressionAlignof"
  | NoexceptExpression                -> "NoexceptExpression"
  | PostfixExpression                 -> "PostfixExpression"
  | PostfixExpressionSubscr           -> "PostfixExpressionSubscr"
  | PostfixExpressionFunCall          -> "PostfixExpressionFunCall"
  | PostfixExpressionFunCallMacro i   -> "PostfixExpressionFunCallMacro:"^i
  | PostfixExpressionExplicitTypeConv -> "PostfixExpressionExplicitTypeConv"
  | PostfixExpressionExplicitTypeConvExpr   -> "PostfixExpressionExplicitTypeConvExpr"
  | PostfixExpressionExplicitTypeConvBraced -> "PostfixExpressionExplicitTypeConvBraced"
  | PostfixExpressionDot              -> "PostfixExpressionDot"
  | PostfixExpressionArrow            -> "PostfixExpressionArrow"
  | PostfixExpressionIncr             -> "PostfixExpressionIncr"
  | PostfixExpressionDecr             -> "PostfixExpressionDecr"
  | PostfixExpressionTypeid           -> "PostfixExpressionTypeid"
  | PostfixExpressionTypeidExpr       -> "PostfixExpressionTypeidExpr"
  | PostfixExpressionTypeidTy         -> "PostfixExpressionTypeidTy"
  | PostfixExpressionDynamic_cast     -> "PostfixExpressionDynamic_cast"
  | PostfixExpressionStatic_cast      -> "PostfixExpressionStatic_cast"
  | PostfixExpressionReinterpret_cast -> "PostfixExpressionReinterpret_cast"
  | PostfixExpressionConst_cast       -> "PostfixExpressionConst_cast"
  | AssignmentExpression              -> "AssignmentExpression"
  | AssignmentExpressionOverloaded i  -> "AssignmentExpressionOverloaded:"^i
  | AssignmentExpressionEq            -> "AssignmentExpressionEq"
  | AssignmentExpressionPlus          -> "AssignmentExpressionPlus"
  | AssignmentExpressionMinus         -> "AssignmentExpressionMinus"
  | AssignmentExpressionMult          -> "AssignmentExpressionMult"
  | AssignmentExpressionDiv           -> "AssignmentExpressionDiv"
  | AssignmentExpressionMod           -> "AssignmentExpressionMod"
  | AssignmentExpressionShiftLeft     -> "AssignmentExpressionShiftLeft"
  | AssignmentExpressionShiftRight    -> "AssignmentExpressionShiftRight"
  | AssignmentExpressionAnd i         -> "AssignmentExpressionAnd:"^i
  | AssignmentExpressionXor i         -> "AssignmentExpressionXor:"^i
  | AssignmentExpressionOr i          -> "AssignmentExpressionOr:"^i
  | ThrowExpression                   -> "ThrowExpression"
  | ExpressionPair                    -> "ExpressionPair"
  | ConditionalExpression             -> "ConditionalExpression"
  | NewExpression                     -> "NewExpression"
  | RefNewExpression                  -> "RefNewExpression"
  | DeleteExpression                  -> "DeleteExpression"
  | DeleteExpressionBracket           -> "DeleteExpressionBracket"
  | YieldExpression                   -> "YieldExpression"
  | AwaitExpression                   -> "AwaitExpression"
  | BlockLiteralExpression            -> "BlockLiteralExpression"

  | ExpressionMacroInvocation i       -> "ExpressionMacroInvocation:"^i
  | LogicalOrMacroInvocation i        -> "LogicalOrMacroInvocation:"^i
  | DefinedMacroExpression i          -> "DefinedMacroExpression:"^i
  | HasIncludeExpression s            -> "HasIncludeExpression:"^s
  | HasAttributeExpression            -> "HasAttributeExpression"

(* Literal *)
  | Literal                       -> "Literal"
  | IntegerLiteral v              -> "IntegerLiteral:"^v
  | CharacterLiteral v            -> "CharacterLiteral:"^v
  | FloatingLiteral v             -> "FloatingLiteral:"^v
  | StringLiteral v               -> "StringLiteral:"^v
  | StringMacro i                 -> "StringMacro:"^i
  | BooleanLiteral v              -> "BooleanLiteral:"^v
  | Nullptr                       -> "Nullptr"
  | ConcatenatedString            -> "ConcatenatedString"
  | UserDefinedCharacterLiteral v -> "UserDefinedCharacterLiteral:"^v
  | UserDefinedStringLiteral v    -> "UserDefinedStringLiteral:"^v
  | UserDefinedFloatingLiteral v  -> "UserDefinedFloatingLiteral:"^v
  | UserDefinedIntegerLiteral v   -> "UserDefinedIntegerLiteral:"^v
  | LiteralMacro i                -> "LiteralMacro:"^i
  | LiteralMacroInvocation i      -> "LiteralMacroInvocation:"^i

(* UnqualifiedId *)
  | UnqualifiedId        -> "UnqualifiedId"
  | OperatorFunctionId   -> "OperatorFunctionId"
  | ConversionFunctionId -> "ConversionFunctionId"
  | LiteralOperatorId s  -> "LiteralOperatorId:"^s
  | Destructor           -> "Destructor"
  | TemplateId           -> "TemplateId"
  | TemplateIdOp         -> "TemplateIdOp"
  | TemplateIdLit        -> "TemplateIdLit"

(* Operator *)
  | Operator      -> "Operator"
  | New           -> "New"
  | Delete        -> "Delete"
  | NewBracket    -> "NewBracket"
  | DeleteBracket -> "DeleteBracket"
  | Parentheses   -> "Parentheses"
  | Brackets      -> "Brackets"
  | MinusGt       -> "MinusGt"
  | MinusGtStar   -> "MinusGtStar"
  | Tilde i       -> "Tilde:"^i
  | Exclam i      -> "Exclam:"^i
  | Plus          -> "Plus"
  | Minus         -> "Minus"
  | Star          -> "Star"
  | Slash         -> "Slash"
  | Perc          -> "Perc"
  | Hat i         -> "Hat:"^i
  | Amp i         -> "Amp:"^i
  | Bar i         -> "Bar:"^i
  | Eq            -> "Eq"
  | PlusEq        -> "PlusEq"
  | MinusEq       -> "MinusEq"
  | StarEq        -> "StarEq"
  | SlashEq       -> "SlashEq"
  | PercEq        -> "PercEq"
  | HatEq i       -> "HatEq:"^i
  | AmpEq i       -> "AmpEq:"^i
  | BarEq i       -> "BarEq:"^i
  | EqEq          -> "EqEq"
  | ExclamEq i    -> "ExclamEq:"^i
  | Lt            -> "Lt"
  | Gt            -> "Gt"
  | LtEq          -> "LtEq"
  | GtEq          -> "GtEq"
  | LtEqGt        -> "LtEqGt"
  | AmpAmp i      -> "AmpAmp:"^i
  | BarBar i      -> "BarBar:"^i
  | LtLt          -> "LtLt"
  | GtGt          -> "GtGt"
  | LtLtEq        -> "LtLtEq"
  | GtGtEq        -> "GtGtEq"
  | PlusPlus      -> "PlusPlus"
  | MinusMinus    -> "MinusMinus"
  | Comma         -> "Comma"
  | Semicolon     -> "Semicolon"
  | Colon         -> "Colon"
  | Co_await      -> "Co_await"

  | DotStar       -> "DotStar"
  | Dot           -> "Dot"

(* DefiningTypeSpecifier *)
  | DefiningTypeSpecifier           -> "DefiningTypeSpecifier"
  | SimpleTypeSpecifier i           -> "SimpleTypeSpecifier:"^i
  | ElaboratedTypeSpecifier         -> "ElaboratedTypeSpecifier"
  | ElaboratedTypeSpecifierClass i  -> "ElaboratedTypeSpecifierClass:"^i
  | ElaboratedTypeSpecifierStruct i -> "ElaboratedTypeSpecifierStruct:"^i
  | ElaboratedTypeSpecifierUnion i  -> "ElaboratedTypeSpecifierUnion:"^i
  | ElaboratedTypeSpecifierEnum i   -> "ElaboratedTypeSpecifierEnum:"^i
  | TypenameSpecifier i             -> "TypenameSpecifier:"^i
  | CvQualifier                     -> "CvQualifier"
  | TypeMacro i                     -> "TypeMacro:"^i
  | Const                           -> "Const"
  | Volatile                        -> "Volatile"
  | Restrict i                      -> "Restrict:"^i
  | MsAsmBlock(a, s)                -> sprintf "MsAsmBlock:%s(%s)" a s
  | MsCdecl i                       -> "MsCdecl:"^i
  | MsStdcall i                     -> "MsStdcall:"^i
  | MsPragma i                      -> "MsPragma:"^i
  | MsWarningSpecifier i            -> "MsWarningSpecifier:"^i
  | MsProperty i                    -> "MsProperty:"^i
  | MsAttributeSpecifier            -> "MsAttributeSpecifier"
  | CallingConvention i             -> "CallingConvention:"^i
  | GnuAsmBlock(a, s)               -> sprintf "GnuAsmBlock:%s%s" a s
  | GnuAttribute i                  -> "GnuAttribute:"^i
  | GnuStatementExpression          -> "GnuStatementExpression"
  | ClassSpecifier                  -> "ClassSpecifier"
  | EnumSpecifier                   -> "EnumSpecifier"

(* BasicType *)
  | BasicType -> "BasicType"
  | Char     -> "Char"
  | Char8_t  -> "Char8_t"
  | Char16_t -> "Char16_t"
  | Char32_t -> "Char32_t"
  | Wchar_t  -> "Wchar_t"
  | Bool     -> "Bool"
  | Short    -> "Short"
  | Int      -> "Int"
  | Long     -> "Long"
  | Signed   -> "Signed"
  | Unsigned -> "Unsigned"
  | Float    -> "Float"
  | Double   -> "Double"
  | Void     -> "Void"
  | UnsignedInt -> "UnsignedInt"
  | UnsignedLong -> "UnsignedLong"

(* AccessSpecifier *)
  | AccessSpecifier -> "AccessSpecifier"
  | Private   -> "Private"
  | Protected -> "Protected"
  | Public    -> "Public"

(* AttributeSpecifier *)
  | AttributeSpecifier                  -> "AttributeSpecifier"
  | StandardAttributeSpecifier          -> "StandardAttributeSpecifier"
  | ContractAttributeSpecifier          -> "ContractAttributeSpecifier"
  | ContractAttributeSpecifierExpects   -> "ContractAttributeSpecifierExpects"
  | ContractAttributeSpecifierEnsures i -> "ContractAttributeSpecifierEnsures:"^i
  | ContractAttributeSpecifierAssert    -> "ContractAttributeSpecifierAssert"
  | AlignmentAttributeSpecifier b       -> sprintf "AlignmentAttributeSpecifier:%B" b

  | AttributeMacro i                -> "AttributeMacro:"^i

(* RefQualifier *)
  | RefQualifier       -> "RefQualifier"
  | RefQualifierAmp    -> "RefQualifierAmp"
  | RefQualifierAmpAmp -> "RefQualifierAmpAmp"

(* PlaceholderTypeSpecifier *)
  | PlaceholderTypeSpecifier         -> "PlaceholderTypeSpecifier"
  | PlaceholderTypeSpecifierAuto     -> "PlaceholderTypeSpecifierAuto"
  | PlaceholderTypeSpecifierDecltype -> "PlaceholderTypeSpecifierDecltype"

(* PtrOperator *)
  | PtrOperator       -> "PtrOperator"
  | PtrOperatorStar   -> "PtrOperatorStar"
  | PtrOperatorAmp    -> "PtrOperatorAmp"
  | PtrOperatorAmpAmp -> "PtrOperatorAmpAmp"
  | PtrOperatorHat    -> "PtrOperatorHat"
  | PtrOperatorMacro i -> "PtrOperatorMacro:"^i

(* Declarator *)
  | Declarator           -> "Declarator"
  | DeclaratorFunc       -> "DeclaratorFunc"
  | PtrDeclarator        -> "PtrDeclarator" (* PtrDeclarator *)
  | PtrDeclaratorPtr     -> "PtrDeclaratorPtr" (* PtrDeclarator *)
  | NoptrDeclarator      -> "NoptrDeclarator"      (* NoptrDeclarator *)
  | NoptrDeclaratorId    -> "NoptrDeclaratorId"    (* NoptrDeclarator *)
  | NoptrDeclaratorParen -> "NoptrDeclaratorParen" (* NoptrDeclarator *)
  | NoptrDeclaratorFunc  -> "NoptrDeclaratorFunc"  (* NoptrDeclarator *)
  | NoptrDeclaratorOldFunc -> "NoptrDeclaratorOldFunc"  (* NoptrDeclarator *)
  | NoptrDeclaratorArray -> "NoptrDeclaratorArray" (* NoptrDeclarator *)
  | DtorMacro i -> "DtorMacro:"^i

(* NoexceptSpecifier *)
  | NoexceptSpecifier      -> "NoexceptSpecifier"
  | NoexceptSpecifierThrow -> "NoexceptSpecifierThrow"
  | NoexceptSpecifierThrowAny -> "NoexceptSpecifierThrowAny"

(* VirtSpecifier *)
  | VirtSpecifier         -> "VirtSpecifier"
  | VirtSpecifierFinal    -> "VirtSpecifierFinal"
  | VirtSpecifierOverride -> "VirtSpecifierOverride"
  | VirtSpecifierMacro i  -> "VirtSpecifierMacro:"^i
  | VirtSpecifierMacroInvocation i  -> "VirtSpecifierMacroInvocation:"^i

(* StorageClassSpecifier *)
  | StorageClassSpecifier             -> "StorageClassSpecifier"
  | StorageClassSpecifierStatic       -> "StorageClassSpecifierStatic"
  | StorageClassSpecifierThread_local -> "StorageClassSpecifierThread_local"
  | StorageClassSpecifierExtern       -> "StorageClassSpecifierExtern"
  | StorageClassSpecifierMutable      -> "StorageClassSpecifierMutable"
  | StorageClassSpecifierRegister     -> "StorageClassSpecifierRegister"
  | StorageClassSpecifierVaxGlobaldef -> "StorageClassSpecifierVaxGlobaldef"

(* FunctionSpecifier *)
  | FunctionSpecifier        -> "FunctionSpecifier"
  | FunctionSpecifierVirtual -> "FunctionSpecifierVirtual"
  | ExplicitSpecifier        -> "ExplicitSpecifier"

(* ClassHead *)
  | ClassHead       -> "ClassHead"
  | ClassHeadClass  -> "ClassHeadClass"
  | ClassHeadStruct -> "ClassHeadStruct"
  | ClassHeadUnion  -> "ClassHeadUnion"
  | ClassHeadMacro i -> "ClassHeadMacro:"^i
  | ClassHeadMacroInvocation i -> "ClassHeadMacroInvocation:"^i
  | ClassHeadMsRefClass -> "ClassHeadMsRefClass"

(* EnumHead *)
  | EnumHead           -> "EnumHead"
  | EnumHeadEnum       -> "EnumHeadEnum"
  | EnumHeadEnumClass  -> "EnumHeadEnumClass"
  | EnumHeadEnumStruct -> "EnumHeadEnumStruct"
  | EnumHeadEnumMacro i -> "EnumHeadEnumMacro:"^i

(* TypeParameterKey *)
  | TypeParameterKey         -> "TypeParameterKey"
  | TypeParameterKeyClass    -> "TypeParameterKeyClass"
  | TypeParameterKeyTypename -> "TypeParameterKeyTypename"

(* FunctionBody *)
  | FunctionBody n      -> "FunctionBody:"^n
  | FunctionBodyDefault -> "FunctionBodyDefault"
  | FunctionBodyDelete  -> "FunctionBodyDelete"
  | FunctionTryBlock n  -> "FunctionTryBlock:"^n
  | FunctionBodyMacro i -> "FunctionBodyMacro:"^i
  | FunctionBodyMacroInvocation i -> "FunctionBodyMacroInvocation:"^i

(* DeclSpecifier *)
  | DeclSpecifier          -> "DeclSpecifier"
  | DeclSpecifierInline    -> "DeclSpecifierInline"
  | DeclSpecifierConstexpr -> "DeclSpecifierConstexpr"
  | DeclSpecifierConsteval -> "DeclSpecifierConsteval"
  | DeclSpecifierConstinit -> "DeclSpecifierConstinit"
  | DeclSpecifierTypedef   -> "DeclSpecifierTypedef"
  | DeclSpecifierFriend    -> "DeclSpecifierFriend"
  | DeclSpecifierMacro i   -> "DeclSpecifierMacro:"^i
  | DeclSpecifierMacroInvocation i -> "DeclSpecifierMacroInvocation:"^i

(* Requirement *)
  | Requirement           -> "Requirement"
  | SimpleRequirement     -> "SimpleRequirement"
  | TypeRequirement       -> "TypeRequirement"
  | CompoundRequirement   -> "CompoundRequirement"
  | ReturnTypeRequirement -> "ReturnTypeRequirement"
  | NestedRequirement     -> "NestedRequirement"

(* AbstractDeclarator *)
  | AbstractDeclarator           -> "AbstractDeclarator"
  | AbstractDeclaratorFunc       -> "AbstractDeclaratorFunc"
  | PtrAbstractDeclarator        -> "PtrAbstractDeclarator"
  | PtrAbstractDeclaratorPtr     -> "PtrAbstractDeclaratorPtr"
  | NoptrAbstractDeclarator      -> "NoptrAbstractDeclarator"
  | NoptrAbstractDeclaratorFunc  -> "NoptrAbstractDeclaratorFunc"
  | NoptrAbstractDeclaratorArray -> "NoptrAbstractDeclaratorArray"
  | NoptrAbstractDeclaratorParen -> "NoptrAbstractDeclaratorParen"

(* NoptrAbstractPackDeclarator *)
  | NoptrAbstractPackDeclaratorFunc -> "NoptrAbstractPackDeclaratorFunc"
  | NoptrAbstractPackDeclaratorArray -> "NoptrAbstractPackDeclaratorArray"

(* SimpleCapture *)
  | SimpleCapture i       -> "SimpleCapture:"^i
  | SimpleCaptureAmp i    -> "SimpleCaptureAmp:"^i
  | SimpleCaptureThis     -> "SimpleCaptureThis"
  | SimpleCaptureStarThis -> "SimpleCaptureStarThis"

(* InitCapture *)
  | InitCapture i    -> "InitCapture:"^i
  | InitCaptureAmp i -> "InitCaptureAmp:"^i

(* LambdaCapture *)
  | LambdaCapture           -> "LambdaCapture"
  | LambdaCaptureDefaultEq  -> "LambdaCaptureDefaultEq"
  | LambdaCaptureDefaultAmp -> "LambdaCaptureDefaultAmp"
  | LambdaCaptureMacroInvocation i -> "LambdaCaptureMacroInvocation:"^i

(* MemberDeclarator *)
  | MemberDeclarator           -> "MemberDeclarator"
  | MemberDeclaratorDecl       -> "MemberDeclaratorDecl"
  | MemberDeclaratorBitField i -> "MemberDeclaratorBitField:"^i

(* Label *)
  | Label i                        -> "Label:"^i
  | CaseLabel                      -> "CaseLabel"
  | RangedCaseLabel                -> "RangedCaseLabel"
  | DefaultLabel                   -> "DefaultLabel"
  | LabelMacroInvocation i         -> "LabelMacroInvocation:"^i

(* ContractLevel *)
  | ContractLevel                  -> "ContractLevel"
  | ContractLevelDefault           -> "ContractLevelDefault"
  | ContractLevelAudit             -> "ContractLevelAudit"
  | ContractLevelAxiom             -> "ContractLevelAxiom"

  | MemberSpecification            -> "MemberSpecification"

  | MemberDeclarationDecl          -> "MemberDeclarationDecl"

(* *)
  | Explicit                       -> "Explicit"
  | Virtual                        -> "Virtual"
  | Template                       -> "Template"
  | Noexcept                       -> "Noexcept"
  | Extern                         -> "Extern"
  | Inline                         -> "Inline"
  | Default                        -> "Default"
  | ColonColon                     -> "ColonColon"
  | Ellipsis                       -> "Ellipsis"

  | PureSpecifier                  -> "PureSpecifier"
  | BaseSpecifier                  -> "BaseSpecifier"
  | BaseClause                     -> "BaseClause"
  | BaseMacro i                    -> "BaseMacro:"^i
  | BaseSpecMacro i                -> "BaseSpecMacro:"^i
  | BaseSpecMacroInvocation i      -> "BaseSpecMacroInvocation:"^i
  | SuffixMacro i                  -> "SuffixMacro:"^i
  | ClassVirtSpecifierFinal        -> "ClassVirtSpecifierFinal"
  | ClassVirtSpecifierMsSealed     -> "ClassVirtSpecifierMsSealed"
  | ClassName i                    -> "ClassName:"^i
  | ClassHeadName n                -> "ClassHeadName:"^n
  | MacroArgument                  -> "MacroArgument"
  | NoptrNewDeclarator             -> "NoptrNewDeclarator"
  | NewInitializer                 -> "NewInitializer"
  | NewInitializerMacro i          -> "NewInitializer:"^i
  | ArgumentsMacro i               -> "ArgumentsMacro:"^i
  | ArgumentsMacroInvocation i     -> "ArgumentsMacroInvocation:"^i
  | NewDeclaratorPtr               -> "NewDeclaratorPtr"
  | NewDeclarator                  -> "NewDeclarator"
  | NewTypeId                      -> "NewTypeId"
  | NewPlacement                   -> "NewPlacement"
  | LambdaDeclarator               -> "LambdaDeclarator"
  | ParenthesizedInitList          -> "ParenthesizedInitList"
  | LambdaIntroducer               -> "LambdaIntroducer"
  | LambdaIntroducerMacro i        -> "LambdaIntroducerMacro:"^i
  | AbstractPackDeclarator         -> "AbstractPackDeclarator"
  | AbstractPack                   -> "AbstractPack"
  | RequirementBody                -> "RequirementBody"
  | RequirementParameterList       -> "RequirementParameterList"
  | MemInitializer                 -> "MemInitializer"
  | MemInitMacroInvocation i       -> "MemInitMacroInvocation:"^i
  | QualifiedTypeName              -> "QualifiedTypeName"
  | InitDeclarator n               -> "InitDeclarator:"^n
  | ConceptDefinition n            -> "ConceptDefinition:"^n
  | CtorInitializer                -> "CtorInitializer"
  | ConstraintLogicalOrExpression i  -> "ConstraintLogicalOrExpression:"^i
  | ConstraintLogicalAndExpression i -> "ConstraintLogicalAndExpression:"^i
  | RequiresClause                 -> "RequiresClause"
  | TypeParameter i                -> "TypeParameter:"^i
  | TemplateHead                   -> "TemplateHead"
  | EnclosingNamespaceSpecifier i  -> "EnclosingNamespaceSpecifier:"^i
  | Enumerator i                   -> "Enumerator:"^i
  | EnumeratorDefinition           -> "EnumeratorDefinition"
  | EnumeratorDefinitionMacro i    -> "EnumeratorDefinitionMacro:"^i
  | TypeMacroInvocation i          -> "TypeMacroInvocation:"^i
  | Condition                      -> "Condition"
  | ParameterDeclaration n         -> "ParameterDeclaration:"^n
  | ParameterDeclarationClause b   -> "ParameterDeclarationClause"^(if b then "Va" else "")
  | ParametersAndQualifiers        -> "ParametersAndQualifiers"
  | ParamDeclMacro i               -> "ParamDeclMacro:"^i
  | ParamDeclMacroInvocation i     -> "ParamDeclMacroInvocation:"^i
  | ParametersMacro i              -> "ParametersMacro:"^i
  | ParametersMacroInvocation i    -> "ParametersMacroInvocation:"^i
  | Handler                        -> "Handler"
  | ExceptionDeclaration           -> "ExceptionDeclaration"
  | ExpressionList                 -> "ExpressionList"
  | EqualInitializer               -> "EqualInitializer"
  | DesignatedInitializerClause    -> "DesignatedInitializerClause"
  | DesignatorField i              -> "DesignatorField:"^i
  | DesignatorIndex                -> "DesignatorIndex"
  | DesignatorRange                -> "DesignatorRange"
  | TrailingReturnType             -> "TrailingReturnType"
  | BracedInitList                 -> "BracedInitList"
  | ForRangeDeclaration            -> "ForRangeDeclaration"
  | Constexpr                      -> "Constexpr"
  | DefiningTypeId                 -> "DefiningTypeId"
  | EnumHeadName i                 -> "EnumHeadName:"^i
  | EnumBase                       -> "EnumBase"
  | QualifiedId                    -> "QualifiedId"
  | QualifiedNamespaceSpecifier n  -> "QualifiedNamespaceSpecifier:"^n
  | TypeName n                     -> "TypeName:"^n
  | ConversionDeclarator           -> "ConversionDeclarator"
  | ConversionTypeId               -> "ConversionTypeId"
  | Typename                       -> "Typename"
  | UsingDeclarator                -> "UsingDeclarator"
  | UsingEnumDeclarator            -> "UsingEnumDeclarator"
  | TypeConstraint n               -> "TypeConstraint:"^n
  | TypeId                         -> "TypeId"
  | DecltypeSpecifier              -> "DecltypeSpecifier"
  | SimpleTemplateId n             -> "SimpleTemplateId:"^n
  | Identifier i                   -> "Identifier:"^i
  | IdentifierMacroInvocation i    -> "IdentifierMacroInvocation:"^i
  | PpConcatenatedIdentifier       -> "PpConcatenatedIdentifier"
  | NestedNameSpecifier            -> "NestedNameSpecifier"
  | NestedNameSpecifierHead        -> "NestedNameSpecifierHead"
  | NestedNameSpecifierIdent i     -> "NestedNameSpecifierIdent:"^i
  | NestedNameSpecifierTempl i     -> "NestedNameSpecifierTempl:"^i
  | NestedNameSpecifierDeclty      -> "NestedNameSpecifierDeclty"
  | PackExpansion                  -> "PackExpansion"
  | AttributeUsingPrefix           -> "AttributeUsingPrefix"
  | Attribute                      -> "Attribute"
  | AttributeToken i               -> "AttributeToken:"^i
  | AttributeScopedToken i         -> "AttributeScopedToken:"^i
  | AttributeNamespace i           -> "AttributeNamespace:"^i
  | AttributeArgumentClause        -> "AttributeArgumentClause"
  | AttributeArgumentClauseMacro i -> "AttributeArgumentClauseMacro:"^i
  | BalancedToken                  -> "BalancedToken"
  | BalancedTokenParen             -> "BalancedTokenParen"
  | BalancedTokenBracket           -> "BalancedTokenBracket"
  | BalancedTokenBrace             -> "BalancedTokenBrace"
  | BalancedTokenSingle s          -> "BalancedTokenSingle:"^s
  | TokenSeq s                     -> "TokenSeq:"^s
  | ObjectLikeMacro                -> "ObjectLikeMacro"
  | FunctionLikeMacro mk           -> "FunctionLikeMacro:"^(macro_kind_to_string mk)
  | OperatorMacro i                -> "OperatorMacro:"^i
  | OperatorMacroInvocation i      -> "OperatorMacroInvocation:"^i
  | DefiningTypeSpecifierSeq       -> "DefiningTypeSpecifierSeq"
  | DeclSpecifierSeq               -> "DeclSpecifierSeq"
  | TypeSpecifierSeq               -> "TypeSpecifierSeq"
  | FunctionHead n                 -> "FunctionHead:"^n
  | FunctionHeadMacro i            -> "FunctionHeadMacro:"^i
  | AccessSpecAnnot i              -> "AccessSpecAnnot:"^i
  | EnumeratorMacroInvocation i    -> "EnumeratorMacroInvocation:"^i
  | AccessSpecMacro i              -> "AccessSpecMacro:"^i
  | CvMacro i                      -> "CvMacro:"^i
  | CvMacroInvocation i            -> "CvMacroInvocation:"^i
  | RefMacro i                     -> "RefMacro:"^i
  | RefMacroInvocation i           -> "RefMacroInvocation:"^i
  | OpeningBrace                   -> "OpeningBrace"
  | ClosingBrace                   -> "ClosingBrace"
  | OpeningBracket                 -> "OpeningBracket"
  | ClosingBracket                 -> "ClosingBracket"
  | DummyBody                      -> "DummyBody"
  | DummyDecl                      -> "DummyDecl"
  | DummyStmt                      -> "DummyStmt"
  | DummyExpr                      -> "DummyExpr"
  | DummyOp                        -> "DummyOp"
  | DummyDtor                      -> "DummyDtor"
  | GnuAsmBlockFragmented a        -> "GnuAsmBlockFragmented:"^a
  | GnuAsmFragment s               -> "GnuAsmFragment:"^s
  (*| GnuAsmQualifier i              -> "GnuAsmQualifier:"^i*)
  | DesignatorFieldOld i           -> "DesignatorFieldOld:"^i
  | DoxygenLine s                  -> "DoxygenLine:"^s
  | NoexceptSpecifierMacro i       -> "NoexceptSpecifierMacro:"^i
  | AttributeMacroInvocation i     -> "AttributeMacroInvocation:"^i
  | CudaExecutionConfiguration     -> "CudaExecutionConfiguration"
  | CudaKernelCall                 -> "CudaKernelCall"
  | SimpleTemplateIdM              -> "SimpleTemplateIdM"
  | NamespaceHead i                -> "NamespaceHead:"^i
  | NamedNamespaceDefinitionHead i -> "NamedNamespaceDefinitionHead:"^i
  | InitializerClause              -> "InitializerClause"
  | TemplParamMacroInvocation i    -> "TemplParamMacroInvocation:"^i
  | PostfixExpressionFunCallGuarded i -> "PostfixExpressionFunCallGuarded:"^i
  | PpIfSectionTemplDecl           -> "PpIfSectionTemplDecl"
  | PpIfSectionTryBlock            -> "PpIfSectionTryBlock"
  | Try                            -> "Try"
  | PpIfSectionHandler             -> "PpIfSectionHandler"
  | BlockHeadMacro i               -> "BlockHeadMacro:"^i
  | BlockEndMacro i                -> "BlockEndMacro:"^i
  | DeclStmtBlock                  -> "DeclStmtBlock"
  | AsmShader s                    -> "AsmShader:"^s
  | AsmName i                      -> "AsmName:"^i
  | AsmOperand                     -> "AsmOperand"
  | AsmDirective i                 -> "AsmDirective:"^i
  | VaArgs s                       -> "VaArgs:"^s
  | PtrMacro i                     -> "PtrMacro:"^i
  | At                             -> "At"
  | ClassBody                      -> "ClassBody"
  | Lparen                         -> "Lparen"
  | Rparen                         -> "Rparen"
  | Asm                            -> "Asm"
  | TemplateArguments              -> "TemplateArguments"
  | SuffixMacroInvocation i        -> "SuffixMacroInvocation:"^i

  | ObjcThrow                         -> "ObjcThrow"
  | ObjcSynchronized                  -> "ObjcSynchronized"
  | ObjcClassDeclarationList          -> "ObjcClassDeclarationList"
  | ObjcProtocolDeclarationList       -> "ObjcProtocolDeclarationList"
  | ObjcProtocolDeclaration i         -> "ObjcProtocolDeclaration:"^i
  | ObjcClassInterface i              -> "ObjcClassInterface:"^i
  | ObjcCategoryInterface(i, c)       -> "ObjcCategoryInterface:"^i^":"^c
  | ObjcSuperclass i                  -> "ObjcSuperclass:"^i
  | ObjcProtocolReferenceList         -> "ObjcProtocolReferenceList"
  | ObjcProtocolReferenceListMacro i  -> "ObjcProtocolReferenceListMacro:"^i
  | ObjcInstanceVariables             -> "ObjcInstanceVariables"
  | ObjcInstanceVariableDeclaration   -> "ObjcInstanceVariableDeclaration"
  | ObjcInterfaceDeclaration          -> "ObjcInterfaceDeclaration"
  | ObjcPrivate                       -> "ObjcPrivate"
  | ObjcPublic                        -> "ObjcPublic"
  | ObjcPackage                       -> "ObjcPackage"
  | ObjcProtected                     -> "ObjcProtected"
  | ObjcStructDeclaration             -> "ObjcStructDeclaration"
  | ObjcStructDeclarator              -> "ObjcStructDeclarator"
  | ObjcPropertyDeclaration           -> "ObjcPropertyDeclaration"
  | ObjcPropertyAttributesDeclaration -> "ObjcPropertyAttributesDeclaration"
  | ObjcClassMethodDeclaration        -> "ObjcClassMethodDeclaration"
  | ObjcInstanceMethodDeclaration     -> "ObjcInstanceMethodDeclaration"
  | ObjcMethodType                    -> "ObjcMethodType"
  | ObjcMethodSelector                -> "ObjcMethodSelector"
  | ObjcMethodSelectorPack            -> "ObjcMethodSelectorPack"
  | ObjcSelector i                    -> "ObjcSelector:"^i
  | ObjcSelectorMacro i               -> "ObjcSelectorMacro:"^i
  | ObjcKeywordSelector               -> "ObjcKeywordSelector"
  | ObjcKeywordDeclarator i           -> "ObjcKeywordDeclarator:"^i
  | ObjcSpecifierQualifier i          -> "ObjcSpecifierQualifier:"^i
  | ObjcProtocolName i                -> "ObjcProtocolName:"^i
  | ObjcClassName i                   -> "ObjcClassName:"^i
  | ObjcPropertyAttribute i           -> "ObjcPropertyAttribute:"^i
  | ObjcMessageExpression             -> "ObjcMessageExpression"
  | ObjcMessageSelector               -> "ObjcMessageSelector"
  | ObjcProtocolExpression            -> "ObjcProtocolExpression"
  | ObjcKeywordArgument i             -> "ObjcKeywordArgument:"^i
  | ObjcProtocolInterfaceDeclarationOptional -> "ObjcProtocolInterfaceDeclarationOptional"
  | ObjcProtocolInterfaceDeclarationRequired -> "ObjcProtocolInterfaceDeclarationRequired"
  | ObjcAutoreleasepool               -> "ObjcAutoreleasepool"
  | ObjcAvailable                     -> "ObjcAvailable"
  | ObjcSelectorExpression i          -> "ObjcSelectorExpression:"^i
  | ObjcEncodeExpression              -> "ObjcEncodeExpression"
  | ObjcTryBlock    -> "ObjcTryBlock"
  | ObjcTry         -> "ObjcTry"
  | ObjcCatchClause -> "ObjcCatchClause"
  | ObjcFinally     -> "ObjcFinally"
  | ObjcMethodMacroInvocation i -> "ObjcMethodMacroInvocation:"^i
  | ObjcKeywordName i -> "ObjcKeywordName:"^i
  | ObjcLiteral    -> "ObjcLiteral"
  | ObjcArray      -> "ObjcArray"
  | ObjcDictionary -> "ObjcDictionary"
  | ObjcKeyValue   -> "ObjcKeyValue"
  | ObjcClass      -> "ObjcClass"

  | SwiftArg i   -> "SwiftArg:"^i
  | SwiftFunCall -> "SwiftFunCall"

  | HugeArray(sz, c) -> sprintf "HugeArray(%d):%s\n" sz c
  | DslMacroArgument -> "DslMacroArgument"
  | ParametersAndQualifiersList -> "ParametersAndQualifiersList"
  | NestedFunctionDefinition n -> "NestedFunctionDefinition:"^n
  | PragmaMacro i -> "PragmaMacro:"^i
  | PragmaMacroInvocation i -> "PragmaMacroInvocation:"^i
  | MockQualifier i -> "MockQualifier:"^i

  | ClassBodyHeadMacro i -> "ClassBodyHeadMacro:"^i
  | ClassBodyEndMacro i -> "ClassBodyEndMacro:"^i
  | ClassBodyHeadMacroInvocation i -> "ClassBodyHeadMacroInvocation:"^i
  | ClassBodyEndMacroInvocation i -> "ClassBodyEndMacroInvocation:"^i
  | InitHeadMacroInvocation i -> "InitHeadMacroInvocation:"^i
  | InitEndMacroInvocation i -> "InitEndMacroInvocation:"^i
  | InitDeclaration -> "InitDeclaration"
  | LiteralMacroArgument s -> "LiteralMacroArgument:"^s


let to_simple_string = function
  | DUMMY -> "DUMMY"
  | EMPTY -> "EMPTY"
  | AMBIGUOUS_CONSTRUCT -> "AMBIGUOUS_CONSTRUCT"
  | PARTIAL_CONSTRUCT   -> "PARTIAL_CONSTRUCT"
  | DECLS               -> "DECLS"
  | MEM_DECLS           -> "MEM_DECLS"
  | EXPRS               -> "EXPRS"
  | STMTS               -> "STMTS"
  | INITS               -> "INITS"
  | LABELS              -> "LABELS"
  | SPECS               -> "SPECS"
  | ETORS               -> "ETORS"
  | OBJC_DECLS          -> "OBJC_DECLS"
  | TEMPL_PARAMS        -> "TEMPL_PARAMS"
  | TEMPL_ARGS          -> "TEMPL_ARGS"
  | DELIM_MACRO i       -> i
  | DELIM_MACRO_ i      -> i
  | Q_PROPERTY          -> "Q_PROPERTY"
  | ERROR s             -> s

  | TranslationUnit -> "<translation-unit>"

(* PpDirective *)
  | PpInclude s              -> "#include "^s
  | PpDefine i               -> "#define "^i
  | PpUndef i                -> "#undef "^i
  | PpLine (j, s)            -> sprintf "#line %d %s" j s
  | PpError s                -> "#error "^s
  | PpPragma s               -> "#pragma "^s
  | PpNull                   -> "#"
  | PpMarker(j, s, jl)       -> sprintf "# %d %s %s" j s
        (String.concat " " (List.map string_of_int jl))
  | PpIf _                   -> "#if"
  | PpIfdef i                -> "#ifdef "^i
  | PpIfndef i               -> "#ifndef "^i
  | PpElif _                 -> "#elif"
  | PpElse _                 -> "#else"
  | PpEndif _                -> "#endif"
  | PpUnknown s              -> "#"^s
  | PpIfSection(j, x)        -> sprintf "<if-section:%d:%s>" j x
  | PpIfSectionFuncDef i     -> i
  | PpIfSectionAltFuncDef    -> "<if-section-alt-func-def>"
  | PpIfSectionBroken        -> "<if-section-broken>"
  | PpIfSectionBrokenIf      -> "<if-section-broken-if>"
  | PpIfSectionBrokenFuncDef -> "<if-section-broken-func-def>"
  | PpIfSectionBrokenDtorFunc -> "<if-section-broken-dtor-func>"
  | PpIfSectionCondExpr      -> "<if-section-cond-expr>"
  | PpIfSectionLogicalAnd    -> "<if-section-logical-and>"
  | PpIfSectionLogicalOr     -> "<if-section-logical-or>"
  | PpIfGroup x              -> sprintf "<if-group:%s>" x
  | PpElifGroup x            -> sprintf "<elif-group:%s>" x
  | PpElseGroup x            -> sprintf "<else-group:%s>" x
  | PpStringized s           -> s
  | PpMacroParam s           -> s
  | PpImport s               -> "#import "^s

  | OmpDirective s           -> "#pragma omp "^s
  | AccDirective s           -> "#pragma acc "^s


(* Declaration *)
  | SimpleDeclaration             -> "<simple-declaration>"
  | AsmDefinition s               -> sprintf "asm(%s)" s
  | NamespaceAliasDefinition i    -> sprintf "namespace %s =" i
  | UsingDeclaration              -> "using"
  | UsingEnumDeclaration          -> "using enum"
  | UsingDirective i              -> "using namespace "^i
  | Static_assertDeclaration      -> "static_assert"
  | AliasDeclaration i            -> "using "^i
  | OpaqueEnumDeclaration         -> "<opaque-enum-declaration>"
  | OpaqueEnumDeclarationClass    -> "class"
  | OpaqueEnumDeclarationStruct   -> "struct"
  | OpaqueEnumDeclarationMacro i  -> i
  | NodeclspecFunctionDeclaration -> "<nodeclspec-function-declaration>"
  | FunctionDefinition n          -> sprintf "<function-definition:%s>" n
  | TemplateDeclaration           -> "<template-declaration>"
  | DeductionGuide n              -> sprintf "<deduction-guide:%s>" n
  | ExplicitInstantiation         -> "template"
  | ExplicitSpecialization        -> "template<>"
  | ExportDeclaration             -> "export"
  | LinkageSpecification s        -> "extern "^s
  | NamedNamespaceDefinition i    -> "namespace "^i
  | UnnamedNamespaceDefinition    -> "namespace"
  | NestedNamespaceDefinition i   -> "namespace "^i
  | NamespaceDefinitionMacro i    -> i
  | EmptyDeclaration              -> ";"
  | AttributeDeclaration          -> "<attribute-declaration>"
  | DeclarationMacro i            -> i
  | DeclarationMacroInvocation i  -> i
  | DeclarationMacroInvocationInvocation -> "<declaration-macro-invocation-invocation>"
  | DeclarationMacroInvocationArrow -> "<declaration-macro-invocation-arrow>"
  | DeclarationMacroInvocationDot -> "<declaration-macro-invocation-dot>"
  | ImportDeclaration s           -> "import "^s


(* Statement *)
  | Statement                  -> "<statement>"
  | ExpressionStatement        -> "<expression-statement>"
  | DeclarationStatement       -> "DeclarationStatement"
  | TryBlock                   -> "TryBlock"
  | LabeledStatement           -> "LabeledStatement"
  | SelectionStatement         -> "SelectionStatement"
  | IfStatement                -> "if"
  | ElseStatement              -> "else"
  | SwitchStatement            -> "switch"
  (*| EmptyStatement             -> "<empty-statement>"*)
  | CompoundStatement          -> "<compound-statement>"
  | IterationStatement         -> "<iteration-statement>"
  | WhileStatement             -> "while"
  | DoStatement                -> "do"
  | ForStatement               -> "for"
  | ForInStatement             -> "for"
  | RangeBasedForStatement     -> "for"
  | JumpStatement              -> "<jump-statement>"
  | BreakStatement             -> "break;"
  | ContinueStatement          -> "continue;"
  | ReturnStatement            -> "return"
  | GotoStatement i            -> "goto "^i
  | ComputedGotoStatement      -> "goto"
  | CoroutineReturnStatement   -> "co_return"
  | StatementMacroInvocation i -> i
  | StatementMacro i           -> i
  | IterationMacroInvocation i -> i
  | IterationMacro i           -> i

(* Expression *)
  | This                              -> "this"
  | ParenthesizedExpression           -> "()"
  | RequiresExpression                -> "requires"
  | FoldExpression                    -> "<fold-expression>"
  | LambdaExpression                  -> "<lambda-expression>"
  | LogicalOrExpression i             -> i
  | LogicalAndExpression i            -> i
  | InclusiveOrExpression i           -> i
  | ExclusiveOrExpression i           -> i
  | AndExpression _                   -> "<and-expression>"
  | EqualityExpression                -> "<equality-expression>"
  | EqualityExpressionEq              -> "=="
  | EqualityExpressionStrictEq        -> "==="
  | EqualityExpressionNeq i           -> i
  | RelationalExpression              -> "<relational-expression>"
  | RelationalExpressionLt            -> "<"
  | RelationalExpressionGt            -> ">"
  | RelationalExpressionLe            -> "<="
  | RelationalExpressionGe            -> ">="
  | CompareExpression                 -> "<=>"
  | ShiftExpression                   -> "<shift-expression>"
  | ShiftExpressionLeft               -> "<<"
  | ShiftExpressionRight              -> ">>"
  | ShiftExpressionRightU             -> ">>>"
  | AdditiveExpression                -> "<additive-expression>"
  | AdditiveExpressionAdd             -> "+"
  | AdditiveExpressionSubt            -> "-"
  | MultiplicativeExpression          -> "<multiplicative-expression>"
  | MultiplicativeExpressionMult      -> "*"
  | MultiplicativeExpressionDiv       -> "/"
  | MultiplicativeExpressionMod       -> "%"
  | PmExpression                      -> "<pm-expression>"
  | PmExpressionClass                 -> ".*"
  | PmExpressionPtr                   -> "->*"
  | CastExpression                    -> "<cast-expression>"
  | CompoundLiteralExpression         -> "<compound-literal-expression>"
  | UnaryExpression                   -> "<unary-expression>"
  | UnaryExpressionIncr               -> "++"
  | UnaryExpressionDecr               -> "--"
  | UnaryExpressionInd                -> "*"
  | UnaryExpressionAddr               -> "&"
  | UnaryExpressionLabelAddr          -> "&&"
  | UnaryExpressionPlus               -> "+"
  | UnaryExpressionMinus              -> "-"
  | UnaryExpressionNeg i              -> i
  | UnaryExpressionCompl i            -> i
  | UnaryExpressionSizeof             -> "sizeof"
  | UnaryExpressionSizeofPack i       -> sprintf "sizeof ... (%s)" i
  | UnaryExpressionAlignof            -> "alignof"
  | NoexceptExpression                -> "noexcept"
  | PostfixExpression                 -> "<postfix-expression>"
  | PostfixExpressionSubscr           -> "<subscripting>"
  | PostfixExpressionFunCall          -> "<function-call>"
  | PostfixExpressionFunCallMacro i   -> i
  | PostfixExpressionExplicitTypeConv -> "<explicit-type-conversion>"
  | PostfixExpressionExplicitTypeConvExpr   -> "<explicit-type-conversion-expr>"
  | PostfixExpressionExplicitTypeConvBraced -> "<explicit-type-conversion-braced>"
  | PostfixExpressionDot              -> "."
  | PostfixExpressionArrow            -> "->"
  | PostfixExpressionIncr             -> "++"
  | PostfixExpressionDecr             -> "--"
  | PostfixExpressionTypeid           -> "typeid"
  | PostfixExpressionTypeidExpr       -> "typeid"
  | PostfixExpressionTypeidTy         -> "typeid"
  | PostfixExpressionDynamic_cast     -> "dynamic_cast"
  | PostfixExpressionStatic_cast      -> "static_cast"
  | PostfixExpressionReinterpret_cast -> "reinterpret_cast"
  | PostfixExpressionConst_cast       -> "const_cast"
  | AssignmentExpression              -> "<assignment-expression>"
  | AssignmentExpressionOverloaded i  -> i
  | AssignmentExpressionEq            -> "="
  | AssignmentExpressionPlus          -> "+="
  | AssignmentExpressionMinus         -> "-="
  | AssignmentExpressionMult          -> "*="
  | AssignmentExpressionDiv           -> "/="
  | AssignmentExpressionMod           -> "%="
  | AssignmentExpressionShiftLeft     -> "<<="
  | AssignmentExpressionShiftRight    -> ">>="
  | AssignmentExpressionAnd i         -> i
  | AssignmentExpressionXor i         -> i
  | AssignmentExpressionOr i          -> i
  | ThrowExpression                   -> "throw"
  | ExpressionPair                    -> "<expression-pair>"
  | ConditionalExpression             -> "<conditional-expression>"
  | NewExpression                     -> "new"
  | RefNewExpression                  -> "ref new"
  | DeleteExpression                  -> "delete"
  | DeleteExpressionBracket           -> "delete[]"
  | YieldExpression                   -> "co_yield"
  | AwaitExpression                   -> "co_await"
  | BlockLiteralExpression            -> "<block-literal-expression>"

  | ExpressionMacroInvocation i       -> i
  | LogicalOrMacroInvocation i        -> i
  | DefinedMacroExpression i          -> sprintf "defined(%s)" i
  | HasIncludeExpression s            -> sprintf "__has_include(%s)" s
  | HasAttributeExpression            -> "__has_cpp_attribute"

(* Literal *)
  | Literal                       -> "<literal>"
  | IntegerLiteral v              -> v
  | CharacterLiteral v            -> v
  | FloatingLiteral v             -> v
  | StringLiteral v               -> v
  | StringMacro i                 -> i
  | BooleanLiteral v              -> v
  | Nullptr                       -> "nullptr"
  | ConcatenatedString            -> "<concatenated-string>"
  | UserDefinedCharacterLiteral v -> v
  | UserDefinedStringLiteral v    -> v
  | UserDefinedFloatingLiteral v  -> v
  | UserDefinedIntegerLiteral v   -> v
  | LiteralMacro i                -> i
  | LiteralMacroInvocation i      -> i

(* UnqualifiedId *)
  | UnqualifiedId        -> "<unqualified-id>"
  | OperatorFunctionId   -> "<operator-function-id>"
  | ConversionFunctionId -> "<conversion-function-id>"
  | LiteralOperatorId s  -> s
  | Destructor           -> "<destructor>"
  | TemplateId           -> "<template-id>"
  | TemplateIdOp         -> "<template-id-op>"
  | TemplateIdLit        -> "<template-id-lit>"

(* Operator *)
  | Operator      -> "<operator>"
  | New           -> "new"
  | Delete        -> "delete"
  | NewBracket    -> "new[]"
  | DeleteBracket -> "delete[]"
  | Parentheses   -> "()"
  | Brackets      -> "[]"
  | MinusGt       -> "->"
  | MinusGtStar   -> "->*"
  | Tilde i       -> i
  | Exclam i      -> i
  | Plus          -> "+"
  | Minus         -> "-"
  | Star          -> "*"
  | Slash         -> "/"
  | Perc          -> "%"
  | Hat i         -> i
  | Amp i         -> i
  | Bar i         -> i
  | Eq            -> "="
  | PlusEq        -> "+="
  | MinusEq       -> "-="
  | StarEq        -> "*="
  | SlashEq       -> "/="
  | PercEq        -> "%="
  | HatEq i       -> i
  | AmpEq i       -> i
  | BarEq i       -> i
  | EqEq          -> "=="
  | ExclamEq i    -> i
  | Lt            -> "<"
  | Gt            -> ">"
  | LtEq          -> "<="
  | GtEq          -> ">="
  | LtEqGt        -> "<=>"
  | AmpAmp i      -> i
  | BarBar i      -> i
  | LtLt          -> "<<"
  | GtGt          -> ">>"
  | LtLtEq        -> "<<="
  | GtGtEq        -> ">>="
  | PlusPlus      -> "++"
  | MinusMinus    -> "--"
  | Comma         -> ","
  | Semicolon     -> ";"
  | Colon         -> ":"
  | Co_await      -> "co_await"

  | DotStar       -> ".*"
  | Dot           -> "."

(* DefiningTypeSpecifier *)
  | DefiningTypeSpecifier           -> "<defining-type-specifier>"
  | SimpleTypeSpecifier i           -> sprintf "<simple-type-specifier:%s>" i
  | ElaboratedTypeSpecifier         -> "<elaborated-type-specifier>"
  | ElaboratedTypeSpecifierClass i  -> "class "^i
  | ElaboratedTypeSpecifierStruct i -> "struct "^i
  | ElaboratedTypeSpecifierUnion i  -> "union "^i
  | ElaboratedTypeSpecifierEnum i   -> "enum "^i
  | TypenameSpecifier i             -> "typename "^i
  | CvQualifier                     -> "<cv-qualifier>"
  | TypeMacro i                     -> i
  | Const                           -> "const"
  | Volatile                        -> "volatile"
  | Restrict i                      -> i

  | MsAsmBlock(a, s)                -> sprintf "%s {%s}" a s
  | MsCdecl i                       -> i
  | MsStdcall i                     -> i
  | MsPragma i                      -> i
  | MsWarningSpecifier i            -> i
  | MsProperty i                    -> sprintf "property %s" i
  | MsAttributeSpecifier            -> "<ms-attribute-specifier>"

  | CallingConvention i             -> i
  | GnuAsmBlock(a, s)               -> sprintf "%s %s" a s
  | GnuAttribute i                  -> i
  | GnuStatementExpression          -> "<gnu-statement-expression>"

  | ClassSpecifier                  -> "<class-specifier>"
  | EnumSpecifier                   -> "<enum-specifier>"

(* BasicType *)
  | BasicType -> "<basic-type>"
  | Char     -> "char"
  | Char8_t  -> "char8_t"
  | Char16_t -> "char16_t"
  | Char32_t -> "char32_t"
  | Wchar_t  -> "wchar_t"
  | Bool     -> "bool"
  | Short    -> "short"
  | Int      -> "int"
  | Long     -> "long"
  | Signed   -> "signed"
  | Unsigned -> "unsigned"
  | Float    -> "float"
  | Double   -> "double"
  | Void     -> "void"
  | UnsignedInt -> "unsigned int"
  | UnsignedLong -> "unsigned long"

(* AccessSpecifier *)
  | AccessSpecifier -> "<access-specifier>"
  | Private   -> "private"
  | Protected -> "protected"
  | Public    -> "public"

(* AttributeSpecifier *)
  | AttributeSpecifier                  -> "<attribute-specifier>"
  | StandardAttributeSpecifier          -> "[[]]"
  | ContractAttributeSpecifier          -> "<contract-attribute-specifier>"
  | ContractAttributeSpecifierExpects   -> "[[expects]]"
  | ContractAttributeSpecifierEnsures i -> sprintf "[[ensures %s]]" i
  | ContractAttributeSpecifierAssert    -> "[[assert]]"
  | AlignmentAttributeSpecifier b       -> sprintf "alignas(%s)" (if b then "..." else "")

  | AttributeMacro i                -> i

(* RefQualifier *)
  | RefQualifier       -> "<ref-qualifier>"
  | RefQualifierAmp    -> "&"
  | RefQualifierAmpAmp -> "&&"

(* PlaceholderTypeSpecifier *)
  | PlaceholderTypeSpecifier         -> "<placeholder-type-specifier>"
  | PlaceholderTypeSpecifierAuto     -> "auto"
  | PlaceholderTypeSpecifierDecltype -> "decltype(auto)"

(* PtrOperator *)
  | PtrOperator       -> "<ptr-operator>"
  | PtrOperatorStar   -> "*"
  | PtrOperatorAmp    -> "&"
  | PtrOperatorAmpAmp -> "&&"
  | PtrOperatorHat    -> "^"
  | PtrOperatorMacro i -> i

(* Declarator *)
  | Declarator           -> "<declarator>"
  | DeclaratorFunc       -> "<declarator-func>"
  | PtrDeclarator        -> "<ptr-declarator>" (* PtrDeclarator *)
  | PtrDeclaratorPtr     -> "<ptr-declarator-ptr>" (* PtrDeclarator *)
  | NoptrDeclarator      -> "<noptr-declarator>"       (* NoptrDeclarator *)
  | NoptrDeclaratorId    -> "<noptr-declarator-id>"    (* NoptrDeclarator *)
  | NoptrDeclaratorParen -> "<noptr-declarator-paren>" (* NoptrDeclarator *)
  | NoptrDeclaratorFunc  -> "<noptr-declarator-func>"     (* NoptrDeclarator *)
  | NoptrDeclaratorOldFunc -> "<noptr-declarator-old-func>"  (* NoptrDeclarator *)
  | NoptrDeclaratorArray -> "<noptr-declarator-array>"     (* NoptrDeclarator *)
  | DtorMacro i -> i

(* NoexceptSpecifier *)
  | NoexceptSpecifier      -> "noexcept()"
  | NoexceptSpecifierThrow -> "throw()"
  | NoexceptSpecifierThrowAny -> "throw(...)"

(* VirtSpecifier *)
  | VirtSpecifier         -> "<virt-specifier>"
  | VirtSpecifierFinal    -> "final"
  | VirtSpecifierOverride -> "override"
  | VirtSpecifierMacro i  -> i
  | VirtSpecifierMacroInvocation i  -> i

(* StorageClassSpecifier *)
  | StorageClassSpecifier             -> "<storage-class-specifier>"
  | StorageClassSpecifierStatic       -> "static"
  | StorageClassSpecifierThread_local -> "thread_local"
  | StorageClassSpecifierExtern       -> "extern"
  | StorageClassSpecifierMutable      -> "mutable"
  | StorageClassSpecifierRegister     -> "register"
  | StorageClassSpecifierVaxGlobaldef -> "globaldef"

(* FunctionSpecifier *)
  | FunctionSpecifier        -> "<function-specifier>"
  | FunctionSpecifierVirtual -> "virtual"
  | ExplicitSpecifier        -> "explicit"

(* ClassHead *)
  | ClassHead       -> "<class-head>"
  | ClassHeadClass  -> "class"
  | ClassHeadStruct -> "struct"
  | ClassHeadUnion  -> "union"
  | ClassHeadMacro i -> i
  | ClassHeadMacroInvocation i -> i
  | ClassHeadMsRefClass -> "ref class"

(* EnumHead *)
  | EnumHead           -> "<enum-head>"
  | EnumHeadEnum       -> "enum"
  | EnumHeadEnumClass  -> "enum class"
  | EnumHeadEnumStruct -> "enum struct"
  | EnumHeadEnumMacro i -> i

(* TypeParameterKey *)
  | TypeParameterKey         -> "<type-parameter-key>"
  | TypeParameterKeyClass    -> "class"
  | TypeParameterKeyTypename -> "typename"

(* FunctionBody *)
  | FunctionBody n      -> sprintf "<function-body:%s>" n
  | FunctionBodyDefault -> "= default;"
  | FunctionBodyDelete  -> "= delete;"
  | FunctionTryBlock n  -> sprintf "<function-try-block:%s>" n
  | FunctionBodyMacro i -> i
  | FunctionBodyMacroInvocation i -> i

(* DeclSpecifier *)
  | DeclSpecifier          -> "<decl-specifier>"
  | DeclSpecifierInline    -> "inline"
  | DeclSpecifierConstexpr -> "constexpr"
  | DeclSpecifierConsteval -> "consteval"
  | DeclSpecifierConstinit -> "constinit"
  | DeclSpecifierTypedef   -> "typedef"
  | DeclSpecifierFriend    -> "friend"
  | DeclSpecifierMacro i   -> i
  | DeclSpecifierMacroInvocation i -> i

(* Requirement *)
  | Requirement           -> "<requirement>"
  | SimpleRequirement     -> "<simple-requirement>"
  | TypeRequirement       -> "<type-requirement>"
  | CompoundRequirement   -> "<compound-requirement>"
  | ReturnTypeRequirement -> "<return-type-requirement>"
  | NestedRequirement     -> "requires"

(* AbstractDeclarator *)
  | AbstractDeclarator           -> "<abstract-declarator>"
  | AbstractDeclaratorFunc       -> "<abstract-declarator-func>"
  | PtrAbstractDeclarator        -> "<ptr-abstract-declarator>"
  | PtrAbstractDeclaratorPtr     -> "<ptr-abstract-declarator-ptr>"
  | NoptrAbstractDeclarator      -> "<noptr-abstract-declarator>"
  | NoptrAbstractDeclaratorFunc  -> "<noptr-abstract-declarator-func>"
  | NoptrAbstractDeclaratorArray -> "<noptr-abstract-declarator-array>"
  | NoptrAbstractDeclaratorParen -> "<noptr-abstract-declarator-paren>"

(* NoptrAbstractPackDeclarator *)
  | NoptrAbstractPackDeclaratorFunc -> "<noptr-abstract-pack-declarator-func>"
  | NoptrAbstractPackDeclaratorArray -> "<noptr-abstract-pack-declarator-array>"

(* SimpleCapture *)
  | SimpleCapture i       -> i
  | SimpleCaptureAmp i    -> "&"^i
  | SimpleCaptureThis     -> "this"
  | SimpleCaptureStarThis -> "*this"

(* InitCapture *)
  | InitCapture i    -> i
  | InitCaptureAmp i -> "&"^i

(* LambdaCapture *)
  | LambdaCapture           -> "<lambda-capture>"
  | LambdaCaptureDefaultEq  -> "="
  | LambdaCaptureDefaultAmp -> "&"
  | LambdaCaptureMacroInvocation i -> i

(* MemberDeclarator *)
  | MemberDeclarator           -> "<member-declarator>"
  | MemberDeclaratorDecl       -> "<member-declarator-decl>"
  | MemberDeclaratorBitField i -> ":"^i

(* Label *)
  | Label i                        -> i^":"
  | CaseLabel                      -> "case:"
  | RangedCaseLabel                -> "case:"
  | DefaultLabel                   -> "default:"
  | LabelMacroInvocation i         -> i

(* ContractLevel *)
  | ContractLevel                  -> "<contract-level>"
  | ContractLevelDefault           -> "default"
  | ContractLevelAudit             -> "audit"
  | ContractLevelAxiom             -> "axiom"

  | MemberSpecification            -> "<member-specification>"

  | MemberDeclarationDecl          -> "<member-declaration-decl>"

(* *)
  | Explicit                       -> "explicit"
  | Virtual                        -> "virtual"
  | Template                       -> "template"
  | Noexcept                       -> "noexcept"
  | Extern                         -> "extern"
  | Inline                         -> "inline"
  | Default                        -> "default"
  | Constexpr                      -> "constexpr"
  | Typename                       -> "typename"
  | ColonColon                     -> "::"
  | Ellipsis                       -> "..."

  | PureSpecifier                  -> "= 0"
  | BaseSpecifier                  -> "<base-specifier>"
  | BaseClause                     -> "<base-clause>"
  | BaseMacro i                    -> i
  | BaseSpecMacro i                -> i
  | BaseSpecMacroInvocation i      -> i
  | SuffixMacro i                  -> i
  | ClassVirtSpecifierFinal        -> "final"
  | ClassVirtSpecifierMsSealed     -> "sealed"
  | ClassName i                    -> i
  | ClassHeadName n                -> n
  | MacroArgument                  -> "<macro-argument>"
  | NoptrNewDeclarator             -> "<noptr-new-declarator>"
  | NewInitializer                 -> "<new-initializer>"
  | NewInitializerMacro i          -> i
  | ArgumentsMacro i               -> i
  | ArgumentsMacroInvocation i     -> i
  | NewDeclaratorPtr               -> "<new-declarator-ptr>"
  | NewDeclarator                  -> "<new-declarator>"
  | NewTypeId                      -> "<new-type-id>"
  | NewPlacement                   -> "<new-placement>"
  | LambdaDeclarator               -> "<lambda-declarator>"
  | ParenthesizedInitList          -> "<parenthesized-init-list>"
  | LambdaIntroducer               -> "<lambda-introducer>"
  | LambdaIntroducerMacro i        -> i
  | AbstractPackDeclarator         -> "<abstract-pack-declarator>"
  | AbstractPack                   -> "<abstract-pack>"
  | RequirementBody                -> "<requirement-body>"
  | RequirementParameterList       -> "<requirement-parameter-list>"
  | MemInitializer                 -> "<mem-initializer>"
  | MemInitMacroInvocation i       -> i
  | QualifiedTypeName              -> "<qualified-type-name>"
  | InitDeclarator n               -> sprintf "<init-declarator:%s>" n
  | ConceptDefinition n            -> "concept "^n
  | CtorInitializer                -> "<ctor-initializer>"
  | ConstraintLogicalOrExpression _  -> "<constraint-logical-or-expression>"
  | ConstraintLogicalAndExpression _ -> "<constraint-logical-and-expression>"
  | RequiresClause                 -> "<requires-clause>"
  | TypeParameter i                -> i
  | TemplateHead                   -> "<template-head>"
  | EnclosingNamespaceSpecifier i  -> i
  | Enumerator i                   -> i
  | EnumeratorDefinition           -> "<enumerator-definition>"
  | EnumeratorDefinitionMacro i    -> i
  | TypeMacroInvocation i          -> i
  | Condition                      -> "<condition>"
  | ParameterDeclaration n         -> sprintf "<parameter-declaration:%s>" n
  | ParameterDeclarationClause b   ->
      sprintf "<parameter-declaration-clause%s>" (if b then "-va" else "")
  | ParametersAndQualifiers        -> "<parameters-and-qualifiers>"
  | ParamDeclMacro i               -> i
  | ParamDeclMacroInvocation i     -> i
  | ParametersMacro i              -> i
  | ParametersMacroInvocation i    -> i
  | Handler                        -> "<handler>"
  | ExceptionDeclaration           -> "<exception-declaration>"
  | ExpressionList                 -> "<expression-list>"
  | EqualInitializer               -> "<equal-initializer>"
  | DesignatedInitializerClause    -> "<designated-initializer-clause>"
  | DesignatorField i              -> "."^i
  | DesignatorIndex                -> "[]"
  | DesignatorRange                -> "[...]"
  | TrailingReturnType             -> "<trailing-return-type>"
  | BracedInitList                 -> "<braced-init-list>"
  | ForRangeDeclaration            -> "<for-range-declaration>"
  | DefiningTypeId                 -> "<defining-type-id>"
  | EnumHeadName i                 -> i
  | EnumBase                       -> "<enum-base>"
  | QualifiedId                    -> "<qualified-id>"
  | QualifiedNamespaceSpecifier n  -> sprintf "<qualified-namespace-specifier:%s>" n
  | TypeName n                     -> n
  | ConversionDeclarator           -> "<conversion-dDeclarator>"
  | ConversionTypeId               -> "<conversion-type-id>"
  | UsingDeclarator                -> "<using-declarator>"
  | UsingEnumDeclarator            -> "<using-enum-declarator>"
  | TypeConstraint n               -> sprintf "<type-constraint:%s>" n
  | TypeId                         -> "<type-id>"
  | DecltypeSpecifier              -> "decltype()"
  | SimpleTemplateId n             -> n
  | Identifier i                   -> i
  | IdentifierMacroInvocation i    -> i
  | PpConcatenatedIdentifier       -> "##"
  | NestedNameSpecifier            -> "<nested-name-specifier>"
  | NestedNameSpecifierHead        -> "::"
  | NestedNameSpecifierIdent i     -> i
  | NestedNameSpecifierTempl i     -> i
  | NestedNameSpecifierDeclty      -> "decltype()"
  | PackExpansion                  -> "..."
  | AttributeUsingPrefix           -> "using:"
  | Attribute                      -> "<attribute>"
  | AttributeToken i               -> i
  | AttributeScopedToken i         -> "::"^i
  | AttributeNamespace i           -> i
  | AttributeArgumentClause        -> "AttributeArgumentClause"
  | AttributeArgumentClauseMacro i -> i
  | BalancedToken                  -> "<balanced-token>"
  | BalancedTokenParen             -> "(<balanced-token>)"
  | BalancedTokenBracket           -> "[<balanced-token>]"
  | BalancedTokenBrace             -> "{<balanced-token>}"
  | BalancedTokenSingle s          -> s
  | TokenSeq s                     -> s
  | ObjectLikeMacro                -> "<object-like-macro>"
  | FunctionLikeMacro mk           ->
      sprintf "<function-like-macro%s>" (macro_kind_to_string mk)
  | OperatorMacro i                -> i
  | OperatorMacroInvocation i      -> i
  | DefiningTypeSpecifierSeq       -> "<defining-type-specifier-seq>"
  | DeclSpecifierSeq               -> "<decl-specifier-seq>"
  | TypeSpecifierSeq               -> "<type-specifier-seq>"
  | FunctionHead n                 -> sprintf "<function-head:%s>" n
  | FunctionHeadMacro i            -> i
  | AccessSpecAnnot i              -> i
  | EnumeratorMacroInvocation i    -> i
  | AccessSpecMacro i              -> i
  | CvMacro i                      -> i
  | CvMacroInvocation i            -> i
  | RefMacro i                     -> i
  | RefMacroInvocation i           -> i
  | OpeningBrace                   -> "{"
  | ClosingBrace                   -> "}"
  | OpeningBracket                 -> "["
  | ClosingBracket                 -> "]"
  | DummyBody                      -> "<dummy-body>"
  | DummyDecl                      -> "<dummy-decl>"
  | DummyStmt                      -> "<dummy-stmt>"
  | DummyExpr                      -> "<dummy-expr>"
  | DummyOp                        -> "<dummy-op>"
  | DummyDtor                      -> "<dummy-dtor>"
  | GnuAsmBlockFragmented a        -> a
  | GnuAsmFragment s               -> s
  (*| GnuAsmQualifier i              -> i*)
  | DesignatorFieldOld i           -> i^":"
  | DoxygenLine s                  -> s
  | NoexceptSpecifierMacro i       -> i
  | AttributeMacroInvocation i     -> i
  | CudaExecutionConfiguration     -> "<<<cuda-execution-configuration>>>"
  | CudaKernelCall                 -> "<cuda-kernel-call>"
  | SimpleTemplateIdM              -> "<simple-template-id-M>"
  | NamespaceHead i                -> i
  | NamedNamespaceDefinitionHead i -> "namespace "^i
  | InitializerClause              -> "<initializer-clause>"
  | TemplParamMacroInvocation i    -> i
  | PostfixExpressionFunCallGuarded i -> i
  | PpIfSectionTemplDecl           -> "<pp-if-section-templ-decl>"
  | PpIfSectionTryBlock            -> "<pp-if-section-try-block>"
  | Try                            -> "try"
  | PpIfSectionHandler             -> "<pp-if-section-handler>"
  | BlockHeadMacro i               -> i
  | BlockEndMacro i                -> i
  | DeclStmtBlock                  -> "<decl-stmt-block>"
  | AsmShader s                    -> s
  | AsmName i                      -> sprintf "%%[%s]" i
  | AsmOperand                     -> "<asm-operand>"
  | AsmDirective i                 -> "."^i
  | VaArgs s                       -> s
  | PtrMacro i                     -> i
  | At                             -> "@"
  | ClassBody                      -> "<class-body>"
  | Lparen                         -> "("
  | Rparen                         -> ")"
  | Asm                            -> "asm"
  | TemplateArguments              -> "<>"
  | SuffixMacroInvocation i        -> i

  | ObjcThrow                         -> "@throw"
  | ObjcSynchronized                  -> "@synchronized"
  | ObjcClassDeclarationList          -> "@class"
  | ObjcProtocolDeclarationList       -> "@protocol"
  | ObjcProtocolDeclaration i         -> "@protocol "^i
  | ObjcClassInterface i              -> "@interface "^i
  | ObjcCategoryInterface(i, c)       -> sprintf "@interface %s (%s)" i c
  | ObjcSuperclass i                  -> ": "^i
  | ObjcProtocolReferenceList         -> "<objc-protocol-reference-list>"
  | ObjcProtocolReferenceListMacro i  -> i
  | ObjcInstanceVariables             -> "<objc-instance-variables>"
  | ObjcInstanceVariableDeclaration   -> "<objc-instance-variable-declaration>"
  | ObjcInterfaceDeclaration          -> "<objc-interface-declaration>"
  | ObjcPrivate                       -> "@private"
  | ObjcPublic                        -> "@public"
  | ObjcPackage                       -> "@package"
  | ObjcProtected                     -> "@protected"
  | ObjcStructDeclaration             -> "<objc-struct-declaration>"
  | ObjcStructDeclarator              -> "<objc-struct-declarator>"
  | ObjcPropertyDeclaration           -> "<objc-property-declaration>"
  | ObjcPropertyAttributesDeclaration -> "<objc-property-attributes-declaration>"
  | ObjcClassMethodDeclaration        -> "<objc-class-method-declaration>"
  | ObjcInstanceMethodDeclaration     -> "<objc-instance-method-declaration>"
  | ObjcMethodType                    -> "<objc-MethodType"
  | ObjcMethodSelector                -> "<objc-method-selector>"
  | ObjcMethodSelectorPack            -> "<objc-method-selector-pack>"
  | ObjcSelector i                    -> i
  | ObjcSelectorMacro i               -> i
  | ObjcKeywordSelector               -> "<objc-keyword-selector>"
  | ObjcKeywordDeclarator i           -> i
  | ObjcSpecifierQualifier i          -> i
  | ObjcProtocolName i                -> i
  | ObjcClassName i                   -> i
  | ObjcPropertyAttribute i           -> i
  | ObjcMessageExpression             -> "<objc-message-expression>"
  | ObjcMessageSelector               -> "<objc-message-selector>"
  | ObjcProtocolExpression            -> "<objc-protocol-expression>"
  | ObjcKeywordArgument i             -> i
  | ObjcProtocolInterfaceDeclarationOptional -> "@optional"
  | ObjcProtocolInterfaceDeclarationRequired -> "@required"
  | ObjcAutoreleasepool               -> "@autoreleasepool"
  | ObjcAvailable                     -> "@available"
  | ObjcSelectorExpression i          -> "@selector "^i
  | ObjcEncodeExpression              -> "@encode"
  | ObjcTryBlock    -> "<try-block>"
  | ObjcTry         -> "@try"
  | ObjcCatchClause -> "@catch"
  | ObjcFinally     -> "@finally"
  | ObjcMethodMacroInvocation i -> i
  | ObjcKeywordName i -> i^":"
  | ObjcLiteral -> "@"
  | ObjcArray      -> "@[]"
  | ObjcDictionary -> "@{}"
  | ObjcKeyValue   -> ":"
  | ObjcClass      -> "@class"

  | SwiftArg i   -> i^":"
  | SwiftFunCall -> "<swift-function-call>"

  | HugeArray(_, c) -> c
  | DslMacroArgument -> "<dsl-macro-argument>"
  | ParametersAndQualifiersList -> "<parameters-and-qualifiers-list>"
  | NestedFunctionDefinition n -> sprintf "<nested-function-definition:%s>" n
  | PragmaMacro i -> i
  | PragmaMacroInvocation i -> i
  | MockQualifier i -> i

  | ClassBodyHeadMacro i -> i
  | ClassBodyEndMacro i -> i
  | ClassBodyHeadMacroInvocation i -> i
  | ClassBodyEndMacroInvocation i -> i
  | InitHeadMacroInvocation i -> i
  | InitEndMacroInvocation i -> i
  | InitDeclaration -> "<init-declaration>"
  | LiteralMacroArgument s -> s

let to_tag ?(strip=false) lab : string * (string * string) list =
  ignore strip;
  match lab with
  | DUMMY -> "DUMMY", []
  | EMPTY -> "EMPTY", []
  | AMBIGUOUS_CONSTRUCT -> "AMBIGUOUS_CONSTRUCT", []
  | PARTIAL_CONSTRUCT   -> "PARTIAL_CONSTRUCT", []
  | DECLS               -> "DECLS", []
  | MEM_DECLS           -> "MEM_DECLS", []
  | EXPRS               -> "EXPRS", []
  | STMTS               -> "STMTS", []
  | INITS               -> "INITS", []
  | LABELS              -> "LABELS", []
  | SPECS               -> "SPECS", []
  | ETORS               -> "ETORS", []
  | OBJC_DECLS          -> "OBJC_DECLS", []
  | TEMPL_PARAMS        -> "TEMPL_PARAMS", []
  | TEMPL_ARGS          -> "TEMPL_ARGS", []
  | DELIM_MACRO i       -> "DELIM_MACRO", ["ident",i]
  | DELIM_MACRO_ i      -> "DELIM_MACRO_", ["ident",i]
  | Q_PROPERTY          -> "Q_PROPERTY", []
  | ERROR s             -> "ERROR", ["line",s]

  | TranslationUnit -> "TranslationUnit", []

(* PpDirective *)
  | PpInclude s              -> "PpInclude", ["line",s]
  | PpDefine i               -> "PpDefine", ["ident",i]
  | PpUndef i                -> "PpUndef", ["ident",i]
  | PpLine (j, s)            -> sprintf "PpLine", ["line_number",string_of_int j;"file_name",s]
  | PpError s                -> "PpError", ["line",s]
  | PpPragma s               -> "PpPragma", ["line",s]
  | PpNull                   -> "PpNull", []
  | PpMarker(j, s, jl)       -> "PpMarker", ["line_number",string_of_int j;
                                             "file_name",s;
                                             "flags",
                                             (String.concat ":" (List.map string_of_int jl))]
  | PpIf x                   -> "PpIf", ["cond",x]
  | PpIfdef i                -> "PpIfdef", ["ident",i]
  | PpIfndef i               -> "PpIfndef", ["ident",i]
  | PpElif x                 -> "PpElif", ["cond",x]
  | PpElse x                 -> "PpElse", ["cond",x]
  | PpEndif x                -> "PpEndif", ["cond",x]
  | PpUnknown s              -> "PpUnknown", ["line",s]
  | PpIfSection(j, x)        -> "PpIfSection", if j = 0 && x = "" then [] else ["level",string_of_int j;"cond",x]
  | PpIfSectionFuncDef i     -> "PpIfSectionFuncDef", ["ident",i]
  | PpIfSectionAltFuncDef    -> "PpIfSectionAltFuncDef", []
  | PpIfSectionBroken        -> "PpIfSectionBroken", []
  | PpIfSectionBrokenIf      -> "PpIfSectionBrokenIf", []
  | PpIfSectionBrokenFuncDef -> "PpIfSectionBrokenFuncDef", []
  | PpIfSectionBrokenDtorFunc -> "PpIfSectionBrokenDtorFunc", []
  | PpIfSectionCondExpr      -> "PpIfSectionCondExpr", []
  | PpIfSectionLogicalAnd    -> "PpIfSectionLogicalAnd", []
  | PpIfSectionLogicalOr     -> "PpIfSectionLogicalOr", []
  | PpIfGroup x              -> "PpIfGroup", ["cond",x]
  | PpElifGroup x            -> "PpElifGroup", ["cond",x]
  | PpElseGroup x            -> "PpElseGroup", ["cond",x]
  | PpStringized s           -> "PpStringized", ["ident",s]
  | PpMacroParam s           -> "PpMacroParam", ["ident",s]
  | PpImport s               -> "PpImport", ["line",s]

  | OmpDirective s           -> "OmpDirective", ["line",s]
  | AccDirective s           -> "AccDirective", ["line",s]


(* Declaration *)
  | SimpleDeclaration             -> "SimpleDeclaration", []
  | AsmDefinition s               -> "AsmDefinition", ["asm",s]
  | NamespaceAliasDefinition i    -> "NamespaceAliasDefinition", ["ident",i]
  | UsingDeclaration              -> "UsingDeclaration", []
  | UsingEnumDeclaration          -> "UsingEnumDeclaration", []
  | UsingDirective i              -> "UsingDirective", ["ident",i]
  | Static_assertDeclaration      -> "Static_assertDeclaration", []
  | AliasDeclaration i            -> "AliasDeclaration", ["ident",xmlenc i]
  | OpaqueEnumDeclaration         -> "OpaqueEnumDeclaration", []
  | OpaqueEnumDeclarationClass    -> "OpaqueEnumDeclarationClass", []
  | OpaqueEnumDeclarationStruct   -> "OpaqueEnumDeclarationStruct", []
  | OpaqueEnumDeclarationMacro i  -> "OpaqueEnumDeclarationMacro", ["ident",i]
  | NodeclspecFunctionDeclaration -> "NodeclspecFunctionDeclaration", []
  | FunctionDefinition n          -> "FunctionDefinition", ["name",xmlenc n]
  | TemplateDeclaration           -> "TemplateDeclaration", []
  | DeductionGuide n              -> "DeductionGuide", ["name",n]
  | ExplicitInstantiation         -> "ExplicitInstantiation", []
  | ExplicitSpecialization        -> "ExplicitSpecialization", []
  | ExportDeclaration             -> "ExportDeclaration", []
  | LinkageSpecification s        -> "LinkageSpecification", ["linkage",s]
  | NamedNamespaceDefinition i    -> "NamedNamespaceDefinition", ["ident",i]
  | UnnamedNamespaceDefinition    -> "UnnamedNamespaceDefinition", []
  | NestedNamespaceDefinition i   -> "NestedNamespaceDefinition", ["ident",i]
  | NamespaceDefinitionMacro i    -> "NamespaceDefinitionMacro", ["ident",i]
  | EmptyDeclaration              -> "EmptyDeclaration", []
  | AttributeDeclaration          -> "AttributeDeclaration", []
  | DeclarationMacro i            -> "DeclarationMacro", ["ident",i]
  | DeclarationMacroInvocation i  -> "DeclarationMacroInvocation", ["ident",i]
  | DeclarationMacroInvocationInvocation -> "DeclarationMacroInvocationInvocation", []
  | DeclarationMacroInvocationArrow -> "DeclarationMacroInvocationArrow", []
  | DeclarationMacroInvocationDot -> "DeclarationMacroInvocationDot", []
  | ImportDeclaration s           -> "ImportDeclaration", ["line",s]


(* Statement *)
  | Statement                  -> "Statement", []
  | ExpressionStatement        -> "ExpressionStatement", []
  | DeclarationStatement       -> "DeclarationStatement", []
  | TryBlock                   -> "TryBlock", []
  | LabeledStatement           -> "LabeledStatement", []
  | SelectionStatement         -> "SelectionStatement", []
  | IfStatement                -> "IfStatement", []
  | ElseStatement              -> "ElseStatement", []
  | SwitchStatement            -> "SwitchStatement", []
  (*| EmptyStatement             -> "EmptyStatement", []*)
  | CompoundStatement          -> "CompoundStatement", []
  | IterationStatement         -> "IterationStatement", []
  | WhileStatement             -> "WhileStatement", []
  | DoStatement                -> "DoStatement", []
  | ForStatement               -> "ForStatement", []
  | ForInStatement             -> "ForInStatement", []
  | RangeBasedForStatement     -> "RangeBasedForStatement", []
  | JumpStatement              -> "JumpStatement", []
  | BreakStatement             -> "BreakStatement", []
  | ContinueStatement          -> "ContinueStatement", []
  | ReturnStatement            -> "ReturnStatement", []
  | GotoStatement i            -> "GotoStatement", ["ident",i]
  | ComputedGotoStatement      -> "ComputedGotoStatement", []
  | CoroutineReturnStatement   -> "CoroutineReturnStatement", []
  | StatementMacroInvocation i -> "StatementMacroInvocation", ["ident",i]
  | StatementMacro i           -> "StatementMacro", ["ident",i]
  | IterationMacroInvocation i -> "IterationMacroInvocation", ["ident",i]
  | IterationMacro i           -> "IterationMacro", ["ident",i]

(* Expression *)
  | This                              -> "This", []
  | ParenthesizedExpression           -> "ParenthesizedExpression", []
  | RequiresExpression                -> "RequiresExpression", []
  | FoldExpression                    -> "FoldExpression", []
  | LambdaExpression                  -> "LambdaExpression", []
  | LogicalOrExpression i             ->
      "LogicalOrExpression", if i = "||" then [] else ["ident",i]
  | LogicalAndExpression i            ->
      "LogicalAndExpression", if i = "&&" then [] else ["ident",i]
  | InclusiveOrExpression i           ->
      "InclusiveOrExpression", if i = "|" then [] else ["ident",i]
  | ExclusiveOrExpression i           ->
      "ExclusiveOrExpression", if i = "^" then [] else ["ident",i]
  | AndExpression i                   ->
      "AndExpression", if i = "&" then [] else ["ident",i]
  | EqualityExpression                -> "EqualityExpression", []
  | EqualityExpressionEq              -> "EqualityExpressionEq", []
  | EqualityExpressionStrictEq        -> "EqualityExpressionStrictEq", []
  | EqualityExpressionNeq i           ->
      "EqualityExpressionNeq", if i = "!=" then [] else ["ident",i]
  | RelationalExpression              -> "RelationalExpression", []
  | RelationalExpressionLt            -> "RelationalExpressionLt", []
  | RelationalExpressionGt            -> "RelationalExpressionGt", []
  | RelationalExpressionLe            -> "RelationalExpressionLe", []
  | RelationalExpressionGe            -> "RelationalExpressionGe", []
  | CompareExpression                 -> "CompareExpression", []
  | ShiftExpression                   -> "ShiftExpression", []
  | ShiftExpressionLeft               -> "ShiftExpressionLeft", []
  | ShiftExpressionRight              -> "ShiftExpressionRight", []
  | ShiftExpressionRightU             -> "ShiftExpressionRightU", []
  | AdditiveExpression                -> "AdditiveExpression", []
  | AdditiveExpressionAdd             -> "AdditiveExpressionAdd", []
  | AdditiveExpressionSubt            -> "AdditiveExpressionSubt", []
  | MultiplicativeExpression          -> "MultiplicativeExpression", []
  | MultiplicativeExpressionMult      -> "MultiplicativeExpressionMult", []
  | MultiplicativeExpressionDiv       -> "MultiplicativeExpressionDiv", []
  | MultiplicativeExpressionMod       -> "MultiplicativeExpressionMod", []
  | PmExpression                      -> "PmExpression", []
  | PmExpressionClass                 -> "PmExpressionClass", []
  | PmExpressionPtr                   -> "PmExpressionPtr", []
  | CastExpression                    -> "CastExpression", []
  | CompoundLiteralExpression         -> "CompoundLiteralExpression", []
  | UnaryExpression                   -> "UnaryExpression", []
  | UnaryExpressionIncr               -> "UnaryExpressionIncr", []
  | UnaryExpressionDecr               -> "UnaryExpressionDecr", []
  | UnaryExpressionInd                -> "UnaryExpressionInd", []
  | UnaryExpressionAddr               -> "UnaryExpressionAddr", []
  | UnaryExpressionLabelAddr          -> "UnaryExpressionLabelAddr", []
  | UnaryExpressionPlus               -> "UnaryExpressionPlus", []
  | UnaryExpressionMinus              -> "UnaryExpressionMinus", []
  | UnaryExpressionNeg i              ->
      "UnaryExpressionNeg", if i = "!" then [] else ["ident",i]
  | UnaryExpressionCompl i            ->
      "UnaryExpressionCompl", if i = "~" then [] else ["ident",i]
  | UnaryExpressionSizeof             -> "UnaryExpressionSizeof", []
  | UnaryExpressionSizeofPack i       -> "UnaryExpressionSizeofPack", ["ident",i]
  | UnaryExpressionAlignof            -> "UnaryExpressionAlignof", []
  | NoexceptExpression                -> "NoexceptExpression", []
  | PostfixExpression                 -> "PostfixExpression", []
  | PostfixExpressionSubscr           -> "PostfixExpressionSubscr", []
  | PostfixExpressionFunCall          -> "PostfixExpressionFunCall", []
  | PostfixExpressionFunCallMacro i   -> "PostfixExpressionFunCallMacro", ["ident",i]
  | PostfixExpressionExplicitTypeConv -> "PostfixExpressionExplicitTypeConv", []
  | PostfixExpressionExplicitTypeConvExpr   -> "PostfixExpressionExplicitTypeConvExpr", []
  | PostfixExpressionExplicitTypeConvBraced -> "PostfixExpressionExplicitTypeConvBraced", []
  | PostfixExpressionDot              -> "PostfixExpressionDot", []
  | PostfixExpressionArrow            -> "PostfixExpressionArrow", []
  | PostfixExpressionIncr             -> "PostfixExpressionIncr", []
  | PostfixExpressionDecr             -> "PostfixExpressionDecr", []
  | PostfixExpressionTypeid           -> "PostfixExpressionTypeid", []
  | PostfixExpressionTypeidExpr       -> "PostfixExpressionTypeidExpr", []
  | PostfixExpressionTypeidTy         -> "PostfixExpressionTypeidTy", []
  | PostfixExpressionDynamic_cast     -> "PostfixExpressionDynamic_cast", []
  | PostfixExpressionStatic_cast      -> "PostfixExpressionStatic_cast", []
  | PostfixExpressionReinterpret_cast -> "PostfixExpressionReinterpret_cast", []
  | PostfixExpressionConst_cast       -> "PostfixExpressionConst_cast", []
  | AssignmentExpression              -> "AssignmentExpression", []
  | AssignmentExpressionOverloaded s  -> "AssignmentExpressionOverloaded", ["operator",s]
  | AssignmentExpressionEq            -> "AssignmentExpressionEq", []
  | AssignmentExpressionPlus          -> "AssignmentExpressionPlus", []
  | AssignmentExpressionMinus         -> "AssignmentExpressionMinus", []
  | AssignmentExpressionMult          -> "AssignmentExpressionMult", []
  | AssignmentExpressionDiv           -> "AssignmentExpressionDiv", []
  | AssignmentExpressionMod           -> "AssignmentExpressionMod", []
  | AssignmentExpressionShiftLeft     -> "AssignmentExpressionShiftLeft", []
  | AssignmentExpressionShiftRight    -> "AssignmentExpressionShiftRight", []
  | AssignmentExpressionAnd i         ->
      "AssignmentExpressionAnd", if i = "&=" then [] else ["ident",i]
  | AssignmentExpressionXor i         ->
      "AssignmentExpressionXor", if i = "^=" then [] else ["ident",i]
  | AssignmentExpressionOr i          ->
      "AssignmentExpressionOr", if i = "|=" then [] else ["ident",i]
  | ThrowExpression                   -> "ThrowExpression", []
  | ExpressionPair                    -> "ExpressionPair", []
  | ConditionalExpression             -> "ConditionalExpression", []
  | NewExpression                     -> "NewExpression", []
  | RefNewExpression                  -> "RefNewExpression", []
  | DeleteExpression                  -> "DeleteExpression", []
  | DeleteExpressionBracket           -> "DeleteExpressionBracket", []
  | YieldExpression                   -> "YieldExpression", []
  | AwaitExpression                   -> "AwaitExpression", []
  | BlockLiteralExpression            -> "BlockLiteralExpression", []

  | ExpressionMacroInvocation i       -> "ExpressionMacroInvocation", ["ident",i]
  | LogicalOrMacroInvocation i        -> "LogicalOrMacroInvocation", ["ident",i]
  | DefinedMacroExpression i          -> "DefinedMacroExpression", ["ident",i]
  | HasIncludeExpression s            -> "HasIncludeExpression", ["include",s]
  | HasAttributeExpression            -> "HasAttributeExpression", []

(* Literal *)
  | Literal                       -> "Literal", []
  | IntegerLiteral v              -> "IntegerLiteral", ["value",xmlenc v]
  | CharacterLiteral v            -> "CharacterLiteral", ["value",xmlenc v]
  | FloatingLiteral v             -> "FloatingLiteral", ["value",xmlenc v]
  | StringLiteral v               -> "StringLiteral", ["value",xmlenc v]
  | StringMacro i                 -> "StringMacro", ["ident",i]
  | BooleanLiteral v              -> "BooleanLiteral", ["value",v]
  | Nullptr                       -> "Nullptr", []
  | ConcatenatedString            -> "ConcatenatedString", []
  | UserDefinedCharacterLiteral v -> "UserDefinedCharacterLiteral", ["value",v]
  | UserDefinedStringLiteral v    -> "UserDefinedStringLiteral", ["value",v]
  | UserDefinedFloatingLiteral v  -> "UserDefinedFloatingLiteral", ["value",v]
  | UserDefinedIntegerLiteral v   -> "UserDefinedIntegerLiteral", ["value",v]
  | LiteralMacro i                -> "LiteralMacro", ["ident",i]
  | LiteralMacroInvocation i      -> "LiteralMacroInvocation", ["ident",i]

(* UnqualifiedId *)
  | UnqualifiedId        -> "UnqualifiedId", []
  | OperatorFunctionId   -> "OperatorFunctionId", []
  | ConversionFunctionId -> "ConversionFunctionId", []
  | LiteralOperatorId s  -> "LiteralOperatorId", ["ident",s]
  | Destructor           -> "Destructor", []
  | TemplateId           -> "TemplateId", []
  | TemplateIdOp         -> "TemplateIdOp", []
  | TemplateIdLit        -> "TemplateIdLit", []

(* Operator *)
  | Operator      -> "Operator", []
  | New           -> "New", []
  | Delete        -> "Delete", []
  | NewBracket    -> "NewBracket", []
  | DeleteBracket -> "DeleteBracket", []
  | Parentheses   -> "Parentheses", []
  | Brackets      -> "Brackets", []
  | MinusGt       -> "MinusGt", []
  | MinusGtStar   -> "MinusGtStar", []
  | Tilde i       -> "Tilde", if i = "~" then [] else ["ident",i]
  | Exclam i      -> "Exclam", if i = "!" then [] else ["ident",i]
  | Plus          -> "Plus", []
  | Minus         -> "Minus", []
  | Star          -> "Star", []
  | Slash         -> "Slash", []
  | Perc          -> "Perc", []
  | Hat i         -> "Hat", if i = "^" then [] else ["ident",i]
  | Amp i         -> "Amp", if i = "&" then [] else ["ident",i]
  | Bar i         -> "Bar", if i = "|" then [] else ["ident",i]
  | Eq            -> "Eq", []
  | PlusEq        -> "PlusEq", []
  | MinusEq       -> "MinusEq", []
  | StarEq        -> "StarEq", []
  | SlashEq       -> "SlashEq", []
  | PercEq        -> "PercEq", []
  | HatEq i       -> "HatEq", if i = "^=" then [] else ["ident",i]
  | AmpEq i       -> "AmpEq", if i = "&=" then [] else ["ident",i]
  | BarEq i       -> "BarEq", if i = "|=" then [] else ["ident",i]
  | EqEq          -> "EqEq", []
  | ExclamEq i    -> "ExclamEq", if i = "!=" then [] else ["ident",i]
  | Lt            -> "Lt", []
  | Gt            -> "Gt", []
  | LtEq          -> "LtEq", []
  | GtEq          -> "GtEq", []
  | LtEqGt        -> "LtEqGt", []
  | AmpAmp i      -> "AmpAmp", if i = "&&" then [] else ["ident",i]
  | BarBar i      -> "BarBar", if i = "||" then [] else ["ident",i]
  | LtLt          -> "LtLt", []
  | GtGt          -> "GtGt", []
  | LtLtEq        -> "LtLtEq", []
  | GtGtEq        -> "GtGtEq", []
  | PlusPlus      -> "PlusPlus", []
  | MinusMinus    -> "MinusMinus", []
  | Comma         -> "Comma", []
  | Semicolon     -> "Semicolon", []
  | Colon         -> "Colon", []
  | Co_await      -> "Co_await", []

  | DotStar       -> "DotStar", []
  | Dot           -> "Dot", []

(* DefiningTypeSpecifier *)
  | DefiningTypeSpecifier           -> "DefiningTypeSpecifier", []
  | SimpleTypeSpecifier i           -> "SimpleTypeSpecifier", ["ident",i]
  | ElaboratedTypeSpecifier         -> "ElaboratedTypeSpecifier", []
  | ElaboratedTypeSpecifierClass i  -> "ElaboratedTypeSpecifierClass", ["ident",i]
  | ElaboratedTypeSpecifierStruct i -> "ElaboratedTypeSpecifierStruct", ["ident",i]
  | ElaboratedTypeSpecifierUnion i  -> "ElaboratedTypeSpecifierUnion", ["ident",i]
  | ElaboratedTypeSpecifierEnum i   -> "ElaboratedTypeSpecifierEnum", ["ident",i]
  | TypenameSpecifier i             -> "TypenameSpecifier", ["ident",i]
  | CvQualifier                     -> "CvQualifier", []
  | TypeMacro i                     -> "TypeMacro", ["ident",i]
  | Const                           -> "Const", []
  | Volatile                        -> "Volatile", []
  | Restrict i                      -> "Restrict", ["ident",i]

  | MsAsmBlock(a, s)                -> "MsAsmBlock", ["ident",a;"block",s]
  | MsCdecl i                       -> "MsCdecl", ["ident",i]
  | MsStdcall i                     -> "MsStdcall", ["ident",i]
  | MsPragma i                      -> "MsPragma", ["ident",i]
  | MsWarningSpecifier i            -> "MsWarningSpecifier", ["ident",i]
  | MsProperty i                    -> "MsProperty", ["ident",i]
  | MsAttributeSpecifier            -> "MsAttributeSpecifier", []

  | CallingConvention i             -> "CallingConvention", ["ident",i]
  | GnuAsmBlock(a, s)               -> "GnuAsmBlock", ["ident",a;"block",s]
  | GnuAttribute i                  ->
      "GnuAttribute", if i = "__attribute__" then [] else ["ident",i]
  | GnuStatementExpression          -> "GnuStatementExpression", []

  | ClassSpecifier                  -> "ClassSpecifier", []
  | EnumSpecifier                   -> "EnumSpecifier", []

(* BasicType *)
  | BasicType -> "BasicType", []
  | Char     -> "Char", []
  | Char8_t  -> "Char8_t", []
  | Char16_t -> "Char16_t", []
  | Char32_t -> "Char32_t", []
  | Wchar_t  -> "Wchar_t", []
  | Bool     -> "Bool", []
  | Short    -> "Short", []
  | Int      -> "Int", []
  | Long     -> "Long", []
  | Signed   -> "Signed", []
  | Unsigned -> "Unsigned", []
  | Float    -> "Float", []
  | Double   -> "Double", []
  | Void     -> "Void", []
  | UnsignedInt -> "UnsignedInt", []
  | UnsignedLong -> "UnsignedLong", []

(* AccessSpecifier *)
  | AccessSpecifier -> "AccessSpecifier", []
  | Private   -> "Private", []
  | Protected -> "Protected", []
  | Public    -> "Public", []

(* AttributeSpecifier *)
  | AttributeSpecifier                  -> "AttributeSpecifier", []
  | StandardAttributeSpecifier          -> "StandardAttributeSpecifier", []
  | ContractAttributeSpecifier          -> "ContractAttributeSpecifier", []
  | ContractAttributeSpecifierExpects   -> "ContractAttributeSpecifierExpects", []
  | ContractAttributeSpecifierEnsures i -> "ContractAttributeSpecifierEnsures", ["ident",i]
  | ContractAttributeSpecifierAssert    -> "ContractAttributeSpecifierAssert", []
  | AlignmentAttributeSpecifier b       -> "AlignmentAttributeSpecifier", ["pack",string_of_bool b]

  | AttributeMacro i                -> "AttributeMacro", ["ident",i]

(* RefQualifier *)
  | RefQualifier       -> "RefQualifier", []
  | RefQualifierAmp    -> "RefQualifierAmp", []
  | RefQualifierAmpAmp -> "RefQualifierAmpAmp", []

(* PlaceholderTypeSpecifier *)
  | PlaceholderTypeSpecifier         -> "PlaceholderTypeSpecifier", []
  | PlaceholderTypeSpecifierAuto     -> "PlaceholderTypeSpecifierAuto", []
  | PlaceholderTypeSpecifierDecltype -> "PlaceholderTypeSpecifierDecltype", []

(* PtrOperator *)
  | PtrOperator       -> "PtrOperator", []
  | PtrOperatorStar   -> "PtrOperatorStar", []
  | PtrOperatorAmp    -> "PtrOperatorAmp", []
  | PtrOperatorAmpAmp -> "PtrOperatorAmpAmp", []
  | PtrOperatorHat    -> "PtrOperatorHat", []
  | PtrOperatorMacro i -> "PtrOperatorMacro", ["ident",i]

(* Declarator *)
  | Declarator           -> "Declarator", []
  | DeclaratorFunc       -> "DeclaratorFunc", []
  | PtrDeclarator        -> "PtrDeclarator", [] (* PtrDeclarator *)
  | PtrDeclaratorPtr     -> "PtrDeclaratorPtr", [] (* PtrDeclarator *)
  | NoptrDeclarator      -> "NoptrDeclarator", []      (* NoptrDeclarator *)
  | NoptrDeclaratorId    -> "NoptrDeclaratorId", []    (* NoptrDeclarator *)
  | NoptrDeclaratorParen -> "NoptrDeclaratorParen", [] (* NoptrDeclarator *)
  | NoptrDeclaratorFunc  -> "NoptrDeclaratorFunc", []  (* NoptrDeclarator *)
  | NoptrDeclaratorOldFunc -> "NoptrDeclaratorOldFunc", [] (* NoptrDeclarator *)
  | NoptrDeclaratorArray -> "NoptrDeclaratorArray", [] (* NoptrDeclarator *)
  | DtorMacro i -> "DtorMacro", ["ident",i]

(* NoexceptSpecifier *)
  | NoexceptSpecifier      -> "NoexceptSpecifier", []
  | NoexceptSpecifierThrow -> "NoexceptSpecifierThrow", []
  | NoexceptSpecifierThrowAny -> "NoexceptSpecifierThrowAny", []

(* VirtSpecifier *)
  | VirtSpecifier         -> "VirtSpecifier", []
  | VirtSpecifierFinal    -> "VirtSpecifierFinal", []
  | VirtSpecifierOverride -> "VirtSpecifierOverride", []
  | VirtSpecifierMacro i  -> "VirtSpecifierMacro", ["ident",i]
  | VirtSpecifierMacroInvocation i  -> "VirtSpecifierMacroInvocation", ["ident",i]

(* StorageClassSpecifier *)
  | StorageClassSpecifier             -> "StorageClassSpecifier", []
  | StorageClassSpecifierStatic       -> "StorageClassSpecifierStatic", []
  | StorageClassSpecifierThread_local -> "StorageClassSpecifierThread_local", []
  | StorageClassSpecifierExtern       -> "StorageClassSpecifierExtern", []
  | StorageClassSpecifierMutable      -> "StorageClassSpecifierMutable", []
  | StorageClassSpecifierRegister     -> "StorageClassSpecifierRegister", []
  | StorageClassSpecifierVaxGlobaldef -> "StorageClassSpecifierVaxGlobaldef", []

(* FunctionSpecifier *)
  | FunctionSpecifier        -> "FunctionSpecifier", []
  | FunctionSpecifierVirtual -> "FunctionSpecifierVirtual", []
  | ExplicitSpecifier        -> "ExplicitSpecifier", []

(* ClassHead *)
  | ClassHead       -> "ClassHead", []
  | ClassHeadClass  -> "ClassHeadClass", []
  | ClassHeadStruct -> "ClassHeadStruct", []
  | ClassHeadUnion  -> "ClassHeadUnion", []
  | ClassHeadMacro i -> "ClassHeadMacro", ["ident",i]
  | ClassHeadMacroInvocation i -> "ClassHeadMacroInvocation", ["ident",i]
  | ClassHeadMsRefClass -> "ClassHeadMsRefClass", []

(* EnumHead *)
  | EnumHead           -> "EnumHead", []
  | EnumHeadEnum       -> "EnumHeadEnum", []
  | EnumHeadEnumClass  -> "EnumHeadEnumClass", []
  | EnumHeadEnumStruct -> "EnumHeadEnumStruct", []
  | EnumHeadEnumMacro i -> "EnumHeadEnumMacro", ["ident",i]

(* TypeParameterKey *)
  | TypeParameterKey         -> "TypeParameterKey", []
  | TypeParameterKeyClass    -> "TypeParameterKeyClass", []
  | TypeParameterKeyTypename -> "TypeParameterKeyTypename", []

(* FunctionBody *)
  | FunctionBody n      -> "FunctionBody", ["name",xmlenc n]
  | FunctionBodyDefault -> "FunctionBodyDefault", []
  | FunctionBodyDelete  -> "FunctionBodyDelete", []
  | FunctionTryBlock n  -> "FunctionTryBlock", ["name",xmlenc n]
  | FunctionBodyMacro i -> "FunctionBodyMacro", ["ident",i]
  | FunctionBodyMacroInvocation i -> "FunctionBodyMacroInvocation", ["ident",i]

(* DeclSpecifier *)
  | DeclSpecifier          -> "DeclSpecifier", []
  | DeclSpecifierInline    -> "DeclSpecifierInline", []
  | DeclSpecifierConstexpr -> "DeclSpecifierConstexpr", []
  | DeclSpecifierConsteval -> "DeclSpecifierConsteval", []
  | DeclSpecifierConstinit -> "DeclSpecifierConstinit", []
  | DeclSpecifierTypedef   -> "DeclSpecifierTypedef", []
  | DeclSpecifierFriend    -> "DeclSpecifierFriend", []
  | DeclSpecifierMacro i   -> "DeclSpecifierMacro", ["ident",i]
  | DeclSpecifierMacroInvocation i -> "DeclSpecifierMacroInvocation", ["ident",i]

(* Requirement *)
  | Requirement           -> "Requirement", []
  | SimpleRequirement     -> "SimpleRequirement", []
  | TypeRequirement       -> "TypeRequirement", []
  | CompoundRequirement   -> "CompoundRequirement", []
  | ReturnTypeRequirement -> "ReturnTypeRequirement", []
  | NestedRequirement     -> "NestedRequirement", []

(* AbstractDeclarator *)
  | AbstractDeclarator           -> "AbstractDeclarator", []
  | AbstractDeclaratorFunc       -> "AbstractDeclaratorFunc", []
  | PtrAbstractDeclarator        -> "PtrAbstractDeclarator", []
  | PtrAbstractDeclaratorPtr     -> "PtrAbstractDeclaratorPtr", []
  | NoptrAbstractDeclarator      -> "NoptrAbstractDeclarator", []
  | NoptrAbstractDeclaratorFunc  -> "NoptrAbstractDeclaratorFunc", []
  | NoptrAbstractDeclaratorArray -> "NoptrAbstractDeclaratorArray", []
  | NoptrAbstractDeclaratorParen -> "NoptrAbstractDeclaratorParen", []

(* NoptrAbstractPackDeclarator *)
  | NoptrAbstractPackDeclaratorFunc -> "NoptrAbstractPackDeclaratorFunc", []
  | NoptrAbstractPackDeclaratorArray -> "NoptrAbstractPackDeclaratorArray", []


(* SimpleCapture *)
  | SimpleCapture i       -> "SimpleCapture", ["ident",i]
  | SimpleCaptureAmp i    -> "SimpleCaptureAmp", ["ident",i]
  | SimpleCaptureThis     -> "SimpleCaptureThis", []
  | SimpleCaptureStarThis -> "SimpleCaptureStarThis", []

(* InitCapture *)
  | InitCapture i    -> "InitCapture", ["ident",i]
  | InitCaptureAmp i -> "InitCaptureAmp", ["ident",i]

(* LambdaCapture *)
  | LambdaCapture           -> "LambdaCapture", []
  | LambdaCaptureDefaultEq  -> "LambdaCaptureDefaultEq", []
  | LambdaCaptureDefaultAmp -> "LambdaCaptureDefaultAmp", []
  | LambdaCaptureMacroInvocation i -> "LambdaCaptureMacroInvocation", ["ident",i]

(* MemberDeclarator *)
  | MemberDeclarator           -> "MemberDeclarator", []
  | MemberDeclaratorDecl       -> "MemberDeclaratorDecl", []
  | MemberDeclaratorBitField i -> "MemberDeclaratorBitField", ["ident",i]

(* Label *)
  | Label i                        -> "Label", ["ident",i]
  | CaseLabel                      -> "CaseLabel", []
  | RangedCaseLabel                -> "RangedCaseLabel", []
  | DefaultLabel                   -> "DefaultLabel", []
  | LabelMacroInvocation i         -> "LabelMacroInvocation", ["ident",i]

(* ContractLevel *)
  | ContractLevel                  -> "ContractLevel", []
  | ContractLevelDefault           -> "ContractLevelDefault", []
  | ContractLevelAudit             -> "ContractLevelAudit", []
  | ContractLevelAxiom             -> "ContractLevelAxiom", []

  | MemberSpecification            -> "MemberSpecification", []

  | MemberDeclarationDecl          -> "MemberDeclarationDecl", []

(* *)
  | Explicit                       -> "Explicit", []
  | Virtual                        -> "Virtual", []
  | Template                       -> "Template", []
  | Noexcept                       -> "Noexcept", []
  | Extern                         -> "Extern", []
  | Inline                         -> "Inline", []
  | Default                        -> "Default", []
  | ColonColon                     -> "ColonColon", []
  | Ellipsis                       -> "Ellipsis", []

  | PureSpecifier                  -> "PureSpecifier", []
  | BaseSpecifier                  -> "BaseSpecifier", []
  | BaseClause                     -> "BaseClause", []
  | BaseMacro i                    -> "BaseMacro", ["ident",i]
  | BaseSpecMacro i                -> "BaseSpecMacro", ["ident",i]
  | BaseSpecMacroInvocation i      -> "BaseSpecMacroInvocation", ["ident",i]
  | SuffixMacro i                  -> "SuffixMacro", ["ident",i]
  | ClassVirtSpecifierFinal        -> "ClassVirtSpecifierFinal", []
  | ClassVirtSpecifierMsSealed     -> "ClassVirtSpecifierMsSealed", []
  | ClassName i                    -> "ClassName", ["ident",i]
  | ClassHeadName n                -> "ClassHeadName", ["name",n]
  | MacroArgument                  -> "MacroArgument", []
  | NoptrNewDeclarator             -> "NoptrNewDeclarator", []
  | NewInitializer                 -> "NewInitializer", []
  | NewInitializerMacro i          -> "NewInitializerMacro", ["ident",i]
  | ArgumentsMacro i               -> "ArgumentsMacro", ["ident",i]
  | ArgumentsMacroInvocation i     -> "ArgumentsMacroInvocation", ["ident",i]
  | NewDeclaratorPtr               -> "NewDeclaratorPtr", []
  | NewDeclarator                  -> "NewDeclarator", []
  | NewTypeId                      -> "NewTypeId", []
  | NewPlacement                   -> "NewPlacement", []
  | LambdaDeclarator               -> "LambdaDeclarator", []
  | ParenthesizedInitList          -> "ParenthesizedInitList", []
  | LambdaIntroducer               -> "LambdaIntroducer", []
  | LambdaIntroducerMacro i        -> "LambdaIntroducer", ["ident",i]
  | AbstractPackDeclarator         -> "AbstractPackDeclarator", []
  | AbstractPack                   -> "AbstractPack", []
  | RequirementBody                -> "RequirementBody", []
  | RequirementParameterList       -> "RequirementParameterList", []
  | MemInitializer                 -> "MemInitializer", []
  | MemInitMacroInvocation i       -> "MemInitMacroInvocation", ["ident",i]
  | QualifiedTypeName              -> "QualifiedTypeName", []
  | InitDeclarator n               -> "InitDeclarator", ["name",n]
  | ConceptDefinition n            -> "ConceptDefinition", ["name",n]
  | CtorInitializer                -> "CtorInitializer", []
  | ConstraintLogicalOrExpression i  ->
      "ConstraintLogicalOrExpression", if i = "||" then [] else ["ident",i]
  | ConstraintLogicalAndExpression i ->
      "ConstraintLogicalAndExpression", if i = "&&" then [] else ["ident",i]
  | RequiresClause                 -> "RequiresClause", []
  | TypeParameter i                -> "TypeParameter", ["ident",i]
  | TemplateHead                   -> "TemplateHead", []
  | EnclosingNamespaceSpecifier i  -> "EnclosingNamespaceSpecifier", ["ident",i]
  | Enumerator i                   -> "Enumerator", ["ident",i]
  | EnumeratorDefinition           -> "EnumeratorDefinition", []
  | EnumeratorDefinitionMacro i    -> "EnumeratorDefinitionMacro", ["ident",i]
  | TypeMacroInvocation i          -> "TypeMacroInvocation", ["ident",i]
  | Condition                      -> "Condition", []
  | ParameterDeclaration n         -> "ParameterDeclaration", ["name",n]
  | ParameterDeclarationClause b   -> "ParameterDeclarationClause", ["is_va",string_of_bool b]
  | ParametersAndQualifiers        -> "ParametersAndQualifiers", []
  | ParamDeclMacro i               -> "ParamDeclMacro", ["ident",i]
  | ParamDeclMacroInvocation i     -> "ParamDeclMacroInvocation", ["ident",i]
  | ParametersMacro i              -> "ParametersMacro", ["ident",i]
  | ParametersMacroInvocation i    -> "ParametersMacroInvocation", ["ident",i]
  | Handler                        -> "Handler", []
  | ExceptionDeclaration           -> "ExceptionDeclaration", []
  | ExpressionList                 -> "ExpressionList", []
  | EqualInitializer               -> "EqualInitializer", []
  | DesignatedInitializerClause    -> "DesignatedInitializerClause", []
  | DesignatorField i              -> "DesignatorField", ["ident",i]
  | DesignatorIndex                -> "DesignatorIndex", []
  | DesignatorRange                -> "DesignatorRange", []
  | TrailingReturnType             -> "TrailingReturnType", []
  | BracedInitList                 -> "BracedInitList", []
  | ForRangeDeclaration            -> "ForRangeDeclaration", []
  | Constexpr                      -> "Constexpr", []
  | DefiningTypeId                 -> "DefiningTypeId", []
  | EnumHeadName i                 -> "EnumHeadName", ["ident",i]
  | EnumBase                       -> "EnumBase", []
  | QualifiedId                    -> "QualifiedId", []
  | QualifiedNamespaceSpecifier n  -> "QualifiedNamespaceSpecifier", ["name",n]
  | TypeName n                     -> "TypeName", ["name",n]
  | ConversionDeclarator           -> "ConversionDeclarator", []
  | ConversionTypeId               -> "ConversionTypeId", []
  | Typename                       -> "Typename", []
  | UsingDeclarator                -> "UsingDeclarator", []
  | UsingEnumDeclarator            -> "UsingEnumDeclarator", []
  | TypeConstraint n               -> "TypeConstraint", ["name",n]
  | TypeId                         -> "TypeId", []
  | DecltypeSpecifier              -> "DecltypeSpecifier", []
  | SimpleTemplateId n             -> "SimpleTemplateId", ["name",n]
  | Identifier i                   -> "Identifier", ["ident",i]
  | IdentifierMacroInvocation i    -> "IdentifierMacroInvocation", ["ident",i]
  | PpConcatenatedIdentifier       -> "PpConcatenatedIdentifier", []
  | NestedNameSpecifier            -> "NestedNameSpecifier", []
  | NestedNameSpecifierHead        -> "NestedNameSpecifierHead", []
  | NestedNameSpecifierIdent i     -> "NestedNameSpecifierIdent", ["ident",xmlenc i]
  | NestedNameSpecifierTempl i     -> "NestedNameSpecifierTempl", ["ident",i]
  | NestedNameSpecifierDeclty      -> "NestedNameSpecifierDeclty", []
  | PackExpansion                  -> "PackExpansion", []
  | AttributeUsingPrefix           -> "AttributeUsingPrefix", []
  | Attribute                      -> "Attribute", []
  | AttributeToken i               -> "AttributeToken", ["ident",i]
  | AttributeScopedToken i         -> "AttributeScopedToken", ["ident",i]
  | AttributeNamespace i           -> "AttributeNamespace", ["ident",i]
  | AttributeArgumentClause        -> "AttributeArgumentClause", []
  | AttributeArgumentClauseMacro i -> "AttributeArgumentClauseMacro", ["ident",i]
  | BalancedToken                  -> "BalancedToken", []
  | BalancedTokenParen             -> "BalancedTokenParen", []
  | BalancedTokenBracket           -> "BalancedTokenBracket", []
  | BalancedTokenBrace             -> "BalancedTokenBrace", []
  | BalancedTokenSingle s          -> "BalancedTokenSingle", ["code",s]
  | TokenSeq s                     -> "TokenSeq", ["code",s]
  | ObjectLikeMacro                -> "ObjectLikeMacro", []
  | FunctionLikeMacro mk           -> "FunctionLikeMacro", macro_kind_to_attrs mk
  | OperatorMacro i                -> "OperatorMacro", ["ident",i]
  | OperatorMacroInvocation i      -> "OperatorMacroInvocation", ["ident",i]
  | DefiningTypeSpecifierSeq       -> "DefiningTypeSpecifierSeq", []
  | DeclSpecifierSeq               -> "DeclSpecifierSeq", []
  | TypeSpecifierSeq               -> "TypeSpecifierSeq", []
  | FunctionHead n                 -> "FunctionHead", ["name", n]
  | FunctionHeadMacro i            -> "FunctionHeadMacro", ["ident",i]
  | AccessSpecAnnot i              -> "AccessSpecAnnot", ["ident",i]
  | EnumeratorMacroInvocation i    -> "EnumeratorMacroInvocation", ["ident",i]
  | AccessSpecMacro i              -> "AccessSpecMacro", ["ident",i]
  | CvMacro i                      -> "CvMacro", ["ident",i]
  | CvMacroInvocation i            -> "CvMacroInvocation", ["ident",i]
  | RefMacro i                     -> "RefMacro", ["ident",i]
  | RefMacroInvocation i           -> "RefMacroInvocation", ["ident",i]
  | OpeningBrace                   -> "OpeningBrace", []
  | ClosingBrace                   -> "ClosingBrace", []
  | OpeningBracket                 -> "OpeningBracket", []
  | ClosingBracket                 -> "ClosingBracket", []
  | DummyBody                      -> "DummyBody", []
  | DummyDecl                      -> "DummyDecl", []
  | DummyStmt                      -> "DummyStmt", []
  | DummyExpr                      -> "DummyExpr", []
  | DummyOp                        -> "DummyOp", []
  | DummyDtor                      -> "DummyDtor", []
  | GnuAsmBlockFragmented a        -> "GnuAsmBlockFragmented", ["ident",a]
  | GnuAsmFragment s               -> "GnuAsmFragment", ["block",s]
  (*| GnuAsmQualifier i              -> "GnuAsmQualifier", ["ident",i]*)
  | DesignatorFieldOld i           -> "DesignatorFieldOld", ["ident",i]
  | DoxygenLine s                  -> "DoxygenLine", ["line",s]
  | NoexceptSpecifierMacro i       -> "NoexceptSpecifierMacro", ["ident",i]
  | AttributeMacroInvocation i     -> "AttributeMacroInvocation", ["ident",i]
  | CudaExecutionConfiguration     -> "CudaExecutionConfiguration", []
  | CudaKernelCall                 -> "CudaKernelCall", []
  | SimpleTemplateIdM              -> "SimpleTemplateIdM", []
  | NamespaceHead i                -> "NamespaceHead", ["ident",i]
  | NamedNamespaceDefinitionHead i -> "NamedNamespaceDefinitionHead", ["ident",i]
  | InitializerClause              -> "InitializerClause", []
  | TemplParamMacroInvocation i    -> "TemplParamMacroInvocation", ["ident",i]
  | PostfixExpressionFunCallGuarded i -> "PostfixExpressionFunCallGuarded", ["ident",i]
  | PpIfSectionTemplDecl           -> "PpIfSectionTemplDecl", []
  | PpIfSectionTryBlock            -> "PpIfSectionTryBlock", []
  | Try                            -> "Try", []
  | PpIfSectionHandler             -> "PpIfSectionHandler", []
  | BlockHeadMacro i               -> "BlockHeadMacro", ["ident",i]
  | BlockEndMacro i                -> "BlockEndMacro", ["ident",i]
  | DeclStmtBlock                  -> "DeclStmtBlock", []
  | AsmShader s                    -> "AsmShader", ["code",s]
  | AsmName i                      -> "AsmName", ["ident",i]
  | AsmOperand                     -> "AsmOperand", []
  | AsmDirective i                 -> "AsmDirective", ["ident",i]
  | VaArgs s                       -> "VaArgs", ["code",s]
  | PtrMacro i                     -> "PtrMacro", ["ident",i]
  | At                             -> "At", []
  | ClassBody                      -> "ClassBody", []
  | Lparen                         -> "Lparen", []
  | Rparen                         -> "Rparen", []
  | Asm                            -> "Asm", []
  | TemplateArguments              -> "TemplateArguments", []
  | SuffixMacroInvocation i        -> "SuffixMacroInvocation", ["ident",i]

  | ObjcThrow                         -> "ObjcThrow", []
  | ObjcSynchronized                  -> "ObjcSynchronized", []
  | ObjcClassDeclarationList          -> "ObjcClassDeclarationList", []
  | ObjcProtocolDeclarationList       -> "ObjcProtocolDeclarationList", []
  | ObjcProtocolDeclaration i         -> "ObjcProtocolDeclaration", ["ident",i]
  | ObjcClassInterface i              -> "ObjcClassInterface", ["ident",i]
  | ObjcCategoryInterface(i, c)       -> "ObjcCategoryInterface", ["ident",i;"category",c]
  | ObjcSuperclass i                  -> "ObjcSuperclass", ["ident",i]
  | ObjcProtocolReferenceList         -> "ObjcProtocolReferenceList", []
  | ObjcProtocolReferenceListMacro i  -> "ObjcProtocolReferenceListMacro", ["ident",i]
  | ObjcInstanceVariables             -> "ObjcInstanceVariables", []
  | ObjcInstanceVariableDeclaration   -> "ObjcInstanceVariableDeclaration", []
  | ObjcInterfaceDeclaration          -> "ObjcInterfaceDeclaration", []
  | ObjcPrivate                       -> "ObjcPrivate", []
  | ObjcPublic                        -> "ObjcPublic", []
  | ObjcPackage                       -> "ObjcPackage", []
  | ObjcProtected                     -> "ObjcProtected", []
  | ObjcStructDeclaration             -> "ObjcStructDeclaration", []
  | ObjcStructDeclarator              -> "ObjcStructDeclarator", []
  | ObjcPropertyDeclaration           -> "ObjcPropertyDeclaration", []
  | ObjcPropertyAttributesDeclaration -> "ObjcPropertyAttributesDeclaration", []
  | ObjcClassMethodDeclaration        -> "ObjcClassMethodDeclaration", []
  | ObjcInstanceMethodDeclaration     -> "ObjcInstanceMethodDeclaration", []
  | ObjcMethodType                    -> "ObjcMethodType", []
  | ObjcMethodSelector                -> "ObjcMethodSelector", []
  | ObjcMethodSelectorPack            -> "ObjcMethodSelectorPack", []
  | ObjcSelector i                    -> "ObjcSelector", ["ident",i]
  | ObjcSelectorMacro i               -> "ObjcSelectorMacro", ["ident",i]
  | ObjcKeywordSelector               -> "ObjcKeywordSelector", []
  | ObjcKeywordDeclarator i           -> "ObjcKeywordDeclarator", ["ident",i]
  | ObjcSpecifierQualifier i          -> "ObjcSpecifierQualifier", ["ident",i]
  | ObjcProtocolName i                -> "ObjcProtocolName", ["ident",i]
  | ObjcClassName i                   -> "ObjcClassName", ["ident",i]
  | ObjcPropertyAttribute i           -> "ObjcPropertyAttribute", ["ident",i]
  | ObjcMessageExpression             -> "ObjcMessageExpression", []
  | ObjcMessageSelector               -> "ObjcMessageSelector", []
  | ObjcProtocolExpression            -> "ObjcProtocolExpression", []
  | ObjcKeywordArgument i             -> "ObjcKeywordArgument", ["ident",i]
  | ObjcProtocolInterfaceDeclarationOptional -> "ObjcProtocolInterfaceDeclarationOptional", []
  | ObjcProtocolInterfaceDeclarationRequired -> "ObjcProtocolInterfaceDeclarationRequired", []
  | ObjcAutoreleasepool               -> "ObjcAutoreleasepool", []
  | ObjcAvailable                     -> "ObjcAvailable", []
  | ObjcSelectorExpression i          -> "ObjcSelectorExpression", ["ident",i]
  | ObjcEncodeExpression              -> "ObjcEncodeExpression", []
  | ObjcTryBlock    -> "ObjcTryBlock", []
  | ObjcTry         -> "ObjcTry", []
  | ObjcCatchClause -> "ObjcCatchClause", []
  | ObjcFinally     -> "ObjcFinally", []
  | ObjcMethodMacroInvocation i -> "ObjcMethodMacroInvocation", ["ident",i]
  | ObjcKeywordName i -> "ObjcKeywordName", ["ident",i]
  | ObjcLiteral -> "ObjcLiteral", []
  | ObjcArray      -> "ObjcArray", []
  | ObjcDictionary -> "ObjcDictionary", []
  | ObjcKeyValue   -> "ObjcKeyValue", []
  | ObjcClass      -> "ObjcClass", []

  | SwiftArg i   -> "SwiftArg", ["ident",i]
  | SwiftFunCall -> "SwiftFunCall", []

  | HugeArray(sz, c) -> "HugeArray", ["size",string_of_int sz;"code", c]
  | DslMacroArgument -> "DslMacroArgument", []
  | ParametersAndQualifiersList -> "ParametersAndQualifiersList", []
  | NestedFunctionDefinition n -> "NestedFunctionDefinition", ["name",xmlenc n]
  | PragmaMacro i -> "PragmaMacro", ["ident",i]
  | PragmaMacroInvocation i -> "PragmaMacroInvocation", ["ident",i]
  | MockQualifier i -> "MockQualifier", ["ident",i]

  | ClassBodyHeadMacro i -> "ClassBodyHeadMacro", ["ident",i]
  | ClassBodyEndMacro i -> "ClassBodyEndMacro", ["ident",i]
  | ClassBodyHeadMacroInvocation i -> "ClassBodyHeadMacroInvocation", ["ident",i]
  | ClassBodyEndMacroInvocation i -> "ClassBodyEndMacroInvocation", ["ident",i]
  | InitHeadMacroInvocation i -> "InitHeadMacroInvocation", ["ident",i]
  | InitEndMacroInvocation i -> "InitEndMacroInvocation", ["ident",i]
  | InitDeclaration -> "InitDeclaration", []
  | LiteralMacroArgument s -> "LiteralMacroArgument", ["code",s]


let get_name ?(strip=false) lab =
  ignore strip;
  match lab with
  | DELIM_MACRO n
  | DELIM_MACRO_ n
  | PpDefine n
  | PpUndef n
  | PpIfdef n
  | PpIfndef n
  | PpStringized n
  | PpMacroParam n
  | NamespaceAliasDefinition n
  | UsingDirective n
  | AliasDeclaration n
  | DeductionGuide n
  | NamedNamespaceDefinition n
  | NestedNamespaceDefinition n
  | NamespaceDefinitionMacro n
  | DeclarationMacro n
  | DeclarationMacroInvocation n
  | GotoStatement n
  | StatementMacroInvocation n
  | StatementMacro n
  | IterationMacroInvocation n
  | IterationMacro n
  | UnaryExpressionSizeofPack n
  | ExpressionMacroInvocation n
  | LogicalOrMacroInvocation n
  | DefinedMacroExpression n
  | StringMacro n
  | LiteralOperatorId n
  | SimpleTypeSpecifier n
  | ElaboratedTypeSpecifierClass n
  | ElaboratedTypeSpecifierStruct n
  | ElaboratedTypeSpecifierUnion n
  | ElaboratedTypeSpecifierEnum n
  | TypenameSpecifier n
  | ContractAttributeSpecifierEnsures n
  | AttributeMacro n
  | VirtSpecifierMacro n
  | VirtSpecifierMacroInvocation n
  | SimpleCapture n
  | SimpleCaptureAmp n
  | MemberDeclaratorBitField n
  | Label n
  | ClassName n
  | ClassHeadName n
  | ClassHeadMacro n
  | ClassHeadMacroInvocation n
  | NewInitializerMacro n
  | ArgumentsMacro n
  | ConceptDefinition n
  | TypeParameter n
  | EnclosingNamespaceSpecifier n
  | Enumerator n
  | EnumeratorDefinitionMacro n
  | TypeMacroInvocation n
  | ParameterDeclaration n
  | ParamDeclMacro n
  | ParamDeclMacroInvocation n
  | ParametersMacro n
  | ParametersMacroInvocation n
  | DesignatorField n
  | DesignatorFieldOld n
  | EnumHeadName n
  | QualifiedNamespaceSpecifier n
  | TypeName n
  | TypeConstraint n
  | SimpleTemplateId n
  | Identifier n
  | IdentifierMacroInvocation n
  | AttributeToken n
  | AttributeScopedToken n
  | AttributeNamespace n
  | OperatorMacro n
  | OperatorMacroInvocation n
  | AccessSpecAnnot n
  | EnumeratorMacroInvocation n
  | AccessSpecMacro n
  | CvMacro n
  | CvMacroInvocation n
  | RefMacro n
  | RefMacroInvocation n
  | LiteralMacroInvocation n
  | NoexceptSpecifierMacro n
  | AttributeMacroInvocation n
  | NamespaceHead n
  | NamedNamespaceDefinitionHead n
  | TemplParamMacroInvocation n
  | PostfixExpressionFunCallGuarded n
  | ObjcClassName n
  | ObjcProtocolDeclaration n
  | ObjcClassInterface n
  | ObjcCategoryInterface(n, _)
  | ObjcSuperclass n
  | ObjcSelector n
  | ObjcSelectorMacro n
  | ObjcKeywordDeclarator n
  | ObjcSpecifierQualifier n
  | ObjcProtocolName n
  | ObjcPropertyAttribute n
  | ObjcKeywordArgument n
  | ObjcSelectorExpression n
  | AttributeArgumentClauseMacro n
  | PtrOperatorMacro n
  | BaseMacro n
  | BaseSpecMacro n
  | BaseSpecMacroInvocation n
  | SuffixMacro n
  | DeclSpecifierMacro n
  | DeclSpecifierMacroInvocation n
  | BlockHeadMacro n
  | BlockEndMacro n
  | AsmName n
  | AsmDirective n
  | MemInitMacroInvocation n
  | InitDeclarator n
  | PpIfSectionFuncDef n
  | OpaqueEnumDeclarationMacro n
  | LiteralMacro n
  | DtorMacro n
  | EnumHeadEnumMacro n
  | FunctionBodyMacroInvocation n
  | LambdaCaptureMacroInvocation n
  | LambdaIntroducerMacro n
  | FunctionHead n
  | FunctionDefinition n
  | FunctionBody n
  | FunctionTryBlock n
  | NestedFunctionDefinition n
  | PragmaMacro n
  | PragmaMacroInvocation n
  | MockQualifier n
  | ClassBodyHeadMacro n
  | ClassBodyEndMacro n
  | ClassBodyHeadMacroInvocation n
  | ClassBodyEndMacroInvocation n
    -> n

  | PpInclude x -> x

  (*| Char     -> "char"
  | Char8_t  -> "char8_t"
  | Char16_t -> "char16_t"
  | Char32_t -> "char32_t"
  | Wchar_t  -> "wchar_t"
  | Bool     -> "bool"
  | Short    -> "short"
  | Int      -> "int"
  | Long     -> "long"
  | Signed   -> "signed"
  | Unsigned -> "unsigned"
  | Float    -> "float"
  | Double   -> "double"
  | Void     -> "void"
  | UnsignedInt -> "unsigned int"
  | UnsignedLong -> "unsigned long"*)

  | _ -> raise Not_found

let get_name_opt lab =
    try
      Some (get_name lab)
    with
      Not_found -> None

let get_names = function
  | lab -> [get_name lab]

let get_label : t -> string = function
  | _ -> raise Not_found

let get_var : t -> string = function
  | _ -> raise Not_found

let get_var_opt : t -> string option = function
  | _ -> None

let get_category lab =
  let c, _ = to_tag lab in
  c

let get_value : t -> string = function
  | IntegerLiteral v
  | CharacterLiteral v
  | FloatingLiteral v
  | StringLiteral v
  | BooleanLiteral v
  | UserDefinedCharacterLiteral v
  | UserDefinedStringLiteral v
  | UserDefinedFloatingLiteral v
  | UserDefinedIntegerLiteral v
      -> v
  | _ -> raise Not_found

let has_value : t -> bool = function
  | IntegerLiteral _
  | CharacterLiteral _
  | FloatingLiteral _
  | StringLiteral _
  | BooleanLiteral _
  | UserDefinedCharacterLiteral _
  | UserDefinedStringLiteral _
  | UserDefinedFloatingLiteral _
  | UserDefinedIntegerLiteral _
      -> true
  | _ -> false

let has_non_trivial_value : t -> bool = function
  | IntegerLiteral s when s <> "0" && s <> "1" -> true
  | CharacterLiteral _ -> true
  | FloatingLiteral s when s <> "0.0" -> true
  | StringLiteral s when s <> "" -> true
  | BooleanLiteral s when s <> "true" && s <> "false" -> true
  | UserDefinedCharacterLiteral _
  | UserDefinedStringLiteral _
  | UserDefinedFloatingLiteral _
  | UserDefinedIntegerLiteral _ -> true
  | _ -> false

let has_non_trivial_tid (*lab*)_ = false (* not yet *)

module ClassKey = struct
  type t =
    | Class
    | Struct
    | Union
    | MacroInvocation of ident
    | MsRefClass

  let to_class_head = function
    | Class  -> ClassHeadClass
    | Struct -> ClassHeadStruct
    | Union  -> ClassHeadUnion
    | MacroInvocation i -> ClassHeadMacroInvocation i
    | MsRefClass -> ClassHeadMsRefClass

  let to_elaborated_type_specifier i = function
    | Class  -> ElaboratedTypeSpecifierClass i
    | Struct -> ElaboratedTypeSpecifierStruct i
    | Union  -> ElaboratedTypeSpecifierUnion i
    | _ -> failwith "Label.ClassKey.to_elaborated_type_specifier"

end (* module ClassKey *)

module EnumKey = struct
  type t =
    | Enum
    | EnumClass
    | EnumStruct
    | EnumMacro of ident

  let to_enum_head = function
    | Enum       -> EnumHeadEnum
    | EnumClass  -> EnumHeadEnumClass
    | EnumStruct -> EnumHeadEnumStruct
    | EnumMacro i -> EnumHeadEnumMacro i

  let to_opaque_enum_declaration = function
    | Enum       -> OpaqueEnumDeclaration
    | EnumClass  -> OpaqueEnumDeclarationClass
    | EnumStruct -> OpaqueEnumDeclarationStruct
    | EnumMacro i -> OpaqueEnumDeclarationMacro i

end (* module EnumKey *)
