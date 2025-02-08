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
(* astml/label.ml *)

[%%prepare_logger]

module Xstring = Diffast_misc.Xstring
module Xprint = Diffast_misc.Xprint
module XML = Diffast_misc.XML
module Otree = Diffast_misc.Otree
module Loc = Diffast_misc.Loc
module Astml = Diffast_core.Astml
module Charpool = Diffast_core.Charpool
module Spec = Diffast_core.Spec
module Parser_options = Diffast_core.Parser_options


let lang_prefix = ""

let sprintf = Printf.sprintf

let parser_attr_name    = Astml.parser_attr_name
let location_attr_name  = Astml.location_attr_name
let frommacro_attr_name = Astml.frommacro_attr_name

let is_initializer_list_attr_name = Astml.is_initializer_list_attr_name

let gid_attr_name       = Astml.add_prefix Otree.cca_prefix Otree.gid_attr_name

let make_conf_file_name parser_name = parser_name^".conf.xml"


let keyroot_depth_min = 1 (* should be specified in conf *)


let non_label_attrs =
  [ location_attr_name;
    frommacro_attr_name;
    is_initializer_list_attr_name;
    gid_attr_name;
(*    Astml.line_terminator_attr_name; *)

    parser_attr_name;
    Astml.source_attr_name;
    Astml.source_digest_attr_name;
  ]

let is_non_label_attr attr =
  List.mem attr non_label_attrs





module type T = sig
  include Spec.LABEL_T

  val get_elem : t -> string
  val get_operator : t -> string

  module CCX : sig
    val is_translation_unit : t -> bool
    val is_pp_stmt : t -> bool
    val is_fun_def : t -> bool
    val is_decl    : t -> bool
    val is_stmt    : t -> bool
    val is_if_stmt : t -> bool
    val is_expr    : t -> bool
  end

end




type attr = string * string

let attr_to_string ((name, value) : attr) =
  sprintf "%s='%s'" name value

let attr_to_xml_string ((name, value) : attr) =
  sprintf "%s='%s'" name (XML.encode_string value)

let find_attr a (attrs : attr list) =
  List.assoc a attrs

type t =
    {         elem_name   : string;
              elem_attrs  : attr list;
              elem_parser : string;
      mutable elem_ast_ns : string;
    }

type annotation = string option

let remove_prefix s =
  try
    let i = String.index s ':' in
    let len = String.length s in
    let i_ = i + 1 in
    if i_ >= len then
      s
    else
      String.sub s i_ (len - i - 1)
  with
    Not_found -> s

let get_elem { elem_name=e; _ } = remove_prefix e

let null_annotation = None

let annotation_to_string = function
  | None -> "<none>"
  | Some x -> x


let is_attr_for_named a =
  let al = remove_prefix a in
  al = "name" ||
  al = Astml.tid_attr_name ||
  al = Astml.ar_tid_attr_name ||
  al = Astml.vars_attr_name ||
  al = Astml.vdids_attr_name

let is_named { elem_attrs=attrs; _ } =
  List.exists
    (fun (a, _) ->
      is_attr_for_named a
    ) attrs

let is_named_orig = is_named (* not yet *)

let is_attr_for_operator a =
  (remove_prefix a) = "operator"

let is_attr_for_value a =
  (remove_prefix a) = "value"

let is_attr_for_string_literal a =
  is_attr_for_value a

let is_attr_for_tid a =
  (remove_prefix a) = "tid"


let is_string_literal { elem_name=name; elem_attrs=attrs; _ } =
  Xstring.endswith name "string" &&
  List.exists
    (fun (a, _) ->
      is_attr_for_string_literal a
    ) attrs

let is_int_literal (*lab*)_ = false (* not yet *)
let is_real_literal (*lab*)_ = false (* not yet *)
let is_statement (*lab*)_ = false (* not yet *)
let is_block (*lab*)_ = false (* not yet *)
let is_primary (*lab*)_ = false (* not yet *)
let is_op (*lab*)_ = false (* not yet *)

let is_scope_creating (*lab*)_ = false (* not yet *)


let to_string { elem_name=elem; elem_attrs=attrs; elem_parser=_; elem_ast_ns=_; } =
  let attrs_s =
    String.concat ""
      (List.map (fun a -> " "^(attr_to_string a)) attrs)
  in
  sprintf "%s%s" elem attrs_s


(* parser configuration file setup *)
let conf_tbl = Hashtbl.create 0

let setup_conf parser_name =
  try
    let conf_file =
      Parser_options.search_conf_file (make_conf_file_name parser_name)
    in
    if not (Hashtbl.mem conf_tbl parser_name) then
      Hashtbl.add conf_tbl parser_name (new Conf.c conf_file)
  with
  | Not_found -> Common.warning_msg "conf for parser \"%s\" not found" parser_name

let _ =
  List.iter setup_conf
    [
(*
      "c";
      "cx";
*)
      "ccx";
(*
      "java";
      "python";
      "verilog";
      "fortran";
*)
    ]

let get_conf parser_name =
  try
    Hashtbl.find conf_tbl parser_name
  with
  | Not_found -> Xprint.failure "conf for parser \"%s\" not setup yet" parser_name

(***********************************)



open Charpool


let create_tbl a =
  let len = Array.length a in
  let tbl = Hashtbl.create len in
  for i = 0 to len - 1 do
    Hashtbl.add tbl a.(i) (mkstr2 i)
  done;
  tbl


let token_tbl =
  let tokens = [
    Astml.cx_ns,
    [| "file"; "global"; "definition"; "init_name_group";
       "init_name"; "single_name"; "spec_elem"; "typeSpecifier";
       "enum_item"; "field_group"; "field"; "specifier"; "name";
       "decl_type"; "attributes"; "block"; "attribute"; "statement";
       "asm_details"; "for_clause"; "expression"; "arguments";
       "constant"; "init_expression"; "initwhat";

       "fundef"; "decdef"; "typedef"; "onlytypedef"; "globasm";
       "pragma"; "linkage"; "transformer"; "exprtransformer";
       "typedef"; "cv"; "attr"; "storage"; "inline"; "type"; "pattern";
       "void"; "char"; "short"; "int"; "long"; "int64"; "Bool";
       "float"; "double"; "signed"; "unsigned"; "named"; "struct";
       "union"; "enum"; "typeof"; "parentype"; "array";
       "ptr"; "proto"; "computation"; "block"; "sequence"; "if";
       "while"; "dowhile"; "for"; "break"; "continue"; "return";
       "switch"; "case"; "caserange"; "default"; "label"; "goto";
       "compgoto"; "definition"; "asm"; "try_except"; "try_finally";
       "ooperand"; "ioperand"; "exp"; "decl"; "unary"; "labeladdr";
       "binary"; "question"; "cast"; "call"; "comma"; "paren";
       "variable"; "sizeof"; "alignof"; "index"; "memberof";
       "memberofptr"; "gnu_body"; "expr_pattern"; "int";
       "char"; "wchar"; "string"; "wstring"; "single"; "compound";
       "infield"; "atindex"; "atindexrange";

       "init";
     |];

    Astml.ccx_ns,
    [| "TranslationUnit";

       "Expression";
       "ArraySubscriptExpression"; "BinaryExpression"; "BinaryTypeIdExpression";
       "CastExpression"; "CompoundStatementExpression"; "ConditionalExpression";
       "DeleteExpression"; "ExpressionList"; "FieldReference"; "FunctionCallExpression";
       "IdExpression"; "LambdaExpression"; "LiteralExpression"; "NewExpression";
       "PackExpansionExpression"; "SimpleTypeConstructorExpression"; "TypeIdExpression";
       "TypeIdInitializerExpression"; "TypenameExpression"; "UnaryExpression";

       "Statement";
       "BreakStatement"; "CaseStatement"; "CatchHandler"; "CompoundStatement";
       "ContinueStatement"; "DeclarationStatement"; "DefaultStatement";
       "DoStatement"; "ExpressionStatement"; "ForStatement"; "GotoStatement";
       "IfStatement"; "LabelStatement"; "NullStatement"; "RangeBasedForStatement";
       "ReturnStatement"; "SwitchStatement"; "TryBlockStatement"; "WhileStatement";

       "Declaration";
       "AliasDeclaration"; "AsmDeclaration"; "ExplicitTemplateInstantiation";
       "FunctionDefinition"; "FunctionWithTryBlock"; "LinkageSpecification";
       "NamespaceAlias"; "NamespaceDefinition"; "SimpleDeclaration";
       "StaticAssertDeclaration"; "TemplateDeclaration"; "TemplateSpecialization";
       "UsingDeclaration"; "UsingDirective"; "VisibilityLabel";

       "Declarator";
       "ArrayDeclarator"; "FieldDeclarator"; "FunctionDeclarator";
       "StandardFunctionDeclarator"; "FunctionTryBlockDeclarator"; "KnrFunctionDeclarator";

       "Designator";
       "ArrayDesignator"; "ArrayRangeDesignator"; "FieldDesignator";

       "DeclSpecifier";
       "CompositeTypeSpecifier"; "CompositeTypeSpecifierClass"; "CompositeTypeSpecifierStruct";
       "CompositeTypeSpecifierUnion"; "ElaboratedTypeSpecifier"; "EnumerationSpecifier";
       "NamedTypeSpecifier"; "SimpleDeclSpecifier"; "TypedefnameSpecifier";
       "TypeTransformationSpecifier";

       "Name";
       "ConversionName"; "ImplicitName"; "OperatorName"; "QualifiedName"; "TemplateId";

       "TemplateParameter";
       "ParameterDeclaration"; "SimpleTypeTemplateParameter"; "TemplatedTypeTemplateParameter";

       "PointerOperator";
       "Pointer"; "PointerToMember"; "ReferenceOperator";

       "Initializer";
       "ConstructorInitializer"; "ConstructorChainInitializer"; "DesignatedInitializer";
       "EqualsInitializer"; "InitializerList";

       "NameSpecifier"; "DecltypeSpecifier";

       "PackExpandable";
       "BaseSpecifier"; "Capture"; "TypeId";

       "AmbiguousTemplateArgument";
       "ArrayModifier";
       "Attribute";
       "Enumerator";

       "PreprocessorIfStatement"; "PreprocessorIfdefStatement"; "PreprocessorEndifStatement";
       "PreprocessorIfndefStatement"; "PreprocessorElseStatement"; "PreprocessorElifStatement";
       "PreprocessorUndefStatement"; "PreprocessorIncludeStatement";
       "PreprocessorObjectStyleMacroDefinition"; "PreprocessorErrorStatement";
       "PreprocessorFunctionStyleMacroDefinition"; "PreprocessorPragmaStatement";

       "Subname"; "Body";
       "Auto"; "Static"; "Extern"; "Register"; "Typedef"; "Mutable";
       "Int"; "Double"; "Char"; "Float"; "Bool"; "Void"; "WcharT"; "Decltype"; "Char16T";
       "Char32T"; "Int128"; "Float128";
       "Volatile"; "Restrict"; "Inline"; "Const"; "Long"; "Short"; "Unsigned"; "Signed";
       "Constexpr"; "Virtual"; "ThreadLocal"; "Friend"; "Explicit"; "Restrict";
       "Parameters"; "Parameter"; "ForInitializer"; "ForCondition"; "ForIncrement";

       "HugeArray"; "MacroName";
     |];

    Astml.c_ns,
    [| "Name"; "Storage"; "Type"; "Expression"; "Statement";
       "Include_file"; "CppDirective"; "SubDeclarator"; "Designator";
       "DefineValue";
       "MacroDeclaration"; "MacroName"; "MacroParameters"; "MacroParameter";
       "MacroSubst"; "DeclarationSpecifiers"; "Declaration"; "InitDeclarator";
       "Declarator"; "FunctionDefinition"; "Inline"; "ParameterDeclaration"; "Ellipsis";
       "Body"; "GccAttribute"; "StructDeclaration"; "StructDeclarator"; "Enumerator";
       "Type"; "AsmColon"; "AsmOperand"; "AsmClobber"; "IfdefStatement"; "WeirdArg";
       "Initializer"; "InitializerFieldOld"; "InitializerIndexOld"; "Arguments";
       "ForInit"; "ForCond"; "ForUpdate"; "HugeArray"; "TranslationUnit";
       "Namespace"; "ExecEval"; "ExecToken"; "FailedToParse";

       "RegularName"; "CppConcatenatedName"; "CppVariadicName"; "CppIdentBuilder";

       "Auto"; "Register"; "Static"; "Extern"; "Typedef";

       "Ident"; "Call"; "Conditional"; "Sequence";
       "PostIncrement"; "PreIncrement"; "PostDecrement"; "PreDecrement";
       "ArrayAccess"; "RecordAccess"; "RecordPtrAccess"; "Sizeof"; "Cast";
       "GccStatementExpr"; "GccConstructor";
       "ParenthesizedExpression"; "New"; "Delete"; "StringConstant";

       "LabelStatement"; "CaseStatement"; "CaseRangeStatement"; "DefaultStatement";
       "CompoundStatement"; "ExpressionStatement"; "IfStatement";
       "SwitchStatement"; "IfdefIteStatement"; "IfdefIte2Statement"; "WhileStatement";
       "DoStatement"; "ForStatement"; "MacroIterationStatement"; "GotoStatement"; "ContinueStatement";
       "BreakStatement"; "ReturnStatement"; "GotoCompoundStatement"; "AsmStatement"; "NestedFunction";
       "MacroStatement"; "Exec";

       "CppDefineObjLike"; "CppDefineFunLike"; "CppUndef"; "CppIf"; "CppElif"; "CppElse";
       "CppIfdef"; "CppIfndef"; "CppEndif"; "CppIncludeLocal"; "CppIncludeNonLocal"; "CppIncludeWeird";
       "CppPragma"; "CppUnknown"; "CppLinemarker";

       "PointerSubDtr"; "ArraySubDtr"; "ParenSubDtr"; "ParametersSubDtr";

       "FieldDesig"; "IndexDesig"; "RangeDesig";

       "PartialDoWhile"; "Text"; "Multi";

       "Void"; "Char"; "Short"; "Int"; "Long"; "Float"; "Double";
       "Signed"; "Unsigned"; "Enum"; "Struct"; "Union"; "TypedefName";
       "GccTypeof"; "Size_t"; "Ssize_t"; "Ptrdiff_t"; "Const"; "Volatile";
       "String"; "Wstring"; "MultiString"; "Character"; "Wcharacter"; "Integer";
       "FloatingPoint"; "Decimal";
       "Add"; "Subt"; "Mult"; "Div"; "Mod"; "ShiftL"; "ShiftR"; "BitAnd"; "BitOr"; "BitXor";
       "Max"; "Min";
       "Decrement"; "Increment";
       "Ref"; "Deref"; "Plus"; "Minus"; "Complement"; "Negation"; "RefLabel";
       "Assign"; "AddAssign"; "SubtAssign"; "MultAssign"; "DivAssign"; "ModAssign";
       "ShiftLAssign"; "ShiftRAssign"; "BitAndAssign"; "BitOrAssign"; "BitXorAssign";

       "Plus"; "Minus"; "Mul"; "Div"; "Mod"; "Shift_l"; "Shift_r"; "And"; "Or"; "Xor";
       "Lt"; "Gt"; "Le"; "Ge"; "Eq"; "NotEq"; "And"; "Or";
     |];

    Astml.java_ns,
    [| "ByteType"; "ShortType"; "IntType"; "LongType"; "CharType"; "FloatType";
       "DoubleType"; "BooleanType"; "ReferenceType"; "Class"; "Interface"; "Void";

       "IntegerLiteral"; "FloatLiteral"; "True"; "False"; "CharLiteral";
       "StringLiteral"; "NullLiteral";

       "Assign"; "MultAssign"; "DivAssign"; "ModAssign"; "AddAssign"; "SubtAssign";
       "ShiftLAssign"; "ShiftRAssign"; "ShiftRUAssign"; "AndAssign"; "XorAssign";
       "OrAssign";

       "PostIncrement"; "PostDecrement"; "PreIncrement"; "PreDecrement"; "Plus"; "Minus";
       "Complement"; "Negation";

       "Mult"; "Div"; "Mod"; "Add"; "Subt"; "ShiftL"; "ShiftR"; "ShiftRU"; "Eq";
       "NotEq"; "Lt"; "Gt"; "Le"; "Ge"; "BitAnd"; "BitOr"; "BitXor"; "And"; "Or";

       "Public"; "Protected"; "Private"; "Static"; "Abstract"; "Final"; "Native";
       "Synchronized"; "Transient"; "Volatile"; "Strictfp"; "Annotation";

       "Name"; "This"; "ClassLiteral"; "ClassLiteralVoid"; "QualifiedThis";
       "StandardInstanceCreation"; "QualifiedInstanceCreation"; "NameQualifiedInstanceCreation";
       "FieldAccess"; "SuperFieldAccess"; "ClassSuperFieldAccess"; "TypeMethodInvocation";
       "ArrayAccess"; "ArrayCreation"; "ParenthesizedExpression";

       "Conditional"; "Instanceof"; "Cast";

       "NormalAnnotation"; "MakerAnnotation"; "SingleElementAnnotation";

       "EmptyStatement"; "AssertStatement"; "IfStatement"; "BasicForStatement";
       "EnhancedForStatement"; "WhileStatement"; "DoStatement"; "TryStatement";
       "SwitchStatement"; "SynchronizedStatement"; "ReturnStatement"; "ThrowStatement";
       "BreakStatement"; "ContinueStatement"; "LabeledStatement"; "ExpressionStatement";

       "TypeBound"; "ThisInvocation"; "SuperInvocation"; "PrimaryInvocation";
       "NameInvocation"; "ConstantLabel"; "DefaultLabel"; "ConditionalElementValue";
       "AnnotationElementValue"; "ArrayInitElementValue"; "ElementValuePair";
       "ConstructorDeclaration"; "StaticInitializer"; "InstanceInitializer";
       "Block"; "VariableDeclarator"; "Chatches"; "CatchClause"; "ForInit"; "ForCond";
       "ForUpdate"; "SwitchBlockStatementGroup"; "DimExpression"; "ArrayCreationInit";
       "ArrayCreationDims"; "Arguments"; "Annotations";
       "TypeArguments"; "Wildcard"; "Parameters"; "Parameter"; "TypeParameter";
       "TypeParameters"; "Initializer"; "Modifiers"; "FieldDeclaration"; "MethodDeclaration";
       "Super"; "Qualifier"; "ReturnType"; "Throws"; "MethodBody"; "Specifier";
       "ClassDeclaration"; "EnumDeclaration"; "EnumConstant"; "Extends"; "Implements";
       "ClassBody"; "EnumBody"; "InterfaceDeclaration"; "AnnotationTypeDeclaration";
       "AnnotationTypeBody"; "ExtendsInterfaces"; "InterfaceBody";
       "PackageDeclaration"; "SingleTypeImportDeclaration"; "TypeImportOnDemandDeclaration";
       "SingleStaticImportDeclaration"; "StaticImportOnDemandDeclaration"; "ImportDeclarations";
       "TypeDeclarations"; "FieldDeclarations"; "CompilationUnit";
     |];

    Astml.python_ns,
    [| (* literal *)
       "IntegerLiteral"; "LongIntegerLiteral"; "FloatNumberLiteral"; "ImagNumberLiteral";
       "StringLiteral"; "unary_operator"; "binary_operator"; "statement";

       (* assignment *)
       "Assign"; "AddAssign"; "SubtAssign"; "MultAssign"; "DivAssign"; "ModAssign";
       "AndAssign"; "OrAssign"; "XorAssign"; "ShiftLAssign"; "ShiftRAssign"; "PowAssign";
       "FDivAssign";

       (* unary-op *)
       "Positive"; "Negative"; "Complement"; "Not";

       (* binary-op *)
       "Mult"; "Div"; "FDiv"; "Mod"; "Add"; "Subt"; "ShiftL"; "ShiftR"; "BitAnd"; "BitOr"; "BitXor";

       (* comp-op *)
       "Eq"; "NotEq"; "Lt"; "Gt"; "Le"; "Ge";  "Is"; "IsNot"; "InOp"; "NotIn";

       (* test *)
       "And"; "Or";

       (* stmt *)
       "SimpleStmt"; "IfStmt"; "WhileStmt"; "ForStmt"; "TryStmt"; "WithStmt"; "FuncDef";
       "ClassDef";

       (* simple-stmt *)
       "ExprStmt"; "PrintStmt"; "DelStmt"; "PassStmt"; "BreakStmt"; "ContinueStmt";
       "ReturnStmt"; "RaiseStmt"; "YieldStmt"; "ImportStmt"; "GlobalStmt"; "ExecStmt";
       "AssertStmt";

       (* primary *)
       "NameAtom"; "ParenAtom"; "TupleAtom"; "YieldAtom"; "TestAtom"; "ListAtom"; "DictAtom";
       "StringConvAtom"; "AttrRef"; "Subscription"; "Slicing"; "Call";

       (* others *)
       "Dummy"; "DottedName"; "Name"; "Lambda"; "Test"; "Power"; "Elif"; "Else";
       "Targets"; "Target"; "Except"; "Suite"; "NamedSuite"; "Parameters";
       "NamedParameters"; "Decorators"; "Decorator"; "Finally"; "In"; "Lhs"; "Rhs";
       "As"; "ListMarker"; "ListIf"; "ListFor"; "DictMarker"; "KeyDatum";
       "SliceItem"; "Lower"; "Upper"; "Stride"; "SliceItemEllipsis"; "Arguments";
       "NamedArguments"; "Argument"; "GenFor"; "GenIf"; "Inheritance"; "Chevron";
       "From"; "Tuple"; "Dict"; "DefParameter"; "Sublist"; "StringLiteral";
       "FileInput";

     |];
  ]
  in
  let len = List.length tokens in (* num of registered langs *)
  let tbl = Hashtbl.create len in
  List.iter
    (fun (lang, a) ->
      Hashtbl.add tbl lang (create_tbl a)
    ) tokens;
  tbl

let attr_name_tbl =
  let attr_names = [|
    (* common *)
    Astml.tid_attr_name;
    Astml.ar_tid_attr_name;
    "constraint";
    "label";
    "name";
    "value";

    (* from cx *)
    "asm"; "attrs"; "clobbers"; "field"; "fields"; "labels"; "lang";
    "op"; "pattern"; "spec"; "storage"; "templ";

    (* from ccx *)
    "active"; "alias"; "assembly";
    "catchAll"; (*"complex";*) "condition"; "const"; "constexpr"; "constant"; "conversionOrOperator";
    "defaulted"; "deleted"; "expansion"; "explicitConstructor"; "exported";
    "field"; "friend"; "fullyQualified"; "global"; "ignored";
    (*"imaginary";*) "inline"; "kind"; "lastName"; "literal"; (*"long"; "longLong";*)
    "mappingName"; "message"; "modifier"; "newTypeId"; "operator";
    "path"; "pointerDeref"; "pureVirtual"; "resolved"; "restrict";
    (*"short"; "signed";*) "static"; "storageClass"; "systemInclude";
    "threadLocal"; "type"; "typeKey"; "typename"; (*"unsigned";*)
    "value"; "varargs"; "variableSized"; "vectored"; "virtual"; "visibility"; "volatile";

    (* from c *)
    "arg"; "content"; "hash"; "kind"; "local"; "operator"; "path"; "register"; "rep";
    "template"; "vars";

    (* from java *)
    "dims"; "ident"; "qualifier"; "va"; "vdids";

  |]
  in
  create_tbl attr_names


let ignored_attr (name, (*v*)_) =
  is_non_label_attr name

let encode_attr (name, value) =
    let v, sep =
      if (String.length value) > string_len_threshold then
	Digest.to_hex (Digest.string value), sep1
      else
	value, sep2
    in
    try
      (Hashtbl.find attr_name_tbl (remove_prefix name))^sep^v
    with
      Not_found -> [%error_log "attr_name not found: \"%s\"" name]; exit 1

let encode_attrs alist =
  let filtered = List.filter (fun a -> not (ignored_attr a)) alist in
  catstr (List.map encode_attr filtered)

(*
let elem_pat = Str.regexp "^\\(.+\\):\\(.+\\)"
let dot_pat  = Str.regexp_string "."
let decomp_elem elem =
  if Str.string_match elem_pat elem 0 then begin
    let lang_prefix = Str.matched_group 1 elem in
    let ln = Str.matched_group 2 elem in
    let names = Str.split dot_pat ln in
    (lang_prefix, names)
  end
  else begin
    [%error_log "illegal element: \"%s\"" elem];
    exit 1
  end

let encode_names lang names =
(*
    [%debug_log "lang=\"%s\" names=[%s]"
      lang (Xlist.to_string (fun x -> x) "; " names)];
*)
  try
    let tbl = Hashtbl.find token_tbl lang in
    let rec encode level = function
      | [] -> ""
      | name::rest ->
	  try
	    let c = Hashtbl.find tbl.(level) name in
	    c^(encode (level + 1) rest)
	  with
	    Not_found ->
              [%fatal_log "name not found: \"%s\"" name];
              exit 1
    in
    encode 0 names
  with
    Not_found ->
      [%fatal_log "lang not found: \"%s\"" lang];
      exit 1

let encode_elem elem =
  let lang_prefix, names = decomp_elem elem in
  encode_names lang_prefix names
*)

let encode { elem_name=elem; elem_attrs=attrs; elem_parser=_; elem_ast_ns=ast_ns; } =
  let tbl = Hashtbl.find token_tbl ast_ns in
  try
    let e = Hashtbl.find tbl elem in
    let a = encode_attrs attrs in
    if a = "" then
      e
    else
      e^sep3^a
  with
    Not_found ->[%error_log "elem not found: \"%s\"" elem]; exit 1



let to_char (*lab*)_ = '0' (* to be implemented *)


let to_simple_string = to_string (* to be implemented *)


let to_short_string ?(ignore_identifiers_flag=false) lab = (* to speed up comparison between labels *)
  ignore ignore_identifiers_flag;
  encode lab

let to_xml_string { elem_name=elem; elem_attrs=attrs; elem_parser=_; _ } =
  let attrs_s =
    String.concat ""
      (List.map (fun a -> " "^(attr_to_xml_string a)) attrs)
  in
  sprintf "%s%s" elem attrs_s

let to_tag ?(strip=false) lab =
  ignore strip;
  lab.elem_name, lab.elem_attrs

let to_elem_data ?(strip=false) ?(afilt=fun _ -> true) loc lab = (* elem name * (string * string) list * content *)
  let __attrs =
    List.filter_map
      (fun (k, v) -> if afilt k then Some (k, XML.encode_string v) else None)
      lab.elem_attrs
  in
  let _attrs =
    if strip then
      __attrs
    else
      (Astml.location_attr_name, Loc.to_attr_value loc) :: __attrs
  in
  let ns = lab.elem_ast_ns in
  let prefix =
    if ns <> "" then
      Astml.get_prefix_by_ns ns
    else
      ""
  in
  let attrs =
    if ns <> "" then
      ("xmlns:"^prefix, ns)::_attrs
    else
      _attrs
  in
  ((if prefix = "" then "" else prefix^":")^lab.elem_name),
  attrs,
  ""


let of_elem_data name attrs _ = (* not yet *)
  { elem_name=name; elem_attrs=attrs; elem_parser=""; elem_ast_ns="" }


let anonymize_attrs attrs =
  List.filter
    (fun (a, _) ->
      let la = remove_prefix a in
      Astml.is_anonymization_resistant_attr la
    ) attrs

let anonymize ?(more=false) { elem_name=e; elem_attrs=attrs; elem_parser=p; elem_ast_ns=ns } =
  ignore more;
  { elem_name=e;
    elem_attrs=anonymize_attrs attrs;
    elem_parser=p;
    elem_ast_ns=ns
  }

let strip lab = lab (* not yet *)

let check_attrs attrs elem_attrs =
  List.for_all
    (fun (a, v) ->
      try
	find_attr a elem_attrs = v
      with
	Not_found -> false
    ) attrs

let conv_pat pat = "^"^pat^"$"

let is_compatible ?(weak=false) _ _ = ignore weak; false

let is_order_insensitive = function
  | _ -> false

let quasi_eq _ _ = false


[%%capture_path
let relabel_allowed (l1, l2) =
  let parser1, parser2 = l1.elem_parser, l2.elem_parser in
  if parser1 <> parser2 then
    failwith "relabel_allowed: labels are parsed by different parsers";

  let name1, name2 = l1.elem_name, l2.elem_name in
  let elem_attrs1, elem_attrs2 = l1.elem_attrs, l2.elem_attrs in

  let matches table =
    List.exists
      (fun ((p1, attrs1), (p2, attrs2)) ->
	let re1 = Str.regexp (conv_pat p1) in
	let re2 = Str.regexp (conv_pat p2) in
	Str.string_match re1 name1 0 &&
	Str.string_match re2 name2 0 &&
	check_attrs attrs1 elem_attrs1 &&
	check_attrs attrs2 elem_attrs2
      ||
	Str.string_match re2 name1 0 &&
	Str.string_match re1 name2 0 &&
	check_attrs attrs2 elem_attrs1 &&
	check_attrs attrs1 elem_attrs2
      ) table
  in
  let res =
    let conf = get_conf parser1 in
    let allowed = matches conf#relabel_allowed_table in
    let disallowed = matches conf#relabel_disallowed_table in
    [%debug_log "allowed: %B" allowed];
    [%debug_log "disallowed: %B" disallowed];
    (allowed || (* anonymize l1 *) name1 = (* anonymize l2 *) name2) && not disallowed
  in
  [%debug_log "%s vs %s -> %B" name1 name2 res];
  res
(* end of func relabel_allowed *)
]

let move_disallowed _ = false

let is_common _ = false

[%%capture_path
let anonymizex tag rules lab =
  let rec scan = function
    | [] -> anonymize lab
    | ((p1, attrs1), (p2, attrs2))::rest ->

	if attrs1 <> [] || attrs2 <> [] then
	  [%warn_log "attribues ignored in <%s>...</%s>" tag tag];

	let re = Str.regexp (conv_pat p1) in
	let name = lab.elem_name in
	if Str.string_match re name 0 then begin
	  let name' = Str.replace_matched p2 name in

	  [%debug_log "%s --> %s" name name'];

	  { elem_name=name';
	    elem_attrs=anonymize_attrs lab.elem_attrs;
	    elem_parser=lab.elem_parser;
	    elem_ast_ns=lab.elem_ast_ns;
	  }
	end
	else
	  scan rest
  in
  scan rules
]

let anonymize2 lab =
  let conf = get_conf lab.elem_parser in
  anonymizex Conf.anonymize2_rules_tag conf#anonymize2_rules lab

let anonymize3 lab =
  let conf = get_conf lab.elem_parser in
  anonymizex Conf.anonymize3_rules_tag conf#anonymize3_rules lab


let rec scan_cats lab = function
  | [] -> false
  | (pat, attrs)::t ->
      let re = Str.regexp (conv_pat pat) in
      if
	Str.string_match re lab.elem_name 0 &&
	check_attrs attrs lab.elem_attrs
      then
	true
      else
	scan_cats lab t

let is_hunk_boundary _ _ = false (* not yet *)

[%%capture_path
let is_collapse_target options lab =
  if options#no_collapse_flag then
    false
  else
    let conf = get_conf lab.elem_parser in
    let res = scan_cats lab conf#collapse_targets in
    [%debug_log "%s -> %B" lab.elem_name res];
    res
]

let forced_to_be_collapsible lab =
  let conf = get_conf lab.elem_parser in
  scan_cats lab conf#forced_to_be_collapsible


let is_to_be_notified lab =
  let conf = get_conf lab.elem_parser in
  scan_cats lab conf#to_be_notified


let is_partition lab =
  let conf = get_conf lab.elem_parser in
  scan_cats lab conf#partition_nodes


let is_boundary lab =
  let conf = get_conf lab.elem_parser in
  let res = scan_cats lab conf#boundary_nodes in
(*
  [%debug_log "%s -> %B" lab.elem_name res];
*)
  res

let is_sequence lab =
  let conf = get_conf lab.elem_parser in
  scan_cats lab conf#sequence_nodes

let is_ntuple lab =
  let conf = get_conf lab.elem_parser in
  scan_cats lab conf#ntuple_nodes


let get_ident_use (*lab*)_ = "" (* not yet *)


(* for fact extraction *)

let get_category lab = to_string (anonymize lab)

let get_name ?(strip=false) { elem_attrs=attrs; _ } =
  ignore strip;
  let rec doit = function
    | [] -> raise Not_found
    | (a, v)::rest ->
        if is_attr_for_named a then
          v
        else
          doit rest
  in
  doit attrs

let get_value { elem_attrs=attrs; _ } =
  let rec doit = function
    | [] -> raise Not_found
    | (a, v)::rest ->
        if is_attr_for_value a then
          v
        else
          doit rest
  in
  doit attrs

let has_value { elem_attrs=attrs; _ } =
  let rec doit = function
    | [] -> false
    | (a, _)::rest ->
        if is_attr_for_value a then
          true
        else
          doit rest
  in
  doit attrs

let has_tid { elem_attrs=attrs; _ } =
  let rec doit = function
    | [] -> false
    | (a, _)::rest ->
        if is_attr_for_tid a then
          true
        else
          doit rest
  in
  doit attrs

let has_non_trivial_value = has_value (* tentative *)
let has_non_trivial_tid = has_tid (* tentative *)

let get_operator { elem_attrs=attrs; _ } =
  let rec doit = function
    | [] -> raise Not_found
    | (a, v)::rest ->
        if is_attr_for_operator a then
          v
        else
          doit rest
  in
  doit attrs

let getlab nd = (Obj.obj nd#data#_label : t)

let cannot_be_keyroot nd =
  let lab = getlab nd in
  let conf = get_conf lab.elem_parser in
  scan_cats lab conf#cannot_be_keyroot

let is_phantom (*lab*)_ = false (* not yet *)

let is_special (*lab*)_ = false (* not yet *)


module CCX = struct

  let is_translation_unit lab =
    match get_elem lab with
    | "TranslationUnit" -> true
    | _ -> false

  let is_pp_stmt lab =
    match get_elem lab with
    | "PreprocessorElifStatement"
    | "PreprocessorElseStatement"
    | "PreprocessorEndifStatement"
    | "PreprocessorErrorStatement"
    | "PreprocessorStatement"
    | "PreprocessorIfdefStatement"
    | "PreprocessorIfndefStatement"
    | "PreprocessorIfStatement"
    | "PreprocessorIncludeStatement"
    | "PreprocessorFunctionStyleMacroDefinition"
    | "PreprocessorObjectStyleMacroDefinition"
    | "PreprocessorPragmaStatement"
    | "PreprocessorUndefStatement"
      -> true
    | _ -> false

  let is_decl lab =
    match get_elem lab with
    | "Declaration"
    | "AliasDeclaration" | "AsmDeclaration" | "ExplicitTemplateInstantiation"
    | "FunctionDefinition" | "FunctionWithTryBlock" | "LinkageSpecification"
    | "NamespaceAlias" | "NamespaceDifinition" | "SimpleDeclaration"
    | "StaticAssertDeclaration" | "TemplateDeclaration" | "TemplateSpecialization"
    | "UsingDeclaration" | "UsingDirective" | "VisibilityLabel"
      -> true
    | _ -> false

  let is_fun_def lab =
    match get_elem lab with
    | "FunctionDefinition" | "FunctionWithTryBlock" -> true
    | _ -> false

  let is_stmt lab =
    match get_elem lab with
    | "Statement"
    | "BreakStatement" | "CaseStatement" | "CatchHandler" | "CompoundStatement"
    | "ContinueStatement" | "DeclarationStatement" | "DefaultStatement"
    | "DoStatement" | "ExpressionStatement" | "ForStatement" | "GotoStatement"
    | "IfStatement" | "LabelStatement" | "NullStatement" | "RangeBasedForStatement"
    | "ReturnStatement" | "SwitchStatement" | "TryBlockStatement" | "WhileStatement"
      -> true
    | _ -> false

  let is_if_stmt lab =
    match get_elem lab with
    | "Statement"
    | "BreakStatement" | "CaseStatement" | "CatchHandler" | "CompoundStatement"
    | "ContinueStatement" | "DeclarationStatement" | "DefaultStatement"
    | "DoStatement" | "ExpressionStatement" | "ForStatement" | "GotoStatement"
    | "IfStatement" | "LabelStatement" | "NullStatement" | "RangeBasedForStatement"
    | "ReturnStatement" | "SwitchStatement" | "TryBlockStatement" | "WhileStatement"
      -> true
    | _ -> false

  let is_expr lab =
    match get_elem lab with
    | "Expression"
    | "ArraySubscriptExpression" | "BinaryExpression" | "BinaryTypeIdExpression"
    | "CastExpression" | "CompoundStatementExpression" | "ConditionalExpression"
    | "DeleteExpression" | "ExpressionList" | "FieldReference" | "FunctionCallExpression"
    | "IdExpression" | "LambdaExpression" | "LiteralExpression" | "NewExpression"
    | "PackExpansionExpression" | "SimpleTypeConstructorExpression" | "TypeIdExpression"
    | "TypeIdInitializerExpression" | "TypenameExpression" | "UnaryExpression"
      -> true
    | _ -> false

end (* of module Label.CCX *)
