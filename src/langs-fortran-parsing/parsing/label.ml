(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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



open Labels
open Label_common

let sprintf = Printf.sprintf

type t =
  | DUMMY

  | EMPTY

  | WEIRD of string

  | ERROR of string

  | Include of string

  | PpDirective of PpDirective.t
  | PpBranch

  | PpBranchDo
  | PpBranchForall
  | PpBranchIf
  | PpBranchSelect
  | PpBranchWhere
  | PpBranchDerivedType
  | PpBranchFunction
  | PpBranchSubroutine
  | PpBranchPu

  | PpBranchEndDo
  | PpBranchEndForall
  | PpBranchEndIf
  | PpBranchEndSelect
  | PpBranchEndWhere
  | PpBranchEndType
  | PpBranchEndFunction
  | PpBranchEndSubroutine
  | PpBranchEndPu

  | PpSectionIf of string
  | PpSectionIfdef of string
  | PpSectionIfndef of string
  | PpSectionElif of string
  | PpSectionElse

  | SubroutineStmtHead of string
  | FunctionStmtHead of string

  | OclDirective of OclDirective.t
  | OCL

  | XlfDirective of Xlf.Directive.t
  | XlfAssertion of Xlf.Assertion.t
  | XlfMisc of Xlf.t
  | XLF

  | DecDirective of Dec.Directive.t
  | DecClause of Dec.Clause.t
  | DecAttribute of Dec.Attribute.t
  | DecMisc of Dec.t
  | DEC

  | OmpDirective of OmpDirective.t
  | OmpClause of OmpClause.t
  | OMP
  | OmpConstruct of OmpConstruct.t

  | AccDirective of AccDirective.t
  | AccClause of AccClause.t
  | ACC
  | AccConstruct of AccConstruct.t

  | LindaCall of LindaCall.t

  | Program
  | ProgramUnit of ProgramUnit.t

  | InternalSubprogram of InternalSubprogram.t
  | ModuleSubprogram of ModuleSubprogram.t

  | Stmt of Stmt.t
  | TypeSpec of TypeSpec.t

  | Ambiguous of Ambiguous.t

  | SpecificationPart
  | ExecutionPart
  | SubprogramPart
  | ImplicitPart

  | Block
  | InterfaceBlock of name option
  | InterfaceBody

  | CaseConstruct
  | DoConstruct of var option
  | ForallConstruct
  | IfConstruct
  | WhereConstruct

  | DerivedTypeDef of name

  | SelectTypeConstruct
  | AssociateConstruct
  | BlockConstruct
  | CriticalConstruct


(* subobject *)
  | ArrayElement of name (* named for Diff/TS *)
  | ArraySection of name (* named for Diff/TS *)
  | StructureComponent of name (* named for Diff/TS *)
  | Substring

  | SectionSubscriptList of name (* named for Diff/TS *)
  | SubscriptTriplet
  | FirstSubscript
  | SecondSubscript
  | Stride

  | SubstringRange

  | StartingPoint
  | EndingPoint

  | ActualArgSpec of name option

  | AltReturnSpec of label

  | PartRef
  | PartName of name

  | Name of name
  | Label of label

  | VariableName of name


(* primary *)
  | Constant of Constant.t
  | ParenExpr
  | ArrayConstructor
  | FunctionReference of name
  | StructureConstructor of name

(* expr *)
  | IntrinsicOperator of IntrinsicOperator.t
  | DefinedOperator of DefinedOperator.t

(* *)
  | LoopControl of var
  | LoopControlWhile
  | LoopControlConcurrent (* F2008 *)

  | GenericSpec of GenericSpec.t

  | Rename
  | OnlyList

  | KindSelector
  | CharSelector
  | LengthSelector
  | LengthSelectorOverride
(*  | CharLenParamValueAsterisk *)
  | TypeParamValueAsterisk (* F2003 *)
  | TypeParamValueColon    (* F2003 *)

  | ExplicitShapeSpec
  | AssumedShapeSpec
  | DeferredShapeSpec
(*  | AssumedSizeSpec *)

  | ComponentDecl of name
(*
  | ComponentAttrSpecPointer
  | ComponentAttrSpecDimension
*)
  | ComponentAttrSpecs

  | InitializationExpr
  | InitializationNull
  | InitializationTarget (* F2008 *)
  | InitializationOldStyle (* GNU *)

  | EntityDecl of name

  | CommonBlockObject of name
  | CommonSpec of name option

  | NamedConstantDef of name

  | AttrSpec of AttrSpec.t
  | AttrSpecs

  | ArraySpec of int
  | ExplicitShapeArray of int
  | AssumedShapeArray of int
  | DeferredShapeArray of int
  | AssumedSizeArray of int
  | AssumedRankArray           (* ISO/IEC TS 29113:2012 *)

  | ComponentArraySpec of int
  | ExplicitShapeComponentArray of int
  | DeferredShapeComponentArray of int

  | AccessSpec of AccessSpec.t
  | TypeAttrSpec of TypeAttrSpec.t

  | StopCode of Constant.t

  | InquireSpec of InquireSpec.t
  | CloseSpec of CloseSpec.t
  | ConnectSpec of ConnectSpec.t
  | PositionSpec of PositionSpec.t
  | IoControlSpec of IoControlSpec.t

  | WaitSpec of WaitSpec.t (* F2003 *)
  | FlushSpec of FlushSpec.t (* F2003 *)


  | BindingAttr of BindingAttr.t (* F2003 *)
  | ProcComponentAttrSpec of ProcComponentAttrSpec.t (* F2003 *)
  | ProcAttrSpec of ProcAttrSpec.t (* F2003 *)

  | InputItemList
  | OutputItemList
  | IoItemList
  | IoLength

  | Format of Format.t

  | IoImpliedDo
  | IoImpliedDoControl of var

  | Array of name

  | EquivalenceSet

  | NamelistGroup of name

  | ObjectName of name

  | DataStmtSet
  | DataStmtValue

(*  | NullInit*)

  | DataImpliedDo
  | DataIDoObject
  | DataIDoObjectList
  | DataStmtObjectList
  | DataStmtValueList

  | PrefixSpec of PrefixSpec.t
  | Prefix
  | DummyArgNameList of name  (* named for Diff/TS *)
  | DummyArgList of name      (* named for Diff/TS *)

  | ActualArgSpecList of name (* named for Diff/TS *)

  | Result of name

  | AlternateReturnIndicator

  | IntentSpec of IntentSpec.t

  | CaseSelector of CaseSelector.t
  | CaseValueRange of CaseValueRange.t

  | ForallHeader
  | ForallTripletSpec of name

  | ImplicitSpec
  | LetterSpec of string * string option

  | FormatSpecification
  | FormatItem of FormatItem.t

  | AcImpliedDo
  | AcImpliedDoControl of var

  | StatVariable
  | ErrmsgVariable (* F2003 *)
  | SourceExpr     (* F2003 *)
  | MoldExpr       (* F2008 *)

  | CommonBlockName of name        (* OpenMP, F2003 *)
  | IntrinsicProcedureName of name (* OpenMP *)

  | LindaFormal (* Linda *)
  | LindaActual (* Linda *)
  | LindaLength (* Linda *)
  | LindaTypeof (* Linda *)

  | Variable

  | PpMacroId of name
  | PpMacroExpr of name
  | PpMacroVariable of name
  | PpMacroEntityDecl of name
  | PpMacroObject of name

  | StructureDecl of name option (* Compaq Fortran *)
  | UnionDecl                    (* Compaq Fortran *)
  | MapDecl                      (* Compaq Fortran *)
  | RecordDecl of name           (* Compaq Fortran *)
  | RecordFieldRef of name       (* Compaq Fortran *)

  | EntityName of name           (* F2003 *)
  | DummyArgName of name
  | ExternalName of name
  | LanguageBindingSpec          (* F2003 *)
  | Suffix                       (* F2003 *)

  | Fragment

  | ModuleNatureIntrinsic    (* F2003 *)
  | ModuleNatureNonIntrinsic (* F2003 *)

  | IfThenBlock
  | ElseIfBlock
  | ElseBlock

  | CrayPointerSpec

  | CaseBlock

  | DoBlock

  | Allocation of name
  | AllocateShapeSpec
  | AllocateShapeSpecList

  | TypeBoundProcDecl of name * name option (* F2008 *)
  | TypeBoundProcedurePart                  (* F2008 *)

  | ProcedureDesignator of name

  | ProcDecl of name (* F2003 *)

  | TypeGuardBlock (* F2003 *)

(*  | InitialProcTarget of name (* F2003 *)*)

  | Association of name (* F2003 *)

  | DeferredCoshapeSpec      (* F2008 *)
  | ExplicitCoshapeSpec      (* F2008 *)
(*  | ExplicitCoshapeSpecUpper (* F2008 *)*)

  | DeferredCoshapeCoarray   (* F2008 *)
  | ExplicitCoshapeCoarray   (* F2008 *)

  | CodimensionDecl of name  (* F2008 *)

  | Enumerator of name       (* F2003 *)
  | EnumDef                  (* F2003 *)

  | BoundsSpec               (* F2003 *)
  | BoundsRemapping          (* F2003 *)
  | BoundsSpecList           (* F2003 *)
  | BoundsRemappingList      (* F2003 *)

  | DataPointerObject of name (* F2003 *)

  | AllocateCoshapeSpec       (* F2008 *)
(*  | AllocateCoshapeSpecUpper  (* F2008 *)*)
  | AllocateCoarraySpec       (* F2008 *)

  | AcquiredLock              (* F2008 *)

  | ImageSelector             (* F2008 *)

  | AllImages                 (* F2008 *)

  | WhereBlock

  | SelectiveOp

  | DefineFileSpec    (* Compaq Fortran *)
  | Options of string (* Compaq Fortran *)

  | ApolloPointerSpec (* Apollo/Domain Fortran *)

  | ProcName of name


let to_string = function
  | DUMMY                     -> "DUMMY"

  | EMPTY                     -> "EMPTY"

  | WEIRD s                   -> "WEIRD:"^s
  | ERROR s                   -> "ERROR:"^s

  | Include s                 -> "Include:"^s

  | PpDirective d             -> "PpDirective."^(PpDirective.to_string d)
  | PpBranch                  -> "PpBranch"
  | PpBranchDo                -> "PpBranchDo"
  | PpBranchForall            -> "PpBranchForall"
  | PpBranchIf                -> "PpBranchIf"
  | PpBranchSelect            -> "PpBranchSelect"
  | PpBranchWhere             -> "PpBranchWhere"
  | PpBranchDerivedType       -> "PpBranchDerivedType"
  | PpBranchFunction          -> "PpBranchFunction"
  | PpBranchSubroutine        -> "PpBranchSubroutine"
  | PpBranchPu                -> "PpBranchPu"

  | PpBranchEndDo             -> "PpBranchEndDo"
  | PpBranchEndForall         -> "PpBranchEndForall"
  | PpBranchEndIf             -> "PpBranchEndIf"
  | PpBranchEndSelect         -> "PpBranchEndSelect"
  | PpBranchEndWhere          -> "PpBranchEndWhere"
  | PpBranchEndType           -> "PpBranchEndType"
  | PpBranchEndFunction       -> "PpBranchEndFunction"
  | PpBranchEndSubroutine     -> "PpBranchEndSubroutine"
  | PpBranchEndPu             -> "PpBranchEndPu"

  | PpSectionIf c             -> "PpSectionIf:"^c
  | PpSectionIfdef n          -> "PpSectionIfdef:"^n
  | PpSectionIfndef n         -> "PpSectionIfndef:"^n
  | PpSectionElif c           -> "PpSectionElif:"^c
  | PpSectionElse             -> "PpSectionElse"

  | SubroutineStmtHead n      -> "SubroutineStmtHead:"^n
  | FunctionStmtHead n        -> "FunctionStmtHead:"^n

  | OclDirective d            -> "OclDirective."^(OclDirective.to_string d)
  | OCL                       -> "OCL"

  | XlfDirective d            -> "XlfDirective."^(Xlf.Directive.to_string d)
  | XlfAssertion a            -> "XlfAssertion."^(Xlf.Assertion.to_string a)
  | XlfMisc x                 -> "Xlf."^(Xlf.to_string x)
  | XLF                       -> "XLF"

  | DecDirective d            -> "DecDirective."^(Dec.Directive.to_string d)
  | DecClause c               -> "DecClause."^(Dec.Clause.to_string c)
  | DecAttribute a            -> "DecAttribute."^(Dec.Attribute.to_string a)
  | DecMisc x                 -> "Dec."^(Dec.to_string x)
  | DEC                       -> "DEC"

  | OmpDirective d            -> "OmpDirective."^(OmpDirective.to_string d)
  | OmpClause c               -> "OmpClause."^(OmpClause.to_string c)
  | OMP                       -> "OMP"
  | OmpConstruct c            -> "OmpConstruct."^(OmpConstruct.to_string c)

  | AccDirective d            -> "AccDirective."^(AccDirective.to_string d)
  | AccClause c               -> "AccClause."^(AccClause.to_string c)
  | ACC                       -> "ACC"
  | AccConstruct c            -> "AccConstruct."^(AccConstruct.to_string c)

  | LindaCall lc              -> "LindaCall."^(LindaCall.to_string lc)

  | Program                   -> "Program"

  | ProgramUnit pu            -> "ProgramUnit."^(ProgramUnit.to_string pu)

  | InternalSubprogram sp     -> "InternalSubprogram."^(InternalSubprogram.to_string sp)
  | ModuleSubprogram sp       -> "ModuleSubprogram."^(ModuleSubprogram.to_string sp)

  | Stmt s                    -> Stmt.to_string s
  | TypeSpec t                -> "TypeSpec."^(TypeSpec.to_string t)

  | Ambiguous a               -> "Ambiguous."^(Ambiguous.to_string a)

  | SpecificationPart         -> "SpecificationPart"
  | ExecutionPart             -> "ExecutionPart"
  | SubprogramPart            -> "SubprogramPart"
  | ImplicitPart              -> "ImplicitPart"

  | Block                     -> "Block"
  | InterfaceBlock n_opt      -> "InterfaceBlock"^(string_opt_to_string ~prefix:":" n_opt)
  | InterfaceBody             -> "InterfaceBody"

  | CaseConstruct             -> "CaseConstruct"
  | DoConstruct v_opt         -> "DoConstruct"^(string_opt_to_string ~prefix:":" v_opt)
  | ForallConstruct           -> "ForallConstruct"
  | IfConstruct               -> "IfConstruct"
  | WhereConstruct            -> "WhereConstruct"

  | DerivedTypeDef n          -> "DerivedTypeDef:"^n

  | SelectTypeConstruct       -> "SelectTypeConstruct"
  | AssociateConstruct        -> "AssociateConstruct"
  | BlockConstruct            -> "BlockConstruct"
  | CriticalConstruct         -> "CriticalConstruct"

  | ArrayElement n            -> "ArrayElement:"^n
  | ArraySection n            -> "ArraySection:"^n
  | StructureComponent n      -> "StructureComponent:"^n
  | Substring                 -> "Substring"


  | SectionSubscriptList n    -> "SectionSubscriptList"^(if n = "" then "" else ":"^n)
  | SubscriptTriplet          -> "SubscriptTriplet"
  | FirstSubscript            -> "FirstSubscript"
  | SecondSubscript           -> "SecondSubscript"
  | Stride                    -> "Stride"

  | SubstringRange            -> "SubstringRange"

  | StartingPoint             -> "StartingPoint"
  | EndingPoint               -> "EndingPoint"

  | ActualArgSpec n_opt       -> "ActualArgSpec"^(string_opt_to_string ~prefix:":" n_opt)

  | AltReturnSpec lab         -> "AltReturnSpec:"^lab

  | PartRef                   -> "PartRef"
  | PartName n                -> "PartName:"^n

  | Name n                    -> "Name:"^n
  | Label lab                 -> "Label:"^lab

  | VariableName n            -> "VariableName:"^n
  | Constant c                -> Constant.to_string c
  | ParenExpr                 -> "ParenExpr"
  | ArrayConstructor          -> "ArrayConstructor"
  | FunctionReference n       -> "FunctionReference:"^n
  | StructureConstructor n    -> "StructureConstructor:"^n

  | IntrinsicOperator op      -> "IntrinsicOperator."^(IntrinsicOperator.to_string op)
  | DefinedOperator op        -> "DefinedOperator."^(DefinedOperator.to_string op)

  | LoopControl v             -> "LoopControl:"^v
  | LoopControlWhile          -> "LoopControlWhile"
  | LoopControlConcurrent     -> "LoopControlConcurrent"

  | GenericSpec g             -> "GenericSpec."^(GenericSpec.to_string g)

  | Rename                    -> "Rename"
  | OnlyList                  -> "OnlyList"

  | KindSelector              -> "KindSelector"
  | CharSelector              -> "CharSelector"
  | LengthSelector            -> "LengthSelector"
  | LengthSelectorOverride    -> "LengthSelectorOverride"
(*  | CharLenParamValueAsterisk -> "CharLenParamValueAsterisk" *)
  | TypeParamValueAsterisk    -> "TypeParamValueAsterisk"
  | TypeParamValueColon       -> "TypeParamValueColon"


  | ExplicitShapeSpec         -> "ExplicitShapeSpec"
  | AssumedShapeSpec          -> "AssumedShapeSpec"
  | DeferredShapeSpec         -> "DeferredShapeSpec"
(*  | AssumedSizeSpec           -> "AssumedSizeSpec" *)

  | ComponentDecl n            -> "ComponentDecl:"^n
(*
  | ComponentAttrSpecPointer   -> "ComponentAttrSpecPointer"
  | ComponentAttrSpecDimension -> "ComponentAttrSpecDimension"
*)
  | ComponentAttrSpecs         -> "ComponentAttrSpecs"

  | InitializationExpr         -> "InitializationExpr"
  | InitializationNull         -> "InitializationNull"
  | InitializationTarget       -> "InitializationTarget"
  | InitializationOldStyle     -> "InitializationOldStyle"

  | EntityDecl n               -> "EntityDecl:"^n

  | CommonBlockObject n        -> "CommonBlockObject:"^n
  | CommonSpec n_opt           -> "CommonSpec"^(string_opt_to_string ~prefix:":" n_opt)

  | NamedConstantDef n         -> "NamedConstantDef:"^n

  | AttrSpec a                 -> "AttrSpec."^(AttrSpec.to_string a)
  | AttrSpecs                  -> "AttrSpecs"

  | ArraySpec i                   -> "ArraySpec:"^(string_of_int i)
  | ExplicitShapeArray i          -> "ExplicitShapeArray:"^(string_of_int i)
  | AssumedShapeArray i           -> "AssumedShapeArray:"^(string_of_int i)
  | DeferredShapeArray i          -> "DeferredShapeArray:"^(string_of_int i)
  | AssumedSizeArray i            -> "AssumedSizeArray:"^(string_of_int i)
  | AssumedRankArray              -> "AssumedRankArray"

  | ComponentArraySpec i          -> "ComponentArraySpec:"^(string_of_int i)
  | ExplicitShapeComponentArray i -> "ExplicitShapeComponentArray:"^(string_of_int i)
  | DeferredShapeComponentArray i -> "DeferredShapeComponentArray:"^(string_of_int i)

  | AccessSpec spec            -> "AccessSpec."^(AccessSpec.to_string spec)
  | TypeAttrSpec spec          -> "TypeAttrSpec."^(TypeAttrSpec.to_string spec)

  | StopCode c                 -> "StopCode."^(Constant.to_string c)

  | InquireSpec spec           -> "InquireSpec."^(InquireSpec.to_string spec)
  | CloseSpec spec             -> "CloseSpec."^(CloseSpec.to_string spec)
  | ConnectSpec spec           -> "ConnectSpec."^(ConnectSpec.to_string spec)
  | PositionSpec spec          -> "PositionSpec."^(PositionSpec.to_string spec)
  | IoControlSpec spec         -> "IoControlSpec."^(IoControlSpec.to_string spec)
  | WaitSpec spec              -> "WaitSpec."^(WaitSpec.to_string spec)
  | FlushSpec spec             -> "FlushSpec."^(FlushSpec.to_string spec)

  | BindingAttr a              -> "BindingAttr."^(BindingAttr.to_string a)
  | ProcComponentAttrSpec s    -> "ProcComponentAttrSpec."^(ProcComponentAttrSpec.to_string s)
  | ProcAttrSpec s             -> "ProcAttrSpec."^(ProcAttrSpec.to_string s)

  | InputItemList              -> "InputItemList"
  | OutputItemList             -> "OutputItemList"
  | IoItemList                 -> "IoItemList"
  | IoLength                   -> "IoLength"

  | Format f                   -> "Format."^(Format.to_string f)

  | IoImpliedDo                -> "IoImpliedDo"
  | IoImpliedDoControl v       -> "IoImpliedDoControl:"^v

  | Array n                    -> "Array:"^n

  | EquivalenceSet             -> "EquivalenceSet"

  | NamelistGroup n            -> "NamelistGroup:"^n

  | ObjectName n               -> "ObjectName:"^n

  | DataStmtSet                -> "DataStmtSet"
  | DataStmtValue              -> "DataStmtValue"

(*  | NullInit                   -> "NullInit"*)

  | DataImpliedDo              -> "DataImpliedDo"
  | DataIDoObject              -> "DataIDoObject"
  | DataIDoObjectList          -> "DataIDoObjectList"
  | DataStmtObjectList         -> "DataStmtObjectList"
  | DataStmtValueList          -> "DataStmtValueList"

  | PrefixSpec p               -> "PrefixSpec."^(PrefixSpec.to_string p)
  | Prefix                     -> "Prefix"
  | DummyArgNameList n         -> "DummyArgNameList"^(if n = "" then "" else ":"^n)
  | DummyArgList n             -> "DummyArgList"^(if n = "" then "" else ":"^n)

  | ActualArgSpecList n        -> "ActualArgSpecList"^(if n = "" then "" else ":"^n)

  | Result n                   -> "Result:"^n

  | AlternateReturnIndicator   -> "AlternateReturnIndicator"

  | IntentSpec spec            -> "IntentSpec."^(IntentSpec.to_string spec)

  | CaseSelector sel           -> "CaseSelector."^(CaseSelector.to_string sel)
  | CaseValueRange r           -> "CaseValueRange."^(CaseValueRange.to_string r)

  | ForallHeader               -> "ForallHeader"
  | ForallTripletSpec n        -> "ForallTripletSpec:"^n

  | ImplicitSpec               -> "ImplicitSpec"
  | LetterSpec(l, l_opt)       -> "LetterSpec:"^l^(string_opt_to_string ~prefix:":" l_opt)

  | FormatSpecification        -> "FormatSpecification"
  | FormatItem i               -> "FormatItem."^(FormatItem.to_string i)

  | AcImpliedDo                -> "AcImpliedDo"
  | AcImpliedDoControl v       -> "AcImpliedDoControl:"^v

  | StatVariable               -> "StatVariable"
  | ErrmsgVariable             -> "ErrmsgVariable"
  | SourceExpr                 -> "SourceExpr"
  | MoldExpr                   -> "MoldExpr"

  | CommonBlockName n          -> "CommonBlockName:"^n (* OpenMP *)

  | IntrinsicProcedureName n   -> "IntrinsicProcedureName:"^n (* OpenMP *)

  | LindaFormal                -> "LindaFormal"
  | LindaActual                -> "LindaActual"
  | LindaLength                -> "LindaLength"
  | LindaTypeof                -> "LindaTypeof"

  | Variable                   -> "Variable"

  | PpMacroId n                -> "PpMacroId:"^n
  | PpMacroExpr n              -> "PpMacroExpr:"^n
  | PpMacroVariable n          -> "PpMacroVariable:"^n
  | PpMacroEntityDecl n        -> "PpMacroEntityDecl:"^n
  | PpMacroObject n            -> "PpMacroObject:"^n

  | StructureDecl n_opt        -> "StructureDecl"^(string_opt_to_string ~prefix:":" n_opt)
  | UnionDecl                  -> "UnionDecl"
  | MapDecl                    -> "MapDecl"
  | RecordDecl n               -> "RecordDecl:"^n
  | RecordFieldRef n           -> "RecordFieldRef:"^n

  | EntityName n               -> "EntityName:"^n
  | DummyArgName n             -> "DummyArgName:"^n
  | ExternalName n             -> "ExternalName:"^n

  | LanguageBindingSpec        -> "LanguageBindingSpec"
  | Suffix                     -> "Suffix"

  | Fragment                   -> "Fragment"

  | ModuleNatureIntrinsic      -> "ModuleNatureIntrinsic"
  | ModuleNatureNonIntrinsic   -> "ModuleNatureNonIntrinsic"

  | IfThenBlock                -> "IfThenBlock"
  | ElseIfBlock                -> "ElseIfBlock"
  | ElseBlock                  -> "ElseBlock"

  | CrayPointerSpec            -> "CrayPointerSpec"

  | CaseBlock                  -> "CaseBlock"

  | DoBlock                    -> "DoBlock"

  | Allocation n               -> "Allocation:"^n
  | AllocateShapeSpec          -> "AllocateShapeSpec"
  | AllocateShapeSpecList      -> "AllocateShapeSpecList"

  | TypeBoundProcDecl(n, n_opt) -> "TypeBoundProcDecl:"^n^(string_opt_to_string ~prefix:":" n_opt)
  | TypeBoundProcedurePart      -> "TypeBoundProcedurePart"

  | ProcedureDesignator n       -> "ProcedureDesignator:"^n

  | ProcDecl n                  -> "ProcDecl:"^n

  | TypeGuardBlock              -> "TypeGuard"

(*  | InitialProcTarget n         -> "InitialProcTarget:"^n*)

  | Association n               -> "Association:"^n

  | DeferredCoshapeSpec         -> "DeferredCoshapeSpec"
  | ExplicitCoshapeSpec         -> "ExplicitCoshapeSpec"
(*  | ExplicitCoshapeSpecUpper    -> "ExplicitCoshapeSpecUpper"*)

  | DeferredCoshapeCoarray      -> "DeferredCoshapeCoarray"
  | ExplicitCoshapeCoarray      -> "ExplicitCoshapeCoarray"

  | CodimensionDecl n           -> "CodimensionDecl:"^n

  | Enumerator n                -> "Enumerator:"^n
  | EnumDef                     -> "EnumDef"

  | BoundsSpec               -> "BoundsSpec"
  | BoundsRemapping          -> "BoundsRemapping"
  | BoundsSpecList           -> "BoundsSpecList"
  | BoundsRemappingList      -> "BoundsRemappingList"

  | DataPointerObject n      -> "DataPointerObject:"^n

  | AllocateCoshapeSpec      -> "AllocateCoshapeSpec"
(*  | AllocateCoshapeSpecUpper -> "AllocateCoshapeSpecUpper"*)
  | AllocateCoarraySpec      -> "AllocateCoarraySpec"

  | AcquiredLock             -> "AcquiredLock"

  | ImageSelector            -> "ImageSelector"

  | AllImages                -> "AllImages"

  | WhereBlock               -> "WhereBlock"

  | SelectiveOp              -> "SelectiveOp"

  | DefineFileSpec           -> "DefineFileSpec"
  | Options s                -> "Options:"^s

  | ApolloPointerSpec        -> "ApolloPointerSpec"

  | ProcName n               -> "ProcName:"^n

let to_simple_string = function
  | DUMMY                     -> "<dummy>"

  | EMPTY                     -> "<empty>"

  | WEIRD s                   -> "<weird:"^s^">"
  | ERROR s                   -> "<error:"^s^">"

  | Include s                 -> "include "^s

  | PpDirective d             -> PpDirective.to_simple_string d
  | PpBranch                  -> "<pp-branch>"
  | PpBranchDo                -> "<pp-branch-do>"
  | PpBranchForall            -> "<pp-branch-forall>"
  | PpBranchIf                -> "<pp-branch-if>"
  | PpBranchSelect            -> "<pp-branch-select>"
  | PpBranchWhere             -> "<pp-branch-where>"
  | PpBranchDerivedType       -> "<pp-branch-derived-type>"
  | PpBranchFunction          -> "<pp-branch-function>"
  | PpBranchSubroutine        -> "<pp-branch-subroutine>"
  | PpBranchPu                -> "<pp-branch-pu>"

  | PpBranchEndDo             -> "<pp-branch-end-do>"
  | PpBranchEndForall         -> "<pp-branch-end-forall>"
  | PpBranchEndIf             -> "<pp-branch-end-if>"
  | PpBranchEndSelect         -> "<pp-branch-end-select>"
  | PpBranchEndWhere          -> "<pp-branch-end-where>"
  | PpBranchEndType           -> "<pp-branch-end-type>"
  | PpBranchEndFunction       -> "<pp-branch-end-function>"
  | PpBranchEndSubroutine     -> "<pp-branch-end-subroutine>"
  | PpBranchEndPu             -> "<pp-branch-end-pu>"

  | PpSectionIf s             -> "<pp-section-if:"^s^">"
  | PpSectionIfdef s          -> "<pp-section-ifdef:"^s^">"
  | PpSectionIfndef s         -> "<pp-section-ifndef:"^s^">"
  | PpSectionElif s           -> "<pp-section-elif:"^s^">"
  | PpSectionElse             -> "<pp-section-else>"

  | SubroutineStmtHead s      -> "subroutine "^s
  | FunctionStmtHead s        -> "function "^s

  | OclDirective d            -> OclDirective.to_simple_string d
  | OCL                       -> "<OCL>"

  | XlfDirective d            -> Xlf.Directive.to_simple_string d
  | XlfAssertion a            -> Xlf.Assertion.to_simple_string a
  | XlfMisc x                 -> Xlf.to_simple_string x
  | XLF                       -> "<XLF>"

  | DecDirective d            -> Dec.Directive.to_simple_string d
  | DecClause c               -> Dec.Clause.to_simple_string c
  | DecAttribute a            -> Dec.Attribute.to_simple_string a
  | DecMisc x                 -> Dec.to_string x
  | DEC                       -> "<DEC>"

  | OmpDirective d            -> OmpDirective.to_simple_string d
  | OmpClause c               -> OmpClause.to_simple_string c
  | OMP                       -> "<OMP>"
  | OmpConstruct c            -> OmpConstruct.to_simple_string c

  | AccDirective d            -> AccDirective.to_simple_string d
  | AccClause c               -> AccClause.to_simple_string c
  | ACC                       -> "<ACC>"
  | AccConstruct c            -> AccConstruct.to_simple_string c

  | LindaCall lc              -> LindaCall.to_simple_string lc

  | Program                   -> "<program>"

  | ProgramUnit pu            -> ProgramUnit.to_simple_string pu

  | InternalSubprogram sp     -> InternalSubprogram.to_simple_string sp
  | ModuleSubprogram sp       -> ModuleSubprogram.to_simple_string sp

  | Stmt s                    -> Stmt.to_simple_string s
  | TypeSpec t                -> TypeSpec.to_simple_string t

  | Ambiguous a               -> Ambiguous.to_simple_string a

  | SpecificationPart         -> "<specification-part>"
  | ExecutionPart             -> "<execution-part>"
  | SubprogramPart            -> "<subprogram-part>"
  | ImplicitPart              -> "<implicit-part>"

  | Block                     -> "<block>"
  | InterfaceBlock n_opt      -> sprintf "<interface-block%s>" (string_opt_to_string ~suffix:":" n_opt)
  | InterfaceBody             -> "<interface-body>"

  | CaseConstruct             -> "<case-construct>"
  | DoConstruct v_opt         -> sprintf "<do-construct%s>" (string_opt_to_string ~suffix:":" v_opt)
  | ForallConstruct           -> "<forall-construct>"
  | IfConstruct               -> "<if-construct>"
  | WhereConstruct            -> "<where-construct>"

  | DerivedTypeDef n          -> sprintf "<derived-type-def:%s>" n

  | SelectTypeConstruct       -> "<select-type-construct>"
  | AssociateConstruct        -> "<associate-construct>"
  | BlockConstruct            -> "<block-construct>"
  | CriticalConstruct         -> "<critical-construct>"

  | ArrayElement n            -> sprintf "<array-element:%s>" n
  | ArraySection n            -> sprintf "<array-section:%s>" n
  | StructureComponent n      -> sprintf "<structure-component:%s>" n
  | Substring                 -> "<substring>"


  | SectionSubscriptList n    -> sprintf "<section-subscript-list%s>" (if n = "" then "" else ":"^n)
  | SubscriptTriplet          -> "<subscript-triplet>"
  | FirstSubscript            -> "<first-subscript>"
  | SecondSubscript           -> "<second-subscript>"
  | Stride                    -> "<stride>"

  | SubstringRange            -> "<substring-range>"

  | StartingPoint             -> "<starting-point>"
  | EndingPoint               -> "<ending-point>"

  | ActualArgSpec n_opt       -> string_opt_to_string ~suffix:"=" n_opt

  | AltReturnSpec lab         -> "*"^lab

  | PartRef                   -> "<part-ref>"
  | PartName n                -> "<part-name:"^n^">"

  | Name n                    -> n
  | Label lab                 -> lab

  | VariableName n            -> n
  | Constant c                -> Constant.to_simple_string c
  | ParenExpr                 -> "<paren-expr>"
  | ArrayConstructor          -> "<array-constructor>"
  | FunctionReference n       -> n
  | StructureConstructor n    -> n

  | IntrinsicOperator op      -> IntrinsicOperator.to_simple_string op
  | DefinedOperator op        -> DefinedOperator.to_simple_string op

  | LoopControl v             -> "<loop-control:"^v^">"
  | LoopControlWhile          -> "<loop-control-while>"
  | LoopControlConcurrent     -> "<loop-control-concurrent>"

  | GenericSpec g             -> GenericSpec.to_simple_string g

  | Rename                    -> "=>"
  | OnlyList                  -> "<only-list>"

  | KindSelector              -> "<kind-selector>"
  | CharSelector              -> "<char-selector>"
  | LengthSelector            -> "<length-selector>"
  | LengthSelectorOverride    -> "<length-selector-override>"
(*  | CharLenParamValueAsterisk -> "*" *)
  | TypeParamValueAsterisk    -> "*"
  | TypeParamValueColon       -> ":"

  | ExplicitShapeSpec         -> "<explicit-shape-spec>"
  | AssumedShapeSpec          -> "<assumed-shape-spec>"
  | DeferredShapeSpec         -> "<deferred-shape-spec>"
(*  | AssumedSizeSpec           -> "<assumed-size-spec>" *)

  | ComponentDecl n            -> n
(*
  | ComponentAttrSpecPointer   -> "<component-attr-spec-pointer>"
  | ComponentAttrSpecDimension -> "<component-attr-spec-dimension>"
*)
  | ComponentAttrSpecs         -> "<component-attr-specs>"

  | InitializationExpr         -> "<initialization-expr>"
  | InitializationNull         -> "null()"
  | InitializationTarget       -> "<initial-data-target>"
  | InitializationOldStyle     -> "<old-style-init>"

  | EntityDecl n               -> n

  | CommonBlockObject n        -> n
  | CommonSpec n_opt           -> "/"^(string_opt_to_string n_opt)^"/"

  | NamedConstantDef n         -> "<named-constant-def:"^n^">"

  | AttrSpec a                 -> AttrSpec.to_simple_string a
  | AttrSpecs                  -> "<attr-specs>"

  | ArraySpec i                   -> "<array-spec:"^(string_of_int i)^">"
  | ExplicitShapeArray i          -> "<explicit-shape:"^(string_of_int i)^">"
  | AssumedShapeArray i           -> "<assumed-shape:"^(string_of_int i)^">"
  | DeferredShapeArray i          -> "<deferred-shape:"^(string_of_int i)^">"
  | AssumedSizeArray i            -> "<assumed-size:"^(string_of_int i)^">"
  | AssumedRankArray              -> "<assumed-rank>"

  | ComponentArraySpec i          -> "<component-array-spec:"^(string_of_int i)^">"
  | ExplicitShapeComponentArray i -> "<explicit-shape:"^(string_of_int i)^">"
  | DeferredShapeComponentArray i -> "<deferred-shape:"^(string_of_int i)^">"

  | AccessSpec spec            -> AccessSpec.to_simple_string spec
  | TypeAttrSpec spec          -> TypeAttrSpec.to_simple_string spec

  | StopCode c                 -> Constant.to_simple_string c

  | InquireSpec spec           -> InquireSpec.to_simple_string spec
  | CloseSpec spec             -> CloseSpec.to_simple_string spec
  | ConnectSpec spec           -> ConnectSpec.to_simple_string spec
  | PositionSpec spec          -> PositionSpec.to_simple_string spec
  | IoControlSpec spec         -> IoControlSpec.to_simple_string spec
  | WaitSpec spec              -> WaitSpec.to_simple_string spec
  | FlushSpec spec             -> FlushSpec.to_simple_string spec

  | BindingAttr a              -> BindingAttr.to_simple_string a
  | ProcComponentAttrSpec s    -> ProcComponentAttrSpec.to_simple_string s
  | ProcAttrSpec s             -> ProcAttrSpec.to_simple_string s

  | InputItemList              -> "<input-item-list>"
  | OutputItemList             -> "<output-item-list>"
  | IoItemList                 -> "<io-item-list>"
  | IoLength                   -> "<iolength>"

  | Format f                   -> Format.to_simple_string f

  | IoImpliedDo                -> "<io-implied-do>"
  | IoImpliedDoControl v       -> "<io-implied-do-control:"^v^">"

  | Array n                    -> n

  | EquivalenceSet             -> "<equivalence-set>"

  | NamelistGroup n            -> "<namelist-group:"^n^">"

  | ObjectName n               -> n

  | DataStmtSet                -> "<data-stmt-set>"
  | DataStmtValue              -> "<data-stmt-value>"

(*  | NullInit                   -> "null()"*)

  | DataImpliedDo              -> "<data-implied-do>"
  | DataIDoObject              -> "<data-i-do-object>"
  | DataIDoObjectList          -> "<data-i-do-object-list>"
  | DataStmtObjectList         -> "<data-stmt-object-list>"
  | DataStmtValueList          -> "<data-stmt-value-list>"

  | PrefixSpec p               -> PrefixSpec.to_simple_string p
  | Prefix                     -> "<prefix>"
  | DummyArgNameList n         -> sprintf "<dummy-arg-name-list%s>" (if n = "" then "" else ":"^n)
  | DummyArgList n             -> sprintf "<dummy-arg-list%s>" (if n = "" then "" else ":"^n)

  | ActualArgSpecList n        -> sprintf "<actual-arg-spec-list%s>" (if n = "" then "" else ":"^n)

  | Result n                   -> "result("^n^")"

  | AlternateReturnIndicator   -> "<alternate-return-indicator>"

  | IntentSpec spec            -> IntentSpec.to_simple_string spec

  | CaseSelector sel           -> CaseSelector.to_simple_string sel
  | CaseValueRange r           -> CaseValueRange.to_simple_string r

  | ForallHeader               -> "<forall-header>"
  | ForallTripletSpec n        -> "<forall-triplet-spec:"^n^">"

  | ImplicitSpec               -> "<implicit-spec>"
  | LetterSpec(l, l_opt)       -> l^(string_opt_to_string ~prefix:"-" l_opt)

  | FormatSpecification        -> "<format-specification>"
  | FormatItem i               -> FormatItem.to_simple_string i

  | AcImpliedDo                -> "<ac-implied-do>"
  | AcImpliedDoControl v       -> "<ac-implied-do-control:"^v^">"

  | StatVariable               -> "<stat-variable>"
  | ErrmsgVariable             -> "<errmsg-variable>"
  | SourceExpr                 -> "<source-expr>"
  | MoldExpr                   -> "<mold-expr>"

  | CommonBlockName n          -> "/"^n^"/" (* OpenMP *)

  | IntrinsicProcedureName n   -> n (* OpenMP *)

  | LindaFormal                -> "<linda-formal>"
  | LindaActual                -> "<linda-actual>"
  | LindaLength                -> "<linda-length>"
  | LindaTypeof                -> "typeof"

  | Variable                   -> "<variable>"

  | PpMacroId n                -> n
  | PpMacroExpr n              -> n
  | PpMacroVariable n          -> n
  | PpMacroEntityDecl n        -> n
  | PpMacroObject n            -> n

  | StructureDecl n_opt        -> sprintf "<structure%s>" (string_opt_to_string ~prefix:":" n_opt)
  | UnionDecl                  -> "<union-decl>"
  | MapDecl                    -> "<map-decl>"
  | RecordDecl n               -> "/"^n^"/"
  | RecordFieldRef n           -> n

  | EntityName n               -> n
  | DummyArgName n             -> n
  | ExternalName n             -> n

  | LanguageBindingSpec        -> "bind(C)"
  | Suffix                     -> "<suffix>"

  | Fragment                   -> "<fragment>"

  | ModuleNatureIntrinsic      -> "intrinsic"
  | ModuleNatureNonIntrinsic   -> "non_intrinsic"

  | IfThenBlock                -> "<if-then-block>"
  | ElseIfBlock                -> "<else-if-block>"
  | ElseBlock                  -> "<else-block>"

  | CrayPointerSpec            -> "<cray-pointer-spec>"

  | CaseBlock                  -> "<case-block>"

  | DoBlock                    -> "<do-block>"

  | Allocation n               -> sprintf "<allocation:%s>" n
  | AllocateShapeSpec          -> "<allocate-shape-spec>"
  | AllocateShapeSpecList      -> "<allocate-shape-spec-list>"

  | TypeBoundProcDecl(n, n_opt) -> n^(string_opt_to_string ~prefix:" => " n_opt)

  | TypeBoundProcedurePart      -> "<type-bound-procedure-part>"

  | ProcedureDesignator n       -> sprintf "<procedure-designator:%s>" n

  | ProcDecl n                  -> sprintf "%s => " n

  | TypeGuardBlock              -> "<type-guard-block>"

(*  | InitialProcTarget n         -> n*)

  | Association n               -> sprintf "association %s =>" n

  | DeferredCoshapeSpec         -> ":"
  | ExplicitCoshapeSpec         -> "<explicit-coshape-spec>"
(*  | ExplicitCoshapeSpecUpper    -> "<explicit-coshape-spec-uppper>"*)

  | DeferredCoshapeCoarray      -> "<deferred-coshape-coarray>"
  | ExplicitCoshapeCoarray      -> "<explicit-coshape-coarray>"

  | CodimensionDecl n           -> n

  | Enumerator n                -> n
  | EnumDef                     -> "<enum-def>"

  | BoundsSpec               -> "<bounds-spec>"
  | BoundsRemapping          -> "<bounds-remapping>"
  | BoundsSpecList           -> "<bounds-spec-list>"
  | BoundsRemappingList      -> "<bounds-remapping-list>"

  | DataPointerObject n      -> n

  | AllocateCoshapeSpec      -> "<allocate-coshape-spec>"
(*  | AllocateCoshapeSpecUpper -> "<allocate-coshape-spec-upper>"*)
  | AllocateCoarraySpec      -> "<allocate-coarray-spec>"

  | AcquiredLock             -> "acquired_lock"

  | ImageSelector            -> "<image-selector>"

  | AllImages                -> "*"

  | WhereBlock               -> "<where-block>"

  | SelectiveOp              -> "<selective-op>"

  | DefineFileSpec           -> "<define-file-spec>"
  | Options s                -> "options "^s

  | ApolloPointerSpec        -> "<apollo-pointer-spec>"

  | ProcName n               -> n

let to_tag ?(strip=false) lab =
  ignore strip;
  match lab with
  | DUMMY                     -> "DUMMY", []

  | EMPTY                     -> "EMPTY", []

  | WEIRD s                   -> "WEIRD", [value_attr_name,s]
  | ERROR s                   -> "ERROR", ["message",s]

  | Include s                 -> "Include", [path_attr_name,strlit_to_encoded_path s]

  | PpDirective d             -> PpDirective.to_tag d
  | PpBranch                  -> "PpBranch", []
  | PpBranchDo                -> "PpBranchDo", []
  | PpBranchForall            -> "PpBranchForall", []
  | PpBranchIf                -> "PpBranchIf", []
  | PpBranchSelect            -> "PpBranchSelect", []
  | PpBranchWhere             -> "PpBranchWhere", []
  | PpBranchDerivedType       -> "PpBranchDerivedType", []
  | PpBranchFunction          -> "PpBranchFunction", []
  | PpBranchSubroutine        -> "PpBranchSubroutine", []
  | PpBranchPu                -> "PpBranchPu", []

  | PpBranchEndDo             -> "PpBranchEndDo", []
  | PpBranchEndForall         -> "PpBranchEndForall", []
  | PpBranchEndIf             -> "PpBranchEndIf", []
  | PpBranchEndSelect         -> "PpBranchEndSelect", []
  | PpBranchEndWhere          -> "PpBranchEndWhere", []
  | PpBranchEndType           -> "PpBranchEndType", []
  | PpBranchEndFunction       -> "PpBranchEndFunction", []
  | PpBranchEndSubroutine     -> "PpBranchEndSubroutine", []
  | PpBranchEndPu             -> "PpBranchEndPu", []

  | PpSectionIf c             -> "PpSectionIf", ["cond",XML.encode_string c]
  | PpSectionIfdef n          -> "PpSectionIfdef", [name_attr_name,n]
  | PpSectionIfndef n         -> "PpSectionIfndef", [name_attr_name,n]
  | PpSectionElif c           -> "PpSectionElif", ["cond",XML.encode_string c]
  | PpSectionElse             -> "PpSectionElse", []

  | SubroutineStmtHead n      -> "SubroutineStmtHead", [name_attr_name,n]
  | FunctionStmtHead n        -> "FunctionStmtHead", [name_attr_name,n]

  | OclDirective d            -> OclDirective.to_tag d
  | OCL                       -> "OCL", []

  | XlfDirective d            -> Xlf.Directive.to_tag d
  | XlfAssertion a            -> Xlf.Assertion.to_tag a
  | XlfMisc x                 -> Xlf.to_tag x
  | XLF                       -> "XLF", []

  | DecDirective d            -> Dec.Directive.to_tag d
  | DecClause c               -> Dec.Clause.to_tag c
  | DecAttribute a            -> Dec.Attribute.to_tag a
  | DecMisc x                 -> Dec.to_tag x
  | DEC                       -> "DEC", []

  | OmpDirective d            -> OmpDirective.to_tag d
  | OmpClause c               -> OmpClause.to_tag c
  | OMP                       -> "OMP", []
  | OmpConstruct c            -> OmpConstruct.to_tag c

  | AccDirective d            -> AccDirective.to_tag d
  | AccClause c               -> AccClause.to_tag c
  | ACC                       -> "ACC", []
  | AccConstruct c            -> AccConstruct.to_tag c

  | LindaCall lc              -> LindaCall.to_tag lc

  | Program                   -> "Program", []

  | ProgramUnit pu            -> ProgramUnit.to_tag pu

  | InternalSubprogram sp     -> InternalSubprogram.to_tag sp
  | ModuleSubprogram sp       -> ModuleSubprogram.to_tag sp

  | Stmt s                    -> Stmt.to_tag s
  | TypeSpec t                -> TypeSpec.to_tag t

  | Ambiguous a               -> Ambiguous.to_tag a

  | SpecificationPart         -> "SpecificationPart", []
  | ExecutionPart             -> "ExecutionPart", []
  | SubprogramPart            -> "SubprogramPart", []
  | ImplicitPart              -> "ImplicitPart", []

  | Block                     -> "Block", []
  | InterfaceBlock n_opt      -> "InterfaceBlock", (string_opt_to_attr name_attr_name n_opt)
  | InterfaceBody             -> "InterfaceBody", []

  | CaseConstruct             -> "CaseConstruct", []
  | DoConstruct v_opt         -> "DoConstruct", (string_opt_to_attr var_attr_name v_opt)
  | ForallConstruct           -> "ForallConstruct", []
  | IfConstruct               -> "IfConstruct", []
  | WhereConstruct            -> "WhereConstruct", []

  | DerivedTypeDef n          -> "DerivedTypeDef", [name_attr_name,n]

  | SelectTypeConstruct       -> "SelectTypeConstruct", []
  | AssociateConstruct        -> "AssociateConstruct", []
  | BlockConstruct            -> "BlockConstruct", []
  | CriticalConstruct         -> "CriticalConstruct", []

  | ArrayElement n            -> "ArrayElement", [name_attr_name,n]
  | ArraySection n            -> "ArraySection", [name_attr_name,n]
  | StructureComponent n      -> "StructureComponent", [name_attr_name,n]
  | Substring                 -> "Substring", []


  | SectionSubscriptList n    -> "SectionSubscriptList", (if n = "" then [] else [name_attr_name,n])
  | SubscriptTriplet          -> "SubscriptTriplet", []
  | FirstSubscript            -> "FirstSubscript", []
  | SecondSubscript           -> "SecondSubscript", []
  | Stride                    -> "Stride", []

  | SubstringRange            -> "SubstringRange", []

  | StartingPoint             -> "StartingPoint", []
  | EndingPoint               -> "EndingPoint", []

  | ActualArgSpec n_opt       -> "ActualArgSpec", (string_opt_to_attr name_attr_name n_opt)

  | AltReturnSpec lab         -> "AltReturnSpec", [label_attr_name,lab]

  | PartRef                   -> "PartRef", []
  | PartName n                -> "PartName", [name_attr_name,n]

  | Name n                    -> "Name", [name_attr_name,n]
  | Label lab                 -> "Label", [label_attr_name,lab]

  | VariableName n            -> "VariableName", [name_attr_name,n]
  | Constant c                -> Constant.to_tag c
  | ParenExpr                 -> "ParenExpr", []
  | ArrayConstructor          -> "ArrayConstructor", []
  | FunctionReference n       -> "FunctionReference", [name_attr_name,n]
  | StructureConstructor n    -> "StructureConstructor", [name_attr_name,n]

  | IntrinsicOperator op      -> IntrinsicOperator.to_tag op
  | DefinedOperator op        -> DefinedOperator.to_tag op

  | LoopControl v             -> "LoopControl", [var_attr_name,v]
  | LoopControlWhile          -> "LoopControlWhile", []
  | LoopControlConcurrent     -> "LoopControlConcurrent", []

  | GenericSpec g             -> GenericSpec.to_tag g

  | Rename                    -> "Rename", []
  | OnlyList                  -> "OnlyList", []

  | KindSelector              -> "KindSelector", []
  | CharSelector              -> "CharSelector", []
  | LengthSelector            -> "LengthSelector", []
  | LengthSelectorOverride    -> "LengthSelectorOverride", []
(*  | CharLenParamValueAsterisk -> "CharLenParamValueAsterisk", [] *)
  | TypeParamValueAsterisk    -> "TypeParamValueAsterisk", []
  | TypeParamValueColon       -> "TypeParamValueColon", []


  | ExplicitShapeSpec         -> "ExplicitShapeSpec", []
  | AssumedShapeSpec          -> "AssumedShapeSpec", []
  | DeferredShapeSpec         -> "DeferredShapeSpec", []
(*  | AssumedSizeSpec           -> "AssumedSizeSpec", [] *)

  | ComponentDecl n            -> "ComponentDecl", [name_attr_name,n]
(*
  | ComponentAttrSpecPointer   -> "ComponentAttrSpecPointer", []
  | ComponentAttrSpecDimension -> "ComponentAttrSpecDimension", []
*)
  | ComponentAttrSpecs         -> "ComponentAttrSpecs", []

  | InitializationExpr         -> "InitializationExpr", []
  | InitializationNull         -> "InitializationNull", []
  | InitializationTarget       -> "InitializationTarget", []
  | InitializationOldStyle     -> "InitializationOldStyle", []

  | EntityDecl n               -> "EntityDecl", [name_attr_name,n]

  | CommonBlockObject n        -> "CommonBlockObject", [name_attr_name,n]
  | CommonSpec n_opt           -> "CommonSpec", (string_opt_to_attr name_attr_name n_opt)

  | NamedConstantDef n         -> "NamedConstantDef", [name_attr_name,n]

  | AttrSpec a                 -> AttrSpec.to_tag a
  | AttrSpecs                  -> "AttrSpecs", []

  | ArraySpec i                -> "ArraySpec", [rank_attr_name,string_of_int i]
  | ExplicitShapeArray i       -> "ExplicitShapeArray", [rank_attr_name,string_of_int i]
  | AssumedShapeArray i        -> "AssumedShapeArray", [rank_attr_name,string_of_int i]
  | DeferredShapeArray i       -> "DeferredShapeArray", [rank_attr_name,string_of_int i]
  | AssumedSizeArray i         -> "AssumedSizeArray", [rank_attr_name,string_of_int i]
  | AssumedRankArray           -> "AssumedRank", []

  | ComponentArraySpec i          -> "ComponentArraySpec", [rank_attr_name,string_of_int i]
  | ExplicitShapeComponentArray i -> "ExplicitShapeComponentArray", [rank_attr_name,string_of_int i]
  | DeferredShapeComponentArray i -> "DeferredShapeComponentArray", [rank_attr_name,string_of_int i]

  | AccessSpec spec            -> AccessSpec.to_tag spec
  | TypeAttrSpec spec          -> TypeAttrSpec.to_tag spec

  | StopCode c                 -> Constant.to_tag c

  | InquireSpec spec           -> InquireSpec.to_tag spec
  | CloseSpec spec             -> CloseSpec.to_tag spec
  | ConnectSpec spec           -> ConnectSpec.to_tag spec
  | PositionSpec spec          -> PositionSpec.to_tag spec
  | IoControlSpec spec         -> IoControlSpec.to_tag spec
  | WaitSpec spec              -> WaitSpec.to_tag spec
  | FlushSpec spec             -> FlushSpec.to_tag spec

  | BindingAttr a              -> BindingAttr.to_tag a
  | ProcComponentAttrSpec s    -> ProcComponentAttrSpec.to_tag s
  | ProcAttrSpec s             -> ProcAttrSpec.to_tag s

  | InputItemList              -> "InputItemList", []
  | OutputItemList             -> "OutputItemList", []
  | IoItemList                 -> "IoItemList", []
  | IoLength                   -> "IoLength", []

  | Format f                   -> Format.to_tag f

  | IoImpliedDo                -> "IoImpliedDo", []
  | IoImpliedDoControl v       -> "IoImpliedDoControl", [var_attr_name,v]

  | Array n                    -> "Array", [name_attr_name,n]

  | EquivalenceSet             -> "EquivalenceSet", []

  | NamelistGroup n            -> "NamelistGroup", [name_attr_name,n]

  | ObjectName n               -> "ObjectName", [name_attr_name,n]

  | DataStmtSet                -> "DataStmtSet", []
  | DataStmtValue              -> "DataStmtValue", []

(*  | NullInit                   -> "NullInit", []*)

  | DataImpliedDo              -> "DataImpliedDo", []
  | DataIDoObject              -> "DataIDoObject", []
  | DataIDoObjectList          -> "DataIDoObjectList", []
  | DataStmtObjectList         -> "DataStmtObjectList", []
  | DataStmtValueList          -> "DataStmtValueList", []

  | PrefixSpec p               -> PrefixSpec.to_tag p
  | Prefix                     -> "Prefix", []
  | DummyArgNameList n         -> "DummyArgNameList", (if n = "" then [] else [name_attr_name,n])
  | DummyArgList n             -> "DummyArgList", (if n = "" then [] else [name_attr_name,n])

  | ActualArgSpecList n        -> "ActualArgSpecList", (if n = "" then [] else [name_attr_name,n])

  | Result n                   -> "Result", [name_attr_name,n]

  | AlternateReturnIndicator   -> "AlternateReturnIndicator", []

  | IntentSpec spec            -> IntentSpec.to_tag spec

  | CaseSelector sel           -> CaseSelector.to_tag sel
  | CaseValueRange r           -> CaseValueRange.to_tag r

  | ForallHeader               -> "ForallHeader", []
  | ForallTripletSpec n        -> "ForallTripletSpec", [name_attr_name,n]

  | ImplicitSpec               -> "ImplicitSpec", []
  | LetterSpec(l, l_opt)       -> "LetterSpec", ("from",l)::(string_opt_to_attr "to" l_opt)

  | FormatSpecification        -> "FormatSpecification", []
  | FormatItem i               -> FormatItem.to_tag i

  | AcImpliedDo                -> "AcImpliedDo", []
  | AcImpliedDoControl v       -> "AcImpliedDoControl", [var_attr_name,v]

  | StatVariable               -> "StatVariable", []
  | ErrmsgVariable             -> "ErrmsgVariable", []
  | SourceExpr                 -> "SourceExpr", []
  | MoldExpr                   -> "MoldExpr", []

  | CommonBlockName n          -> "CommonBlockName", [name_attr_name,n]

  | IntrinsicProcedureName n   -> "IntrinsicProcedureName", [name_attr_name,n]

  | LindaFormal                -> "LindaFormal", []
  | LindaActual                -> "LindaActual", []
  | LindaLength                -> "LindaLength", []
  | LindaTypeof                -> "LindaTypeof", []

  | Variable                   -> "Variable", []

  | PpMacroId n                -> "PpMacroId", [name_attr_name,n]
  | PpMacroExpr n              -> "PpMacroExpr", [name_attr_name,n]
  | PpMacroVariable n          -> "PpMacroVariable", [name_attr_name,n]
  | PpMacroEntityDecl n        -> "PpMacroEntityDecl", [name_attr_name,n]
  | PpMacroObject n            -> "PpMacroObject", [name_attr_name,n]

  | StructureDecl n_opt        -> "StructureDecl", (string_opt_to_attr name_attr_name n_opt)
  | UnionDecl                  -> "UnionDecl", []
  | MapDecl                    -> "MapDecl", []
  | RecordDecl n               -> "RecordDecl", [name_attr_name,n]
  | RecordFieldRef n           -> "RecordFieldRef", [name_attr_name,n]

  | EntityName n               -> "EntityName", [name_attr_name,n]
  | DummyArgName n             -> "DummyArgName", [name_attr_name,n]
  | ExternalName n             -> "ExternalName", [name_attr_name,n]

  | LanguageBindingSpec        -> "LanguageBindingSpec", []
  | Suffix                     -> "Suffix", []

  | Fragment                   -> "Fragment", []

  | ModuleNatureIntrinsic      -> "ModuleNatureIntrinsic", []
  | ModuleNatureNonIntrinsic   -> "ModuleNatureNonIntrinsic", []

  | IfThenBlock                -> "IfThenBlock", []
  | ElseIfBlock                -> "ElseIfBlock", []
  | ElseBlock                  -> "ElseBlock", []

  | CrayPointerSpec            -> "CrayPointerSpec", []

  | CaseBlock                  -> "CaseBlock", []

  | DoBlock                    -> "DoBlock", []

  | Allocation n               -> "Allocation", [name_attr_name,n]
  | AllocateShapeSpec          -> "AllocateShapeSpec", []
  | AllocateShapeSpecList      -> "AllocateShapeSpecList", []

  | TypeBoundProcDecl(n, n_opt) -> "TypeBoundProcDecl", (name_attr_name,n)::(string_opt_to_attr proc_name_attr_name n_opt)

  | TypeBoundProcedurePart      -> "TypeBoundProcedurePart", []

  | ProcedureDesignator n       -> "ProcedureDesignator", [name_attr_name,n]

  | ProcDecl n                  -> "ProcDecl", [name_attr_name,n]

  | TypeGuardBlock              -> "TypeGuardBlock", []

(*  | InitialProcTarget n         -> "InitialProcTarget", [name_attr_name,n]*)

  | Association n               -> "Association", [name_attr_name,n]

  | DeferredCoshapeSpec         -> "DeferredCoshapeSpec", []
  | ExplicitCoshapeSpec         -> "ExplicitCoshapeSpec", []
(*  | ExplicitCoshapeSpecUpper    -> "ExplicitCoshapeSpecUpper", []*)

  | DeferredCoshapeCoarray      -> "DeferredCoshapeCoarray", []
  | ExplicitCoshapeCoarray      -> "ExplicitCoshapeCoarray", []

  | CodimensionDecl n           -> "CodimensionDecl", [name_attr_name,n]

  | Enumerator n                -> "Enumerator", [name_attr_name,n]
  | EnumDef                     -> "EnumDef", []

  | BoundsSpec               -> "BoundsSpec", []
  | BoundsRemapping          -> "BoundsRemapping", []
  | BoundsSpecList           -> "BoundsSpecList", []
  | BoundsRemappingList      -> "BoundsRemappingList", []

  | DataPointerObject n      -> "DataPointerObject", [name_attr_name,n]

  | AllocateCoshapeSpec      -> "AllocateCoshapeSpec", []
(*  | AllocateCoshapeSpecUpper -> "AllocateCoshapeSpecUpper", []*)
  | AllocateCoarraySpec      -> "AllocateCoarraySpec", []

  | AcquiredLock             -> "AcquiredLock", []

  | ImageSelector            -> "ImageSelector", []

  | AllImages                -> "AllImages", []

  | WhereBlock               -> "WhereBlock", []

  | SelectiveOp              -> "SelectiveOp", []

  | DefineFileSpec           -> "DefineFileSpec", []
  | Options s                -> "Options", ["options",XML.encode_string s]

  | ApolloPointerSpec        -> "ApolloPointerSpec", []

  | ProcName n               -> "ProcName", [name_attr_name,n]

let get_value = function
  | Constant c -> Constant.get_value c
  | _ -> raise Not_found

let has_value = function
  | Constant _ -> true
  | _ -> false

let has_non_trivial_value lab = (* not yet *)
  try
    let v = get_value lab in
    v <> "0" && v <> "1"
  with
    Not_found -> false

let has_non_trivial_tid (*lab*)_ = false (* not yet *)

let get_name ?(strip=false) lab =
  ignore strip;
  match lab with
  | Name n
  | VariableName n
  | FunctionReference n
  | StructureConstructor n
  | PartName n
  | ComponentDecl n
  | EntityDecl n
  | CommonBlockObject n
  | NamedConstantDef n
  | Array n
  | NamelistGroup n
  | ObjectName n
  | Result n
(*
  | AcImpliedDoControl n
  | IoImpliedDoControl n
  | LoopControl n
*)
  | CommonBlockName n
  | IntrinsicProcedureName n
  | DerivedTypeDef n

  | ArrayElement n
  | ArraySection n
  | StructureComponent n

  | PpMacroId n
  | PpMacroExpr n
  | PpMacroVariable n
  | PpMacroEntityDecl n
  | PpMacroObject n

  | RecordDecl n
  | RecordFieldRef n

  | EntityName n
  | DummyArgName n
  | ExternalName n

  | TypeBoundProcDecl(n, _)
  | ProcedureDesignator n
  | ProcDecl n
(*  | InitialProcTarget n*)
  | Association n
  | CodimensionDecl n
  | Enumerator n

  | DataPointerObject n

  | SubroutineStmtHead n
  | FunctionStmtHead n

  | ProcName n

    -> n

  | ProgramUnit pu      -> ProgramUnit.get_name pu
  | InternalSubprogram sp -> InternalSubprogram.get_name sp
  | ModuleSubprogram sp   -> ModuleSubprogram.get_name sp
  | Stmt s              -> Stmt.get_name s
  | TypeSpec t          -> TypeSpec.get_name t
  | Ambiguous a         -> Ambiguous.get_name a
  | Constant c          -> Constant.get_name c
  | DefinedOperator op  -> DefinedOperator.get_name op
  | GenericSpec g       -> GenericSpec.get_name g
  | StopCode c          -> Constant.get_name c
  | IoControlSpec is    -> IoControlSpec.get_name is
  | BindingAttr a       -> BindingAttr.get_name a
  | ProcComponentAttrSpec s -> ProcComponentAttrSpec.get_name s
  | PrefixSpec p        -> PrefixSpec.get_name p
  | PpDirective d       -> PpDirective.get_name d
  | OmpDirective d      -> OmpDirective.get_name d
  | AccDirective d      -> AccDirective.get_name d
  | XlfDirective d      -> Xlf.Directive.get_name d
  | XlfMisc x           -> Xlf.get_name x
  | DecDirective d      -> Dec.Directive.get_name d
  | DecAttribute a      -> Dec.Attribute.get_name a

  | InterfaceBlock n_opt
  | ActualArgSpec n_opt
  | CommonSpec n_opt
  | StructureDecl n_opt
    -> begin
      match n_opt with
      | Some n -> n
      | _ -> raise Not_found
    end
  | _ -> raise Not_found

let get_name_opt = function
  | Name n
  | VariableName n
  | FunctionReference n
  | StructureConstructor n
  | PartName n
  | ComponentDecl n
  | EntityDecl n
  | CommonBlockObject n
  | NamedConstantDef n
  | Array n
  | NamelistGroup n
  | ObjectName n
  | Result n
(*
  | AcImpliedDoControl n
  | IoImpliedDoControl n
  | LoopControl n
*)
  | CommonBlockName n
  | IntrinsicProcedureName n
  | DerivedTypeDef n

  | ArrayElement n
  | ArraySection n
  | StructureComponent n

  | PpMacroId n
  | PpMacroExpr n
  | PpMacroVariable n
  | PpMacroEntityDecl n
  | PpMacroObject n

  | RecordDecl n
  | RecordFieldRef n

  | EntityName n
  | DummyArgName n
  | ExternalName n

  | TypeBoundProcDecl(n, _)

  | ProcedureDesignator n

  | ProcDecl n

(*  | InitialProcTarget n*)

  | Association n
  | CodimensionDecl n
  | Enumerator n

  | DataPointerObject n

  | SubroutineStmtHead n
  | FunctionStmtHead n

  | ProcName n

    -> Some n

  | ProgramUnit pu      -> ProgramUnit.get_name_opt pu
  | InternalSubprogram sp -> InternalSubprogram.get_name_opt sp
  | ModuleSubprogram sp   -> ModuleSubprogram.get_name_opt sp
  | Stmt s              -> Stmt.get_name_opt s
  | TypeSpec t          -> TypeSpec.get_name_opt t
  | Ambiguous a         -> Ambiguous.get_name_opt a
  | Constant c          -> Constant.get_name_opt c
  | DefinedOperator op  -> DefinedOperator.get_name_opt op
  | GenericSpec g       -> GenericSpec.get_name_opt g
  | StopCode c          -> Constant.get_name_opt c
  | IoControlSpec is    -> IoControlSpec.get_name_opt is
  | BindingAttr a       -> BindingAttr.get_name_opt a
  | ProcComponentAttrSpec s -> ProcComponentAttrSpec.get_name_opt s
  | PrefixSpec p        -> PrefixSpec.get_name_opt p
  | PpDirective d       -> PpDirective.get_name_opt d
  | OmpDirective d      -> OmpDirective.get_name_opt d
  | AccDirective d      -> AccDirective.get_name_opt d
  | XlfDirective d      -> Xlf.Directive.get_name_opt d
  | XlfMisc x           -> Xlf.get_name_opt x
  | DecDirective d      -> Dec.Directive.get_name_opt d
  | DecAttribute a      -> Dec.Attribute.get_name_opt a

  | InterfaceBlock n_opt
  | ActualArgSpec n_opt
  | CommonSpec n_opt
  | StructureDecl n_opt
    -> n_opt
  | _ -> None


let get_names = function
  | OclDirective d -> OclDirective.get_names d
  | Stmt s -> Stmt.get_names s
  | lab -> [get_name lab]

let get_label = function
  | Stmt stmt          -> Stmt.get_label stmt
  | PositionSpec spec  -> PositionSpec.get_label spec
  | ConnectSpec spec   -> ConnectSpec.get_label spec
  | CloseSpec spec     -> CloseSpec.get_label spec
  | IoControlSpec spec -> IoControlSpec.get_label spec
  | InquireSpec spec   -> InquireSpec.get_label spec
  | WaitSpec spec      -> WaitSpec.get_label spec
  | FlushSpec spec     -> FlushSpec.get_label spec
  | Format f           -> Format.get_label f

  | Label lab
  | AltReturnSpec lab -> lab

  | _ -> raise Not_found

let get_var = function
  | Stmt stmt -> Stmt.get_var stmt

  | AcImpliedDoControl v
  | IoImpliedDoControl v
  | LoopControl v
    -> v

  | DoConstruct v_opt ->
      begin
        match v_opt with
        | Some x -> x
        | _ -> raise Not_found
      end

  | _ -> raise Not_found

let get_var_opt = function
  | Stmt stmt -> Stmt.get_var_opt stmt

  | AcImpliedDoControl v
  | IoImpliedDoControl v
  | LoopControl v
    -> Some v

  | DoConstruct v_opt -> v_opt

  | _ -> None

let is_error = function
  | ERROR _ -> true
  | _ -> false




let mklabeledstmt lab x = Stmt (Stmt.mklabeled lab x)
let mkstmt x = Stmt (Stmt.mk x)

let mkambiguous_desig n = Ambiguous (Ambiguous.Designator n)
let mkambiguous_namedtuple n = Ambiguous (Ambiguous.NamedTuple n)
let mkambiguous_tuple() = Ambiguous Ambiguous.Tuple

let mkambiguous_subobject() = Ambiguous Ambiguous.Subobject
let mkambiguous_triplet_or_range() = Ambiguous Ambiguous.TripletOrRange
let mkambiguous_first() = Ambiguous Ambiguous.First
let mkambiguous_second() = Ambiguous Ambiguous.Second
let mkambiguous_data_stmt_constant() = Ambiguous Ambiguous.DataStmtConstant

let mkambiguous_deferred() = Ambiguous Ambiguous.Deferred
let mkambiguous_assumed() = Ambiguous Ambiguous.Assumed
let mkambiguous_assumedsize() = Ambiguous Ambiguous.AssumedSize

(*
let mkambiguous_ppexpr n = Ambiguous (Ambiguous.PpExpr n)
let mkambiguous_pptypespec n = Ambiguous (Ambiguous.PpTypeSpec n)
*)

let mkambiguous_generic_spec_or_use_name n = Ambiguous (Ambiguous.GenericSpecOrUseName n)

let mkocl lab = OclDirective lab

let mkxlfd lab = XlfDirective lab
let mkxlfa lab = XlfAssertion lab
let mkxlf lab = XlfMisc lab

let mkdecd lab = DecDirective lab
let mkdecc lab = DecClause lab
let mkdeca lab = DecAttribute lab
let mkdec lab = DecMisc lab

let mkomp lab = OmpDirective lab
let mkompc lab = OmpClause lab

let mkacc lab = AccDirective lab
let mkaccc lab = AccClause lab

let mklinda lab = LindaCall lab

let access_spec_to_attr_spec = function
  | AccessSpec spec -> AttrSpec (AccessSpec.to_attr_spec spec)
  | _ -> assert false

let access_spec_to_type_attr_spec = function
  | AccessSpec spec -> TypeAttrSpec (AccessSpec.to_type_attr_spec spec)
  | _ -> assert false

let access_spec_to_proc_attr_spec = function
  | AccessSpec spec -> ProcAttrSpec (AccessSpec.to_proc_attr_spec spec)
  | _ -> assert false

let type_spec_to_prefix_spec = function
  | TypeSpec t -> PrefixSpec (PrefixSpec.TypeSpec t)
  | _ -> assert false

let relabstmt lab _lab' =
  match lab with
  | Stmt s -> Stmt (Stmt.relab s _lab')
  | _ -> assert false



let is_specification_part_construct = function
  | DerivedTypeDef _
  | EnumDef
  | InterfaceBlock _
  | PpDirective _
  | PpBranch
  | PpSectionIf _
  | PpSectionIfdef _
  | PpSectionIfndef _
  | Include _
    -> true

  | Stmt s -> Stmt.is_specification_part_stmt s
  | OclDirective d -> OclDirective.is_specification_part d
  | XlfDirective d -> Xlf.Directive.is_specification_part d
  | DecDirective d -> Dec.Directive.is_specification_part d
  | OmpDirective d -> OmpDirective.is_specification_part d
  | AccDirective d -> AccDirective.is_specification_part d

  | _ -> false

let is_execution_part_construct = function
  | CaseConstruct
  | DoConstruct _
  | ForallConstruct
  | IfConstruct
  | WhereConstruct
  | SelectTypeConstruct
  | AssociateConstruct
  | BlockConstruct
  | CriticalConstruct
  | PpDirective _
  | PpBranch
  | PpSectionIf _
  | PpSectionIfdef _
  | PpSectionIfndef _
  | PpBranchDo
  | PpBranchForall
  | PpBranchIf
  | PpBranchSelect
  | PpBranchWhere
  | PpBranchDerivedType
  | PpBranchEndDo
  | PpBranchEndForall
  | PpBranchEndIf
  | PpBranchEndSelect
  | PpBranchEndWhere
  | PpBranchEndType
  | Include _
      -> true

  | Stmt s -> Stmt.is_execution_part_stmt s
  | OclDirective d -> OclDirective.is_execution_part d
  | XlfDirective d -> Xlf.Directive.is_execution_part d
  | DecDirective d -> Dec.Directive.is_execution_part d
  | OmpDirective d -> OmpDirective.is_execution_part d
  | AccDirective d -> AccDirective.is_execution_part d

  | _ -> false

let is_ambiguous_desig = function
  | Ambiguous (Ambiguous.Designator _) -> true
  | _ -> false

let is_ambiguous_tuple = function
  | Ambiguous Ambiguous.Tuple -> true
  | _ -> false

let is_ambiguous_triplet_or_range = function
  | Ambiguous Ambiguous.TripletOrRange -> true
  | _ -> false

let is_ambiguous_data_stmt_constant = function
  | Ambiguous Ambiguous.DataStmtConstant -> true
  | _ -> false

let is_ambiguous = function
  | Ambiguous _ -> true
  | _ -> false

let is_array_spec = function
  | ArraySpec _
  | ExplicitShapeArray _
  | AssumedShapeArray _
  | DeferredShapeArray _
  | AssumedSizeArray _
  | AssumedRankArray
    -> true
  | _ -> false

let is_component_array_spec = function
  | ExplicitShapeComponentArray _
  | DeferredShapeComponentArray _
      -> true
  | _ -> false

let is_coarray_spec = function
  | DeferredCoshapeCoarray
  | ExplicitCoshapeCoarray
    -> true
  | _ -> false


let get_generic_name = function
  | GenericSpec s -> GenericSpec.get_name s
  | _ -> raise Not_found

let is_subscript_triplet = function
  | SubscriptTriplet -> true
  | _ -> false

(*let is_part_name = function
  | PartName _ -> true
  | _ -> false*)

let is_section_subscript_list = function
  | SectionSubscriptList _ -> true
  | _ -> false

let is_stmt = function
  | Stmt _ -> true
  | _ -> false

let is_statement = is_stmt

let get_stmt_label = function
  | Stmt stmt -> Stmt.get_stmt_label stmt
  | _ -> raise Not_found

let is_action_stmt = function
  | Stmt stmt -> Stmt.is_action_stmt stmt
  | _ -> false

let is_type_decl_stmt = function
  | Stmt stmt -> Stmt.is_type_decl_stmt stmt
  | _ -> false

let is_do_stmt = function
  | Stmt stmt -> Stmt.is_do_stmt stmt
  | PpBranchDo -> true
  | _ -> false

let is_if_stmt = function
  | Stmt stmt -> Stmt.is_if_stmt stmt
  | _ -> false

let is_arithmetic_if_stmt = function
  | Stmt stmt -> Stmt.is_arithmetic_if_stmt stmt
  | _ -> false

let is_if_then_stmt = function
  | Stmt stmt -> Stmt.is_if_then_stmt stmt
  | PpBranchIf -> true
  | _ -> false

let is_else_if_stmt = function
  | Stmt stmt -> Stmt.is_else_if_stmt stmt
  | _ -> false

let is_else_stmt = function
  | Stmt stmt -> Stmt.is_else_stmt stmt
  | _ -> false

let is_end_if_stmt = function
  | Stmt stmt -> Stmt.is_end_if_stmt stmt
  | PpBranchEndIf -> true
  | _ -> false

let is_end_do_stmt = function
  | Stmt stmt -> Stmt.is_end_do_stmt stmt
  | PpBranchEndDo -> true
  | _ -> false

let is_if_construct = function
  | IfConstruct -> true
  | _ -> false

let is_do_construct = function
  | DoConstruct _ -> true
  | _ -> false

let is_constant = function
  | Constant _ -> true
  | _ -> false

let is_var_name = function
  | VariableName _ -> true
  | _ -> false

let is_part_name = function
  | PartName _ -> true
  | _ -> false

let is_entity_decl = function
  | EntityDecl _ -> true
  | _ -> false

let is_assignment_stmt = function
  | Stmt stmt -> Stmt.is_assignment_stmt stmt
  | _ -> false

let get_external_subprogram_name = function
  | ProgramUnit
      (ProgramUnit.FunctionSubprogram n |
      ProgramUnit.SubroutineSubprogram n) -> n
  | _ -> raise Not_found

let get_module_subprogram_name = function
  | ModuleSubprogram (ModuleSubprogram.FunctionSubprogram n |
    ModuleSubprogram.SubroutineSubprogram n) -> n
  | _ -> raise Not_found

let get_value = function
  | Constant c -> Constant.get_value c
  | _ -> raise Not_found

let get_category lab =
  let name, _ = to_tag lab in
  name

let is_ocl_directive = function
  | OclDirective _ -> true
  | _ -> false

let is_omp_directive = function
  | OmpDirective _ -> true
  | _ -> false

let is_acc_directive = function
  | AccDirective _ -> true
  | _ -> false

let is_xlf_directive = function
  | XlfDirective _ -> true
  | _ -> false

let is_dec_directive = function
  | DecDirective _ -> true
  | _ -> false

let is_directive = function
  | OclDirective _
  | OmpDirective _
  | AccDirective _
  | XlfDirective _
  | DecDirective _
    -> true
  | _ -> false

let is_pp_directive = function
  | PpDirective _ -> true
  | _ -> false

let is_pp_directive_branch = function
  | PpDirective d -> begin
     match d.PpDirective.pp_label with
     | PpDirective.Branch _ -> true
     | _ -> false
  end
  | _ -> false

let is_pp_section = function
  | PpSectionIf _
  | PpSectionIfdef _
  | PpSectionIfndef _
  | PpSectionElif _
  | PpSectionElse
    -> true
  | _ -> false

let is_pp_section_omp = function
  | PpSectionIfdef n -> n = "_OPENMP"
  | _ -> false

let is_pp_branch = function
  | PpBranch
  | PpBranchDo
  | PpBranchForall
  | PpBranchIf
  | PpBranchSelect
  | PpBranchWhere
  | PpBranchDerivedType
  | PpBranchEndDo
  | PpBranchEndForall
  | PpBranchEndIf
  | PpBranchEndSelect
  | PpBranchEndWhere
  | PpBranchEndType
    -> true
  | _ -> false


let is_fragment = function
  | Fragment -> true
  | _ -> false

let is_subroutine_stmt_head = function
  | SubroutineStmtHead _ -> true
  | _ -> false

let is_function_stmt_head = function
  | FunctionStmtHead _ -> true
  | _ -> false


(* *)


let anonymize ?(more=false) = function
  | PartName _                        -> PartName ""
  | Name _                            -> Name ""
  | VariableName _                    -> if more then Variable else VariableName ""
  | FunctionReference _               -> FunctionReference ""
  | StructureConstructor _            -> StructureConstructor ""
  | ComponentDecl _                   -> ComponentDecl ""
  | EntityDecl _                      -> EntityDecl ""
  | CommonBlockObject _               -> CommonBlockObject ""
  | NamedConstantDef _                -> NamedConstantDef ""
  | IoImpliedDoControl _              -> IoImpliedDoControl ""
  | Array _                           -> Array ""
  | NamelistGroup _                   -> NamelistGroup ""
  | ObjectName _                      -> ObjectName ""
  | Result _                          -> Result ""
  | ForallTripletSpec _               -> ForallTripletSpec ""
  | AcImpliedDoControl _              -> AcImpliedDoControl ""
  | CommonBlockName _                 -> CommonBlockName ""
  | IntrinsicProcedureName _          -> IntrinsicProcedureName ""

  | AltReturnSpec _                   -> AltReturnSpec ""
  | Label _                           -> Label ""

  | ActualArgSpec _                   -> ActualArgSpec None
  | CommonSpec _                      -> CommonSpec None

  | ArraySpec _                       -> ArraySpec 0
  | ExplicitShapeArray _              -> ExplicitShapeArray 0
  | AssumedShapeArray _               -> AssumedShapeArray 0
  | DeferredShapeArray _              -> DeferredShapeArray 0
  | AssumedSizeArray _                -> AssumedSizeArray 0
  | ComponentArraySpec _              -> ComponentArraySpec 0
  | ExplicitShapeComponentArray _     -> ExplicitShapeComponentArray 0
  | DeferredShapeComponentArray _     -> DeferredShapeComponentArray 0

  | Stmt s                            -> Stmt (Stmt.anonymize s)
  | PpDirective d                     -> PpDirective (PpDirective.anonymize d)
  | OclDirective d                    -> OclDirective (OclDirective.anonymize d)
  | OmpClause c                       -> OmpClause (OmpClause.anonymize c)
  | OmpDirective d                    -> OmpDirective (OmpDirective.anonymize d)
  | OmpConstruct c                    -> OmpConstruct (OmpConstruct.anonymize c)
  | XlfDirective d                    -> XlfDirective (Xlf.Directive.anonymize d)
  | XlfMisc x                         -> XlfMisc (Xlf.anonymize x)
  | DecDirective d                    -> DecDirective (Dec.Directive.anonymize d)
  | DecClause c                       -> DecClause (Dec.Clause.anonymize c)
  | DecAttribute a                    -> DecAttribute (Dec.Attribute.anonymize a)
  | DecMisc x                         -> DecMisc (Dec.anonymize x)

  | ProgramUnit pu                    -> ProgramUnit (ProgramUnit.anonymize pu)

  | InternalSubprogram is             -> InternalSubprogram (InternalSubprogram.anonymize is)
  | ModuleSubprogram is               -> ModuleSubprogram (ModuleSubprogram.anonymize is)

  | TypeSpec t                        -> TypeSpec (TypeSpec.anonymize t)
  | Ambiguous a                       -> if more then Variable else Ambiguous (Ambiguous.anonymize a)
  | Constant c                        -> Constant (Constant.anonymize c)
  | GenericSpec g                     -> GenericSpec (GenericSpec.anonymize g)
(*
  | IntrinsicOperator op              -> IntrinsicOperator (IntrinsicOperator.anonymize op)
  | DefinedOperator op                -> DefinedOperator (DefinedOperator.anonymize op)
  | AttrSpec a                        -> AttrSpec (AttrSpec.anonymize a)
*)
  | StopCode c                        -> Constant (Constant.anonymize c)
  | Format f                          -> Format (Format.anonymize f)
  | PrefixSpec p                      -> PrefixSpec (PrefixSpec.anonymize p)
(*
  | CaseSelector sel                  -> CaseSelector (CaseSelector.anonymize sel)
  | CaseValueRange r                  -> CaseValueRange (CaseValueRange.anonymize r)
*)
  | FormatItem i                      -> FormatItem (FormatItem.anonymize i)
(*
  | AccessSpec spec                   -> AccessSpec (AccessSpec.anonymize spec)
*)
  | TypeAttrSpec spec                 -> TypeAttrSpec (TypeAttrSpec.anonymize spec)
  | InquireSpec spec                  -> InquireSpec (InquireSpec.anonymize spec)
  | CloseSpec spec                    -> CloseSpec (CloseSpec.anonymize spec)
  | ConnectSpec spec                  -> ConnectSpec (ConnectSpec.anonymize spec)
  | PositionSpec spec                 -> PositionSpec (PositionSpec.anonymize spec)
  | IoControlSpec spec                -> IoControlSpec (IoControlSpec.anonymize spec)
(*
  | IntentSpec spec                   -> IntentSpec (IntentSpec.anonymize spec)
*)

  | Include _                         -> Include ""
  | Options _                         -> Options ""

  | LetterSpec(_, _)                  -> LetterSpec("", None)

  | SectionSubscriptList _            -> SectionSubscriptList ""
  | DummyArgNameList _                -> DummyArgNameList ""
  | DummyArgList _                    -> DummyArgList ""
  | ActualArgSpecList _               -> ActualArgSpecList ""

  | ArrayElement _                    -> if more then Variable else (ArrayElement "")
  | ArraySection _                    -> if more then Variable else (ArraySection "")
  | StructureComponent _              -> if more then Variable else (StructureComponent "")
  | Substring as lab                  -> if more then Variable else lab

  | PpMacroId _                       -> PpMacroId ""
  | PpMacroExpr _                     -> PpMacroExpr ""
  | PpMacroVariable _                 -> PpMacroVariable ""
  | PpMacroEntityDecl _               -> PpMacroEntityDecl ""
  | PpMacroObject _                   -> PpMacroObject ""

  | StructureDecl _                   -> StructureDecl None
  | RecordDecl _                      -> RecordDecl ""
  | RecordFieldRef _                  -> RecordFieldRef ""

  | EntityName _                      -> EntityName ""
  | DummyArgName _                    -> DummyArgName ""

  | PpSectionIf _                     -> PpSectionIf ""
  | PpSectionIfdef _                  -> PpSectionIfdef ""
  | PpSectionIfndef _                 -> PpSectionIfndef ""
  | PpSectionElif _                   -> PpSectionElif ""

  | WaitSpec sp                  -> WaitSpec (WaitSpec.anonymize sp)
  | FlushSpec sp                 -> FlushSpec (FlushSpec.anonymize sp)
  | BindingAttr a                -> BindingAttr (BindingAttr.anonymize a)
  | ProcComponentAttrSpec sp     -> ProcComponentAttrSpec(ProcComponentAttrSpec.anonymize sp)
  | ProcAttrSpec sp              -> ProcAttrSpec (ProcAttrSpec.anonymize sp)
  | ExternalName _               -> ExternalName ""
  | TypeBoundProcDecl(_, _)      -> TypeBoundProcDecl("", None)
  | ProcedureDesignator _        -> ProcedureDesignator ""
  | ProcDecl _                   -> ProcDecl ""
  | Association _                -> Association ""
  | CodimensionDecl _            -> CodimensionDecl ""
  | Enumerator _                 -> Enumerator ""
  | DataPointerObject _          -> DataPointerObject ""

  | SubroutineStmtHead _         -> SubroutineStmtHead ""
  | FunctionStmtHead _           -> FunctionStmtHead ""

  | ProcName _                   -> ProcName ""

  | lab -> lab


exception Not_a_construct_head of t

let mk_endchk_x ?(multi=true) is_ctor mklab slab _elab_opt =
  fun lab next_lab_opt ->
    match _elab_opt with
    | Some _elab -> begin
        let elab = mklab _elab in

        if lab = elab then begin
          true
        end
        else begin
          if is_ctor lab then begin
            match next_lab_opt with
            | Some next_lab ->
                not multi ||
                (anonymize next_lab) = (anonymize slab) ||
                (next_lab <> elab && not (is_ctor next_lab))
            | None -> true
          end
          else
            raise (Not_a_construct_head lab)
        end
    end
    | None -> begin
        if is_ctor lab then begin
          match next_lab_opt with
          | Some next_lab ->
              not multi ||
              (anonymize next_lab) = (anonymize slab) ||
              not (is_ctor next_lab)
          | None -> true
        end
        else
          raise (Not_a_construct_head lab)
    end

let is_do_like_construct = function
  | OmpDirective omp -> begin
      match omp with
      | OmpDirective.Do _
      | OmpDirective.Simd
      | OmpDirective.ParallelDo _
      | OmpDirective.Distribute _
      | OmpDirective.DistributeParallelDo _
      | OmpDirective.TeamsDistribute _
      | OmpDirective.TargetTeamsDistribute _
      | OmpDirective.TeamsDistributeParallelDo _
      | OmpDirective.TargetTeamsDistributeParallelDo _
        -> true
      | _ -> false
  end
  | OmpConstruct omp -> begin
      match omp with
      | OmpConstruct.Do _
      | OmpConstruct.Simd
      | OmpConstruct.ParallelDo _
      | OmpConstruct.Distribute _
      | OmpConstruct.DistributeParallelDo _
      | OmpConstruct.TeamsDistribute _
      | OmpConstruct.TargetTeamsDistribute _
      | OmpConstruct.TeamsDistributeParallelDo _
      | OmpConstruct.TargetTeamsDistributeParallelDo _
        -> true
      | _ -> false
  end
  | AccDirective acc -> begin
      match acc with
      | AccDirective.Loop
      | AccDirective.ParallelLoop
      | AccDirective.KernelsLoop
      | AccDirective.Parallel
      | AccDirective.Kernels
      | AccDirective.Data
        -> true
      | _ -> false
  end
  | AccConstruct acc -> begin
      match acc with
      | AccConstruct.Loop
      | AccConstruct.ParallelLoop
      | AccConstruct.KernelsLoop
      | AccConstruct.Parallel
      | AccConstruct.Kernels
      | AccConstruct.Data
          -> true
      | _ -> false
  end
  | DecDirective dec -> begin
      match dec with
      | DecDirective.Block_loop
      | DecDirective.Code_align _
      | DecDirective.DistributePoint
      | DecDirective.Forceinline _
      | DecDirective.Inline _
      | DecDirective.Ivdep _
      | DecDirective.LoopCount _
      | DecDirective.Noblock_loop
      | DecDirective.Nofusion
      | DecDirective.Noinline
      | DecDirective.Noparallel
      | DecDirective.Nounroll
      | DecDirective.Nounroll_and_jam
      | DecDirective.Novector
      | DecDirective.Parallel
      | DecDirective.Simd
      | DecDirective.Unroll _
      | DecDirective.Unroll_and_jam _
      | DecDirective.Vector
          -> true
      | _ -> false
  end
  | _ -> false

let is_do_or_like_construct x =
  (is_do_like_construct x) || (is_do_construct x)

let mk_endchk_loops ?(multi=true) mklab slab _elab_opt =
  mk_endchk_x ~multi is_do_or_like_construct mklab slab _elab_opt

let mk_endchk_assigns ?(multi=true) mklab slab _elab_opt =
  mk_endchk_x ~multi is_assignment_stmt mklab slab _elab_opt


let omp_mk_endchk elab = fun lab _ -> lab = (OmpDirective elab)

let omp_mk_endchk_loops ?(multi=true) =
  mk_endchk_loops ~multi (fun x -> OmpDirective x)

let omp_mk_endchk_assigns ?(multi=true) =
  mk_endchk_assigns ~multi (fun x -> OmpDirective x)

let omp_get_endchk_and_construct dtv =
  let mk_endchk_loops = omp_mk_endchk_loops (OmpDirective dtv) in
  let mk_endchk_assign = omp_mk_endchk_assigns ~multi:false (OmpDirective dtv) in
  match dtv with
  | OmpDirective.Atomic(a_opt, seq_cst) ->
      mk_endchk_assign (Some (OmpDirective.EndAtomic)),
      OmpConstruct.Atomic(a_opt, seq_cst)

  | OmpDirective.Critical n_opt         ->
      (omp_mk_endchk (OmpDirective.EndCritical n_opt)), OmpConstruct.Critical n_opt

  | OmpDirective.Master                 ->
      (omp_mk_endchk OmpDirective.EndMaster), OmpConstruct.Master

  | OmpDirective.Ordered                ->
      (omp_mk_endchk OmpDirective.EndOrdered), OmpConstruct.Ordered

  | OmpDirective.Parallel               ->
      (omp_mk_endchk OmpDirective.EndParallel), OmpConstruct.Parallel

  | OmpDirective.Sections               ->
      (omp_mk_endchk OmpDirective.EndSections), OmpConstruct.Sections

  | OmpDirective.Single                 ->
      (omp_mk_endchk OmpDirective.EndSingle), OmpConstruct.Single

  | OmpDirective.Task                   ->
      (omp_mk_endchk OmpDirective.EndTask), OmpConstruct.Task

  | OmpDirective.Workshare              ->
      (omp_mk_endchk OmpDirective.EndWorkshare), OmpConstruct.Workshare

  | OmpDirective.ParallelSections       ->
      (omp_mk_endchk OmpDirective.EndParallelSections), OmpConstruct.ParallelSections

  | OmpDirective.ParallelWorkshare      ->
      (omp_mk_endchk OmpDirective.EndParallelWorkshare), OmpConstruct.ParallelWorkshare

  | OmpDirective.Target                 ->
      (omp_mk_endchk OmpDirective.EndTarget), OmpConstruct.Target

  | OmpDirective.TargetData             ->
      (omp_mk_endchk OmpDirective.EndTargetData), OmpConstruct.TargetData

  | OmpDirective.Teams                  ->
      (omp_mk_endchk OmpDirective.EndTeams), OmpConstruct.Teams

  | OmpDirective.TargetTeams            ->
      (omp_mk_endchk OmpDirective.EndTargetTeams), OmpConstruct.TargetTeams

  | OmpDirective.Taskgroup              ->
      (omp_mk_endchk OmpDirective.EndTaskgroup), OmpConstruct.Taskgroup

  | OmpDirective.Do simd ->
      mk_endchk_loops (Some (OmpDirective.EndDo simd)),
      OmpConstruct.Do simd

  | OmpDirective.Simd ->
      mk_endchk_loops (Some OmpDirective.EndSimd),
      OmpConstruct.Simd

  | OmpDirective.ParallelDo simd ->
      mk_endchk_loops (Some (OmpDirective.EndParallelDo simd)),
      OmpConstruct.ParallelDo simd

  | OmpDirective.Distribute simd ->
      mk_endchk_loops (Some (OmpDirective.EndDistribute simd)),
      OmpConstruct.Distribute simd

  | OmpDirective.DistributeParallelDo simd ->
      mk_endchk_loops (Some (OmpDirective.EndDistributeParallelDo simd)),
      OmpConstruct.DistributeParallelDo simd

  | OmpDirective.TeamsDistribute simd ->
      mk_endchk_loops (Some (OmpDirective.EndTeamsDistribute simd)),
      OmpConstruct.TeamsDistribute simd

  | OmpDirective.TargetTeamsDistribute simd ->
      mk_endchk_loops (Some (OmpDirective.EndTargetTeamsDistribute simd)),
      OmpConstruct.TargetTeamsDistribute simd

  | OmpDirective.TeamsDistributeParallelDo simd ->
      mk_endchk_loops (Some (OmpDirective.EndTeamsDistributeParallelDo simd)),
      OmpConstruct.TeamsDistributeParallelDo simd

  | OmpDirective.TargetTeamsDistributeParallelDo simd ->
      mk_endchk_loops (Some (OmpDirective.EndTargetTeamsDistributeParallelDo simd)),
      OmpConstruct.TargetTeamsDistributeParallelDo simd

  | _ -> raise Not_found


let acc_mk_endchk elab = fun lab _ -> lab = (AccDirective elab)

let acc_mk_endchk_loops ?(multi=false) =
  mk_endchk_loops ~multi (fun x -> AccDirective x)

let acc_get_endchk_and_construct dtv =
  match dtv with
  | AccDirective.Atomic a_opt ->
      acc_mk_endchk AccDirective.EndAtomic, AccConstruct.Atomic a_opt

  | AccDirective.Parallel ->
      acc_mk_endchk AccDirective.EndParallel, AccConstruct.Parallel

  | AccDirective.Kernels ->
      acc_mk_endchk AccDirective.EndKernels, AccConstruct.Kernels

  | AccDirective.ParallelLoop ->
      acc_mk_endchk AccDirective.EndParallelLoop, AccConstruct.ParallelLoop

  | AccDirective.KernelsLoop ->
      acc_mk_endchk AccDirective.EndKernelsLoop, AccConstruct.KernelsLoop

  | AccDirective.Data ->
      acc_mk_endchk AccDirective.EndData, AccConstruct.Data

  | AccDirective.Host_data ->
      acc_mk_endchk AccDirective.EndHost_data, AccConstruct.Host_data

  | AccDirective.Loop ->
      acc_mk_endchk_loops (AccDirective dtv) None, AccConstruct.Loop

  | _ -> raise Not_found


let get_endchk_and_construct = function
  | OmpDirective d ->
      let chk, c = omp_get_endchk_and_construct d in
      chk, OmpConstruct c

  | AccDirective d ->
      let chk, c = acc_get_endchk_and_construct d in
      chk, AccConstruct c

  | _ -> raise Not_found

let has_endchk lab =
  try
    let _ = get_endchk_and_construct lab in
    true
  with
    Not_found -> false
