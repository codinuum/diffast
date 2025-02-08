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

[%%prepare_logger]

(*open Printf*)
open Common

open Label_common
open Labels


type t =
    | Dummy
    | Error
    | Empty
    | SourceText
    | LibraryText
    | CompilerDirective of CompilerDirective.t
    | ModuleDeclaration of ModuleSpec.t * identifier
    | UdpDeclaration of identifier
    | NetDeclaration of identifier list
    | BindDirective of identifier
    | Expr of Expression.t
    | Stmt of Statement.t
    | NetType of NetType.t
    | LocalParameterDeclaration of identifier list
    | ParameterDeclaration of identifier list
    | ParameterPortDeclaration
    | ModuleBody
    | Instantiation of identifier
    | GateInstantiation of Gate.t
    | ContinuousAssign
    | Assign
    | ConcurrentAssertionItem
    | DeferredImmediateAssertionItem
    | PpIdentifier of identifier
    | PackedDimension
    | ParamAssignment of identifier
    | DefparamAssignment
    | IdSelect of identifier
    | Select
    | Range
    | RangePlus
    | RangeMinus
    | RangeForeach
    | Root
    | This
    | Super
    | Cellpin of identifier
    | CellpinStar
    | CellpinAnon
    | DelayValue of identifier
    | PackageScope of identifier
    | PackageScopeUnit
    | PackageScopeLocal
    | PackageImport of identifier
    | PackageImportAny
    | LifetimeStatic
    | LifetimeAutomatic
    | EndLabel of identifier
    | EndLabelNew
    | ClassType of identifier
    | DataType of DataType.t
    | ImplicitDataType
    | VarDeclAssignments
    | Signed
    | Unsigned
    | ArgsDotted of identifier
    | Tagged
    | StructUnionBody
    | StructUnionMember
    | ClassScopeId of identifier
    | Void
    | EnumNameDeclaration of identifier
    | EnumBody
    | IdClassSel of identifier
    | Variable of identifier
    | Extern
    | PackageImportDeclaration
    | PackageImportItem of identifier
    | Packed
    | ParameterValueAssignment
    | Ports
    | PortsStar
    | BitSelect
    | VariableDeclAssignment of identifier
    | DynamicArrayNew
    | VariableDimension
    | VariableDimensionStar
    | GenItemBegin
    | GenBlockId of identifier
    | GenerateRegion
    | Scalared
    | Vectored
    | DelayControl
    | NetSig of identifier
    | ParameterOverride
    | PortDeclaration
    | PortDirection of PortDirection.t
    | Strength of Strength.t
    | StrengthSupply0
    | StrengthSupply1
    | StrengthSpec
    | VarDataType
    | Port of identifier
    | InterfacePort of identifier
    | InterfacePortInterface
    | ModportIdentifier of identifier
    | PortMulti
    | ExprScope
    | ExprScopeThis
    | ExprScopeSuper
    | ExprScopeDot
    | ExprScopeDotSuper
    | CondPredicate
    | CondPattern
    | Dist
    | DistItem
    | DistWeight
    | DistWeightRange
    | ArrayRange
    | ArrayRangePlus
    | ArrayRangeMinus
    | CastingTypeSimple
    | CastingTypeSigned
    | CastingTypeUnsigned
    | CastingTypeString
    | CastingTypeConst
    | ValueRange
    | Pattern
    | PatternId of identifier
    | PatternStar
    | PatternTagged of identifier
    | EventControl
    | EventControlStar
    | EventControlParenStar
    | EventControlRepeat
    | EvExpr of EventExpression.t
    | CaseItem
    | CaseItemDefault
    | CaseInsideItem
    | CaseInsideItemDefault
    | CaseItems
    | CaseItemsMatches
    | CaseItemsInside
    | With
    | Args
    | ConstraintBlock
    | ForInit
    | ForInitItemDT of identifier
    | ForInitItemLval
    | StreamingConcat
    | OrderRL
    | OrderLR
    | StreamConcat
    | Solve
    | SolveBefore
    | ActionBlock
    | CycleDelay of string
    | CycleDelayId of identifier
    | CycleDelayParen
    | Priority
    | Unique
    | Unique0
    | InstRange
    | InstName of identifier
    | PExpr of PropertyExpression.t
    | ClockingEvent of identifier
    | ClockingEventParen
    | PropertyCase
    | PropertyCaseDefault
    | DisableIff
    | CycleDelayRange of string
    | CycleDelayRangeId of identifier
    | CycleDelayRangeParen
    | CycleDelayRangeBracket
    | CycleDelayRangeBracketStar
    | CycleDelayRangeBracketPlus
    | SExpr of SequenceExpression.t
    | ConsecutiveRepetition
    | NonconsecutiveRepetition
    | GotoRepetition
    | NetAlias
    | InitialConstruct
    | FinalConstruct
    | AlwaysConstruct of AlwaysSpec.t
    | ConcurrentAssertionItemLabeled of identifier
    | ConcurrentAssertionStmt of ConcurrentAssertion.t
    | DeferredImmediateAssertionItemLabeled of identifier
    | DeferredImmediateAssertionStmt of DeferredImmediateAssertion.t
    | SimpleImmediateAssertionStmt of SimpleImmediateAssertion.t
    | CheckerInstantiation of identifier
    | LoopGenerateConstruct
    | GenvarDeclaration of identifier list
    | GenvarIterationAssign of AssignmentOperator.t * identifier
    | GenvarIterationIncOrDec of IncOrDecOperator.t * identifier
    | GenvarIdDecl of identifier
    | GenvarInitId of identifier
    | GenvarInit
    | SpecifyBlock
    | SpecparamDeclaration
    | SpecparamAssignmentId of identifier (* specparam assignment*)
    | SpecparamAssignmentPulseControl of identifier
    | PulsestyleDeclarationOnevent
    | PulsestyleDeclarationOndetect
    | ShowcancelledDeclaration
    | NoshowcancelledDeclaration
    | SpecifyTerminalDescriptor
    | InputOrOutputId of identifier
    | InterfaceIdentifier of identifier
    | ProgramDeclaration of identifier
    | InterfaceDeclaration of identifier
    | InterfaceDeclarationExtern of identifier
    | TimeUnitsDeclaration
    | TimeUnit of string
    | Timeprecision of string
    | PackageDeclaration of identifier
    | AnonymousProgram
    | AnonymousProgramItemEmpty
    | FunctionDeclaration of identifier
    | FunctionPrototype of identifier
    | FuncId of identifier
    | FuncIdVoid of identifier
    | FuncIdNew
    | TfIdScoped of identifier
    | TaskDeclaration of identifier
    | TaskPrototype of identifier
    | ClassCtorPrototype
    | TfPortListPart
    | TfBody
    | TfPortDeclaration
    | TfPortItemAssignment of identifier
    | TfPortItem
    | TfVariableIdentifier of identifier
    | CheckerDeclaration of identifier
    | PropertyDeclaration of identifier
    | PropertyDeclBody
    | PropertyPortItem
    | PropertyPortItemDir
    | PropertyPortItemAssignment of identifier
    | SequenceDeclaration of identifier
    | SequenceDeclBody
    | LetDeclaration of identifier
    | PropertyStatementSpec
    | AssertionVariableDeclaration
    | SequenceFormalTypeSequence
    | SequenceFormalTypeUntyped
    | DataDeclarationVar
    | Const
    | DataDeclarationVarClass
    | TypeDeclaration of identifier
    | ScopedType of identifier
    | TypeIdentifier of identifier
    | TypeDeclEnum
    | TypeDeclStruct
    | TypeDeclUnion
    | TypeDeclClass
    | VirtualInterfaceDeclaration of identifier
    | ModportDeclaration of identifier list
    | ModportItem of identifier
    | ModportSimplePortsDecl
    | ModportClockingDecl of identifier
    | ModportTfPortsDeclImport
    | ModportTfPortsDeclExport
    | ModportSimplePort of identifier
    | ModportSimplePortDot of identifier
    | ModportTfPort of identifier
    | CovergroupDeclaration of identifier
    | Paren
    | CoverageOption of identifier * identifier
    | CoverPoint
    | CoverPointLabeled of identifier
    | CoverCross
    | CoverCrossLabeled of identifier
    | CrossItem of identifier
    | Iff
    | BinsList
    | BinsEmpty
    | SelectBins
    | SelectBinsEmpty
    | Bins of BinsSpec.t * identifier
    | BinsSelection of BinsSpec.t * identifier
    | BinsExpressionVar of identifier
    | BinsExpression of identifier * identifier
    | NBins
    | SelCondBinsof
    | SelExprNot
    | SelExprAnd
    | SelExprOr
    | SelExprParen
    | Intersect
    | Wildcard
    | TransSet
    | TransRangeList
    | RepeatRange
    | TransItem
    | TransRepetitionConsecutive (* trans repetition *)
    | TransRepetitionNonconsecutive (* trans repetition *)
    | TransRepetitionGoto (* trans repetition *)
    | Default
    | DefaultSequence
    | OpenRangeList
    | CoverageEventWith of identifier
    | CoverageEventBlockEvent
    | BlockEventExpression
    | BlockEventExpressionBegin
    | BlockEventExpressionEnd
    | HierarchicalBtfIdentifier of identifier
    | PackageExportDeclarationStar
    | PackageExportDeclaration
    | DpiImport of string
    | DpiExportFunc of string * identifier
    | DpiExportTask of string * identifier
    | DpiImportLabel of identifier
    | DpiTfImportPropertyContext
    | DpiTfImportPropertyPure
    | ExternConstraintDeclaration
    | Static
    | Virtual
    | ClassDeclaration of identifier
    | ClassExtends
    | ClassItemEmpty
    | ClassMethod
    | Qualifier of Qualifier.t
    | ClassBody
    | ClassConstraint of identifier
    | Pure
    | ClassProperty
    | PackageOrGenerateItemEmpty
    | Forkjoin
    | ExternTfDeclaration of identifier
    | TimingCheck of TimingCheck.t
    | SystemTimingCheck
    | Notifier of identifier
    | Delayed of identifier
    | TimingCheckEvent
    | TimingCheckEventControlPosedge
    | TimingCheckEventControlNegedge
    | TimingCheckEventControl
    | EdgeDescriptor of string
    | OverloadDeclaration of OverloadOperator.t * identifier
    | Params
    | ClockingDeclaration of identifier
    | Global
    | ClockingBody
    | ClockingItemDefault
    | ClockingItem
    | DefaultSkewInput
    | DefaultSkewOutput
    | DefaultSkewInputOutput
    | ClockingDirectionInput
    | ClockingDirectionInputOutput
    | ClockingDirectionInout
    | ClockingSkewPosedge
    | ClockingSkewNegedge
    | ClockingSkewEdge
    | ClockingSkew
    | ClockingDeclAssign of identifier
    | Production of identifier
    | ProductionItem of identifier
    | RsCodeBlock
    | RsRule
    | RsProductionList
    | RsProductionListRandJoin
    | WeightSpecInt of string
    | WeightSpecId
    | WeightSpec
    | RsProdIf
    | RsProdRepeat
    | RsProdCase
    | RsCaseItem
    | RsCaseItemDefault
    | CheckerOrGenerateItemEmpty
    | ConditionalGenerateConstructCase
    | ConditionalGenerateConstructIf
    | ElaborationSystemTask of SystemTask.t
    | CaseGenerateItem
    | CaseGenerateItemDefault
    | AssignmentPattern
    | AssignmentPatternExpr
    | PatternKey
    | PatternKeyDefault
    | PatternMember
    | SimplePathDeclaration
    | ParallelPathDescription
    | FullPathDescription
    | PathInputs
    | PathOutputs
    | PathDelayValue
    | PolarityPlus
    | PolarityMinus
    | EdgePosedge
    | EdgeNegedge
    | EdgeSensitivePathDeclaration
    | ParallelEdgeSensitivePathDescription
    | FullEdgeSensitivePathDescription
    | ParallelEdgeSensitivePathDescriptionSub
    | FullEdgeSensitivePathDescriptionSub
    | StateDependentPathDeclarationIf
    | StateDependentPathDeclarationIfnone
    | VariableLvalue
    | AttributeInstance
    | AttrSpec of identifier
    | UdpPort of identifier
    | UdpPortDeclaration
    | UdpOutputDeclaration of identifier
    | UdpOutputDeclarationReg of identifier
    | UdpInputDeclaration
    | UdpRegDeclaration of identifier
    | SequentialBody
    | CombinationalBody
    | UdpInitialStmt of identifier * string
    | SequentialEntry
    | EdgeIndicator
    | EdgeSymbol of string
    | LevelSymbol of string
    | OutputSymbol of string
    | CombinationalEntry
    | NextStateMinus
    | UdpPortsStar
    | UdpPorts
    | UdpPortDecls
    | UdpDeclarationPorts
    | AttributeInstances
    | ConfigDeclaration of identifier
    | DesignStatement
    | CellId of identifier
    | LibraryIdentifier of identifier
    | LiblistClause
    | CellClause of identifier
    | UseClause
    | ColonConfig
    | InstanceName
    | InstanceIdentifier of identifier
    | TopModuleIdentifier of identifier
    | InstClause
    | ConfigRuleStatementDefault
    | ConfigRuleStatement
    | LibraryDeclaration of identifier
    | Incdir
    | FilePathSpec of string
    | IncludeStatement of string
    | PragmaExpression of identifier
    | PragmaValueTuple
    | PragmaValueNum of string
    | PragmaValueStr of string
    | PragmaValueId of identifier
    | PackageImportDecls
    | ParamPorts
    | Ranges
    | VariableDimensions
    | CaseConds
    | NetDeclAssignments of identifier list
    | ParamAssignments of identifier list
    | MacroExpr of string
    | MacroStmt of string
    | Var

let to_string = function
    | Dummy                                    -> "Dummy"
    | Error                                    -> "Error"
    | Empty                                    -> "Empty"
    | SourceText                               -> "SourceText"
    | LibraryText                              -> "LibraryText"
    | CompilerDirective cd                     -> CompilerDirective.to_string cd
    | ModuleDeclaration(mspec, id)             -> "ModuleDeclaration:"^(ModuleSpec.to_string mspec)^":"^id
    | UdpDeclaration id                        -> "UdpDeclaration:"^id
    | NetDeclaration ids                       -> "NetDeclaration:"^(String.concat "," ids)
    | BindDirective id                         -> "BindDirective:"^id
    | Expr e                                   -> Expression.to_string e
    | Stmt stmt                                -> Statement.to_string stmt
    | NetType nt                               -> NetType.to_string nt
    | LocalParameterDeclaration ids            -> "LocalParameterDeclaration:"^(String.concat "," ids)
    | ParameterDeclaration ids                 -> "ParameterDeclaration:"^(String.concat "," ids)
    | ParameterPortDeclaration                 -> "ParameterPortDeclaration"
    | ModuleBody                               -> "ModuleBody"
    | Instantiation id                         -> "Instantiation:"^id
    | GateInstantiation g                      -> "GateInstantiation:"^(Gate.to_string g)
    | ContinuousAssign                         -> "ContinuousAssign"
    | Assign                                   -> "Assign"
    | ConcurrentAssertionItem                  -> "ConcurrentAssertionItem"
    | DeferredImmediateAssertionItem           -> "DeferredImmediateAssertionItem"
    | PpIdentifier id                          -> "PpIdentifier:"^id
    | PackedDimension                          -> "PackedDimension"
    | ParamAssignment id                       -> "ParamAssignment:"^id
    | DefparamAssignment                       -> "DefparamAssignment"
    | IdSelect id                              -> "IdSelect:"^id
    | Select                                   -> "Select"
    | Range                                    -> "Range"
    | RangePlus                                -> "RangePlus"
    | RangeMinus                               -> "RangeMinus"
    | RangeForeach                             -> "RangeForeach"
    | Root                                     -> "Root"
    | This                                     -> "This"
    | Super                                    -> "Super"
    | Cellpin id                               -> "Cellpin:"^id
    | CellpinStar                              -> "CellpinStar"
    | CellpinAnon                              -> "CellpinAnon"
    | DelayValue id                            -> "DelayValue:"^id
    | PackageScope id                          -> "PackageScope:"^id
    | PackageScopeUnit                         -> "PackageScopeUnit"
    | PackageScopeLocal                        -> "PackageScopeLocal"
    | PackageImport id                         -> "PackageImport:"^id
    | PackageImportAny                         -> "PackageImportAny"
    | LifetimeStatic                           -> "LifetimeStatic"
    | LifetimeAutomatic                        -> "LifetimeAutomatic"
    | EndLabel id                              -> "EndLabel:"^id
    | EndLabelNew                              -> "EndLabelNew"
    | ClassType id                             -> "ClassType:"^id
    | DataType dt                              -> DataType.to_string dt
    | ImplicitDataType                         -> "ImplicitDataType"
    | VarDeclAssignments                       -> "VarDeclAssignments"
    | Signed                                   -> "Signed"
    | Unsigned                                 -> "Unsigned"
    | ArgsDotted id                            -> "ArgsDotted:"^id
    | Tagged                                   -> "Tagged"
    | StructUnionBody                          -> "StructUnionBody"
    | StructUnionMember                        -> "StructUnionMember"
    | ClassScopeId id                          -> "ClassScopeId:"^id
    | Void                                     -> "Void"
    | EnumNameDeclaration id                   -> "EnumNameDeclaration:"^id
    | EnumBody                                 -> "EnumBody"
    | IdClassSel id                            -> "IdClassSel:"^id
    | Variable id                              -> "Variable:"^id
    | Extern                                   -> "Extern"
    | PackageImportDeclaration                 -> "PackageImportDeclaration"
    | PackageImportItem id                     -> "PackageImportItem:"^id
    | Packed                                   -> "Packed"
    | ParameterValueAssignment                 -> "ParameterValueAssignment"
    | Ports                                    -> "Ports"
    | PortsStar                                -> "PortsStar"
    | BitSelect                                -> "BitSelect"
    | VariableDeclAssignment id                -> "VariableDeclAssignment:"^id
    | DynamicArrayNew                          -> "DynamicArrayNew"
    | VariableDimension                        -> "VariableDimension"
    | VariableDimensionStar                    -> "VariableDimensionStar"
    | GenItemBegin                             -> "GenItemBegin"
    | GenBlockId id                            -> "GenBlockId:"^id
    | GenerateRegion                           -> "GenerateRegion"
    | Scalared                                 -> "Scalared"
    | Vectored                                 -> "Vectored"
    | DelayControl                             -> "DelayControl"
    | NetSig id                                -> "NetSig:"^id
    | ParameterOverride                        -> "ParameterOverride"
    | PortDeclaration                          -> "PortDeclaration"
    | PortDirection pd                         -> "PortDirection:"^(PortDirection.to_string pd)
    | Strength strength                        -> "Strength:"^(Strength.to_string strength)
    | StrengthSupply0                          -> "StrengthSupply0"
    | StrengthSupply1                          -> "StrengthSupply1"
    | StrengthSpec                             -> "StrengthSpec"
    | VarDataType                              -> "VarDataType"
    | Port id                                  -> "Port:"^id
    | InterfacePort id                         -> "InterfacePort:"^id
    | InterfacePortInterface                   -> "InterfacePortInterface"
    | ModportIdentifier id                     -> "ModportIdentifier:"^id
    | PortMulti                                -> "PortMulti"
    | ExprScope                                -> "ExprScope"
    | ExprScopeThis                            -> "ExprScopeThis"
    | ExprScopeSuper                           -> "ExprScopeSuper"
    | ExprScopeDot                             -> "ExprScopeDot"
    | ExprScopeDotSuper                        -> "ExprScopeDotSuper"
    | CondPredicate                            -> "CondPredicate"
    | CondPattern                              -> "CondPattern"
    | Dist                                     -> "Dist"
    | DistItem                                 -> "DistItem"
    | DistWeight                               -> "DistWeight"
    | DistWeightRange                          -> "DistWeightRange"
    | ArrayRange                               -> "ArrayRange"
    | ArrayRangePlus                           -> "ArrayRangePlus"
    | ArrayRangeMinus                          -> "ArrayRangeMinus"
    | CastingTypeSimple                        -> "CastingTypeSimple"
    | CastingTypeSigned                        -> "CastingTypeSigned"
    | CastingTypeUnsigned                      -> "CastingTypeUnsigned"
    | CastingTypeString                        -> "CastingTypeString"
    | CastingTypeConst                         -> "CastingTypeConst"
    | ValueRange                               -> "ValueRange"
    | Pattern                                  -> "Pattern"
    | PatternId id                             -> "PatternId:"^id
    | PatternStar                              -> "PatternStar"
    | PatternTagged id                         -> "PatternTagged:"^id
    | EventControl                             -> "EventControl"
    | EventControlStar                         -> "EventControlStar"
    | EventControlParenStar                    -> "EventControlParenStar"
    | EventControlRepeat                       -> "EventControlRepeat"
    | EvExpr ee                                -> EventExpression.to_string ee
    | CaseItem                                 -> "CaseItem"
    | CaseItemDefault                          -> "CaseItemDefault"
    | CaseInsideItem                           -> "CaseInsideItem"
    | CaseInsideItemDefault                    -> "CaseInsideItemDefault"
    | CaseItems                                -> "CaseItems"
    | CaseItemsMatches                         -> "CaseItemsMatches"
    | CaseItemsInside                          -> "CaseItemsInside"
    | With                                     -> "With"
    | Args                                     -> "Args"
    | ConstraintBlock                          -> "ConstraintBlock"
    | ForInit                                  -> "ForInit"
    | ForInitItemDT id                         -> "ForInitItemDT:"^id
    | ForInitItemLval                          -> "ForInitItemLval"
    | StreamingConcat                          -> "StreamingConcat"
    | OrderRL                                  -> "OrderRL"
    | OrderLR                                  -> "OrderLR"
    | StreamConcat                             -> "StreamConcat"
    | Solve                                    -> "Solve"
    | SolveBefore                              -> "SolveBefore"
    | ActionBlock                              -> "ActionBlock"
    | CycleDelay s                             -> "CycleDelay:"^s
    | CycleDelayId id                          -> "CycleDelayId:"^id
    | CycleDelayParen                          -> "CycleDelayParen"
    | Priority                                 -> "Priority"
    | Unique                                   -> "Unique"
    | Unique0                                  -> "Unique0"
    | InstRange                                -> "InstRange"
    | InstName id                              -> "InstName:"^id
    | PExpr pe                                 -> PropertyExpression.to_string pe
    | ClockingEvent id                         -> "ClockingEvent:"^id
    | ClockingEventParen                       -> "ClockingEventParen"
    | PropertyCase                             -> "PropertyCase"
    | PropertyCaseDefault                      -> "PropertyCaseDefault"
    | DisableIff                               -> "DisableIff"
    | CycleDelayRange s                        -> "CycleDelayRange:"^s
    | CycleDelayRangeId id                     -> "CycleDelayRangeId:"^id
    | CycleDelayRangeParen                     -> "CycleDelayRangeParen"
    | CycleDelayRangeBracket                   -> "CycleDelayRangeBracket"
    | CycleDelayRangeBracketStar               -> "CycleDelayRangeBracketStar"
    | CycleDelayRangeBracketPlus               -> "CycleDelayRangeBracketPlus"
    | SExpr se                                 -> SequenceExpression.to_string se
    | ConsecutiveRepetition                    -> "ConsecutiveRepetition"
    | NonconsecutiveRepetition                 -> "NonconsecutiveRepetition"
    | GotoRepetition                           -> "GotoRepetition"
    | NetAlias                                 -> "NetAlias"
    | InitialConstruct                         -> "InitialConstruct"
    | FinalConstruct                           -> "FinalConstruct"
    | AlwaysConstruct aspec                    -> "AlwaysConstruct:"^(AlwaysSpec.to_string aspec)
    | ConcurrentAssertionItemLabeled id        -> "ConcurrentAssertionItemLabeled:"^id
    | ConcurrentAssertionStmt ca               -> ConcurrentAssertion.to_string ca
    | DeferredImmediateAssertionItemLabeled id -> "DeferredImmediateAssertionItemLabeled:"^id
    | DeferredImmediateAssertionStmt dia       -> DeferredImmediateAssertion.to_string dia
    | SimpleImmediateAssertionStmt sia         -> SimpleImmediateAssertion.to_string sia
    | CheckerInstantiation id                  -> "CheckerInstantiation:"^id
    | LoopGenerateConstruct                    -> "LoopGenerateConstruct"
    | GenvarDeclaration ids                    -> "GenvarDeclaration:"^(String.concat "," ids)
    | GenvarIterationAssign(ao, id)            -> "GenvarIteration:"^(AssignmentOperator.to_string ao)^":"^id
    | GenvarIterationIncOrDec(iod, id)         -> "GenvarIteration:"^(IncOrDecOperator.to_string iod)^":"^id
    | GenvarIdDecl id                          -> "GenvarIdDecl:"^id
    | GenvarInitId id                          -> "GenvarInitId:"^id
    | GenvarInit                               -> "GenvarInit"
    | SpecifyBlock                             -> "SpecifyBlock"
    | SpecparamDeclaration                     -> "SpecparamDeclaration"
    | SpecparamAssignmentId id                 -> "SpecparamAssignmentId:"^id
    | SpecparamAssignmentPulseControl id       -> "SpecparamAssignmentPulseControl:"^id
    | PulsestyleDeclarationOnevent             -> "PulsestyleDeclarationOnevent"
    | PulsestyleDeclarationOndetect            -> "PulsestyleDeclarationOndetect"
    | ShowcancelledDeclaration                 -> "ShowcancelledDeclaration"
    | NoshowcancelledDeclaration               -> "NoshowcancelledDeclaration"
    | SpecifyTerminalDescriptor                -> "SpecifyTerminalDescriptor"
    | InputOrOutputId id                       -> "InputOrOutputId:"^id
    | InterfaceIdentifier id                   -> "InterfaceIdentifier:"^id
    | ProgramDeclaration id                    -> "ProgramDeclaration:"^id
    | InterfaceDeclaration id                  -> "InterfaceDeclaration:"^id
    | InterfaceDeclarationExtern id            -> "InterfaceDeclarationExtern:"^id
    | TimeUnitsDeclaration                     -> "TimeUnitsDeclaration"
    | TimeUnit s                               -> "TimeUnit:"^s
    | Timeprecision s                          -> "Timeprecision:"^s
    | PackageDeclaration id                    -> "PackageDeclaration:"^id
    | AnonymousProgram                         -> "AnonymousProgram"
    | AnonymousProgramItemEmpty                -> "AnonymousProgramItemEmpty"
    | FunctionDeclaration id                   -> "FunctionDeclaration:"^id
    | FunctionPrototype id                     -> "FunctionPrototype:"^id
    | FuncId id                                -> "FuncId:"^id
    | FuncIdVoid id                            -> "FuncIdVoid:"^id
    | FuncIdNew                                -> "FuncIdNew"
    | TfIdScoped id                            -> "TfIdScoped:"^id
    | TaskDeclaration id                       -> "TaskDeclaration:"^id
    | TaskPrototype id                         -> "TaskPrototype:"^id
    | ClassCtorPrototype                       -> "ClassCtorPrototype"
    | TfPortListPart                           -> "TfPortListPart"
    | TfBody                                   -> "TfBody"
    | TfPortDeclaration                        -> "TfPortDeclaration"
    | TfPortItemAssignment id                  -> "TfPortItemAssignment:"^id
    | TfPortItem                               -> "TfPortItem"
    | TfVariableIdentifier id                  -> "TfVariableIdentifier:"^id
    | CheckerDeclaration id                    -> "CheckerDeclaration:"^id
    | PropertyDeclaration id                   -> "PropertyDeclaration:"^id
    | PropertyDeclBody                         -> "PropertyDeclBody"
    | PropertyPortItem                         -> "PropertyPortItem"
    | PropertyPortItemDir                      -> "PropertyPortItemDir"
    | PropertyPortItemAssignment id            -> "PropertyPortItemAssignment:"^id
    | SequenceDeclaration id                   -> "SequenceDeclaration:"^id
    | SequenceDeclBody                         -> "SequenceDeclBody"
    | LetDeclaration id                        -> "LetDeclaration:"^id
    | PropertyStatementSpec                    -> "PropertyStatementSpec"
    | AssertionVariableDeclaration             -> "AssertionVariableDeclaration"
    | SequenceFormalTypeSequence               -> "SequenceFormalTypeSequence"
    | SequenceFormalTypeUntyped                -> "SequenceFormalTypeUntyped"
    | DataDeclarationVar                       -> "DataDeclarationVar"
    | Const                                    -> "Const"
    | DataDeclarationVarClass                  -> "DataDeclarationVarClass"
    | TypeDeclaration id                       -> "TypeDeclaration:"^id
    | ScopedType id                            -> "ScopedType:"^id
    | TypeIdentifier id                        -> "TypeIdentifier:"^id
    | TypeDeclEnum                             -> "TypeDeclEnum"
    | TypeDeclStruct                           -> "TypeDeclStruct"
    | TypeDeclUnion                            -> "TypeDeclUnion"
    | TypeDeclClass                            -> "TypeDeclClass"
    | VirtualInterfaceDeclaration id           -> "VirtualInterfaceDeclaration:"^id
    | ModportDeclaration ids                   -> "ModportDeclaration:"^(String.concat "," ids)
    | ModportItem id                           -> "ModportItem:"^id
    | ModportSimplePortsDecl                   -> "ModportSimplePortsDecl"
    | ModportClockingDecl id                   -> "ModportClockingDecl:"^id
    | ModportTfPortsDeclImport                 -> "ModportTfPortsDeclImport"
    | ModportTfPortsDeclExport                 -> "ModportTfPortsDeclExport"
    | ModportSimplePort id                     -> "ModportSimplePort:"^id
    | ModportSimplePortDot id                  -> "ModportSimplePortDot:"^id
    | ModportTfPort id                         -> "ModportTfPort:"^id
    | CovergroupDeclaration id                 -> "CovergroupDeclaration:"^id
    | Paren                                    -> "Paren"
    | CoverageOption(id1, id2)                 -> "CoverageOption:"^id1^":"^id2
    | CoverPoint                               -> "CoverPoint"
    | CoverPointLabeled id                     -> "CoverPointLabeled:"^id
    | CoverCross                               -> "CoverCross"
    | CoverCrossLabeled id                     -> "CoverCrossLabeled:"^id
    | CrossItem id                             -> "CrossItem:"^id
    | Iff                                      -> "Iff"
    | BinsList                                 -> "BinsList"
    | BinsEmpty                                -> "BinsEmpty"
    | SelectBins                               -> "SelectBins"
    | SelectBinsEmpty                          -> "SelectBinsEmpty"
    | Bins(bspec, id)                          -> "Bins:"^(BinsSpec.to_string bspec)^":"^id
    | BinsSelection(bspec, id)                 -> "BinsSelection:"^(BinsSpec.to_string bspec)^":"^id
    | BinsExpressionVar id                     -> "BinsExpressionVar:"^id
    | BinsExpression(id1, id2)                 -> "BinsExpression:"^id1^":"^id2
    | NBins                                    -> "NBins"
    | SelCondBinsof                            -> "SelCondBinsof"
    | SelExprNot                               -> "SelExprNot"
    | SelExprAnd                               -> "SelExprAnd"
    | SelExprOr                                -> "SelExprOr"
    | SelExprParen                             -> "SelExprParen"
    | Intersect                                -> "Intersect"
    | Wildcard                                 -> "Wildcard"
    | TransSet                                 -> "TransSet"
    | TransRangeList                           -> "TransRangeList"
    | RepeatRange                              -> "RepeatRange"
    | TransItem                                -> "TransItem"
    | TransRepetitionConsecutive               -> "TransRepetitionConsecutive"
    | TransRepetitionNonconsecutive            -> "TransRepetitionNonconsecutive"
    | TransRepetitionGoto                      -> "TransRepetitionGoto"
    | Default                                  -> "Default"
    | DefaultSequence                          -> "DefaultSequence"
    | OpenRangeList                            -> "OpenRangeList"
    | CoverageEventWith id                     -> "CoverageEventWith:"^id
    | CoverageEventBlockEvent                  -> "CoverageEventBlockEvent"
    | BlockEventExpression                     -> "BlockEventExpression"
    | BlockEventExpressionBegin                -> "BlockEventExpressionBegin"
    | BlockEventExpressionEnd                  -> "BlockEventExpressionEnd"
    | HierarchicalBtfIdentifier id             -> "HierarchicalBtfIdentifier:"^id
    | PackageExportDeclarationStar             -> "PackageExportDeclarationStar"
    | PackageExportDeclaration                 -> "PackageExportDeclaration"
    | DpiImport s                              -> "DpiImport:"^s
    | DpiExportFunc(s, id)                     -> "DpiExportFunc:"^s^":"^id
    | DpiExportTask(s, id)                     -> "DpiExportTask:"^s^":"^id
    | DpiImportLabel id                        -> "DpiImportLabel:"^id
    | DpiTfImportPropertyContext               -> "DpiTfImportPropertyContext"
    | DpiTfImportPropertyPure                  -> "DpiTfImportPropertyPure"
    | ExternConstraintDeclaration              -> "ExternConstraintDeclaration"
    | Static                                   -> "Static"
    | Virtual                                  -> "Virtual"
    | ClassDeclaration id                      -> "ClassDeclaration:"^id
    | ClassExtends                             -> "ClassExtends"
    | ClassItemEmpty                           -> "ClassItemEmpty"
    | ClassMethod                              -> "ClassMethod"
    | Qualifier q                              -> "Qualifier:"^(Qualifier.to_string q)
    | ClassBody                                -> "ClassBody"
    | ClassConstraint id                       -> "ClassConstraint:"^id
    | Pure                                     -> "Pure"
    | ClassProperty                            -> "ClassProperty"
    | PackageOrGenerateItemEmpty               -> "PackageOrGenerateItemEmpty"
    | Forkjoin                                 -> "Forkjoin"
    | ExternTfDeclaration id                   -> "ExternTfDeclaration:"^id
    | TimingCheck tc                           -> TimingCheck.to_string tc
    | SystemTimingCheck                        -> "SystemTimingCheck"
    | Notifier id                              -> "Notifier:"^id
    | Delayed id                               -> "Delayed:"^id
    | TimingCheckEvent                         -> "TimingCheckEvent"
    | TimingCheckEventControlPosedge           -> "TimingCheckEventControlPosedge"
    | TimingCheckEventControlNegedge           -> "TimingCheckEventControlNegedge"
    | TimingCheckEventControl                  -> "TimingCheckEventControl"
    | EdgeDescriptor s                         -> "EdgeDescriptor:"^s
    | OverloadDeclaration(oo, id)              -> "OverloadDeclaration:"^(OverloadOperator.to_string oo)^":"^id
    | Params                                   -> "Params"
    | ClockingDeclaration id                   -> "ClockingDeclaration:"^id
    | Global                                   -> "Global"
    | ClockingBody                             -> "ClockingBody"
    | ClockingItemDefault                      -> "ClockingItemDefault"
    | ClockingItem                             -> "ClockingItem"
    | DefaultSkewInput                         -> "DefaultSkewInput"
    | DefaultSkewOutput                        -> "DefaultSkewOutput"
    | DefaultSkewInputOutput                   -> "DefaultSkewInputOutput"
    | ClockingDirectionInput                   -> "ClockingDirectionInput"
    | ClockingDirectionInputOutput             -> "ClockingDirectionInputOutput"
    | ClockingDirectionInout                   -> "ClockingDirectionInout"
    | ClockingSkewPosedge                      -> "ClockingSkewPosedge"
    | ClockingSkewNegedge                      -> "ClockingSkewNegedge"
    | ClockingSkewEdge                         -> "ClockingSkewEdge"
    | ClockingSkew                             -> "ClockingSkew"
    | ClockingDeclAssign id                    -> "ClockingDeclAssign:"^id
    | Production id                            -> "Production:"^id
    | ProductionItem id                        -> "ProductionItem:"^id
    | RsCodeBlock                              -> "RsCodeBlock"
    | RsRule                                   -> "RsRule"
    | RsProductionList                         -> "RsProductionList"
    | RsProductionListRandJoin                 -> "RsProductionListRandJoin"
    | WeightSpecInt s                          -> "WeightSpecInt:"^s
    | WeightSpecId                             -> "WeightSpecId"
    | WeightSpec                               -> "WeightSpec"
    | RsProdIf                                 -> "RsProdIf"
    | RsProdRepeat                             -> "RsProdRepeat"
    | RsProdCase                               -> "RsProdCase"
    | RsCaseItem                               -> "RsCaseItem"
    | RsCaseItemDefault                        -> "RsCaseItemDefault"
    | CheckerOrGenerateItemEmpty               -> "CheckerOrGenerateItemEmpty"
    | ConditionalGenerateConstructCase         -> "ConditionalGenerateConstructCase"
    | ConditionalGenerateConstructIf           -> "ConditionalGenerateConstructIf"
    | ElaborationSystemTask st                 -> "ElaborationSystemTask:"^(SystemTask.to_string st)
    | CaseGenerateItem                         -> "CaseGenerateItem"
    | CaseGenerateItemDefault                  -> "CaseGenerateItemDefault"
    | AssignmentPattern                        -> "AssignmentPattern"
    | AssignmentPatternExpr                    -> "AssignmentPatternExpr"
    | PatternKey                               -> "PatternKey"
    | PatternKeyDefault                        -> "PatternKeyDefault"
    | PatternMember                            -> "PatternMember"
    | SimplePathDeclaration                    -> "SimplePathDeclaration"
    | ParallelPathDescription                  -> "ParallelPathDescription"
    | FullPathDescription                      -> "FullPathDescription"
    | PathInputs                               -> "PathInputs"
    | PathOutputs                              -> "PathOutputs"
    | PathDelayValue                           -> "PathDelayValue"
    | PolarityPlus                             -> "PolarityPlus"
    | PolarityMinus                            -> "PolarityMinus"
    | EdgePosedge                              -> "EdgePosedge"
    | EdgeNegedge                              -> "EdgeNegedge"
    | EdgeSensitivePathDeclaration             -> "EdgeSensitivePathDeclaration"
    | ParallelEdgeSensitivePathDescription     -> "ParallelEdgeSensitivePathDescription"
    | FullEdgeSensitivePathDescription         -> "FullEdgeSensitivePathDescription"
    | ParallelEdgeSensitivePathDescriptionSub  -> "ParallelEdgeSensitivePathDescriptionSub"
    | FullEdgeSensitivePathDescriptionSub      -> "FullEdgeSensitivePathDescriptionSub"
    | StateDependentPathDeclarationIf          -> "StateDependentPathDeclarationIf"
    | StateDependentPathDeclarationIfnone      -> "StateDependentPathDeclarationIfnone"
    | VariableLvalue                           -> "VariableLvalue"
    | AttributeInstance                        -> "AttributeInstance"
    | AttrSpec id                              -> "AttrSpec:"^id
    | UdpPort id                               -> "UdpPort:"^id
    | UdpPortDeclaration                       -> "UdpPortDeclaration"
    | UdpOutputDeclaration id                  -> "UdpOutputDeclaration:"^id
    | UdpOutputDeclarationReg id               -> "UdpOutputDeclarationReg:"^id
    | UdpInputDeclaration                      -> "UdpInputDeclaration"
    | UdpRegDeclaration id                     -> "UdpRegDeclaration:"^id
    | SequentialBody                           -> "SequentialBody"
    | CombinationalBody                        -> "CombinationalBody"
    | UdpInitialStmt(id, s)                    -> "UdpInitialStmt:"^id^":"^s
    | SequentialEntry                          -> "SequentialEntry"
    | EdgeIndicator                            -> "EdgeIndicator"
    | EdgeSymbol s                             -> "EdgeSymbol:"^s
    | LevelSymbol s                            -> "LevelSymbol:"^s
    | OutputSymbol s                           -> "OutputSymbol:"^s
    | CombinationalEntry                       -> "CombinationalEntry"
    | NextStateMinus                           -> "NextStateMinus"
    | UdpPortsStar                             -> "UdpPortsStar"
    | UdpPorts                                 -> "UdpPorts"
    | UdpPortDecls                             -> "UdpPortDecls"
    | UdpDeclarationPorts                      -> "UdpDeclarationPorts"
    | AttributeInstances                       -> "AttributeInstances"
    | ConfigDeclaration id                     -> "ConfigDeclaration:"^id
    | DesignStatement                          -> "DesignStatement"
    | CellId id                                -> "CellId:"^id
    | LibraryIdentifier id                     -> "LibraryIdentifier:"^id
    | LiblistClause                            -> "LiblistClause"
    | CellClause id                            -> "CellClause:"^id
    | UseClause                                -> "UseClause"
    | ColonConfig                              -> "ColonConfig"
    | InstanceName                             -> "InstanceName"
    | InstanceIdentifier id                    -> "InstanceIdentifier:"^id
    | TopModuleIdentifier id                   -> "TopModuleIdentifier:"^id
    | InstClause                               -> "InstClause"
    | ConfigRuleStatementDefault               -> "ConfigRuleStatementDefault"
    | ConfigRuleStatement                      -> "ConfigRuleStatement"
    | LibraryDeclaration id                    -> "LibraryDeclaration:"^id
    | Incdir                                   -> "Incdir"
    | FilePathSpec s                           -> "FilePathSpec:"^s
    | IncludeStatement s                       -> "IncludeStatement:"^s
    | PragmaExpression id                      -> "PragmaExpression:"^id
    | PragmaValueTuple                         -> "PragmaValueTuple"
    | PragmaValueNum s                         -> "PragmaValueNum:"^s
    | PragmaValueStr s                         -> "PragmaValueStr:"^s
    | PragmaValueId id                         -> "PragmaValueId:"^id
    | PackageImportDecls                       -> "PackageImportDecls"
    | ParamPorts                               -> "ParamPorts"
    | Ranges                                   -> "Ranges"
    | VariableDimensions                       -> "VariableDimensions"
    | CaseConds                                -> "CaseConds"
    | NetDeclAssignments ids                   -> "NetDeclAssignments:"^(String.concat "," ids)
    | ParamAssignments ids                     -> "ParamAssignments:"^(String.concat "," ids)
    | MacroExpr s                              -> "MacroExpr:"^s
    | MacroStmt s                              -> "MacroStmt:"^s
    | Var                                      -> "Var"

let to_simple_string = function
    | Dummy                                    -> "<dummy>"
    | Error                                    -> "<error>"
    | Empty                                    -> ";"
    | SourceText                               -> "<source_text>"
    | LibraryText                              -> "<library_text>"
    | CompilerDirective cd                     -> CompilerDirective.to_simple_string cd
    | ModuleDeclaration(mspec, id)             -> (ModuleSpec.to_rep mspec)^" "^id
    | UdpDeclaration id                        -> "primitive "^id
    | NetDeclaration ids                       -> "<net_decl:"^(String.concat "," ids)^">"
    | BindDirective id                         -> "bind "^id
    | Expr e                                   -> Expression.to_simple_string e
    | Stmt stmt                                -> Statement.to_simple_string stmt
    | NetType nt                               -> NetType.to_simple_string nt
    | LocalParameterDeclaration _              -> "<local_param_decl>"
    | ParameterDeclaration _                   -> "<param_decl>"
    | ParameterPortDeclaration                 -> "<param_port_decl>"
    | ModuleBody                               -> "<module_body>"
    | Instantiation id                         -> "<inst:"^id^">"
    | GateInstantiation g                      -> Gate.to_simple_string g
    | ContinuousAssign                         -> "<continuous_assign>"
    | Assign                                   -> "assign"
    | ConcurrentAssertionItem                  -> "<concur_assert_item>"
    | DeferredImmediateAssertionItem           -> "<deferred_immediate_assert_item>"
    | PpIdentifier id                          -> id
    | PackedDimension                          -> "<packed_dim>"
    | ParamAssignment id                       -> "<param_assign:"^id^">"
    | DefparamAssignment                       -> "<def_param_assign>"
    | IdSelect id                              -> id
    | Select                                   -> "<sel>"
    | Range                                    -> ":"
    | RangePlus                                -> ":+"
    | RangeMinus                               -> ":-"
    | RangeForeach                             -> "<range_foreach>"
    | Root                                     -> "$root"
    | This                                     -> "this"
    | Super                                    -> "super"
    | Cellpin id                               -> "."^id
    | CellpinStar                              -> ".*"
    | CellpinAnon                              -> "<cellpin_anon>"
    | DelayValue id                            -> id
    | PackageScope id                          -> id^"::"
    | PackageScopeUnit                         -> "$unit::"
    | PackageScopeLocal                        -> "local::"
    | PackageImport id                         -> id
    | PackageImportAny                         -> "*"
    | LifetimeStatic                           -> "static"
    | LifetimeAutomatic                        -> "automatic"
    | EndLabel id                              -> ":"^id
    | EndLabelNew                              -> ":new"
    | ClassType id                             -> id
    | DataType dt                              -> DataType.to_simple_string dt
    | ImplicitDataType                         -> "<implicit_data_type>"
    | VarDeclAssignments                       -> "<var_decl_assignments>"
    | Signed                                   -> "signed"
    | Unsigned                                 -> "unsigned"
    | ArgsDotted id                            -> "."^id
    | Tagged                                   -> "tagged"
    | StructUnionBody                          -> "<struct_union_body>"
    | StructUnionMember                        -> "<struct_union_mem>"
    | ClassScopeId id                          -> id
    | Void                                     -> "void"
    | EnumNameDeclaration id                   -> id
    | EnumBody                                 -> "<enum_body>"
    | IdClassSel id                            -> id
    | Variable id                              -> id
    | Extern                                   -> "extern"
    | PackageImportDeclaration                 -> "import"
    | PackageImportItem id                     -> id^"::"
    | Packed                                   -> "packed"
    | ParameterValueAssignment                 -> "<param_val_assign>"
    | Ports                                    -> "<ports>"
    | PortsStar                                -> "(*)"
    | BitSelect                                -> "<bit_sel>"
    | VariableDeclAssignment id                -> "<var_decl_assign:"^id^">"
    | DynamicArrayNew                          -> "new[]"
    | VariableDimension                        -> "<var_dim>"
    | VariableDimensionStar                    -> "[*]"
    | GenItemBegin                             -> "<gen_item_begin>"
    | GenBlockId id                            -> ":"^id
    | GenerateRegion                           -> "generate"
    | Scalared                                 -> "scalared"
    | Vectored                                 -> "vectored"
    | DelayControl                             -> "#"
    | NetSig id                                -> id
    | ParameterOverride                        -> "defparam"
    | PortDeclaration                          -> "<port_decl>"
    | PortDirection pd                         -> PortDirection.to_simple_string pd
    | Strength strength                        -> Strength.to_rep strength
    | StrengthSupply0                          -> "supply0"
    | StrengthSupply1                          -> "supply1"
    | StrengthSpec                             -> "spec"
    | VarDataType                              -> "<var_datatype>"
    | Port id                                  -> id
    | InterfacePort id                         -> id
    | InterfacePortInterface                   -> "interface"
    | ModportIdentifier id                     -> id
    | PortMulti                                -> "<port_multi>"
    | ExprScope                                -> "<expr_scope>"
    | ExprScopeThis                            -> "this"
    | ExprScopeSuper                           -> "super"
    | ExprScopeDot                             -> "."
    | ExprScopeDotSuper                        -> ".super"
    | CondPredicate                            -> "&&&"
    | CondPattern                              -> "matches"
    | Dist                                     -> "dist"
    | DistItem                                 -> "<dist_item>"
    | DistWeight                               -> ":="
    | DistWeightRange                          -> ":/"
    | ArrayRange                               -> "<array_range>"
    | ArrayRangePlus                           -> ":+"
    | ArrayRangeMinus                          -> ":-"
    | CastingTypeSimple                        -> "<casting_type_simple>"
    | CastingTypeSigned                        -> "signed"
    | CastingTypeUnsigned                      -> "unsigned"
    | CastingTypeString                        -> "string"
    | CastingTypeConst                         -> "const"
    | ValueRange                               -> "<value_range>"
    | Pattern                                  -> "<pat>"
    | PatternId id                             -> "."^id
    | PatternStar                              -> ".*"
    | PatternTagged id                         -> "tagged:"^id
    | EventControl                             -> "@"
    | EventControlStar                         -> "@*"
    | EventControlParenStar                    -> "@(*)"
    | EventControlRepeat                       -> "repeat"
    | EvExpr ee                                -> EventExpression.to_simple_string ee
    | CaseItem                                 -> "<case_item>"
    | CaseItemDefault                          -> "default"
    | CaseInsideItem                           -> "<case_inside_item>"
    | CaseInsideItemDefault                    -> "default"
    | CaseItems                                -> "<case_items>"
    | CaseItemsMatches                         -> "matches"
    | CaseItemsInside                          -> "inside"
    | With                                     -> "with"
    | Args                                     -> "<args>"
    | ConstraintBlock                          -> "<constraint_block>"
    | ForInit                                  -> "<for_ini>"
    | ForInitItemDT id                         -> id
    | ForInitItemLval                          -> "<for_ini_item_lval>"
    | StreamingConcat                          -> "<streaming_concat>"
    | OrderRL                                  -> "<<"
    | OrderLR                                  -> ">>"
    | StreamConcat                             -> "<stream_concat>"
    | Solve                                    -> "solve"
    | SolveBefore                              -> "<solve_before>"
    | ActionBlock                              -> "<act_block>"
    | CycleDelay s                             -> "##"^s
    | CycleDelayId id                          -> "##"^id
    | CycleDelayParen                          -> "##"
    | Priority                                 -> "priority"
    | Unique                                   -> "unique"
    | Unique0                                  -> "unique0"
    | InstRange                                -> "<inst_range>"
    | InstName id                              -> id
    | PExpr pe                                 -> PropertyExpression.to_simple_string pe
    | ClockingEvent id                         -> "@"^id
    | ClockingEventParen                       -> "@"
    | PropertyCase                             -> "<prop_case>"
    | PropertyCaseDefault                      -> "default"
    | DisableIff                               -> "disable iff"
    | CycleDelayRange s                        -> "##"^s
    | CycleDelayRangeId id                     -> "##"^id
    | CycleDelayRangeParen                     -> "##"
    | CycleDelayRangeBracket                   -> "##[]"
    | CycleDelayRangeBracketStar               -> "##[*]"
    | CycleDelayRangeBracketPlus               -> "##[+]"
    | SExpr se                                 -> SequenceExpression.to_simple_string se
    | ConsecutiveRepetition                    -> "[*]"
    | NonconsecutiveRepetition                 -> "[=]"
    | GotoRepetition                           -> "[->]"
    | NetAlias                                 -> "alias"
    | InitialConstruct                         -> "initial"
    | FinalConstruct                           -> "final"
    | AlwaysConstruct aspec                    -> AlwaysSpec.to_rep aspec
    | ConcurrentAssertionItemLabeled id        -> id^":"
    | ConcurrentAssertionStmt ca               -> ConcurrentAssertion.to_simple_string ca
    | DeferredImmediateAssertionItemLabeled id -> id^":"
    | DeferredImmediateAssertionStmt dia       -> DeferredImmediateAssertion.to_simple_string dia
    | SimpleImmediateAssertionStmt sia         -> SimpleImmediateAssertion.to_simple_string sia
    | CheckerInstantiation id                  -> id
    | LoopGenerateConstruct                    -> "for"
    | GenvarDeclaration _                      -> "genvar"
    | GenvarIterationAssign(ao, id)            -> "genvar_iter:"^(AssignmentOperator.to_string ao)^":"^id
    | GenvarIterationIncOrDec(iod, id)         -> "genvar_iter:"^(IncOrDecOperator.to_string iod)^":"^id
    | GenvarIdDecl id                          -> "<genvar_id_decl:"^id^">"
    | GenvarInitId id                          -> "<genvar_ini_id:"^id^">"
    | GenvarInit                               -> "genvar"
    | SpecifyBlock                             -> "specify"
    | SpecparamDeclaration                     -> "specparam"
    | SpecparamAssignmentId id                 -> id
    | SpecparamAssignmentPulseControl id       -> "PATHPULSE$"^id
    | PulsestyleDeclarationOnevent             -> "pulsestyle_onevent"
    | PulsestyleDeclarationOndetect            -> "pulsestyle_ondetect"
    | ShowcancelledDeclaration                 -> "showcancelled"
    | NoshowcancelledDeclaration               -> "noshowcancelled"
    | SpecifyTerminalDescriptor                -> "<spec_term_desc>"
    | InputOrOutputId id                       -> id
    | InterfaceIdentifier id                   -> id
    | ProgramDeclaration id                    -> "program "^id
    | InterfaceDeclaration id                  -> "interface "^id
    | InterfaceDeclarationExtern id            -> "extern interface "^id
    | TimeUnitsDeclaration                     -> "timeunits"
    | TimeUnit s                               -> s
    | Timeprecision s                          -> s
    | PackageDeclaration id                    -> "package "^id
    | AnonymousProgram                         -> "program"
    | AnonymousProgramItemEmpty                -> ";"
    | FunctionDeclaration id                   -> "function "^id
    | FunctionPrototype id                     -> "function "^id
    | FuncId id                                -> "<func_id:"^id^">"
    | FuncIdVoid id                            -> "<fun_id_void:"^id^">"
    | FuncIdNew                                -> "new"
    | TfIdScoped id                            -> id
    | TaskDeclaration id                       -> "task "^id
    | TaskPrototype id                         -> "task "^id
    | ClassCtorPrototype                       -> "<class_ctor_proto>"
    | TfPortListPart                           -> "<tf_port_list_part>"
    | TfBody                                   -> "<tf_body>"
    | TfPortDeclaration                        -> "<tf_port_decl>"
    | TfPortItemAssignment id                  -> "<tf_port_item_assign:"^id^">"
    | TfPortItem                               -> "<tf_port_item>"
    | TfVariableIdentifier id                  -> id
    | CheckerDeclaration id                    -> "checker "^id
    | PropertyDeclaration id                   -> "property "^id
    | PropertyDeclBody                         -> "<prop_decl_body>"
    | PropertyPortItem                         -> "<prop_port_item>"
    | PropertyPortItemDir                      -> "<prop_port_item_dir>"
    | PropertyPortItemAssignment id            -> "<prop_port_item_assign:"^id^">"
    | SequenceDeclaration id                   -> "sequence "^id
    | SequenceDeclBody                         -> "<seq_decl_body>"
    | LetDeclaration id                        -> "let "^id
    | PropertyStatementSpec                    -> "<prop_stmt_spec>"
    | AssertionVariableDeclaration             -> "<asser_var_decl>"
    | SequenceFormalTypeSequence               -> "sequence"
    | SequenceFormalTypeUntyped                -> "untyped"
    | DataDeclarationVar                       -> "<data_decl_var>"
    | Const                                    -> "const"
    | DataDeclarationVarClass                  -> "<data_decl_var_class>"
    | TypeDeclaration id                       -> "typedef "^id
    | ScopedType id                            -> "<scoped_type:"^id^">"
    | TypeIdentifier id                        -> id
    | TypeDeclEnum                             -> "enum"
    | TypeDeclStruct                           -> "struct"
    | TypeDeclUnion                            -> "union"
    | TypeDeclClass                            -> "class"
    | VirtualInterfaceDeclaration id           -> "virtual interface "^id
    | ModportDeclaration ids                   -> "modport "^(String.concat "," ids)
    | ModportItem id                           -> "<modport_item:"^id^">"
    | ModportSimplePortsDecl                   -> "<modport_simple_ports_decl>"
    | ModportClockingDecl id                   -> "clocking "^id
    | ModportTfPortsDeclImport                 -> "import"
    | ModportTfPortsDeclExport                 -> "export"
    | ModportSimplePort id                     -> id
    | ModportSimplePortDot id                  -> "."^id
    | ModportTfPort id                         -> id
    | CovergroupDeclaration id                 -> "covergroup "^id
    | Paren                                    -> "()"
    | CoverageOption(id1, id2)                 -> "<coverage_opt:"^id1^":"^id2^">"
    | CoverPoint                               -> "coverpoint"
    | CoverPointLabeled id                     -> id^":coverpoint"
    | CoverCross                               -> "covercross"
    | CoverCrossLabeled id                     -> id^":covercross"
    | CrossItem id                             -> "<cross_item:"^id^">"
    | Iff                                      -> "iff"
    | BinsList                                 -> "<bins_list>"
    | BinsEmpty                                -> ";"
    | SelectBins                               -> "<sel_bins>"
    | SelectBinsEmpty                          -> ";"
    | Bins(bspec, id)                          -> (BinsSpec.to_rep bspec)^" "^id
    | BinsSelection(bspec, id)                 -> (BinsSpec.to_rep bspec)^" "^id
    | BinsExpressionVar id                     -> id
    | BinsExpression(id1, id2)                 -> id1^"."^id2
    | NBins                                    -> "[]"
    | SelCondBinsof                            -> "binsof"
    | SelExprNot                               -> "!"
    | SelExprAnd                               -> "&&"
    | SelExprOr                                -> "||"
    | SelExprParen                             -> "()"
    | Intersect                                -> "intersect"
    | Wildcard                                 -> "wildcard"
    | TransSet                                 -> "<trans_set>"
    | TransRangeList                           -> "<trans_range_list>"
    | RepeatRange                              -> "<repeat_range>"
    | TransItem                                -> "<trans_item>"
    | TransRepetitionConsecutive               -> "[*]"
    | TransRepetitionNonconsecutive            -> "[=]"
    | TransRepetitionGoto                      -> "[->]"
    | Default                                  -> "default"
    | DefaultSequence                          -> "default sequence"
    | OpenRangeList                            -> "<open_range_list>"
    | CoverageEventWith id                     -> "with function "^id
    | CoverageEventBlockEvent                  -> "@@"
    | BlockEventExpression                     -> "<block_ev_expr>"
    | BlockEventExpressionBegin                -> "begin"
    | BlockEventExpressionEnd                  -> "end"
    | HierarchicalBtfIdentifier id             -> "<hierarchical_Btf_id:"^id^">"
    | PackageExportDeclarationStar             -> "export *::*"
    | PackageExportDeclaration                 -> "export"
    | DpiImport s                              -> "import "^s
    | DpiExportFunc(s, id)                     -> "export "^s^" function "^id
    | DpiExportTask(s, id)                     -> "export "^s^" task "^id
    | DpiImportLabel id                        -> id^"="
    | DpiTfImportPropertyContext               -> "context"
    | DpiTfImportPropertyPure                  -> "pure"
    | ExternConstraintDeclaration              -> "constraint"
    | Static                                   -> "static"
    | Virtual                                  -> "virtual"
    | ClassDeclaration id                      -> "class "^id
    | ClassExtends                             -> "extends"
    | ClassItemEmpty                           -> ";"
    | ClassMethod                              -> "<class_meth>"
    | Qualifier q                              -> Qualifier.to_simple_string q
    | ClassBody                                -> "<class_body>"
    | ClassConstraint id                       -> "constraint "^id
    | Pure                                     -> "pure"
    | ClassProperty                            -> "<class_prop>"
    | PackageOrGenerateItemEmpty               -> ";"
    | Forkjoin                                 -> "forkjoin"
    | ExternTfDeclaration _                    -> "extern"
    | TimingCheck tc                           -> TimingCheck.to_simple_string tc
    | SystemTimingCheck                        -> "<sys_timing_check>"
    | Notifier id                              -> "<notifier:"^id^""
    | Delayed id                               -> "<delayed:"^id^">"
    | TimingCheckEvent                         -> "<timing_check_ev>"
    | TimingCheckEventControlPosedge           -> "posedge"
    | TimingCheckEventControlNegedge           -> "negedge"
    | TimingCheckEventControl                  -> "edge"
    | EdgeDescriptor s                         -> s
    | OverloadDeclaration(oo, id)              -> (OverloadOperator.to_simple_string oo)^" "^id
    | Params                                   -> "<params>"
    | ClockingDeclaration id                   -> "clocking "^id
    | Global                                   -> "global"
    | ClockingBody                             -> "<clocking_body>"
    | ClockingItemDefault                      -> "default"
    | ClockingItem                             -> "<clocking_item>"
    | DefaultSkewInput                         -> "input"
    | DefaultSkewOutput                        -> "output"
    | DefaultSkewInputOutput                   -> "input output"
    | ClockingDirectionInput                   -> "input"
    | ClockingDirectionInputOutput             -> "input output"
    | ClockingDirectionInout                   -> "inout"
    | ClockingSkewPosedge                      -> "posedge"
    | ClockingSkewNegedge                      -> "negedge"
    | ClockingSkewEdge                         -> "edge"
    | ClockingSkew                             -> "<clocking_skew>"
    | ClockingDeclAssign id                    -> "<clocking_decl_assign:"^id^">"
    | Production id                            -> "<prod:"^id^">"
    | ProductionItem id                        -> "<prod_item:"^id^">"
    | RsCodeBlock                              -> "<rs_code_block>"
    | RsRule                                   -> "<rs_rule>"
    | RsProductionList                         -> "<rs_prod_list>"
    | RsProductionListRandJoin                 -> "rand join"
    | WeightSpecInt s                          -> s
    | WeightSpecId                             -> "<weight_spec_id>"
    | WeightSpec                               -> "<weight_spec>"
    | RsProdIf                                 -> "if"
    | RsProdRepeat                             -> "repeat"
    | RsProdCase                               -> "case"
    | RsCaseItem                               -> "<rs_case_item>"
    | RsCaseItemDefault                        -> "default"
    | CheckerOrGenerateItemEmpty               -> ";"
    | ConditionalGenerateConstructCase         -> "case"
    | ConditionalGenerateConstructIf           -> "if"
    | ElaborationSystemTask st                 -> SystemTask.to_simple_string st
    | CaseGenerateItem                         -> "<case_gen_item>"
    | CaseGenerateItemDefault                  -> "default"
    | AssignmentPattern                        -> "<assign_pat>"
    | AssignmentPatternExpr                    -> "<assign_pat_expr>"
    | PatternKey                               -> "<pat_key>"
    | PatternKeyDefault                        -> "default"
    | PatternMember                            -> "<pat_mem>"
    | SimplePathDeclaration                    -> "<simple_path_decl>"
    | ParallelPathDescription                  -> "<par_path_desc>"
    | FullPathDescription                      -> "<full_path_desc>"
    | PathInputs                               -> "<path_inputs>"
    | PathOutputs                              -> "<path_outputs>"
    | PathDelayValue                           -> "<path_delay_val>"
    | PolarityPlus                             -> "+"
    | PolarityMinus                            -> "-"
    | EdgePosedge                              -> "posedge"
    | EdgeNegedge                              -> "negedge"
    | EdgeSensitivePathDeclaration             -> "<edge_sensitive_path_decl>"
    | ParallelEdgeSensitivePathDescription     -> "<par_edge_sensitive_path_desc>"
    | FullEdgeSensitivePathDescription         -> "<full_edge_sensitive_path_desc>"
    | ParallelEdgeSensitivePathDescriptionSub  -> "<par_edge_sensitive_path_desc_sub>"
    | FullEdgeSensitivePathDescriptionSub      -> "<full_edge_sensitive_path_desc_sub>"
    | StateDependentPathDeclarationIf          -> "if"
    | StateDependentPathDeclarationIfnone      -> "ifnone"
    | VariableLvalue                           -> "<var_lval>"
    | AttributeInstance                        -> "(* *)"
    | AttrSpec id                              -> "<attr_spec:"^id^">"
    | UdpPort id                               -> id
    | UdpPortDeclaration                       -> "<udp_port_decl>"
    | UdpOutputDeclaration id                  -> "output "^id
    | UdpOutputDeclarationReg id               -> "output reg "^id
    | UdpInputDeclaration                      -> "input"
    | UdpRegDeclaration id                     -> "reg "^id
    | SequentialBody                           -> "<seq_body>"
    | CombinationalBody                        -> "<combi_body>"
    | UdpInitialStmt(id, s)                    -> "initial "^id^"="^s
    | SequentialEntry                          -> "<seq_entry>"
    | EdgeIndicator                            -> "<edge_ind>"
    | EdgeSymbol s                             -> s
    | LevelSymbol s                            -> s
    | OutputSymbol s                           -> s
    | CombinationalEntry                       -> "<combi_entry>"
    | NextStateMinus                           -> "-"
    | UdpPortsStar                             -> "(.*)"
    | UdpPorts                                 -> "<udp_ports>"
    | UdpPortDecls                             -> "<udp_port_decls>"
    | UdpDeclarationPorts                      -> "<udp_decl_ports>"
    | AttributeInstances                       -> "<attr_insts>"
    | ConfigDeclaration id                     -> "config "^id
    | DesignStatement                          -> "design"
    | CellId id                                -> id
    | LibraryIdentifier id                     -> id
    | LiblistClause                            -> "liblist"
    | CellClause id                            -> "cell "^id
    | UseClause                                -> "use"
    | ColonConfig                              -> ":config"
    | InstanceName                             -> "<instance_name>"
    | InstanceIdentifier id                    -> id
    | TopModuleIdentifier id                   -> id
    | InstClause                               -> "instance"
    | ConfigRuleStatementDefault               -> "default"
    | ConfigRuleStatement                      -> "<conf_rule_stmt>"
    | LibraryDeclaration id                    -> "library "^id
    | Incdir                                   -> "-incdir"
    | FilePathSpec s                           -> s
    | IncludeStatement s                       -> "include "^s^";"
    | PragmaExpression id                      -> "<pragma_expr:"^id^">"
    | PragmaValueTuple                         -> "<pragma_val_tuple>"
    | PragmaValueNum s                         -> s
    | PragmaValueStr s                         -> s
    | PragmaValueId id                         -> id
    | PackageImportDecls                       -> "<package_import_decls>"
    | ParamPorts                               -> "<param_ports>"
    | Ranges                                   -> "<ranges>"
    | VariableDimensions                       -> "<variable_dimensions>"
    | CaseConds                                -> "<case_conds>"
    | NetDeclAssignments ids                   -> "<net_decl_assigns:"^(String.concat "," ids)^">"
    | ParamAssignments ids                     -> "<param_assigns:"^(String.concat "," ids)^">"

    | MacroExpr s                              -> "<macro_expr:"^s^">"
    | MacroStmt s                              -> "<macro_stmt:"^s^">"

    | Var                                      -> "var"

let to_tag ?(strip=false) lab =
  ignore strip;
  let name, attrs =
    match lab with
    | Dummy                                    -> "DUMMY", []
    | Error                                    -> "ERROR", []
    | Empty                                    -> "EMPTY", []
    | SourceText                               -> "SourceText", []
    | LibraryText                              -> "LibraryText", []
    | CompilerDirective cd                     -> CompilerDirective.to_tag cd
    | ModuleDeclaration(mspec, id)             -> "ModuleDecl", [spec_attr_name,ModuleSpec.to_rep mspec;ident_attr_name,id]
    | UdpDeclaration id                        -> "UdpDecl", [ident_attr_name,id]
    | NetDeclaration ids                       -> "NetDecl", [ident_attr_name,String.concat ";" ids]
    | BindDirective id                         -> "BindDirective", [ident_attr_name,id]
    | Expr e                                   -> Expression.to_tag e
    | Stmt stmt                                -> Statement.to_tag stmt
    | NetType nt                               -> NetType.to_tag nt
    | LocalParameterDeclaration ids            -> "LocalParamDecl", [ident_attr_name,String.concat ";" ids]
    | ParameterDeclaration ids                 -> "ParamDecl", [ident_attr_name,String.concat ";" ids]
    | ParameterPortDeclaration                 -> "ParamPortDecl", []
    | ModuleBody                               -> "ModuleBody", []
    | Instantiation id                         -> "Instantiation", [ident_attr_name,id]
    | GateInstantiation g                      -> "GateInstantiataion", ["gate",Gate.to_simple_string g]
    | ContinuousAssign                         -> "ContinuousAssign", []
    | Assign                                   -> "Assign", []
    | ConcurrentAssertionItem                  -> "ConcurrentAssertionItem", []
    | DeferredImmediateAssertionItem           -> "DeferredImmediateAssertItem", []
    | PpIdentifier id                          -> "PpIdentifier", [ident_attr_name,id]
    | PackedDimension                          -> "PackedDimension", []
    | ParamAssignment id                       -> "ParamAssignment", [ident_attr_name,id]
    | DefparamAssignment                       -> "DefparamAssign", []
    | IdSelect id                              -> "IdSelect", [ident_attr_name,id]
    | Select                                   -> "Select", []
    | Range                                    -> "Range", []
    | RangePlus                                -> "RangePlus", []
    | RangeMinus                               -> "RangeMinus", []
    | RangeForeach                             -> "RangeForeach", []
    | Root                                     -> "Root", []
    | This                                     -> "This", []
    | Super                                    -> "Super", []
    | Cellpin id                               -> "Cellpin", [ident_attr_name,id]
    | CellpinStar                              -> "Cellpin_Star", []
    | CellpinAnon                              -> "Cellpin_Anon", []
    | DelayValue id                            -> "DelayValue", [ident_attr_name,id]
    | PackageScope id                          -> "PackageScope", [ident_attr_name,id]
    | PackageScopeUnit                         -> "PackageScopeUnit", []
    | PackageScopeLocal                        -> "PackageScopeLocal", []
    | PackageImport id                         -> "PackageImport", [ident_attr_name,id]
    | PackageImportAny                         -> "PackageImportAny", []
    | LifetimeStatic                           -> "LifetimeStatic", []
    | LifetimeAutomatic                        -> "LifetimeAutomatic", []
    | EndLabel id                              -> "EndLabel", [ident_attr_name,id]
    | EndLabelNew                              -> "EndLabelNew", []
    | ClassType id                             -> "ClassType", [ident_attr_name,id]
    | DataType dt                              -> DataType.to_tag dt
    | ImplicitDataType                         -> "ImplicitDataType", []
    | VarDeclAssignments                       -> "VarDeclAssignments", []
    | Signed                                   -> "Signed", []
    | Unsigned                                 -> "Unsigned", []
    | ArgsDotted id                            -> "ArgsDotted", [ident_attr_name,id]
    | Tagged                                   -> "Tagged", []
    | StructUnionBody                          -> "StructUnionBody", []
    | StructUnionMember                        -> "StructUnionMem", []
    | ClassScopeId id                          -> "ClassScopeId", [ident_attr_name,id]
    | Void                                     -> "Void", []
    | EnumNameDeclaration id                   -> "EnumNameDecl", [ident_attr_name,id]
    | EnumBody                                 -> "EnumBody", []
    | IdClassSel id                            -> "IdClassSel", [ident_attr_name,id]
    | Variable id                              -> "Var", [ident_attr_name,id]
    | Extern                                   -> "Extern", []
    | PackageImportDeclaration                 -> "PackageImportDecl", []
    | PackageImportItem id                     -> "PackageImportItem", [ident_attr_name,id]
    | Packed                                   -> "Packed", []
    | ParameterValueAssignment                 -> "ParamValAssign", []
    | Ports                                    -> "Ports", []
    | PortsStar                                -> "PortsStar", []
    | BitSelect                                -> "BitSel", []
    | VariableDeclAssignment id                -> "VarDeclAssign", [ident_attr_name,id]
    | DynamicArrayNew                          -> "DynArrayNew", []
    | VariableDimension                        -> "VarDim", []
    | VariableDimensionStar                    -> "VarDimStar", []
    | GenItemBegin                             -> "GenItemBegin", []
    | GenBlockId id                            -> "GenBlockId", [ident_attr_name,id]
    | GenerateRegion                           -> "GenerateRegion", []
    | Scalared                                 -> "Scalared", []
    | Vectored                                 -> "Vectored", []
    | DelayControl                             -> "DelayControl", []
    | NetSig id                                -> "NetSig", [ident_attr_name,id]
    | ParameterOverride                        -> "ParamOverride", []
    | PortDeclaration                          -> "PortDecl", []
    | PortDirection pd                         -> PortDirection.to_tag pd
    | Strength strength                        -> Strength.to_tag strength
    | StrengthSupply0                          -> "StrengthSupply0", []
    | StrengthSupply1                          -> "StrengthSupply1", []
    | StrengthSpec                             -> "StrengthSpec", []
    | VarDataType                              -> "VarDataType", []
    | Port id                                  -> "Port", [ident_attr_name,id]
    | InterfacePort id                         -> "InterfacePort", [ident_attr_name,id]
    | InterfacePortInterface                   -> "Interface", []
    | ModportIdentifier id                     -> "ModportId", [ident_attr_name,id]
    | PortMulti                                -> "PortMulti", []
    | ExprScope                                -> "ExprScope", []
    | ExprScopeThis                            -> "ExprScopeThis", []
    | ExprScopeSuper                           -> "ExprScopeSuper", []
    | ExprScopeDot                             -> "ExprScopeDot", []
    | ExprScopeDotSuper                        -> "ExprScopeDotSuper", []
    | CondPredicate                            -> "CondPred", []
    | CondPattern                              -> "CondPat", []
    | Dist                                     -> "Dist", []
    | DistItem                                 -> "DistItem", []
    | DistWeight                               -> "DistWeight", []
    | DistWeightRange                          -> "DistWeightRange", []
    | ArrayRange                               -> "ArrayRange", []
    | ArrayRangePlus                           -> "ArrayRangePlus", []
    | ArrayRangeMinus                          -> "ArrayRangeMinus", []
    | CastingTypeSimple                        -> "CastingTypeSimple", []
    | CastingTypeSigned                        -> "CastingTypeSigned", []
    | CastingTypeUnsigned                      -> "CastingTypeUnsigned", []
    | CastingTypeString                        -> "CastingTypeString", []
    | CastingTypeConst                         -> "CastingTypeConst", []
    | ValueRange                               -> "ValueRange", []
    | Pattern                                  -> "Pattern", []
    | PatternId id                             -> "PatternId", [ident_attr_name,id]
    | PatternStar                              -> "PatternStar", []
    | PatternTagged id                         -> "PatternTagged", [ident_attr_name,id]
    | EventControl                             -> "EventControl", []
    | EventControlStar                         -> "EventControlStar", []
    | EventControlParenStar                    -> "EventControlParenStar", []
    | EventControlRepeat                       -> "EventControlRepeat", []
    | EvExpr ee                                -> EventExpression.to_tag ee
    | CaseItem                                 -> "CaseItem", []
    | CaseItemDefault                          -> "CaseItemDefault", []
    | CaseInsideItem                           -> "CaseInsideItem", []
    | CaseInsideItemDefault                    -> "CaseInsideItemDefault", []
    | CaseItems                                -> "CaseItems", []
    | CaseItemsMatches                         -> "CaseItemMatches", []
    | CaseItemsInside                          -> "CaseItemInside", []
    | With                                     -> "With", []
    | Args                                     -> "Args", []
    | ConstraintBlock                          -> "ConstraintBlock", []
    | ForInit                                  -> "ForInit", []
    | ForInitItemDT id                         -> "ForInitItemDt", [ident_attr_name,id]
    | ForInitItemLval                          -> "ForInitItemLval", []
    | StreamingConcat                          -> "StreamingConcat", []
    | OrderRL                                  -> "OrderRL", []
    | OrderLR                                  -> "OrderLR", []
    | StreamConcat                             -> "StreamConcat", []
    | Solve                                    -> "Solve", []
    | SolveBefore                              -> "SolveBefore", []
    | ActionBlock                              -> "ActionBlock", []
    | CycleDelay s                             -> "CycleDelay", ["delay",XML.encode_string s]
    | CycleDelayId id                          -> "CycleDelayId", [ident_attr_name,id]
    | CycleDelayParen                          -> "CycleDelayParen", []
    | Priority                                 -> "Priority", []
    | Unique                                   -> "Unique", []
    | Unique0                                  -> "Unique0", []
    | InstRange                                -> "InstRange", []
    | InstName id                              -> "InstName", [ident_attr_name,id]
    | PExpr pe                                 -> PropertyExpression.to_tag pe
    | ClockingEvent id                         -> "ClockingEvent", [ident_attr_name,id]
    | ClockingEventParen                       -> "ClockingEventParen", []
    | PropertyCase                             -> "PropertyCase", []
    | PropertyCaseDefault                      -> "PropertyCaseDefault", []
    | DisableIff                               -> "DisableIff", []
    | CycleDelayRange s                        -> "CycleDelayRange", ["delay",XML.encode_string s]
    | CycleDelayRangeId id                     -> "CycleDelayRangeId", [ident_attr_name,id]
    | CycleDelayRangeParen                     -> "CycleDelayRangeParen", []
    | CycleDelayRangeBracket                   -> "CycleDelayRangeBracket", []
    | CycleDelayRangeBracketStar               -> "CycleDelayRangeBracketStar", []
    | CycleDelayRangeBracketPlus               -> "CycleDelayRangeBracketPlus", []
    | SExpr se                                 -> SequenceExpression.to_tag se
    | ConsecutiveRepetition                    -> "ConsecutiveRepetition", []
    | NonconsecutiveRepetition                 -> "NonconsecutiveRepetition", []
    | GotoRepetition                           -> "GotoRepetition", []
    | NetAlias                                 -> "NetAlias", []
    | InitialConstruct                         -> "InitialConstruct", []
    | FinalConstruct                           -> "FinalConstruct", []
    | AlwaysConstruct aspec                    -> "AlwaysConstruct", [spec_attr_name,AlwaysSpec.to_rep aspec]
    | ConcurrentAssertionItemLabeled id        -> "ConcurrentAssertionItem", [label_attr_name,id]
    | ConcurrentAssertionStmt ca               -> ConcurrentAssertion.to_tag ca
    | DeferredImmediateAssertionItemLabeled id -> "DeferredImmediateAssertionItem", [label_attr_name,id]
    | DeferredImmediateAssertionStmt dia       -> DeferredImmediateAssertion.to_tag dia
    | SimpleImmediateAssertionStmt sia         -> SimpleImmediateAssertion.to_tag sia
    | CheckerInstantiation id                  -> "CheckerInst", [ident_attr_name,id]
    | LoopGenerateConstruct                    -> "LoopGenerateConstruct", []
    | GenvarDeclaration ids                    -> "GenvarDecl", [ident_attr_name,String.concat ";" ids]
    | GenvarIterationAssign(ao, id)            -> "GenvarIter", ["op",AssignmentOperator.to_tag_name ao;ident_attr_name,id]
    | GenvarIterationIncOrDec(iod, id)         -> "GenvarIter", ["op",IncOrDecOperator.to_tag_name iod;ident_attr_name,id]
    | GenvarIdDecl id                          -> "GenvarIdDecl", [ident_attr_name,id]
    | GenvarInitId id                          -> "GenvarInitId", [ident_attr_name,id]
    | GenvarInit                               -> "GenvarInit", []
    | SpecifyBlock                             -> "SpecifyBlock", []
    | SpecparamDeclaration                     -> "SpecparamDecl", []
    | SpecparamAssignmentId id                 -> "SpecparamAssignmentId", [ident_attr_name,id]
    | SpecparamAssignmentPulseControl id       -> "SpecparamAssignmentPulseControl", [ident_attr_name,id]
    | PulsestyleDeclarationOnevent             -> "PulsestyleDeclOnevent", []
    | PulsestyleDeclarationOndetect            -> "PulsestyleDeclOndetect", []
    | ShowcancelledDeclaration                 -> "Showcancelled", []
    | NoshowcancelledDeclaration               -> "Noshowcancelled", []
    | SpecifyTerminalDescriptor                -> "SpecifyTerminalDtor", []
    | InputOrOutputId id                       -> "InputOrOutputId", [ident_attr_name,id]
    | InterfaceIdentifier id                   -> "InterfaceId", [ident_attr_name,id]
    | ProgramDeclaration id                    -> "ProgramDecl", [ident_attr_name,id]
    | InterfaceDeclaration id                  -> "InterfaceDecl", [ident_attr_name,id]
    | InterfaceDeclarationExtern id            -> "InterfaceDeclExtern", [ident_attr_name,id]
    | TimeUnitsDeclaration                     -> "TimeunitsDecl", []
    | TimeUnit s                               -> "Timeunit", ["unit",XML.encode_string s]
    | Timeprecision s                          -> "Timeprecision", ["precision",XML.encode_string s]
    | PackageDeclaration id                    -> "PackageDecl", [ident_attr_name,id]
    | AnonymousProgram                         -> "AnonymousProg", []
    | AnonymousProgramItemEmpty                -> "AnonymousProgItemEmpty", []
    | FunctionDeclaration id                   -> "FunctionDecl", [ident_attr_name,id]
    | FunctionPrototype id                     -> "FunctionPrototype", [ident_attr_name,id]
    | FuncId id                                -> "FunctionId", [ident_attr_name,id]
    | FuncIdVoid id                            -> "FunctionIdVoid", [ident_attr_name,id]
    | FuncIdNew                                -> "FunctionIdNew", []
    | TfIdScoped id                            -> "TfIdScoped", [ident_attr_name,id]
    | TaskDeclaration id                       -> "TaskDecl", [ident_attr_name,id]
    | TaskPrototype id                         -> "TaskPrototype", [ident_attr_name,id]
    | ClassCtorPrototype                       -> "ClassCtorProto", []
    | TfPortListPart                           -> "TfPortListPart", []
    | TfBody                                   -> "TfBody", []
    | TfPortDeclaration                        -> "TfPortDecl", []
    | TfPortItemAssignment id                  -> "TfPortItemAssign", [ident_attr_name,id]
    | TfPortItem                               -> "TfPortItem", []
    | TfVariableIdentifier id                  -> "TfVarId", [ident_attr_name,id]
    | CheckerDeclaration id                    -> "CheckerDecl", [ident_attr_name,id]
    | PropertyDeclaration id                   -> "PropertyDecl", [ident_attr_name,id]
    | PropertyDeclBody                         -> "PropertyDeclBody", []
    | PropertyPortItem                         -> "PropertyPortItem", []
    | PropertyPortItemDir                      -> "PropertyPortItemDir", []
    | PropertyPortItemAssignment id            -> "PropertyPortItemAssign", [ident_attr_name,id]
    | SequenceDeclaration id                   -> "SequenceDecl", [ident_attr_name,id]
    | SequenceDeclBody                         -> "SequenceDeclBody", []
    | LetDeclaration id                        -> "LetDecl", [ident_attr_name,id]
    | PropertyStatementSpec                    -> "PropertyStmtSpec", []
    | AssertionVariableDeclaration             -> "AssertionVarDecl", []
    | SequenceFormalTypeSequence               -> "SequenceFormalTypeSequence", []
    | SequenceFormalTypeUntyped                -> "SequenceFormalTypeUntyped", []
    | DataDeclarationVar                       -> "DataDeclVar", []
    | Const                                    -> "Const", []
    | DataDeclarationVarClass                  -> "DataDeclVarClass", []
    | TypeDeclaration id                       -> "TypeDecl", [ident_attr_name,id]
    | ScopedType id                            -> "ScopedType", [ident_attr_name,id]
    | TypeIdentifier id                        -> "TypeId", [ident_attr_name,id]
    | TypeDeclEnum                             -> "TypeDeclEnum", []
    | TypeDeclStruct                           -> "TypeDeclStruct", []
    | TypeDeclUnion                            -> "TypeDeclUnion", []
    | TypeDeclClass                            -> "TypeDeclClass", []
    | VirtualInterfaceDeclaration id           -> "VirtualInterfaceDecl", [ident_attr_name,id]
    | ModportDeclaration ids                   -> "ModportDecl", [ident_attr_name,String.concat ";" ids]
    | ModportItem id                           -> "ModportItem", [ident_attr_name,id]
    | ModportSimplePortsDecl                   -> "ModportSimplePortsDecl", []
    | ModportClockingDecl id                   -> "ModportClockingDecl", [ident_attr_name,id]
    | ModportTfPortsDeclImport                 -> "ModportTfPortsDeclImport", []
    | ModportTfPortsDeclExport                 -> "ModportTfPortsDeclExport", []
    | ModportSimplePort id                     -> "ModportSimplePort", [ident_attr_name,id]
    | ModportSimplePortDot id                  -> "ModportSimplePortDot.", [ident_attr_name,id]
    | ModportTfPort id                         -> "ModportTfPort", [ident_attr_name,id]
    | CovergroupDeclaration id                 -> "CovergroupDecl", [ident_attr_name,id]
    | Paren                                    -> "Paren", []
    | CoverageOption(id1, id2)                 -> "CoverageOption", ["inst",id1;"opt",id2]
    | CoverPoint                               -> "Coverpoint", []
    | CoverPointLabeled id                     -> "Coverpoint", [label_attr_name,id]
    | CoverCross                               -> "Covercross", []
    | CoverCrossLabeled id                     -> "Covercross", [label_attr_name,id]
    | CrossItem id                             -> "CrossItem", [ident_attr_name,id]
    | Iff                                      -> "Iff", []
    | BinsList                                 -> "BinsList", []
    | BinsEmpty                                -> "BinsEmpty", []
    | SelectBins                               -> "SelectBins", []
    | SelectBinsEmpty                          -> "SelectBinsEmpty", []
    | Bins(bspec, id)                          -> "Bins", [spec_attr_name,BinsSpec.to_rep bspec;ident_attr_name,id]
    | BinsSelection(bspec, id)                 -> "BinsSelection", [spec_attr_name,BinsSpec.to_rep bspec;ident_attr_name,id]
    | BinsExpressionVar id                     -> "BinsExprVar", [ident_attr_name,id]
    | BinsExpression(id1, id2)                 -> "BinsExpr", ["cover_point",id1;"bins",id2]
    | NBins                                    -> "NBins", []
    | SelCondBinsof                            -> "SelCondBinsof", []
    | SelExprNot                               -> "SelExprNot", []
    | SelExprAnd                               -> "SelExprAnd", []
    | SelExprOr                                -> "SelExprOr", []
    | SelExprParen                             -> "SelExprParen", []
    | Intersect                                -> "Intersect", []
    | Wildcard                                 -> "Wildcard", []
    | TransSet                                 -> "TransSet", []
    | TransRangeList                           -> "TransRangeList", []
    | RepeatRange                              -> "RepeatRange", []
    | TransItem                                -> "TransItem", []
    | TransRepetitionConsecutive               -> "TransRepetitionConsecutive", []
    | TransRepetitionNonconsecutive            -> "TransRepetitionNonconsecutive", []
    | TransRepetitionGoto                      -> "TransRepetitionGoto", []
    | Default                                  -> "Default", []
    | DefaultSequence                          -> "DefaultSequence", []
    | OpenRangeList                            -> "OpenRangeList", []
    | CoverageEventWith id                     -> "CoverageEventWith", [ident_attr_name,id]
    | CoverageEventBlockEvent                  -> "CoverageEventBlockEvent", []
    | BlockEventExpression                     -> "BlockEventExpr", []
    | BlockEventExpressionBegin                -> "BlockEventExprBegin", []
    | BlockEventExpressionEnd                  -> "BlockEventExprEnd", []
    | HierarchicalBtfIdentifier id             -> "HierarchicalBtfId", [ident_attr_name,id]
    | PackageExportDeclarationStar             -> "PackageExportDeclStar", []
    | PackageExportDeclaration                 -> "PackageExportDecl", []
    | DpiImport s                              -> "DpiImport", ["dpi_spec",XML.encode_string s]
    | DpiExportFunc(s, id)                     -> "DpiExportFunc", ["dpi_spec",XML.encode_string s;ident_attr_name,id]
    | DpiExportTask(s, id)                     -> "DpiExportTask", ["dpi_spec",XML.encode_string s;ident_attr_name,id]
    | DpiImportLabel id                        -> "DpiImportLabel", [label_attr_name,id]
    | DpiTfImportPropertyContext               -> "DpiTfImportPropertyContext", []
    | DpiTfImportPropertyPure                  -> "DpiTfImportPropertyPure", []
    | ExternConstraintDeclaration              -> "ExternConstraintDecl", []
    | Static                                   -> "Static", []
    | Virtual                                  -> "Virtual", []
    | ClassDeclaration id                      -> "ClassDecl", [ident_attr_name,id]
    | ClassExtends                             -> "ClassExtends", []
    | ClassItemEmpty                           -> "ClassItemEmpty", []
    | ClassMethod                              -> "ClassMethod", []
    | Qualifier q                              -> Qualifier.to_tag q
    | ClassBody                                -> "ClassBody", []
    | ClassConstraint id                       -> "ClassConstraint", [ident_attr_name,id]
    | Pure                                     -> "Pure", []
    | ClassProperty                            -> "ClassProperty", []
    | PackageOrGenerateItemEmpty               -> "PackageOrGenerateItemEmpty", []
    | Forkjoin                                 -> "Forkjoin", []
    | ExternTfDeclaration id                   -> "ExternTfDecl", [ident_attr_name,id]
    | TimingCheck tc                           -> TimingCheck.to_tag tc
    | SystemTimingCheck                        -> "SystemTimingCheck", []
    | Notifier id                              -> "Notifier", [ident_attr_name,id]
    | Delayed id                               -> "Delayed", [ident_attr_name,id]
    | TimingCheckEvent                         -> "TimingCheckEvent", []
    | TimingCheckEventControlPosedge           -> "TimingCheckEventControlPosedge", []
    | TimingCheckEventControlNegedge           -> "TimingCheckEventControlNegedge", []
    | TimingCheckEventControl                  -> "TimingCheckEventControl", []
    | EdgeDescriptor s                         -> "EdgeDesc", ["desc",s]
    | OverloadDeclaration(oo, id)              -> "OverloadDecl", ["op",OverloadOperator.to_tag_name oo;ident_attr_name,id]
    | Params                                   -> "Params", []
    | ClockingDeclaration id                   -> "ClockingDecl", [ident_attr_name,id]
    | Global                                   -> "Global", []
    | ClockingBody                             -> "Clockingbody", []
    | ClockingItemDefault                      -> "ClockingItemDefault", []
    | ClockingItem                             -> "ClockingItem", []
    | DefaultSkewInput                         -> "defaultSkewInput", []
    | DefaultSkewOutput                        -> "defaultSkewOutput", []
    | DefaultSkewInputOutput                   -> "defaultSkewInputOutput", []
    | ClockingDirectionInput                   -> "ClockingDirInput", []
    | ClockingDirectionInputOutput             -> "ClockingDirInputOutput", []
    | ClockingDirectionInout                   -> "ClockingDirInout", []
    | ClockingSkewPosedge                      -> "ClockingSkewPosedge", []
    | ClockingSkewNegedge                      -> "ClockingSkewNegedge", []
    | ClockingSkewEdge                         -> "ClockingSkewEdge", []
    | ClockingSkew                             -> "ClockingSkew", []
    | ClockingDeclAssign id                    -> "ClockingDeclAssign", [ident_attr_name,id]
    | Production id                            -> "Production", [ident_attr_name,id]
    | ProductionItem id                        -> "ProductionItem", [ident_attr_name,id]
    | RsCodeBlock                              -> "RsCode_block", []
    | RsRule                                   -> "RsRule", []
    | RsProductionList                         -> "RsProductionList", []
    | RsProductionListRandJoin                 -> "RsProductionListRandJoin", []
    | WeightSpecInt s                          -> "WeightSpecInt", [value_attr_name,XML.encode_string s]
    | WeightSpecId                             -> "WeightSpecId", []
    | WeightSpec                               -> "WeightSpec", []
    | RsProdIf                                 -> "RsProdIf", []
    | RsProdRepeat                             -> "RsProdRepeat", []
    | RsProdCase                               -> "RsProdCase", []
    | RsCaseItem                               -> "RsCaseItem", []
    | RsCaseItemDefault                        -> "RsCaseItemDefault", []
    | CheckerOrGenerateItemEmpty               -> "CheckerOrGenerateItemEmpty", []
    | ConditionalGenerateConstructCase         -> "ConditionalGenerateConstructCase", []
    | ConditionalGenerateConstructIf           -> "ConditionalGenerateConstructIf", []
    | ElaborationSystemTask st                 -> "ElaborationSystemTask", ["task",SystemTask.to_simple_string st]
    | CaseGenerateItem                         -> "CaseGenerateItem", []
    | CaseGenerateItemDefault                  -> "CaseGenerateItemDefault", []
    | AssignmentPattern                        -> "AssignmentPattern", []
    | AssignmentPatternExpr                    -> "AssignmentPatternExpr", []
    | PatternKey                               -> "PatternKey", []
    | PatternKeyDefault                        -> "PatternKeyDefault", []
    | PatternMember                            -> "PatternMember", []
    | SimplePathDeclaration                    -> "SimplePathDecl", []
    | ParallelPathDescription                  -> "ParallelPathDesc", []
    | FullPathDescription                      -> "FullPathDesc", []
    | PathInputs                               -> "PathInputs", []
    | PathOutputs                              -> "PathOutputs", []
    | PathDelayValue                           -> "PathDelayValue", []
    | PolarityPlus                             -> "PolarityPlus", []
    | PolarityMinus                            -> "PolarityMinus", []
    | EdgePosedge                              -> "Posedge", []
    | EdgeNegedge                              -> "Negedge", []
    | EdgeSensitivePathDeclaration             -> "EdgeSensitivePathDecl", []
    | ParallelEdgeSensitivePathDescription     -> "ParallelEdgeSensitivePathDesc", []
    | FullEdgeSensitivePathDescription         -> "FullEdgeSensitivePathDesc", []
    | ParallelEdgeSensitivePathDescriptionSub  -> "ParallelEdgeSensitivePathDesc_sub", []
    | FullEdgeSensitivePathDescriptionSub      -> "FullEdgeSensitivePathDesc_sub", []
    | StateDependentPathDeclarationIf          -> "StateDependentPathDeclIf", []
    | StateDependentPathDeclarationIfnone      -> "StateDependentPathDeclIfnone", []
    | VariableLvalue                           -> "VariableLvalue", []
    | AttributeInstance                        -> "AttributeInstance", []
    | AttrSpec id                              -> "AttrSpec", [ident_attr_name,id]
    | UdpPort id                               -> "UdpPort", [ident_attr_name,id]
    | UdpPortDeclaration                       -> "UdpPortDecl", []
    | UdpOutputDeclaration id                  -> "UdpOutputDecl", [ident_attr_name,id]
    | UdpOutputDeclarationReg id               -> "UdpOutputDeclReg ", [ident_attr_name,id]
    | UdpInputDeclaration                      -> "UdpInputDecl", []
    | UdpRegDeclaration id                     -> "UdpRegDecl", [ident_attr_name,id]
    | SequentialBody                           -> "SequentialBody", []
    | CombinationalBody                        -> "CombinationalBody", []
    | UdpInitialStmt(id, s)                    -> "UdpInitialStmt", ["output_port",id;value_attr_name,XML.encode_string s]
    | SequentialEntry                          -> "SequentialEntry", []
    | EdgeIndicator                            -> "EdgeIndicator", []
    | EdgeSymbol s                             -> "EdgeSymbol", ["symbol",XML.encode_string s]
    | LevelSymbol s                            -> "LevelSymbol", ["symbol",XML.encode_string s]
    | OutputSymbol s                           -> "OutputSymbol", ["symbol",XML.encode_string s]
    | CombinationalEntry                       -> "CombinationalEntry", []
    | NextStateMinus                           -> "NextStateMinus", []
    | UdpPortsStar                             -> "UdpPortsStar", []
    | UdpPorts                                 -> "UdpPorts", []
    | UdpPortDecls                             -> "UdpPortDecls", []
    | UdpDeclarationPorts                      -> "UdpDeclPorts", []
    | AttributeInstances                       -> "AttributeInstances", []
    | ConfigDeclaration id                     -> "ConfigDecl", [ident_attr_name,id]
    | DesignStatement                          -> "DesignStmt", []
    | CellId id                                -> "CellId", [ident_attr_name,id]
    | LibraryIdentifier id                     -> "LibraryId", [ident_attr_name,id]
    | LiblistClause                            -> "LiblistClause", []
    | CellClause id                            -> "CellClause", [ident_attr_name,id]
    | UseClause                                -> "UseClause", []
    | ColonConfig                              -> "ColonConfig", []
    | InstanceName                             -> "InstanceName", []
    | InstanceIdentifier id                    -> "InstanceId", [ident_attr_name,id]
    | TopModuleIdentifier id                   -> "TopModuleId", [ident_attr_name,id]
    | InstClause                               -> "InstClause", []
    | ConfigRuleStatementDefault               -> "ConfigRuleStmtDefault", []
    | ConfigRuleStatement                      -> "ConfigRuleStmt", []
    | LibraryDeclaration id                    -> "LibraryDecl", [ident_attr_name,id]
    | Incdir                                   -> "Incdir", []
    | FilePathSpec s                           -> "FilePathSpec", [path_attr_name,strlit_to_encoded_path s]
    | IncludeStatement s                       -> "IncludeStmt", [path_attr_name,strlit_to_encoded_path s]
    | PragmaExpression id                      -> "PragmaExpr", [ident_attr_name,id]
    | PragmaValueTuple                         -> "PragmaValueTuple", []
    | PragmaValueNum s                         -> "PragmaValueNumber", [value_attr_name,XML.encode_string s]
    | PragmaValueStr s                         -> "PragmaValueString", [value_attr_name,XML.encode_string s]
    | PragmaValueId id                         -> "PragmaValueId", [ident_attr_name,id]
    | PackageImportDecls                       -> "PackageImportDecls", []
    | ParamPorts                               -> "ParamPorts", []
    | Ranges                                   -> "Ranges", []
    | VariableDimensions                       -> "VariableDimensions", []
    | CaseConds                                -> "CaseConds", []
    | NetDeclAssignments ids                   -> "NetDeclAssignments", [ident_attr_name,String.concat ";" ids]
    | ParamAssignments ids                     -> "ParamAssignments", [ident_attr_name,String.concat ";" ids]
    | MacroExpr s                              -> "MacroExpr", [ident_attr_name,s]
    | MacroStmt s                              -> "MacroStmt", [ident_attr_name,s]
    | Var                                      -> "Var", []
  in
  name, attrs



let get_identifiers = function
  | NetDeclaration ids
  | ModportDeclaration ids
  | GenvarDeclaration ids
  | NetDeclAssignments ids
  | ParamAssignments ids
  | LocalParameterDeclaration ids
  | ParameterDeclaration ids
    -> ids
  | _ -> raise Not_found

[%%capture_path
let get_identifier lab =
  [%debug_log "\"%s\"" (to_string lab)];
  match lab with
  | Expr e -> Expression.get_identifier e
  | Stmt s -> Statement.get_identifier s
  | DataType dt -> DataType.get_identifier dt
  | EvExpr ee -> EventExpression.get_identifier ee
  | PExpr pe -> PropertyExpression.get_identifier pe
  | SExpr se -> SequenceExpression.get_identifier se

  | ModuleDeclaration(_, id)
  | UdpDeclaration id
  | BindDirective id
  | Instantiation id
  | PpIdentifier id
  | ParamAssignment id
  | IdSelect id
  | Cellpin id
  | DelayValue id
  | PackageScope id
  | PackageImport id
  | EndLabel id
  | ClassType id
  | ArgsDotted id
  | ClassScopeId id
  | EnumNameDeclaration id
  | Variable id
  | PackageImportItem id
  | VariableDeclAssignment id
  | GenBlockId id
  | NetSig id
  | Port id
  | InterfacePort id
  | ModportIdentifier id
  | PatternId id
  | PatternTagged id
  | ForInitItemDT id
  | CycleDelayId id
  | InstName id
  | ClockingEvent id
  | CycleDelayRangeId id
  | ConcurrentAssertionItemLabeled id
  | DeferredImmediateAssertionItemLabeled id
  | CheckerInstantiation id
  | GenvarIterationAssign(_, id)
  | GenvarIterationIncOrDec(_, id)
  | GenvarIdDecl id
  | GenvarInitId id
  | SpecparamAssignmentId id
  | SpecparamAssignmentPulseControl id
  | InputOrOutputId id
  | InterfaceIdentifier id
  | ProgramDeclaration id
  | InterfaceDeclaration id
  | InterfaceDeclarationExtern id
  | PackageDeclaration id
  | FunctionDeclaration id
  | FunctionPrototype id
  | FuncId id
  | FuncIdVoid id
  | TfIdScoped id
  | TaskDeclaration id
  | TaskPrototype id
  | TfPortItemAssignment id
  | TfVariableIdentifier id
  | CheckerDeclaration id
  | PropertyDeclaration id
  | PropertyPortItemAssignment id
  | SequenceDeclaration id
  | LetDeclaration id
  | TypeDeclaration id
  | ScopedType id
  | TypeIdentifier id
  | VirtualInterfaceDeclaration id
  | ModportItem id
  | ModportClockingDecl id
  | ModportSimplePort id
  | ModportSimplePortDot id
  | ModportTfPort id
  | CovergroupDeclaration id
  | CoverageOption(_,  id)
  | CoverPointLabeled id
  | CoverCrossLabeled id
  | CrossItem id
  | Bins(_, id)
  | BinsSelection(_, id)
  | BinsExpressionVar id
  | BinsExpression(_, id)
  | CoverageEventWith id
  | HierarchicalBtfIdentifier id
  | DpiExportFunc(_, id)
  | DpiExportTask(_, id)
  | ClassDeclaration id
  | ClassConstraint id
  | ExternTfDeclaration id
  | Notifier id
  | Delayed id
  | OverloadDeclaration(_, id)
  | ClockingDeclaration id
  | ClockingDeclAssign id
  | Production id
  | ProductionItem id
  | AttrSpec id
  | UdpPort id
  | UdpOutputDeclaration id
  | UdpOutputDeclarationReg id
  | UdpRegDeclaration id
  | UdpInitialStmt(id, _)
  | ConfigDeclaration id
  | CellId id
  | LibraryIdentifier id
  | CellClause id
  | InstanceIdentifier id
  | TopModuleIdentifier id
  | LibraryDeclaration id
    -> id

  | FuncIdNew -> "new"

  | _ -> raise Not_found
]


let pexpr_to_stmt = function
  | PExpr PropertyExpression.Case -> Stmt Statement.Case
  | PExpr PropertyExpression.If   -> Stmt Statement.Conditional
  | PExpr x                       -> Stmt (Statement.PExpr x)
  | x -> raise (Invalid_argument ("Ast.Label.pexpr_to_stmt: "^(to_string x)))

let expr_to_stmt = function
  | Expr x -> Stmt (Statement.Expr x)
  | _ -> raise (Invalid_argument "Ast.Label.expr_to_stmt")



let expr_of_integral_number i = Expr (Expression.IntegralNumber i)

let expr e = Expr e
let expr_uo uo = Expr (Expression.UOp uo)
let expr_bo bo = Expr (Expression.BOp bo)
let expr_ao ao = Expr (Expression.OperatorAssignment ao)

let pexpr pe = PExpr pe

let sexpr se = SExpr se

let ev_expr ee = EvExpr ee

let stmt s = Stmt s
let stmt_ao ao = Stmt (Statement.OperatorAssignment ao)

let sia_stmt ss = SimpleImmediateAssertionStmt ss
let dia_stmt ds = DeferredImmediateAssertionStmt ds
let ca_stmt cs  = ConcurrentAssertionStmt cs

let qualifier q = Qualifier q

let timing_check tc = TimingCheck tc

let data_type dt = DataType dt

let net_type nt = NetType nt

let compiler_directive cd = CompilerDirective cd

let is_error = function
  | Error -> true
  | _ -> false
