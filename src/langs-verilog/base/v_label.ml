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
(* verilog/label.ml *)

module Loc = Diffast_misc.Loc
module Astml = Diffast_core.Astml
module Lang_base = Diffast_core.Lang_base
module Spec = Diffast_core.Spec
module Charpool = Diffast_core.Charpool
module Ast = Verilog_parsing.Ast
module Labels = Verilog_parsing.Labels
module Label = Verilog_parsing.Label



module Ls = Labels

type identifier = string

let lang_prefix = Astml.verilog_prefix

(*let ident_attr_name = "ident"
let label_attr_name = "label"
let value_attr_name = "value"
let path_attr_name  = "path"
let spec_attr_name  = "spec"*)

let keyroot_depth_min = 2

type tie_id = Lang_base.tie_id

let null_tid      = Lang_base.null_tid
let mktid         = Lang_base.mktid
let tid_to_string = Lang_base.tid_to_string
let anonymize_tid = Lang_base.anonymize_tid
let mktidattr     = Lang_base.mktidattr


(*let strlit_to_encoded_path s =
  XML.encode_string (Astml.str_lit_to_path s)*)




module type T = sig
  include Spec.LABEL_T

  val lang_prefix              : string

  val is_always_construct    : t -> bool
  val is_timing_control      : t -> bool
  val is_continuous_assign   : t -> bool
  val is_blocking_assign     : t -> bool
  val is_non_blocking_assign : t -> bool
  val is_if                  : t -> bool
  val is_case                : t -> bool
  val is_case_item           : t -> bool
  val is_case_cond           : t -> bool
  val is_module_decl         : t -> bool
  val is_ports               : t -> bool
  val is_port                : t -> bool
  val is_port_dir            : t -> bool
  val is_net_type            : t -> bool
  val is_data_type           : t -> bool
  val is_var_data_type       : t -> bool
  val is_signing             : t -> bool
  val is_ranges              : t -> bool
  val is_variable_dims       : t -> bool
  val is_inst                : t -> bool
  val is_initial_construct   : t -> bool
  val is_final_construct     : t -> bool
  val is_generate_region     : t -> bool
  val is_param_port_decl     : t -> bool
  val is_param_assign        : t -> bool
  val is_data_decl_var       : t -> bool
  val is_net_decl            : t -> bool
  val is_reg                 : t -> bool
  val is_wire                : t -> bool
  val is_expr                : t -> bool
  val is_stmt                : t -> bool

  val is_pp_define           : t -> bool
  val is_pp_include          : t -> bool

  val is_source_text         : t -> bool

  val getlab                 : Spec.node_t -> t

end




let conv_loc
    { Ast.Loc.start_offset = so;
      Ast.Loc.end_offset   = eo;
      Ast.Loc.start_line   = sl;
      Ast.Loc.start_char   = sc;
      Ast.Loc.end_line     = el;
      Ast.Loc.end_char     = ec;
      _
    } =
  Loc.make so eo sl sc el ec

open Charpool


module OverloadOperator = struct
  include Ls.OverloadOperator

  let to_short_string = function
    | Add    -> mkstr 0
    | Incr   -> mkstr 1
    | Subt   -> mkstr 2
    | Decr   -> mkstr 3
    | Mult   -> mkstr 4
    | Pow    -> mkstr 5
    | Div    -> mkstr 6
    | Mod    -> mkstr 7
    | Eq     -> mkstr 8
    | Neq    -> mkstr 9
    | Lt     -> mkstr 10
    | Le     -> mkstr 11
    | Gt     -> mkstr 12
    | Ge     -> mkstr 13
    | Assign -> mkstr 14

end (* of module OverloadOperator *)


module AssignmentOperator = struct
  include Ls.AssignmentOperator

  let to_short_string = function
    | Eq        -> mkstr 0
    | AddEq     -> mkstr 1
    | SubtEq    -> mkstr 2
    | MultEq    -> mkstr 3
    | DivEq     -> mkstr 4
    | ModEq     -> mkstr 5
    | AndEq     -> mkstr 6
    | OrEq      -> mkstr 7
    | XorEq     -> mkstr 8
    | ShiftLEq  -> mkstr 9
    | ShiftREq  -> mkstr 10
    | SShiftREq -> mkstr 11

end (* of module AssignmentOperator *)

module IncOrDecOperator = struct
  include Ls.IncOrDecOperator

  let to_short_string = function
    | PreIncr  -> mkstr 0
    | PreDecr  -> mkstr 1
    | PostIncr -> mkstr 2
    | PostDecr -> mkstr 3

end (* of module IncOrDecOperator *)

module UnaryOperator = struct
  include Ls.UnaryOperator

  let to_short_string = function
    | Plus  -> mkstr 0
    | Minus -> mkstr 1
    | Not   -> mkstr 2
    | And   -> mkstr 3
    | Neg   -> mkstr 4
    | Or    -> mkstr 5
    | Xor   -> mkstr 6
    | Nand  -> mkstr 7
    | Nor   -> mkstr 8
    | Xnor  -> mkstr 9
    | Inc   -> mkstr 10
    | Dec   -> mkstr 11

end (* of module UnaryOperator *)

module BinaryOperator = struct
  include Ls.BinaryOperator

  let to_short_string = function
    | Add        -> mkstr 0
    | Subt       -> mkstr 1
    | Mult       -> mkstr 2
    | Div        -> mkstr 3
    | Mod        -> mkstr 4
    | Eq         -> mkstr 5
    | Neq        -> mkstr 6
    | CaseEq     -> mkstr 7
    | CaseNeq    -> mkstr 8
    | WildEq     -> mkstr 9
    | WildNeq    -> mkstr 10
    | LogAnd     -> mkstr 11
    | LogOr      -> mkstr 12
    | Pow        -> mkstr 13
    | Lt         -> mkstr 14
    | Le         -> mkstr 15
    | Gt         -> mkstr 16
    | Ge         -> mkstr 17
    | And        -> mkstr 18
    | Or         -> mkstr 19
    | Xor        -> mkstr 20
    | Xnor       -> mkstr 21
    | Nor        -> mkstr 22
    | Nand       -> mkstr 23
    | ShiftL     -> mkstr 24
    | ShiftR     -> mkstr 25
    | SShiftR    -> mkstr 26
    | Constraint -> mkstr 27
    | LtMinusGt  -> mkstr 28

end (* of module BinaryOperator *)

module TimingCheck = struct
  include Ls.TimingCheck

  let anonymize = function
    | Setup
    | Hold
    | Recovery
    | Removal
    | Skew
    | Setuphold
    | Recrem
    | Timeskew
    | Fullskew
    | Period
    | Width
    | Nochange  -> Anonymous
    | x         -> x

  let to_short_string = function
    | Setup     -> mkstr 0
    | Hold      -> mkstr 1
    | Recovery  -> mkstr 2
    | Removal   -> mkstr 3
    | Skew      -> mkstr 4
    | Setuphold -> mkstr 5
    | Recrem    -> mkstr 6
    | Timeskew  -> mkstr 7
    | Fullskew  -> mkstr 8
    | Period    -> mkstr 9
    | Width     -> mkstr 10
    | Nochange  -> mkstr 11

    | Anonymous -> mkstr 12

end (* of module TimingCheck *)

module SystemTask = struct
  include Ls.SystemTask

  let anonymize = function
    | Error
    | Fatal
    | Info
    | Root
    | Unit
    | Warning -> Anonymous
    | x -> x

  let to_short_string = function
    | Error   -> mkstr 0
    | Fatal   -> mkstr 1
    | Info    -> mkstr 2
    | Root    -> mkstr 3
    | Unit    -> mkstr 4
    | Warning -> mkstr 5
    | Anonymous -> mkstr 6

end (* of module SystemTask *)

module Qualifier = struct
  include Ls.Qualifier

  let to_short_string = function
    | Protected   -> mkstr 0
    | Local       -> mkstr 1
    | Static      -> mkstr 2
    | Virtual     -> mkstr 3
    | PureVirtual -> mkstr 4
    | Rand        -> mkstr 5
    | Randc       -> mkstr 6
    | Automatic   -> mkstr 7

end (* of module Qualifier *)

module NetType = struct
  include Ls.NetType

  let anonymize = function
      | Supply0
      | Supply1
      | Tri
      | Tri0
      | Tri1
      | Triand
      | Trior
      | Trireg
      | Wand
      | Wire
      | Uwire
      | Wor     -> Anonymous
      | x       -> x

  let to_short_string = function
    | Supply0 -> mkstr 1
    | Supply1 -> mkstr 2
    | Tri     -> mkstr 3
    | Tri0    -> mkstr 4
    | Tri1    -> mkstr 5
    | Triand  -> mkstr 6
    | Trior   -> mkstr 7
    | Trireg  -> mkstr 8
    | Wand    -> mkstr 9
    | Wire    -> mkstr 10
    | Uwire   -> mkstr 11
    | Wor     -> mkstr 12

    | Anonymous -> mkstr 13

end (* of module NetType *)

module PortDirection = struct
  include Ls.PortDirection

  let anonymize = function
    | Input
    | Output
    | Inout
    | Ref
    | ConstRef -> Anonymous
    | x        -> x

  let to_short_string = function
    | Input    -> mkstr 0
    | Output   -> mkstr 1
    | Inout    -> mkstr 2
    | Ref      -> mkstr 3
    | ConstRef -> mkstr 4

    | Anonymous -> mkstr 5

end (* of module PortDirection *)

module Gate = struct
  include Ls.Gate

  let anonymize = function
    | Gate _
    | And
    | Buf
    | Nand
    | Nor
    | Not
    | Or
    | Xnor
    | Xor  -> Anonymous
    | x    -> x

  let gate_to_short_string = function
    | Ls.BUFIF0       -> mkstr 0
    | Ls.BUFIF1       -> mkstr 1
    | Ls.CMOS         -> mkstr 2
    | Ls.NMOS         -> mkstr 3
    | Ls.PMOS         -> mkstr 4
    | Ls.NOTIF0       -> mkstr 5
    | Ls.NOTIF1       -> mkstr 6
    | Ls.RCMOS        -> mkstr 7
    | Ls.RNMOS        -> mkstr 8
    | Ls.RPMOS        -> mkstr 9
    | Ls.PULLDOWN     -> mkstr 10
    | Ls.PULLUP       -> mkstr 11
    | Ls.RTRAN        -> mkstr 12
    | Ls.RTRANIF0     -> mkstr 13
    | Ls.RTRANIF1     -> mkstr 14
    | Ls.TRAN         -> mkstr 15
    | Ls.TRANIF0      -> mkstr 16
    | Ls.TRANIF1      -> mkstr 17

  let to_short_string = function
    | Gate g -> catstr [mkstr 0; gate_to_short_string g]
    | And  -> mkstr 1
    | Buf  -> mkstr 2
    | Nand -> mkstr 3
    | Nor  -> mkstr 4
    | Not  -> mkstr 5
    | Or   -> mkstr 6
    | Xnor -> mkstr 7
    | Xor  -> mkstr 8

    | Anonymous -> mkstr 9

end (* of module Gate *)

module DataType = struct
  include Ls.DataType

  let anonymize = function
    | PsType _           -> PsType ""
    | VirtualInterface _ -> VirtualInterface ""
    | PsCovergroup _     -> PsCovergroup ""
    | ClassScopeType _   -> ClassScopeType ""
    | Named _            -> Named ""
    | dt                 -> dt

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Byte                -> mkstr 0
    | Shortint            -> mkstr 1
    | Int                 -> mkstr 2
    | Longint             -> mkstr 3
    | Integer             -> mkstr 4
    | Time                -> mkstr 5
    | Bit                 -> mkstr 6
    | Logic               -> mkstr 7
    | Reg                 -> mkstr 8
    | Shortreal           -> mkstr 9
    | Real                -> mkstr 10
    | Realtime            -> mkstr 11
    | Struct              -> mkstr 12
    | Union               -> mkstr 13
    | Enum                -> mkstr 14
    | PsType id           -> combo 15 [id]
    | String              -> mkstr 16
    | Chandle             -> mkstr 17
    | Event               -> mkstr 18
    | VirtualInterface id -> combo 19 [id]
    | TypeReference       -> mkstr 20
    | PsCovergroup id     -> combo 21 [id]
    | ClassScopeType id   -> combo 22 [id]
    | ClassType           -> mkstr 23
    | Named id            -> combo 24 [id]
    | Implicit            -> mkstr 25

end (* of module DataType *)

module Expression = struct
  include Ls.Expression

  let anonymize = function
    | IntegralNumber _ -> IntegralNumber ""
    | RealNumber _     -> RealNumber ""
    | TimeNumber _     -> TimeNumber ""
    | Tagged _         -> Tagged ""
    | SystemFCall _    -> SystemFCall ""
    | SystemTCall st   -> SystemTCall (SystemTask.anonymize st)
    | TfCall _         -> TfCall ""
    | MethodCall _     -> MethodCall ""
    | e                -> e

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | IntegralNumber s      -> mkstr_str 0 s
    | RealNumber s          -> mkstr_str 2 s
    | TimeNumber s          -> mkstr_str 4 s
    | Null                  -> mkstr 5
    | UOp uo                -> catstr [mkstr 6; UnaryOperator.to_short_string uo]
    | BOp bo                -> catstr [mkstr 7; BinaryOperator.to_short_string bo]
    | Cond                  -> mkstr 8
    | Paren                 -> mkstr 9
    | Tagged id             -> combo 10 [id]
    | Inside                -> mkstr 11
    | Concat                -> mkstr 12
    | EmptyQueue            -> mkstr 13
    | Last                  -> mkstr 14
    | MinTypeMax            -> mkstr 15
    | Cast                  -> mkstr 16
    | Constraint            -> mkstr 17
    | ConstraintIf          -> mkstr 18
    | ConstraintForeach     -> mkstr 19
    | ConstraintSet         -> mkstr 20
    | Stream                -> mkstr 21
    | PreIncr               -> mkstr 22
    | PreDecr               -> mkstr 23
    | OperatorAssignment ao -> catstr [mkstr 24; AssignmentOperator.to_short_string ao]
    | SystemFCall id        -> combo 25 [id]
    | SystemTCall st        -> catstr [mkstr 26; SystemTask.to_short_string st]
    | TfCall id             -> combo 27 [id]
    | MethodCall id         -> combo 28 [id]
    | ArrayMethodCallUnique -> mkstr 29
    | ArrayMethodCallAnd    -> mkstr 30
    | ArrayMethodCallOr     -> mkstr 31
    | ArrayMethodCallXor    -> mkstr 32
    | CycleDelayConstRange  -> mkstr 33
    | ConstantRange         -> mkstr 34
    | ClassNew              -> mkstr 35
    | ClassNewA             -> mkstr 36
    | PostIncr              -> mkstr 37
    | PostDecr              -> mkstr 38

end (* of module Expression *)

module EventExpression = struct
  include Ls.EventExpression

  let to_short_string = function
    | Posedge -> mkstr 0
    | Negedge -> mkstr 1
    | Edge    -> mkstr 2
    | Iff     -> mkstr 3
    | Or      -> mkstr 4
    | Multi   -> mkstr 5

end (* of module EventExpression *)

module PropertyExpression = struct
  include Ls.PropertyExpression

  let to_short_string = function
    | Not                      -> mkstr 0
    | Strong                   -> mkstr 1
    | Weak                     -> mkstr 2
    | ImplicationOverlapped    -> mkstr 3
    | ImplicationNonOverlapped -> mkstr 4
    | SharpMinusSharp          -> mkstr 5
    | SharpEqSharp             -> mkstr 6
    | Nexttime                 -> mkstr 7
    | S_nexttime               -> mkstr 8
    | Always                   -> mkstr 9
    | S_always                 -> mkstr 10
    | Eventually               -> mkstr 11
    | S_eventually             -> mkstr 12
    | Until                    -> mkstr 13
    | S_until                  -> mkstr 14
    | Until_with               -> mkstr 15
    | S_until_with             -> mkstr 16
    | Implies                  -> mkstr 17
    | Iff                      -> mkstr 18
    | Accept_on                -> mkstr 19
    | Sync_accept_on           -> mkstr 20
    | Reject_on                -> mkstr 21
    | Sync_reject_on           -> mkstr 22
    | If                       -> mkstr 23
    | Case                     -> mkstr 24
    | Spec                     -> mkstr 25

end (* of module PropertyExpression *)

module SequenceExpression = struct
  include Ls.SequenceExpression

  let to_short_string = function
    | Concat     -> mkstr 0
    | Repetition -> mkstr 1
    | OnMatch    -> mkstr 2
    | And        -> mkstr 3
    | Or         -> mkstr 4
    | Intersect  -> mkstr 5
    | First_match -> mkstr 6
    | Throughout -> mkstr 7
    | Within     -> mkstr 8
    | Clocking   -> mkstr 9

end (* of module SequenceExpression *)

module JoinSpec = struct
  include Ls.JoinSpec

  let to_short_string = function
    | NORMAL -> mkstr 0
    | ANY    -> mkstr 1
    | NONE   -> mkstr 2
;
end

module Statement = struct
  include Ls.Statement

  let anonymize = function
    | Labeled _       -> Labeled ""
    | ParBlock(_, js) -> ParBlock("", js)
    | SeqBlock _      -> SeqBlock ""
    | Randsequence _  -> Randsequence ""
    | Expr e          -> Expr (Expression.anonymize e)
    | stmt            -> stmt

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Empty                   -> mkstr 0
    | OperatorAssignment ao   -> catstr [mkstr 1; AssignmentOperator.to_string ao]
    | Labeled id              -> combo 3 [id]
    | BlockingAssignment      -> mkstr 4
    | NonBlockingAssignment   -> mkstr 5
    | Assign                  -> mkstr 6
    | Deassign                -> mkstr 7
    | Force                   -> mkstr 8
    | Release                 -> mkstr 9
    | Case                    -> mkstr 10
    | Casex                   -> mkstr 11
    | Casez                   -> mkstr 12
    | Conditional             -> mkstr 13
    | IncOrDec                -> mkstr 14
    | SubroutineCall          -> mkstr 15
    | SubroutineCallVoid      -> mkstr 16
    | Disable                 -> mkstr 17
    | DisableFork             -> mkstr 18
    | EventTrigger            -> mkstr 19
    | EventTriggerNonBlocking -> mkstr 20
    | Forever                 -> mkstr 21
    | Repeat                  -> mkstr 22
    | While                   -> mkstr 23
    | For                     -> mkstr 24
    | Do                      -> mkstr 25
    | Foreach                 -> mkstr 26
    | Return                  -> mkstr 27
    | Break                   -> mkstr 28
    | Continue                -> mkstr 29
    | ParBlock(id, js)        -> catstr [mkstr 30; id; JoinSpec.to_short_string js]
    | ProceduralTimingControl -> mkstr 31
    | SeqBlock id             -> combo 32 [id]
    | Wait                    -> mkstr 33
    | WaitFork                -> mkstr 34
    | WaitOrder               -> mkstr 35
    | ProceduralAssertion     -> mkstr 36
    | ClockingDrive           -> mkstr 37
    | Randsequence id         -> combo 38 [id]
    | Randcase                -> mkstr 39
    | ExpectProperty          -> mkstr 40
    | Expr e                  -> catstr [mkstr 41; Expression.to_short_string e]
    | PExpr pe                -> catstr [mkstr 42; PropertyExpression.to_short_string pe]

end (* of module Statement *)

module CompilerDirective = struct
  include Ls.CompilerDirective

  let anonymize = function
    | Define _                  -> Define ""
    | Undef _                   -> Undef ""
    | Include _                 -> Include ""
    | SysInclude _              -> SysInclude ""
    | Timescale(_, _)           -> Timescale("", "")
    | Error _                   -> Error ""
    | Line(_, _, _)             -> Line("", "", "")
    | Pragma _                  -> Pragma ""
    | Begin_keywords _          -> Begin_keywords ""
    | Default_decay_time _      -> Default_decay_time ""
    | Default_trireg_strength _ -> Default_trireg_strength ""
    | cd                        -> cd

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Define id                 -> combo 0 [id]
    | Undef id                  -> combo 1 [id]
    | Undefineall               -> mkstr 2
    | Include s                 -> mkstr_str 3 s
    | SysInclude s              -> mkstr_str 5 s
    | Timescale(s1, s2)         -> mkstr_strs 7 [s1; s2]
    | Error s                   -> mkstr_str 9 s
    | Line(n1, s, n2)           -> mkstr_strs 11 [n1; s; n2]
    | Resetall                  -> mkstr 13
    | Default_nettypeNone       -> mkstr 14
    | Default_nettype           -> mkstr 15
    | Pragma id                 -> combo 16 [id]
    | Begin_keywords s          -> mkstr_str 17 s
    | End_keywords              -> mkstr 19
    | Default_decay_time s      -> mkstr_str 21 s
    | Default_trireg_strength s -> mkstr_str 23 s
    | Delay_mode_distributed    -> mkstr 25
    | Delay_mode_path           -> mkstr 26
    | Delay_mode_unit           -> mkstr 27
    | Delay_mode_zero           -> mkstr 28
    | Celldefine                -> mkstr 29
    | Endcelldefine             -> mkstr 30
    | Unconnected_drive         -> mkstr 31
    | Nounconnected_drive       -> mkstr 32

end (* of module CompilerDirective *)


module Strength = struct
  include Ls.Strength

  let anonymize = function
    | HIGHZ0
    | HIGHZ1
    | LARGE
    | MEDIUM
    | SMALL
    | PULL0
    | PULL1
    | STRONG0
    | STRONG1
    | WEAK0
    | WEAK1        -> Anonymous
    | x            -> x

  let to_short_string = function
    | HIGHZ0       -> mkstr 0
    | HIGHZ1       -> mkstr 1
    | LARGE        -> mkstr 2
    | MEDIUM       -> mkstr 3
    | SMALL        -> mkstr 4
    | PULL0        -> mkstr 5
    | PULL1        -> mkstr 6
    | STRONG0      -> mkstr 7
    | STRONG1      -> mkstr 8
    | WEAK0        -> mkstr 9
    | WEAK1        -> mkstr 10

    | Anonymous -> mkstr 11

end

module SimpleImmediateAssertion = struct
  include Ls.SimpleImmediateAssertion

  let to_short_string = function
    | Assert -> mkstr 0
    | Assume -> mkstr 1
    | Cover  -> mkstr 2

end

module DeferredImmediateAssertion = struct
  include Ls.DeferredImmediateAssertion

  let anonymize = function
    | Assert _
    | Assume _
    | Cover  _ -> Anonymous
    | x        -> x

  let to_short_string = function
    | Assert s -> mkstr_str 0 s
    | Assume s -> mkstr_str 2 s
    | Cover s  -> mkstr_str 4 s

    | Anonymous -> mkstr 5

end

module ConcurrentAssertion = struct
  include Ls.ConcurrentAssertion

  let to_short_string = function
    | AssertProp   -> mkstr 0
    | AssumeProp   -> mkstr 1
    | CoverProp    -> mkstr 2
    | CoverSeq     -> mkstr 3
    | RestrictProp -> mkstr 4

end


module ModuleSpec = struct
  include Ls.ModuleSpec

  let to_short_string = function
    | NORMAL    -> mkstr 0
    | MACRO     -> mkstr 1

end

module AlwaysSpec = struct
  include Ls.AlwaysSpec

  let to_short_string = function
    | NORMAL -> mkstr 0
    | COMB   -> mkstr 1
    | FF     -> mkstr 2
    | LATCH  -> mkstr 3

end

module BinsSpec = struct
  include Ls.BinsSpec

  let to_short_string = function
    | Normal  -> mkstr 0
    | Illegal -> mkstr 1
    | Ignore  -> mkstr 2

end

type annotation = string option

let null_annotation = None

let annotation_to_string = function
  | None -> "<none>"
  | Some x -> x


include Label

let f x = CompilerDirective.anonymize x

let strip lab = lab (* not yet *)

let anonymize ?(more=false) lab =
  ignore more;
  match lab with
    | CompilerDirective cd                    -> CompilerDirective (CompilerDirective.anonymize cd)
    | ModuleDeclaration(mspec, _)             -> ModuleDeclaration(mspec, "")
    | UdpDeclaration _                        -> UdpDeclaration ""
    | BindDirective _                         -> BindDirective ""
    | Expr e                                  -> Expr (Expression.anonymize e)
    | Stmt stmt                               -> Stmt (Statement.anonymize stmt)
    | NetType nt                              -> NetType (NetType.anonymize nt)
    | Instantiation _                         -> Instantiation ""
    | GateInstantiation g                     -> GateInstantiation (Gate.anonymize g)
    | PpIdentifier _                          -> PpIdentifier ""
    | ParamAssignment _                       -> ParamAssignment ""
    | IdSelect _                              -> IdSelect ""
    | Cellpin _                               -> Cellpin ""
    | DelayValue _                            -> DelayValue ""
    | PackageScope _                          -> PackageScope ""
    | PackageImport _                         -> PackageImport ""
    | EndLabel _                              -> EndLabel ""
    | ClassType _                             -> ClassType ""
    | DataType dt                             -> DataType (DataType.anonymize dt)
    | ArgsDotted _                            -> ArgsDotted ""
    | ClassScopeId _                          -> ClassScopeId ""
    | EnumNameDeclaration _                   -> EnumNameDeclaration ""
    | Variable _                              -> Variable ""
    | PackageImportItem _                     -> PackageImportItem ""
    | VariableDeclAssignment _                -> VariableDeclAssignment ""
    | GenBlockId _                            -> GenBlockId ""
    | NetSig _                                -> NetSig ""
    | PortDirection pd                        -> PortDirection (PortDirection.anonymize pd)
    | Strength strength                       -> Strength (Strength.anonymize strength)
    | Port _                                  -> Port ""
    | InterfacePort _                         -> InterfacePort ""
    | ModportIdentifier _                     -> ModportIdentifier ""
    | PatternId _                             -> PatternId ""
    | PatternTagged _                         -> PatternTagged ""
    | ForInitItemDT _                         -> ForInitItemDT ""
    | CycleDelay _                            -> CycleDelay ""
    | CycleDelayId _                          -> CycleDelayId ""
    | InstName _                              -> InstName ""
    | ClockingEvent _                         -> ClockingEvent ""
    | CycleDelayRange _                       -> CycleDelayRange ""
    | CycleDelayRangeId _                     -> CycleDelayRangeId ""
    | ConcurrentAssertionItemLabeled _        -> ConcurrentAssertionItemLabeled ""
    | DeferredImmediateAssertionItemLabeled _ -> DeferredImmediateAssertionItemLabeled ""
    | DeferredImmediateAssertionStmt dia      -> DeferredImmediateAssertionStmt (DeferredImmediateAssertion.anonymize dia)
    | CheckerInstantiation _                  -> CheckerInstantiation ""
    | GenvarIterationAssign(ao, _)            -> GenvarIterationAssign(ao, "")
    | GenvarIterationIncOrDec(iod, _)         -> GenvarIterationIncOrDec(iod, "")
    | GenvarIdDecl _                          -> GenvarIdDecl ""
    | GenvarInitId _                          -> GenvarInitId ""
    | SpecparamAssignmentId _                 -> SpecparamAssignmentId ""
    | SpecparamAssignmentPulseControl _       -> SpecparamAssignmentPulseControl ""
    | InputOrOutputId _                       -> InputOrOutputId ""
    | InterfaceIdentifier _                   -> InterfaceIdentifier ""
    | ProgramDeclaration _                    -> ProgramDeclaration ""
    | InterfaceDeclaration _                  -> InterfaceDeclaration ""
    | InterfaceDeclarationExtern _            -> InterfaceDeclarationExtern ""
    | TimeUnit _                              -> TimeUnit ""
    | Timeprecision _                         -> Timeprecision ""
    | PackageDeclaration _                    -> PackageDeclaration ""
    | FunctionDeclaration _                   -> FunctionDeclaration ""
    | FunctionPrototype _                     -> FunctionPrototype ""
    | FuncId _                                -> FuncId ""
    | FuncIdVoid _                            -> FuncIdVoid ""
    | TfIdScoped _                            -> TfIdScoped ""
    | TaskDeclaration _                       -> TaskDeclaration ""
    | TaskPrototype _                         -> TaskPrototype ""
    | TfPortItemAssignment _                  -> TfPortItemAssignment ""
    | TfVariableIdentifier _                  -> TfVariableIdentifier ""
    | CheckerDeclaration _                    -> CheckerDeclaration ""
    | PropertyDeclaration _                   -> PropertyDeclaration ""
    | PropertyPortItemAssignment _            -> PropertyPortItemAssignment ""
    | SequenceDeclaration _                   -> SequenceDeclaration ""
    | LetDeclaration _                        -> LetDeclaration ""
    | TypeDeclaration _                       -> TypeDeclaration ""
    | ScopedType _                            -> ScopedType ""
    | TypeIdentifier _                        -> TypeIdentifier ""
    | VirtualInterfaceDeclaration _           -> VirtualInterfaceDeclaration ""
    | ModportItem _                           -> ModportItem ""
    | ModportClockingDecl _                   -> ModportClockingDecl ""
    | ModportSimplePort _                     -> ModportSimplePort ""
    | ModportSimplePortDot _                  -> ModportSimplePortDot ""
    | ModportTfPort _                         -> ModportTfPort ""
    | CovergroupDeclaration _                 -> CovergroupDeclaration ""
    | CoverageOption(_, _)                    -> CoverageOption("", "")
    | CoverPointLabeled _                     -> CoverPointLabeled ""
    | CoverCrossLabeled _                     -> CoverCrossLabeled ""
    | CrossItem _                             -> CrossItem ""
    | Bins(bspec, _)                          -> Bins(bspec, "")
    | BinsSelection(bspec, _)                 -> BinsSelection(bspec, "")
    | BinsExpressionVar _                     -> BinsExpressionVar ""
    | BinsExpression(_, _)                    -> BinsExpression("", "")
    | CoverageEventWith _                     -> CoverageEventWith ""
    | HierarchicalBtfIdentifier _             -> HierarchicalBtfIdentifier ""
    | DpiImport _                             -> DpiImport ""
    | DpiExportFunc(_, _)                     -> DpiExportFunc("", "")
    | DpiExportTask(_, _)                     -> DpiExportTask("", "")
    | DpiImportLabel _                        -> DpiImportLabel ""
    | ClassDeclaration _                      -> ClassDeclaration ""
    | ClassConstraint _                       -> ClassConstraint ""
    | ExternTfDeclaration _                   -> ExternTfDeclaration ""
    | TimingCheck tc                          -> TimingCheck (TimingCheck.anonymize tc)
    | Notifier _                              -> Notifier ""
    | Delayed _                               -> Delayed ""
    | EdgeDescriptor _                        -> EdgeDescriptor ""
    | OverloadDeclaration(oo, _)              -> OverloadDeclaration(oo, "")
    | ClockingDeclaration _                   -> ClockingDeclaration ""
    | ClockingDeclAssign _                    -> ClockingDeclAssign ""
    | Production _                            -> Production ""
    | ProductionItem _                        -> ProductionItem ""
    | ElaborationSystemTask st                -> ElaborationSystemTask (SystemTask.anonymize st)
    | AttrSpec _                              -> AttrSpec ""
    | UdpPort _                               -> UdpPort ""
    | UdpOutputDeclaration _                  -> UdpOutputDeclaration ""
    | UdpOutputDeclarationReg _               -> UdpOutputDeclarationReg ""
    | UdpRegDeclaration _                     -> UdpRegDeclaration ""
    | UdpInitialStmt(_, _)                    -> UdpInitialStmt("", "")
    | EdgeSymbol _                            -> EdgeSymbol ""
    | LevelSymbol _                           -> LevelSymbol ""
    | OutputSymbol _                          -> OutputSymbol ""
    | ConfigDeclaration _                     -> ConfigDeclaration ""
    | CellId _                                -> CellId ""
    | LibraryIdentifier _                     -> LibraryIdentifier ""
    | CellClause _                            -> CellClause ""
    | InstanceIdentifier _                    -> InstanceIdentifier ""
    | TopModuleIdentifier _                   -> TopModuleIdentifier ""
    | LibraryDeclaration _                    -> LibraryDeclaration ""
    | FilePathSpec _                          -> FilePathSpec ""
    | IncludeStatement _                      -> IncludeStatement ""
    | PragmaExpression _                      -> PragmaExpression ""
    | PragmaValueNum _                        -> PragmaValueNum ""
    | PragmaValueStr _                        -> PragmaValueStr ""
    | PragmaValueId _                         -> PragmaValueId ""

    | NetDeclaration _                        -> NetDeclaration []
    | LocalParameterDeclaration _             -> LocalParameterDeclaration []
    | ParameterDeclaration _                  -> ParameterDeclaration []
    | GenvarDeclaration _                     -> GenvarDeclaration []
    | ModportDeclaration _                    -> ModportDeclaration []
    | NetDeclAssignments _                    -> NetDeclAssignments []
    | ParamAssignments _                      -> ParamAssignments []

    | MacroExpr _                             -> MacroExpr ""
    | MacroStmt _                             -> MacroStmt ""

    | lab                                     -> lab

let anonymize2 = anonymize ~more:true

let anonymize3 = anonymize ~more:true



let to_short_string ?(ignore_identifiers_flag=false) =
    let combo2 = combo2 ~ignore_identifiers_flag in function
    | Dummy                                    -> mkstr2 0
    | Error                                    -> mkstr2 1
    | Empty                                    -> mkstr2 2
    | SourceText                               -> mkstr2 3
    | LibraryText                              -> mkstr2 4
    | CompilerDirective cd                     ->
	catstr [mkstr2 5; CompilerDirective.to_short_string ~ignore_identifiers_flag cd]

    | ModuleDeclaration(mspec, id)             ->
	catstr ([mkstr2 6; ModuleSpec.to_short_string mspec] @ (encode_ids [id]))

    | UdpDeclaration id                        -> combo2 7 [id]
    | NetDeclaration ids                       -> combo2 8 ids
    | BindDirective id                         -> combo2 9 [id]
    | Expr e                                   ->
	catstr [mkstr2 10; Expression.to_short_string ~ignore_identifiers_flag e]

    | Stmt stmt                                ->
	catstr [mkstr2 11; Statement.to_short_string ~ignore_identifiers_flag stmt]

    | NetType nt                               -> catstr [mkstr2 12; NetType.to_short_string nt]
    | LocalParameterDeclaration ids            -> combo2 13 ids
    | ParameterDeclaration ids                 -> combo2 14 ids
    | ParameterPortDeclaration                 -> mkstr2 15
    | ModuleBody                               -> mkstr2 16
    | Instantiation id                         -> combo2 17 [id]
    | GateInstantiation g                      -> catstr [mkstr2 18; Gate.to_short_string g]
    | ContinuousAssign                         -> mkstr2 19
    | Assign                                   -> mkstr2 20
    | ConcurrentAssertionItem                  -> mkstr2 21
    | DeferredImmediateAssertionItem           -> mkstr2 22
    | PpIdentifier id                          -> combo2 23 [id]
    | PackedDimension                          -> mkstr2 24
    | ParamAssignment id                       -> combo2 25 [id]
    | DefparamAssignment                       -> mkstr2 26
    | IdSelect id                              -> combo2 27 [id]
    | Select                                   -> mkstr2 28
    | Range                                    -> mkstr2 29
    | RangePlus                                -> mkstr2 30
    | RangeMinus                               -> mkstr2 31
    | RangeForeach                             -> mkstr2 32
    | Root                                     -> mkstr2 33
    | This                                     -> mkstr2 34
    | Super                                    -> mkstr2 35
    | Cellpin id                               -> combo2 36 [id]
    | CellpinStar                              -> mkstr2 37
    | CellpinAnon                              -> mkstr2 38
    | DelayValue id                            -> combo2 39 [id]
    | PackageScope id                          -> combo2 40 [id]
    | PackageScopeUnit                         -> mkstr2 41
    | PackageScopeLocal                        -> mkstr2 42
    | PackageImport id                         -> combo2 43 [id]
    | PackageImportAny                         -> mkstr2 44
    | LifetimeStatic                           -> mkstr2 45
    | LifetimeAutomatic                        -> mkstr2 46
    | EndLabel id                              -> combo2 47 [id]
    | EndLabelNew                              -> mkstr2 48
    | ClassType id                             -> combo2 49 [id]
    | DataType dt                              ->
	catstr [mkstr2 50; DataType.to_short_string ~ignore_identifiers_flag dt]
    | Signed                                   -> mkstr2 51
    | Unsigned                                 -> mkstr2 52
    | ArgsDotted id                            -> combo2 53 [id]
    | Tagged                                   -> mkstr2 54
    | StructUnionBody                          -> mkstr2 55
    | StructUnionMember                        -> mkstr2 56
    | ClassScopeId id                          -> combo2 57 [id]
    | Void                                     -> mkstr2 58
    | EnumNameDeclaration id                   -> combo2 59 [id]
    | EnumBody                                 -> mkstr2 60
    | IdClassSel id                            -> combo2 61 [id]
    | Variable id                              -> combo2 62 [id]
    | Extern                                   -> mkstr2 63
    | PackageImportDeclaration                 -> mkstr2 64
    | PackageImportItem id                     -> combo2 65 [id]
    | Packed                                   -> mkstr2 66
    | ParameterValueAssignment                 -> mkstr2 67
    | Ports                                    -> mkstr2 68
    | PortsStar                                -> mkstr2 69
    | BitSelect                                -> mkstr2 70
    | VariableDeclAssignment id                -> combo2 71 [id]
    | DynamicArrayNew                          -> mkstr2 72
    | VariableDimension                        -> mkstr2 73
    | VariableDimensionStar                    -> mkstr2 74
    | GenItemBegin                             -> mkstr2 75
    | GenBlockId id                            -> combo2 76 [id]
    | GenerateRegion                           -> mkstr2 77
    | Scalared                                 -> mkstr2 78
    | Vectored                                 -> mkstr2 79
    | DelayControl                             -> mkstr2 80
    | NetSig id                                -> combo2 81 [id]
    | ParameterOverride                        -> mkstr2 82
    | PortDeclaration                          -> mkstr2 83
    | PortDirection pd                         -> catstr [mkstr2 84; PortDirection.to_short_string pd]
    | Strength strength                        -> catstr [mkstr2 85; Strength.to_short_string strength]
    | StrengthSupply0                          -> mkstr2 86
    | StrengthSupply1                          -> mkstr2 87
    | StrengthSpec                             -> mkstr2 88
    | VarDataType                              -> mkstr2 89
    | Port id                                  -> combo2 90 [id]
    | InterfacePort id                         -> combo2 91 [id]
    | InterfacePortInterface                   -> mkstr2 92
    | ModportIdentifier id                     -> combo2 93 [id]
    | PortMulti                                -> mkstr2 94
    | ExprScope                                -> mkstr2 95
    | ExprScopeThis                            -> mkstr2 96
    | ExprScopeSuper                           -> mkstr2 97
    | ExprScopeDot                             -> mkstr2 98
    | ExprScopeDotSuper                        -> mkstr2 99
    | CondPredicate                            -> mkstr2 100
    | CondPattern                              -> mkstr2 101
    | Dist                                     -> mkstr2 102
    | DistItem                                 -> mkstr2 103
    | DistWeight                               -> mkstr2 104
    | DistWeightRange                          -> mkstr2 105
    | ArrayRange                               -> mkstr2 106
    | ArrayRangePlus                           -> mkstr2 107
    | ArrayRangeMinus                          -> mkstr2 108
    | CastingTypeSimple                        -> mkstr2 109
    | CastingTypeSigned                        -> mkstr2 110
    | CastingTypeUnsigned                      -> mkstr2 111
    | CastingTypeString                        -> mkstr2 112
    | CastingTypeConst                         -> mkstr2 113
    | ValueRange                               -> mkstr2 114
    | Pattern                                  -> mkstr2 115
    | PatternId id                             -> combo2 116 [id]
    | PatternStar                              -> mkstr2 117
    | PatternTagged id                         -> combo2 118 [id]
    | EventControl                             -> mkstr2 119
    | EventControlStar                         -> mkstr2 120
    | EventControlParenStar                    -> mkstr2 121
    | EventControlRepeat                       -> mkstr2 122
    | EvExpr ee                                -> catstr [mkstr2 123; EventExpression.to_short_string ee]
    | CaseItem                                 -> mkstr2 124
    | CaseItemDefault                          -> mkstr2 125
    | CaseInsideItem                           -> mkstr2 126
    | CaseInsideItemDefault                    -> mkstr2 127
    | CaseItems                                -> mkstr2 128
    | CaseItemsMatches                         -> mkstr2 129
    | CaseItemsInside                          -> mkstr2 130
    | With                                     -> mkstr2 131
    | Args                                     -> mkstr2 132
    | ConstraintBlock                          -> mkstr2 133
    | ForInit                                  -> mkstr2 134
    | ForInitItemDT id                         -> combo2 135 [id]
    | ForInitItemLval                          -> mkstr2 136
    | StreamingConcat                          -> mkstr2 137
    | OrderRL                                  -> mkstr2 138
    | OrderLR                                  -> mkstr2 139
    | StreamConcat                             -> mkstr2 140
    | Solve                                    -> mkstr2 141
    | SolveBefore                              -> mkstr2 142
    | ActionBlock                              -> mkstr2 143
    | CycleDelay s                             -> mkstr2_str 144 s
    | CycleDelayId id                          -> combo2 146 [id]
    | CycleDelayParen                          -> mkstr2 147
    | Priority                                 -> mkstr2 148
    | Unique                                   -> mkstr2 149
    | Unique0                                  -> mkstr2 150
    | InstRange                                -> mkstr2 151
    | InstName id                              -> combo2 152 [id]
    | PExpr pe                                 -> catstr [mkstr2 153; PropertyExpression.to_short_string pe]
    | ClockingEvent id                         -> combo2 154 [id]
    | ClockingEventParen                       -> mkstr2 155
    | PropertyCase                             -> mkstr2 156
    | PropertyCaseDefault                      -> mkstr2 157
    | DisableIff                               -> mkstr2 158
    | CycleDelayRange s                        -> mkstr2_str 159 s
    | CycleDelayRangeId id                     -> combo2 161 [id]
    | CycleDelayRangeParen                     -> mkstr2 162
    | CycleDelayRangeBracket                   -> mkstr2 163
    | CycleDelayRangeBracketStar               -> mkstr2 164
    | CycleDelayRangeBracketPlus               -> mkstr2 165
    | SExpr se                                 -> catstr [mkstr2 166; SequenceExpression.to_short_string se]
    | ConsecutiveRepetition                    -> mkstr2 167
    | NonconsecutiveRepetition                 -> mkstr2 168
    | GotoRepetition                           -> mkstr2 169
    | NetAlias                                 -> mkstr2 170
    | InitialConstruct                         -> mkstr2 171
    | FinalConstruct                           -> mkstr2 172
    | AlwaysConstruct aspec                    -> catstr [mkstr2 173; AlwaysSpec.to_short_string aspec]
    | ConcurrentAssertionItemLabeled id        -> combo2 174 [id]
    | ConcurrentAssertionStmt ca               -> catstr [mkstr2 175; ConcurrentAssertion.to_short_string ca]
    | DeferredImmediateAssertionItemLabeled id -> combo2 176 [id]
    | DeferredImmediateAssertionStmt dia       -> catstr [mkstr2 177; DeferredImmediateAssertion.to_short_string dia]
    | SimpleImmediateAssertionStmt sia         -> catstr [mkstr2 178; SimpleImmediateAssertion.to_short_string sia]
    | CheckerInstantiation id                  -> combo2 179 [id]
    | LoopGenerateConstruct                    -> mkstr2 180
    | GenvarDeclaration ids                    -> combo2 181 ids
    | GenvarIterationAssign(ao, id)            -> catstr ([mkstr2 182; AssignmentOperator.to_short_string ao] @ (encode_ids [id]))
    | GenvarIdDecl id                          -> combo2 183 [id]
    | GenvarInitId id                          -> combo2 184 [id]
    | GenvarInit                               -> mkstr2 185
    | SpecifyBlock                             -> mkstr2 186
    | SpecparamDeclaration                     -> mkstr2 187
    | SpecparamAssignmentId id                 -> combo2 188 [id]
    | SpecparamAssignmentPulseControl id       -> combo2 189 [id]
    | PulsestyleDeclarationOnevent             -> mkstr2 190
    | PulsestyleDeclarationOndetect            -> mkstr2 191
    | ShowcancelledDeclaration                 -> mkstr2 192
    | NoshowcancelledDeclaration               -> mkstr2 193
    | SpecifyTerminalDescriptor                -> mkstr2 194
    | InputOrOutputId id                       -> combo2 195 [id]
    | InterfaceIdentifier id                   -> combo2 196 [id]
    | ProgramDeclaration id                    -> combo2 197 [id]
    | InterfaceDeclaration id                  -> combo2 198 [id]
    | InterfaceDeclarationExtern id            -> combo2 199 [id]
    | TimeUnitsDeclaration                     -> mkstr2 200
    | TimeUnit s                               -> mkstr2_str 201 s
    | Timeprecision s                          -> mkstr2_str 203 s
    | PackageDeclaration id                    -> combo2 205 [id]
    | AnonymousProgram                         -> mkstr2 206
    | AnonymousProgramItemEmpty                -> mkstr2 207
    | FunctionDeclaration id                   -> combo2 208 [id]
    | FunctionPrototype id                     -> combo2 209 [id]
    | FuncId id                                -> combo2 210 [id]
    | FuncIdVoid id                            -> combo2 211 [id]
    | FuncIdNew                                -> mkstr2 212
    | TfIdScoped id                            -> combo2 213 [id]
    | TaskDeclaration id                       -> combo2 214 [id]
    | TaskPrototype id                         -> combo2 215 [id]
    | ClassCtorPrototype                       -> mkstr2 216
    | TfPortListPart                           -> mkstr2 218
    | TfBody                                   -> mkstr2 219
    | TfPortDeclaration                        -> mkstr2 220
    | TfPortItemAssignment id                  -> combo2 221 [id]
    | TfPortItem                               -> mkstr2 222
    | TfVariableIdentifier id                  -> combo2 225 [id]
    | CheckerDeclaration id                    -> combo2 226 [id]
    | PropertyDeclaration id                   -> combo2 227 [id]
    | PropertyDeclBody                         -> mkstr2 228
    | PropertyPortItem                         -> mkstr2 229
    | PropertyPortItemDir                      -> mkstr2 230
    | PropertyPortItemAssignment id            -> combo2 231 [id]
    | SequenceDeclaration id                   -> combo2 234 [id]
    | SequenceDeclBody                         -> mkstr2 235
    | LetDeclaration id                        -> combo2 236 [id]
    | PropertyStatementSpec                    -> mkstr2 237
    | AssertionVariableDeclaration             -> mkstr2 238
    | SequenceFormalTypeSequence               -> mkstr2 239
    | SequenceFormalTypeUntyped                -> mkstr2 240
    | DataDeclarationVar                       -> mkstr2 241
    | Const                                    -> mkstr2 243
    | DataDeclarationVarClass                  -> mkstr2 244
    | TypeDeclaration id                       -> combo2 246 [id]
    | ScopedType id                            -> combo2 247 [id]
    | TypeIdentifier id                        -> combo2 248 [id]
    | TypeDeclEnum                             -> mkstr2 249
    | TypeDeclStruct                           -> mkstr2 250
    | TypeDeclUnion                            -> mkstr2 251
    | TypeDeclClass                            -> mkstr2 252
    | VirtualInterfaceDeclaration id           -> combo2 253 [id]
    | ModportDeclaration ids                   -> combo2 254 ids
    | ModportItem id                           -> combo2 255 [id]
    | ModportSimplePortsDecl                   -> mkstr2 256
    | ModportClockingDecl id                   -> combo2 257 [id]
    | ModportTfPortsDeclImport                 -> mkstr2 258
    | ModportTfPortsDeclExport                 -> mkstr2 259
    | ModportSimplePort id                     -> combo2 260 [id]
    | ModportSimplePortDot id                  -> combo2 261 [id]
    | ModportTfPort id                         -> combo2 262 [id]
    | CovergroupDeclaration id                 -> combo2 263 [id]
    | Paren                                    -> mkstr2 264
    | CoverageOption(id1, id2)                 -> combo2 265 [id1; id2]
    | CoverPoint                               -> mkstr2 266
    | CoverPointLabeled id                     -> combo2 267 [id]
    | CoverCross                               -> mkstr2 268
    | CoverCrossLabeled id                     -> combo2 269 [id]
    | CrossItem id                             -> combo2 270 [id]
    | Iff                                      -> mkstr2 271
    | BinsList                                 -> mkstr2 272
    | BinsEmpty                                -> mkstr2 273
    | SelectBins                               -> mkstr2 274
    | SelectBinsEmpty                          -> mkstr2 275
    | Bins(bspec, id)                          -> catstr ([mkstr2 276; BinsSpec.to_rep bspec] @ (encode_ids [id]))
    | BinsSelection(bspec, id)                 -> catstr ([mkstr2 277; BinsSpec.to_rep bspec] @ (encode_ids [id]))
    | BinsExpressionVar id                     -> combo2 278 [id]
    | BinsExpression(id1, id2)                 -> combo2 279 [id1;id2]
    | NBins                                    -> mkstr2 280
    | SelCondBinsof                            -> mkstr2 281
    | SelExprNot                               -> mkstr2 282
    | SelExprAnd                               -> mkstr2 283
    | SelExprOr                                -> mkstr2 284
    | SelExprParen                             -> mkstr2 285
    | Intersect                                -> mkstr2 286
    | Wildcard                                 -> mkstr2 287
    | TransSet                                 -> mkstr2 288
    | TransRangeList                           -> mkstr2 289
    | RepeatRange                              -> mkstr2 290
    | TransItem                                -> mkstr2 291
    | TransRepetitionConsecutive               -> mkstr2 292
    | TransRepetitionNonconsecutive            -> mkstr2 293
    | TransRepetitionGoto                      -> mkstr2 294
    | Default                                  -> mkstr2 295
    | DefaultSequence                          -> mkstr2 296
    | OpenRangeList                            -> mkstr2 297
    | CoverageEventWith id                     -> combo2 298 [id]
    | CoverageEventBlockEvent                  -> mkstr2 299
    | BlockEventExpression                     -> mkstr2 300
    | BlockEventExpressionBegin                -> mkstr2 301
    | BlockEventExpressionEnd                  -> mkstr2 302
    | HierarchicalBtfIdentifier id             -> combo2 303 [id]
    | PackageExportDeclarationStar             -> mkstr2 304
    | PackageExportDeclaration                 -> mkstr2 305
    | DpiImport s                              -> mkstr2_str 306 s

    | DpiExportFunc(s, id)                     ->
	let strs, no_digest = encode_strs [s] in
	let idx = if no_digest then 308 else 307 in
	catstr ((mkstr2 idx)::(strs @ (encode_ids [id])))

    | DpiExportTask(s, id)                     ->
	let strs, no_digest = encode_strs [s] in
	let idx = if no_digest then 310 else 309 in
	catstr ((mkstr2 idx)::(strs @ (encode_ids [id])))

    | DpiImportLabel id                        -> combo2 311 [id]
    | DpiTfImportPropertyContext               -> mkstr2 312
    | DpiTfImportPropertyPure                  -> mkstr2 313
    | ExternConstraintDeclaration              -> mkstr2 314
    | Static                                   -> mkstr2 315
    | Virtual                                  -> mkstr2 316
    | ClassDeclaration id                      -> combo2 317 [id]
    | ClassExtends                             -> mkstr2 318
    | ClassItemEmpty                           -> mkstr2 319
    | ClassMethod                              -> mkstr2 320
    | Qualifier q                              -> catstr [mkstr2 321; Qualifier.to_short_string q]
    | ClassBody                                -> mkstr2 322
    | ClassConstraint id                       -> combo2 323 [id]
    | Pure                                     -> mkstr2 324
    | ClassProperty                            -> mkstr2 325
    | PackageOrGenerateItemEmpty               -> mkstr2 326
    | Forkjoin                                 -> mkstr2 327
    | ExternTfDeclaration id                   -> combo2 328 [id]
    | TimingCheck tc                           -> catstr [mkstr2 329; TimingCheck.to_short_string tc]
    | SystemTimingCheck                        -> mkstr2 330
    | Notifier id                              -> combo2 331 [id]
    | Delayed id                               -> combo2 332 [id]
    | TimingCheckEvent                         -> mkstr2 333
    | TimingCheckEventControlPosedge           -> mkstr2 334
    | TimingCheckEventControlNegedge           -> mkstr2 335
    | TimingCheckEventControl                  -> mkstr2 336
    | EdgeDescriptor s                         -> mkstr2_str 337 s
    | OverloadDeclaration(oo, id)              -> catstr ([mkstr2 339; OverloadOperator.to_short_string oo] @ (encode_ids [id]))
    | Params                                   -> mkstr2 340
    | ClockingDeclaration id                   -> combo2 341 [id]
    | Global                                   -> mkstr2 342
    | ClockingBody                             -> mkstr2 343
    | ClockingItemDefault                      -> mkstr2 344
    | ClockingItem                             -> mkstr2 345
    | DefaultSkewInput                         -> mkstr2 346
    | DefaultSkewOutput                        -> mkstr2 347
    | DefaultSkewInputOutput                   -> mkstr2 348
    | ClockingDirectionInput                   -> mkstr2 349
    | ClockingDirectionInputOutput             -> mkstr2 350
    | ClockingDirectionInout                   -> mkstr2 351
    | ClockingSkewPosedge                      -> mkstr2 352
    | ClockingSkewNegedge                      -> mkstr2 353
    | ClockingSkewEdge                         -> mkstr2 354
    | ClockingSkew                             -> mkstr2 355
    | ClockingDeclAssign id                    -> combo2 356 [id]
    | Production id                            -> combo2 357 [id]
    | ProductionItem id                        -> combo2 358 [id]
    | RsCodeBlock                              -> mkstr2 359
    | RsRule                                   -> mkstr2 360
    | RsProductionList                         -> mkstr2 361
    | RsProductionListRandJoin                 -> mkstr2 362
    | WeightSpecInt s                          -> mkstr2_str 363 s
    | WeightSpecId                             -> mkstr2 365
    | WeightSpec                               -> mkstr2 366
    | RsProdIf                                 -> mkstr2 367
    | RsProdRepeat                             -> mkstr2 368
    | RsProdCase                               -> mkstr2 369
    | RsCaseItem                               -> mkstr2 370
    | RsCaseItemDefault                        -> mkstr2 371
    | CheckerOrGenerateItemEmpty               -> mkstr2 372
    | ConditionalGenerateConstructCase         -> mkstr2 373
    | ConditionalGenerateConstructIf           -> mkstr2 374
    | ElaborationSystemTask st                 -> catstr [mkstr2 375; SystemTask.to_short_string st]
    | CaseGenerateItem                         -> mkstr2 376
    | CaseGenerateItemDefault                  -> mkstr2 377
    | AssignmentPattern                        -> mkstr2 378
    | AssignmentPatternExpr                    -> mkstr2 379
    | PatternKey                               -> mkstr2 380
    | PatternKeyDefault                        -> mkstr2 381
    | PatternMember                            -> mkstr2 382
    | SimplePathDeclaration                    -> mkstr2 383
    | ParallelPathDescription                  -> mkstr2 384
    | FullPathDescription                      -> mkstr2 385
    | PathInputs                               -> mkstr2 386
    | PathOutputs                              -> mkstr2 387
    | PathDelayValue                           -> mkstr2 388
    | PolarityPlus                             -> mkstr2 389
    | PolarityMinus                            -> mkstr2 390
    | EdgePosedge                              -> mkstr2 391
    | EdgeNegedge                              -> mkstr2 392
    | EdgeSensitivePathDeclaration             -> mkstr2 393
    | ParallelEdgeSensitivePathDescription     -> mkstr2 394
    | FullEdgeSensitivePathDescription         -> mkstr2 395
    | ParallelEdgeSensitivePathDescriptionSub  -> mkstr2 396
    | FullEdgeSensitivePathDescriptionSub      -> mkstr2 397
    | StateDependentPathDeclarationIf          -> mkstr2 398
    | StateDependentPathDeclarationIfnone      -> mkstr2 399
    | VariableLvalue                           -> mkstr2 400
    | AttributeInstance                        -> mkstr2 401
    | AttrSpec id                              -> combo2 402 [id]
    | UdpPort id                               -> combo2 403 [id]
    | UdpPortDeclaration                       -> mkstr2 404
    | UdpOutputDeclaration id                  -> combo2 405 [id]
    | UdpOutputDeclarationReg id               -> combo2 406 [id]
    | UdpInputDeclaration                      -> mkstr2 407
    | UdpRegDeclaration id                     -> combo2 408 [id]
    | SequentialBody                           -> mkstr2 409
    | CombinationalBody                        -> mkstr2 410
    | UdpInitialStmt(id, s)                    ->
	let strs, no_digest = encode_strs [s] in
	let idx = if no_digest then 412 else 411 in
	catstr ((mkstr2 idx)::((encode_ids [id]) @ strs))

    | SequentialEntry                          -> mkstr2 413
    | EdgeIndicator                            -> mkstr2 414
    | EdgeSymbol s                             -> mkstr2_str 415 s
    | LevelSymbol s                            -> mkstr2_str 417 s
    | OutputSymbol s                           -> mkstr2_str 419 s
    | CombinationalEntry                       -> mkstr2 421
    | NextStateMinus                           -> mkstr2 422
    | UdpPortsStar                             -> mkstr2 423
    | UdpPorts                                 -> mkstr2 424
    | UdpPortDecls                             -> mkstr2 425
    | UdpDeclarationPorts                      -> mkstr2 426
    | AttributeInstances                       -> mkstr2 427
    | ConfigDeclaration id                     -> combo2 428 [id]
    | DesignStatement                          -> mkstr2 429
    | CellId id                                -> combo2 430 [id]
    | LibraryIdentifier id                     -> combo2 431 [id]
    | LiblistClause                            -> mkstr2 432
    | CellClause id                            -> combo2 433 [id]
    | UseClause                                -> mkstr2 434
    | ColonConfig                              -> mkstr2 435
    | InstanceName                             -> mkstr2 436
    | InstanceIdentifier id                    -> combo2 437 [id]
    | TopModuleIdentifier id                   -> combo2 438 [id]
    | InstClause                               -> mkstr2 439
    | ConfigRuleStatementDefault               -> mkstr2 440
    | ConfigRuleStatement                      -> mkstr2 441
    | LibraryDeclaration id                    -> combo2 442 [id]
    | Incdir                                   -> mkstr2 443
    | FilePathSpec s                           -> mkstr2_str 444 s
    | IncludeStatement s                       -> mkstr2_str 446 s
    | PragmaExpression id                      -> combo2 448 [id]
    | PragmaValueTuple                         -> mkstr2 449
    | PragmaValueNum s                         -> mkstr2_str 450 s
    | PragmaValueStr s                         -> mkstr2_str 452 s
    | PragmaValueId id                         -> combo2 454 [id]
    | PackageImportDecls                       -> mkstr2 455
    | ParamPorts                               -> mkstr2 456
    | Ranges                                   -> mkstr2 457
    | VariableDimensions                       -> mkstr2 458
    | CaseConds                                -> mkstr2 459
    | NetDeclAssignments ids                   -> combo2 460 ids
    | ParamAssignments ids                     -> combo2 461 ids

    | MacroExpr s                              -> mkstr2_str 462 s
    | MacroStmt s                              -> mkstr2_str 464 s

    | ImplicitDataType                         -> mkstr2 466
    | VarDeclAssignments                       -> mkstr2 467
    | Var                                      -> mkstr2 468

    | GenvarIterationIncOrDec(iod, id)         -> catstr ([mkstr2 182; IncOrDecOperator.to_short_string iod] @ (encode_ids [id]))


let is_hunk_boundary _ _ = false (* not yet *)

(* These labels are collapsible whether they are leaves or not. *)
let forced_to_be_collapsible (*lab*)_ =
  false


let is_collapse_target options lab =
  if options#no_collapse_flag then
    false
  else
    match lab with
    | ModuleDeclaration _
    | UdpDeclaration _
    | InterfaceDeclaration _
    | InterfaceDeclarationExtern _
    | ProgramDeclaration _
    | PackageDeclaration _
    | NetDeclaration _
    | DataDeclarationVar
    | DataDeclarationVarClass
    | TypeDeclaration _
    | PackageImportDeclaration
    | VirtualInterfaceDeclaration _
    | TaskDeclaration _
    | TaskPrototype _
    | FunctionDeclaration _
    | FunctionPrototype _
    | DpiImport _
    | DpiExportFunc _
    | DpiExportTask _
    | ExternConstraintDeclaration
    | ClassDeclaration _
    | ClassCtorPrototype
    | ParameterDeclaration _
    | LocalParameterDeclaration _
    | CovergroupDeclaration _
    | OverloadDeclaration _
    | ConcurrentAssertionItemLabeled _
    | ConcurrentAssertionStmt _
    | DeferredImmediateAssertionItemLabeled _
    | DeferredImmediateAssertionStmt _
    | SimpleImmediateAssertionStmt _
    | AnonymousProgram
    | TimeUnitsDeclaration
    | BindDirective _
    | ConfigDeclaration _

(* module_declaration related *)
    | PackageImportDecls
    | ParamPorts
    | Ports
    | Ranges
    | VariableDimensions
    | ModuleBody
    | PortDeclaration
    | GenerateRegion
    | ParameterOverride
    | GateInstantiation _
    | Instantiation _
    | CheckerInstantiation _
    | CheckerDeclaration _
    | PropertyDeclaration _
    | SequenceDeclaration _
    | LetDeclaration _
    | GenvarDeclaration _
    | ClockingDeclaration _
    | ContinuousAssign
    | NetAlias
    | InitialConstruct
    | FinalConstruct
    | AlwaysConstruct _
    | LoopGenerateConstruct
    | ConditionalGenerateConstructCase
    | ConditionalGenerateConstructIf
    | SpecifyBlock
    | SpecparamDeclaration

(* udp_declaration related *)
    | UdpPorts
    | UdpPortDecls
    | UdpDeclarationPorts
    | CombinationalBody
    | SequentialBody
    | CombinationalEntry
    | SequentialEntry

(* interface_declaration related *)
    | ModportDeclaration _
    | ExternTfDeclaration _

(* program_declaration related *)
    | ElaborationSystemTask _

(* package_declaration related *)
    | PackageExportDeclaration

(* net_declaration related *)

(* data_declaration related *)

(* task_declaration related *)
(* function_declaration related *)
    | TfPortListPart
    | TfBody

(* dpi_import_export related *)

(* extern_constraint_declaration related *)
    | ConstraintBlock
    | Solve
    | SolveBefore

(* class_declaration related *)
    | ClassExtends
    | ClassProperty
    | ClassMethod
    | ClassConstraint _
    | ClassBody

(* parameter_declaration related *)

(* covergroup_declaration related *)
    | CoverageEventWith _
    | CoverageEventBlockEvent
    | ClockingEventParen
    | ParamAssignment _

(* overload_declaration related *)
    | Params

(* assertion_item_declaration related *)
    | PropertyDeclBody
    | PropertyStatementSpec
    | SequenceDeclBody
    | AssertionVariableDeclaration

(* anonymous_program related *)

(* bind_directive related *)

(* config_declaration related *)
    | DesignStatement

(* clocking_declaration related *)
    | ClockingBody

(* data_type related *)
    | DataType (
      DataType.Struct
    | DataType.Union
    | DataType.Enum
    | DataType.VirtualInterface _
    | DataType.PsType _
    | DataType.ClassScopeType _
    | DataType.PsCovergroup _
    | DataType.ClassType
     )
    | StructUnionBody
    | StructUnionMember
    | EnumBody
    | EnumNameDeclaration _

(* others *)
    | PortMulti
    | Args
    | CaseConds
    | NetDeclAssignments _
    | ParamAssignments _

    | Expr _
    | PExpr _
    | SExpr _
    | Stmt _

      -> true

    | _ -> false


let is_to_be_notified = function
  | ModuleDeclaration _
  | UdpDeclaration _
  | InterfaceDeclaration _
  | InterfaceDeclarationExtern _
  | ProgramDeclaration _
  | PackageDeclaration _
  | NetDeclaration _
  | DataDeclarationVar
  | DataDeclarationVarClass
  | TypeDeclaration _
  | PackageImportDeclaration
  | VirtualInterfaceDeclaration _
  | TaskDeclaration _
  | TaskPrototype _
  | FunctionDeclaration _
  | FunctionPrototype _
  | DpiImport _
  | DpiExportFunc _
  | DpiExportTask _
  | ExternConstraintDeclaration
  | ClassDeclaration _
  | ClassCtorPrototype
  | ParameterDeclaration _
  | LocalParameterDeclaration _
  | CovergroupDeclaration _
  | OverloadDeclaration _
  | ConcurrentAssertionItemLabeled _
  | ConcurrentAssertionStmt _
  | DeferredImmediateAssertionItemLabeled _
  | DeferredImmediateAssertionStmt _
  | SimpleImmediateAssertionStmt _
  | AnonymousProgram
  | TimeUnitsDeclaration
  | BindDirective _
  | ConfigDeclaration _
  | GenvarDeclaration _
  | ModportDeclaration _
    -> true
  | _ -> false




let is_boundary = function
  | SourceText
  | LibraryText
  | ModuleDeclaration _
  | UdpDeclaration _
  | InterfaceDeclaration _
  | InterfaceDeclarationExtern _
  | ProgramDeclaration _
  | PackageDeclaration _
  | NetDeclaration _
  | DataDeclarationVar
  | DataDeclarationVarClass
  | TypeDeclaration _
  | PackageImportDeclaration
  | VirtualInterfaceDeclaration _
  | TaskDeclaration _
  | TaskPrototype _
  | FunctionDeclaration _
  | FunctionPrototype _
  | DpiImport _
  | DpiExportFunc _
  | DpiExportTask _
  | ExternConstraintDeclaration
  | ClassDeclaration _
  | ClassCtorPrototype
  | ParameterDeclaration _
  | LocalParameterDeclaration _
  | CovergroupDeclaration _
  | OverloadDeclaration _
  | ConcurrentAssertionItemLabeled _
  | ConcurrentAssertionStmt _
  | DeferredImmediateAssertionItemLabeled _
  | DeferredImmediateAssertionStmt _
  | SimpleImmediateAssertionStmt _
  | AnonymousProgram
  | TimeUnitsDeclaration
  | BindDirective _
  | ConfigDeclaration _ -> true
  | _ -> false


let is_partition = function
  | CompilerDirective _
  | ModuleDeclaration _
  | UdpDeclaration _
  | InterfaceDeclaration _
  | InterfaceDeclarationExtern _
  | ProgramDeclaration _
  | PackageDeclaration _
  | NetDeclaration _
  | BindDirective _
    -> true
  | _ -> false

let is_sequence = function
  | SourceText
  | LibraryText
  | ModuleBody
  | StructUnionBody
  | EnumBody
  | PropertyDeclBody
  | SequenceDeclBody
  | ClassBody
  | ClockingBody
  | SequentialBody
  | CombinationalBody
    -> true
  | _ -> false

let is_ntuple = function
  (* not yet *)
  | _ -> false


(* for fact extraction *)

let get_category lab =
  let name, _ = to_tag lab in
  name


let get_name ?(strip=false) lab =
  ignore strip;
  let n =
    match lab with
    | CompilerDirective cd     -> CompilerDirective.get_name cd
    | Expr e                   -> Expression.get_name e
    | Stmt stmt                -> Statement.get_name stmt
    | TimingCheck tc           -> TimingCheck.get_name tc
    | ElaborationSystemTask st -> SystemTask.get_name st
    | DataType dt              -> DataType.get_name dt

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
    | CoverPointLabeled id
    | CoverCrossLabeled id
    | CrossItem id
    | Bins(_, id)
    | BinsSelection(_, id)
    | BinsExpressionVar id
    | CoverageEventWith id
    | HierarchicalBtfIdentifier id
    | DpiExportFunc(_, id)
    | DpiExportTask(_, id)
    | DpiImportLabel id
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
    | PragmaExpression id
    | PragmaValueId id
	-> id

    | CoverageOption(id1, id2)
    | BinsExpression(id1, id2)
        -> id1^"."^id2

    | _ -> raise Not_found
  in
  if n = "" then
    raise Not_found
  else
    n

let get_names = function
  | NetDeclaration ids
  | LocalParameterDeclaration ids
  | ParameterDeclaration ids
  | GenvarDeclaration ids
  | ModportDeclaration ids
  | NetDeclAssignments ids
  | ParamAssignments ids
    ->
      if ids = [] then
	raise Not_found
      else
	ids

  | _ -> raise Not_found

let get_value = function
  | Expr expr -> Expression.get_value expr
  | _ -> raise Not_found

let has_value = function
  | Expr (Expression.IntegralNumber _
  | Expression.RealNumber _
  | Expression.TimeNumber _)
    -> true
  | _ -> false

let has_non_trivial_value lab =
  try
    let v = get_value lab in
    v <> "0" && v <> "1"
  with
    Not_found -> false

let has_non_trivial_tid (*lab*)_ = false (* not yet *)

let is_compatible ?(weak=false) _ _ = ignore weak; false

let is_order_insensitive = function
  | _ -> false

let quasi_eq _ _ = false

let relabel_allowed = function
  | ModuleDeclaration _, ModuleDeclaration _
  | Expr _, Expr _
  | Stmt _, Stmt _
  | EvExpr _, EvExpr _
  | PExpr _, PExpr _
  | SExpr _, SExpr _
  | AlwaysConstruct _, AlwaysConstruct _
  | ConcurrentAssertionStmt _, ConcurrentAssertionStmt _
  | DeferredImmediateAssertionStmt _, DeferredImmediateAssertionStmt _
  | SimpleImmediateAssertionStmt _, SimpleImmediateAssertionStmt _
  | GenvarIterationAssign _, GenvarIterationAssign _
  | GenvarIterationIncOrDec _, GenvarIterationIncOrDec _
  | GenvarIterationAssign _, GenvarIterationIncOrDec _
  | GenvarIterationIncOrDec _, GenvarIterationAssign _
  | Bins _, Bins _
  | BinsSelection _, BinsSelection _
  | Qualifier _, Qualifier _
  | TimingCheck _, TimingCheck _
  | OverloadDeclaration _, OverloadDeclaration _
    -> true
  | l1, l2 -> anonymize2 l1 = anonymize2 l2

let move_disallowed _ = false

let is_common _ = false

let get_ident_use = function
  | IdSelect id -> id
  | _ -> ""

let to_char (*lab*)_ = '0'

let has_names lab =
  try
    ignore (get_names lab);
    true
  with Not_found -> false

let has_a_name lab =
  try
    ignore (get_name lab);
    true
  with Not_found -> false

let is_named lab =
  has_a_name lab || has_names lab

let is_named_orig = is_named (* not yet *)

let to_elem_data = Astml.to_elem_data lang_prefix to_tag

let of_elem_data (*name*)_ (*attrs*)_ _ = Dummy (* not yet *)


let getlab nd = (Obj.obj nd#data#_label : t)

let cannot_be_keyroot nd =
  match getlab nd with
  | SourceText
  | LibraryText
    -> true
  | _ -> false

let is_string_literal (*lab*)_ = false (* not yet *)
let is_int_literal (*lab*)_ = false (* not yet *)
let is_real_literal (*lab*)_ = false (* not yet *)

let is_phantom = function
  | AttributeInstances
  | PackageImportDecls
  | Ranges
  | VariableDimensions
      -> true
  | _ -> false

let is_special _ = false

let is_always_construct = function
  | AlwaysConstruct _ -> true
  | _ -> false

let is_timing_control = function
  | DelayControl
  | EventControl
  | EventControlStar
  | EventControlParenStar
  | EventControlRepeat
  | CycleDelay _
  | CycleDelayId _
  | CycleDelayParen
    -> true
  | _ -> false

let is_continuous_assign = function
  | ContinuousAssign -> true
  | _ -> false

let is_blocking_assign = function
  | Stmt Statement.BlockingAssignment -> true
  | _ -> false

let is_non_blocking_assign = function
  | Stmt Statement.NonBlockingAssignment -> true
  | _ -> false

let is_if = function
  | Stmt Statement.Conditional -> true
  | _ -> false

let is_case = function
  | Stmt (
    Statement.Case |
    Statement.Casex |
    Statement.Casez
   ) -> true
  | _ -> false

let is_case_item = function
  | CaseItem
  | CaseItemDefault -> true
  | _ -> false

let is_case_cond = function
  | CaseConds -> true
  | _ -> false

let is_module_decl = function
  | ModuleDeclaration _ -> true
  | _ -> false

let is_ports = function
  | Ports
  | PortsStar -> true
  | _ -> false

let is_port = function
  | Port _ -> true
  | _ -> false

let is_port_dir = function
  | PortDirection _ -> true
  | _ -> false

let is_net_type = function
  | NetType _ -> true
  | _ -> false

let is_data_type = function
  | DataType _ -> true
  | _ -> false

let is_var_data_type = function
  | VarDataType -> true
  | _ -> false

let is_signing = function
  | Signed
  | Unsigned -> true
  | _ -> false

let is_ranges = function
  | Ranges -> true
  | _ -> false

let is_variable_dims = function
  | VariableDimensions -> true
  | _ -> false

let is_inst = function
  | Instantiation _ -> true
  | _ -> false

let is_initial_construct = function
  | InitialConstruct -> true
  | _ -> false

let is_final_construct = function
  | FinalConstruct -> true
  | _ -> false

let is_generate_region = function
  | GenerateRegion -> true
  | _ -> false

let is_param_port_decl = function
  | ParameterPortDeclaration -> true
  | _ -> false

let is_param_assign = function
  | ParamAssignment _ -> true
  | _ -> false

let is_data_decl_var = function
  | DataDeclarationVar -> true
  | _ -> false

let is_net_decl = function
  | NetDeclaration _ -> true
  | _ -> false

let is_reg = function
  | DataType DataType.Reg -> true
  | _ -> false

let is_wire = function
  | NetType (NetType.Wire | NetType.Uwire) -> true
  | _ -> false

let is_expr = function
  | Expr _ -> true
  | _ -> false

let is_op = function (* not yet *)
  | _ -> false

let is_scope_creating = function (* not yet *)
  | _ -> false

let is_stmt = function
  | Stmt _ -> true
  | _ -> false

let is_statement = is_stmt

let is_primary _ = false (* not yet *)
let is_block _ = false (* not yet *)

let is_pp_define = function
  | CompilerDirective (CompilerDirective.Define _) -> true
  | _ -> false

let is_pp_include = function
  | CompilerDirective (
    CompilerDirective.Include _ |
    CompilerDirective.SysInclude _
   ) -> true
  | _ -> false

let is_source_text = function
  | SourceText -> true
  | _ -> false
