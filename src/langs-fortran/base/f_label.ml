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

(* fortran/label.ml *)

module Xlist = Diffast_misc.Xlist
module Loc = Diffast_misc.Loc
module Lang_base = Diffast_core.Lang_base
module Spec = Diffast_core.Spec
module Charpool = Diffast_core.Charpool
module Astml = Diffast_core.Astml
module Ast = Fortran_parsing.Ast
module Label_common = Fortran_parsing.Label_common
module Labels = Fortran_parsing.Labels
module Label = Fortran_parsing.Label
module Pinfo = Fortran_parsing.Pinfo

let keyroot_depth_min = 4

type tie_id = Lang_base.tie_id

let null_tid      = Lang_base.null_tid
let mktid         = Lang_base.mktid
let tid_to_string = Lang_base.tid_to_string
let anonymize_tid = Lang_base.anonymize_tid
let mktidattr     = Lang_base.mktidattr



module type T = sig
  include Spec.LABEL_T

  val lang_prefix               : string

  val is_case_construct         : t -> bool
  val is_do_construct           : t -> bool
  val is_forall_construct       : t -> bool
  val is_if_construct           : t -> bool
  val is_where_construct        : t -> bool
  val is_derived_type_def       : t -> bool
  val is_interface_block        : t -> bool
  val is_select_type_construct  : t -> bool
  val is_associate_construct    : t -> bool
  val is_block_construct        : t -> bool
  val is_critical_construct     : t -> bool

  val is_primary                : t -> bool
  val is_expr                   : t -> bool
  val is_stmt                   : t -> bool

  val is_if_stmt                : t -> bool
  val is_arithmetic_if_stmt     : t -> bool
  val is_if_then_stmt           : t -> bool
  val is_else_if_stmt           : t -> bool
  val is_else_stmt              : t -> bool

  val is_pp_directive           : t -> bool
  val is_pp_define              : t -> bool
  val is_pp_include             : t -> bool
  val is_ocl_directive          : t -> bool
  val is_omp_directive          : t -> bool
  val is_acc_directive          : t -> bool
  val is_dec_directive          : t -> bool

  val is_program                : t -> bool

  val is_program_unit           : t -> bool

  val is_program_unit_or_fragment   : t -> bool
  val is_program_unit_or_subprogram : t -> bool

  val is_main_program           : t -> bool
  val is_function               : t -> bool
  val is_subroutine             : t -> bool
  val is_subprogram             : t -> bool

  val is_ext_function           : t -> bool
  val is_ext_subroutine         : t -> bool

  val is_int_function           : t -> bool
  val is_int_subroutine         : t -> bool

  val is_mod_function           : t -> bool
  val is_mod_subroutine         : t -> bool

  val is_module                 : t -> bool
  val is_block_data             : t -> bool

  val is_block                  : t -> bool

  val is_entity_decl            : t -> bool
  val is_type_decl_stmt         : t -> bool
  val is_var_name               : t -> bool
  val is_part_name              : t -> bool

  val is_if_then_block    : t -> bool
  val is_else_block       : t -> bool
  val is_else_if_block    : t -> bool
  val is_where_block      : t -> bool
  val is_case_block       : t -> bool
  val is_type_guard_block : t -> bool
  val is_do_block         : t -> bool

  val is_pp_branch            : t -> bool
  val is_pp_branch_do         : t -> bool
  val is_pp_branch_end_do     : t -> bool
  val is_pp_branch_if         : t -> bool
  val is_pp_branch_end_if     : t -> bool
  val is_pp_branch_forall     : t -> bool
  val is_pp_branch_end_forall : t -> bool
  val is_pp_branch_where      : t -> bool
  val is_pp_branch_end_where  : t -> bool
  val is_pp_branch_select     : t -> bool
  val is_pp_branch_end_select : t -> bool

  val is_pp_section_ifdef  : t -> bool
  val is_pp_section_ifndef : t -> bool
  val is_pp_section_if     : t -> bool
  val is_pp_section_elif   : t -> bool
  val is_pp_section_else   : t -> bool

  val is_omp_construct     : t -> bool
  val is_acc_construct     : t -> bool

  val is_fragment          : t -> bool

  val is_execution_part    : t -> bool
  val is_subprogram_part   : t -> bool

  val is_section_subscript_list : t -> bool
  val is_ambiguous              : t -> bool

  val is_container_unit         : t -> bool

  val getlab                    : Spec.node_t -> t

  val get_var                   : t -> string
  val get_pp_include_path       : t -> string
  val get_label                 : t -> string
  val get_stmt_label            : t -> string

end


let conv_loc
    { Ast.Loc.filename     = fn;
      Ast.Loc.start_offset = so;
      Ast.Loc.end_offset   = eo;
      Ast.Loc.start_line   = sl;
      Ast.Loc.start_char   = sc;
      Ast.Loc.end_line     = el;
      Ast.Loc.end_char     = ec;
    } =
  Loc.make ~fname:fn so eo sl sc el ec

open Charpool



include Label_common

module HeaderFile = struct
  include Labels.HeaderFile

  let to_short_string = function
    | User s   -> mkstr_str 0 s
    | System s -> mkstr_str 2 s
    | Macro(n, _) -> combo 4 [n]
    | Generated s -> mkstr_str 5 s
end

module PpDirective = struct
  include Labels.PpDirective

  let branch_to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in
    function
      | If c     -> mkstr_str 0 c
      | Elif c   -> mkstr_str 2 c
      | Ifdef n  -> combo 4 [n]
      | Ifndef n -> combo 5 [n]
      | Else     -> mkstr 6
      | Endif _  -> mkstr 7

  let message_to_short_string = function
    | Error m   -> mkstr_str 0 m
    | Warning m -> mkstr_str 2 m

  let _to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in
    function
      | Define(n, b)  -> mkstr_strs 0 [n;b]
      | Undef n       -> combo 2 [n]
      | Include h     -> mkstr_str 3 (HeaderFile.to_short_string h)
      | Branch b      -> mkstr_str 5 (branch_to_short_string ~ignore_identifiers_flag b)
      | Message m     -> mkstr_str 7 (message_to_short_string m)
      | Unknown(d, r) -> mkstr_strs 11 [d;r]

  let to_short_string x = _to_short_string x.pp_label

end

module ProgramUnit = struct
  include Labels.ProgramUnit

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in
    function
      | FunctionSubprogram n   -> combo 0 [n]
      | SubroutineSubprogram n -> combo 1 [n]
      | Module n               -> combo 2 [n]
      | MainProgram n_opt      -> combo 3 (opt_to_list n_opt)
      | BlockData n_opt        -> combo 4 (opt_to_list n_opt)
      | Submodule n            -> combo 5 [n]

end

module InternalSubprogram = struct
  include Labels.InternalSubprogram

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in
    function
      | FunctionSubprogram n   -> combo 0 [n]
      | SubroutineSubprogram n -> combo 1 [n]

end

module ModuleSubprogram = struct
  include Labels.ModuleSubprogram

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in
    function
      | FunctionSubprogram n       -> combo 0 [n]
      | SubroutineSubprogram n     -> combo 1 [n]
      | SeparateModuleSubprogram n -> combo 2 [n]

end

module IntentSpec = struct
  include Labels.IntentSpec

  let to_short_string = function
    | In    -> mkstr 0
    | Out   -> mkstr 1
    | Inout -> mkstr 2

end

module AttrSpec = struct
  include Labels.AttrSpec

  let to_short_string = function
    | Parameter   -> mkstr 0
    | Public      -> mkstr 1
    | Private     -> mkstr 2
    | Allocatable -> mkstr 3
    | Dimension   -> mkstr 4
    | External    -> mkstr 5
    | Intrinsic   -> mkstr 6
    | Optional    -> mkstr 7
    | Pointer     -> mkstr 8
    | Save        -> mkstr 9
    | Target      -> mkstr 10
    | Intent i    -> catstr [mkstr 11; IntentSpec.to_short_string i]

    | Asynchronous -> mkstr 13
    | Bind         -> mkstr 14
    | Protected    -> mkstr 15
    | Value        -> mkstr 16
    | Volatile     -> mkstr 17

    | Automatic    -> mkstr 18
    | Static       -> mkstr 19

    | Codimension  -> mkstr 20
    | Contiguous   -> mkstr 21

    | Device   -> mkstr 22
    | Managed  -> mkstr 23
    | Constant -> mkstr 24
    | Shared   -> mkstr 25
    | Pinned   -> mkstr 26
    | Texture  -> mkstr 27

end

module AccessSpec = struct
  include Labels.AccessSpec

  let to_short_string = function
    | Private -> mkstr 0
    | Public  -> mkstr 1

end

module TypeAttrSpec = struct
  include Labels.TypeAttrSpec

  let to_short_string = function
    | Abstract  -> mkstr 0
    | Bind      -> mkstr 1
    | Extends n -> combo 2 [n]
    | Private   -> mkstr 3
    | Public    -> mkstr 4

end

module Stmt = struct
  include Labels.Stmt

  let _to_short_string ?(ignore_identifiers_flag=false) =
    let combo2 = combo2 ~ignore_identifiers_flag in function
    | AllocatableStmt          -> mkstr2 0
    | AllocateStmt             -> mkstr2 1
    | ArithmeticIfStmt         -> mkstr2 2
    | AssignedGotoStmt         -> mkstr2 3
    | AssignmentStmt           -> mkstr2 4
    | BackspaceStmt            -> mkstr2 5
    | CloseStmt                -> mkstr2 6
    | CommonStmt               -> mkstr2 7
    | ComponentDefStmt         -> mkstr2 8
    | ComputedGotoStmt         -> mkstr2 9
    | ContainsStmt             -> mkstr2 10
    | ContinueStmt             -> mkstr2 11
    | DataStmt                 -> mkstr2 12
    | DeallocateStmt           -> mkstr2 13
    | DimensionStmt            -> mkstr2 14
    | EndStmt                  -> mkstr2 15
    | EndfileStmt              -> mkstr2 16
    | EndInterfaceStmt         -> mkstr2 17
    | EquivalenceStmt          -> mkstr2 18
    | ExternalStmt             -> mkstr2 19
    | ForallStmt               -> mkstr2 20
    | FormatStmt               -> mkstr2 21
    | GotoStmt                 -> mkstr2 22
    | IfStmt                   -> mkstr2 23
    | ImplicitStmt             -> mkstr2 24
    | InquireStmt              -> mkstr2 25
    | IntentStmt               -> mkstr2 26
    | InterfaceStmt n_opt      -> combo2 27 (opt_to_list n_opt)
    | IntrinsicStmt            -> mkstr2 28
    | ProcedureStmt            -> mkstr2 29
    | NamelistStmt             -> mkstr2 30
    | NullifyStmt              -> mkstr2 31
    | OpenStmt                 -> mkstr2 32
    | OptionalStmt             -> mkstr2 33
    | ParameterStmt            -> mkstr2 34
    | PauseStmt                -> mkstr2 35
    | PointerAssignmentStmt    -> mkstr2 36
    | PointerStmt              -> mkstr2 37
    | PrintStmt                -> mkstr2 38
    | PrivateStmt              -> mkstr2 39
    | SequenceStmt             -> mkstr2 40
    | ReadStmt                 -> mkstr2 41
    | ReturnStmt               -> mkstr2 42
    | RewindStmt               -> mkstr2 43
    | SaveStmt                 -> mkstr2 44
    | StopStmt                 -> mkstr2 45
    | TargetStmt               -> mkstr2 46
    | TypeDeclarationStmt ns   -> combo2 47 ns
    | WhereStmt                -> mkstr2 48
    | WriteStmt                -> mkstr2 49

    | CallStmt n               -> combo2 50 [n]
    | DerivedTypeStmt n        -> combo2 51 [n]
    | EntryStmt n              -> combo2 52 [n]
    | FunctionStmt n           -> combo2 53 [n]
    | ModuleStmt n             -> combo2 54 [n]
    | ProgramStmt n            -> combo2 55 [n]
    | StmtFunctionStmt n       -> combo2 56 [n]
    | SubroutineStmt n         -> combo2 57 [n]
    | UseStmt n                -> combo2 58 [n]

    | BlockDataStmt n_opt       -> combo2 59 (opt_to_list n_opt)
    | CaseStmt n_opt            -> combo2 60 (opt_to_list n_opt)
    | CycleStmt n_opt           -> combo2 61 (opt_to_list n_opt)
    | ElseIfStmt n_opt          -> combo2 62 (opt_to_list n_opt)
    | ElseStmt n_opt            -> combo2 63 (opt_to_list n_opt)
    | ElsewhereStmt n_opt       -> combo2 64 (opt_to_list n_opt)
    | EndBlockDataStmt n_opt    -> combo2 65 (opt_to_list n_opt)
    | EndDoStmt n_opt           -> combo2 66 (opt_to_list n_opt)
    | EndForallStmt n_opt       -> combo2 67 (opt_to_list n_opt)
    | EndFunctionStmt n_opt     -> combo2 68 (opt_to_list n_opt)
    | EndIfStmt n_opt           -> combo2 69 (opt_to_list n_opt)
    | EndModuleStmt n_opt       -> combo2 70 (opt_to_list n_opt)
    | EndProgramStmt n_opt      -> combo2 71 (opt_to_list n_opt)
    | EndSelectStmt n_opt       -> combo2 72 (opt_to_list n_opt)
    | EndSubroutineStmt n_opt   -> combo2 73 (opt_to_list n_opt)
    | EndTypeStmt n_opt         -> combo2 74 (opt_to_list n_opt)
    | EndWhereStmt n_opt        -> combo2 75 (opt_to_list n_opt)
    | ExitStmt n_opt            -> combo2 76 (opt_to_list n_opt)
    | ForallConstructStmt n_opt -> combo2 77 (opt_to_list n_opt)
    | IfThenStmt n_opt          -> combo2 78 (opt_to_list n_opt)
    | SelectCaseStmt n_opt      -> combo2 79 (opt_to_list n_opt)
    | WhereConstructStmt n_opt  -> combo2 80 (opt_to_list n_opt)

    | AccessStmt a                -> catstr [mkstr2 81; AccessSpec.to_short_string a]
    | AssignStmt l                -> combo2 82 [l]
    | DoStmt(n_opt, l_opt, v_opt) ->
        combo2 83 ((opt_to_list n_opt) @ (opt_to_list l_opt) @ (opt_to_list v_opt))

    | PpMacroStmt n               -> combo2 84 [n]

    | StructureStmt n_opt         -> combo2 85 (opt_to_list n_opt)
    | EndStructureStmt            -> mkstr2 86
    | UnionStmt                   -> mkstr2 87
    | EndUnionStmt                -> mkstr2 88
    | MapStmt                     -> mkstr2 89
    | EndMapStmt                  -> mkstr2 90
    | RecordStmt                  -> mkstr2 91

    | AsynchronousStmt -> mkstr2 92
    | BindStmt         -> mkstr2 93
    | ProtectedStmt    -> mkstr2 94
    | ValueStmt        -> mkstr2 95
    | VolatileStmt     -> mkstr2 96

    | AbstractInterfaceStmt -> mkstr2 97
    | ImportStmt            -> mkstr2 98

    | PpMacroId _           -> mkstr2 99

    | AcceptStmt     -> mkstr2 100
    | DecodeStmt     -> mkstr2 101
    | DefineFileStmt -> mkstr2 102
    | DeleteStmt     -> mkstr2 103
    | EncodeStmt     -> mkstr2 104
    | FindStmt       -> mkstr2 105
    | RewriteStmt    -> mkstr2 106
    | TypeStmt       -> mkstr2 107
    | UnlockStmt     -> mkstr2 108
    | VirtualStmt    -> mkstr2 109

    | AssociateStmt n_opt             -> combo2 110 (opt_to_list n_opt)
    | BlockStmt n_opt                 -> combo2 111 (opt_to_list n_opt)
    | CriticalStmt n_opt              -> combo2 112 (opt_to_list n_opt)
    | EndAssociateStmt n_opt          -> combo2 113 (opt_to_list n_opt)
    | EndEnumStmt                     -> mkstr2 114
    | EndBlockStmt n_opt              -> combo2 115 (opt_to_list n_opt)
    | EndCriticalStmt n_opt           -> combo2 116 (opt_to_list n_opt)
    | EnumDefStmt                     -> mkstr2 117
    | EnumeratorDefStmt               -> mkstr2 118
    | FlushStmt                       -> mkstr2 119
    | BindingPrivateStmt              -> mkstr2 120
    | FinalProcedureStmt              -> mkstr2 121
    | TypeBoundGenericStmt            -> mkstr2 122
    | ProcComponentDefStmt            -> mkstr2 123
    | ProcedureDeclarationStmt        -> mkstr2 124
    | SelectTypeStmt n_opt            -> combo2 125 (opt_to_list n_opt)
    | TypeIsTypeGuardStmt n_opt       -> combo2 126 (opt_to_list n_opt)
    | ClassIsTypeGuardStmt n_opt      -> combo2 127 (opt_to_list n_opt)
    | ClassDefaultTypeGuardStmt n_opt -> combo2 128 (opt_to_list n_opt)
    | EndSelectTypeStmt n_opt         -> combo2 129 (opt_to_list n_opt)
    | WaitStmt                        -> mkstr2 130
    | TypeBoundProcedureStmt n_opt    -> combo2 131 (opt_to_list n_opt)
    | ErrorStopStmt                   -> mkstr2 132
    | CodimensionStmt                 -> mkstr2 133
    | ContiguousStmt                  -> mkstr2 134
    | LockStmt                        -> mkstr2 135
    | SyncAllStmt                     -> mkstr2 136
    | SyncImagesStmt                  -> mkstr2 137
    | SyncMemoryStmt                  -> mkstr2 138
    | SubmoduleStmt(a, p_opt, n)      -> combo2 139 (a :: (opt_to_list p_opt) @ [n])
    | EndSubmoduleStmt n_opt          -> combo2 140 (opt_to_list n_opt)
    | AutomaticStmt                   -> mkstr2 141
    | StaticStmt                      -> mkstr2 142
    | MpSubprogramStmt n              -> combo2 143 [n]
    | EndMpSubprogramStmt n_opt       -> combo2 144 (opt_to_list n_opt)

  let to_short_string ?(ignore_identifiers_flag=false) = function
    | Labeled(lab, stmt) -> catstr ((_to_short_string stmt)::(encode_ids ~ignore_identifiers_flag [lab]))
    | Nonlabeled stmt -> _to_short_string stmt

end

module Ambiguous = struct
  include Labels.Ambiguous

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Tuple            -> mkstr 0
    | Primary          -> mkstr 1
    | Subobject        -> mkstr 2
    | TripletOrRange   -> mkstr 3
    | First            -> mkstr 4
    | Second           -> mkstr 5
    | DataStmtConstant -> mkstr 6
    | Assumed          -> mkstr 7
    | Deferred         -> mkstr 8
    | AssumedSize      -> mkstr 9

    | Designator n      -> combo 10 [n]
    | NamedTuple n      -> combo 11 [n]
    | NamedDataObject n -> combo 12 [n]

    | ArrayAccess n -> combo 13 [n]
(*
    | PpExpr n     -> combo 14 [n]
    | PpTypeSpec n -> combo 15 [n]
*)
    | GenericSpecOrUseName n -> combo 16 [n]

end

module Constant = struct
  include Labels.Constant

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | BozLiteralConstant s         -> catstr [mkstr 0; s]
    | CharLiteralConstant s        -> catstr [mkstr 1; s]
    | IntLiteralConstant s         -> catstr [mkstr 2; s]
    | LogicalLiteralConstant s     -> catstr [mkstr 3; s]
    | RealLiteralConstant s        -> catstr [mkstr 4; s]
    | ComplexLiteralConstant(r, i) -> catstr [mkstr 5; r; i]
    | NamedConstant n              -> combo 6 [n]
    | HollerithConstant s          -> catstr [mkstr 7; s]
    | PpMacroConstant n            -> combo 8 [n]
    | SignedIntLiteralConstant s   -> catstr [mkstr 9; s]
    | SignedRealLiteralConstant s  -> catstr [mkstr 10; s]

end

module IntrinsicOperator = struct
  include Labels.IntrinsicOperator

  let to_short_string = function
    | AND    -> mkstr 0
    | OR     -> mkstr 1
    | NOT    -> mkstr 2
    | EQV    -> mkstr 3
    | GE     -> mkstr 4
    | GT     -> mkstr 5
    | LE     -> mkstr 6
    | LT     -> mkstr 7
    | EQ     -> mkstr 8
    | NE     -> mkstr 9
    | NEQV   -> mkstr 10
    | Mult   -> mkstr 11
    | Div    -> mkstr 12
    | Power  -> mkstr 13
    | Add    -> mkstr 14
    | Subt   -> mkstr 15
    | Concat -> mkstr 16
    | Eq     -> mkstr 17
    | Neq    -> mkstr 18
    | Lt     -> mkstr 19
    | Le     -> mkstr 20
    | Gt     -> mkstr 21
    | Ge     -> mkstr 22
    | Id     -> mkstr 23
    | Neg    -> mkstr 24
end

module DefinedOperator = struct
  include Labels.DefinedOperator

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | DefinedOp s       -> combo 0 [s]
    | DefinedUnaryOp s  -> combo 1 [s]
    | DefinedBinaryOp s -> combo 2 [s]

end

module OclDirective = struct
  include Labels.OclDirective

  let align_to_short_string = function
    | Aaligned   -> mkstr 0
    | Aunaligned -> mkstr 1

  let prefetch_spec_to_short_string = function
    | Pauto -> mkstr 0
    | Psoft -> mkstr 1

  let listv_scope_to_short_string = function
    | Sall  -> mkstr 0
    | Sthen -> mkstr 1
    | Selse -> mkstr 2

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | ERROR                            -> mkstr 0
    | ArrayFusion                      -> mkstr 2
    | EndArrayFusion                   -> mkstr 3
    | Eval                             -> mkstr 4
    | Noeval                           -> mkstr 5
    | Fltld                            -> mkstr 6
    | Nofltld                          -> mkstr 7
    | FpRelaxed                        -> mkstr 8
    | NofpRelaxed                      -> mkstr 9
    | Nomfunc                          -> mkstr 10
    | LoopNofusion                     -> mkstr 11
    | Preex                            -> mkstr 12
    | Nopreex                          -> mkstr 13
    | Prefetch                         -> mkstr 14
    | Noprefetch                       -> mkstr 15
    | PrefetchInfer                    -> mkstr 16
    | PrefetchNoinfer                  -> mkstr 17
    | Nostriping                       -> mkstr 18
    | Swp                              -> mkstr 19
    | Noswp                            -> mkstr 20
    | UnrollFull                       -> mkstr 21
    | Nounroll                         -> mkstr 22
    | Nosimd                           -> mkstr 23
    | EndCacheSectorSize               -> mkstr 24
    | EndCacheSubsector                -> mkstr 25
    | LoopNofission                    -> mkstr 26
    | Noxfill                          -> mkstr 27
    | PrefetchStrong                   -> mkstr 28
    | PrefetchNostrong                 -> mkstr 29
    | PrefetchStrongL2                 -> mkstr 30
    | PrefetchNostrongL2               -> mkstr 31
    | FpContract                       -> mkstr 32
    | NofpContract                     -> mkstr 33
    | LoopNoblocking                   -> mkstr 34
    | Nouxsimd                         -> mkstr 35
    | ArrayPrivate                     -> mkstr 36
    | NoarrayPrivate                   -> mkstr 37
    | Noalias                          -> mkstr 38
    | Serial                           -> mkstr 39
    | Parallel                         -> mkstr 40
    | ParallelStrong                   -> mkstr 41
    | Reduction                        -> mkstr 42
    | Noreduction                      -> mkstr 43
    | LoopNointerchange                -> mkstr 44

    | Noarraypad n                     -> combo 45 [n]

    | ArraySubscript ns                -> combo 46 ns
    | LoopInterchange ns               -> combo 47 ns
    | Novrec ns                        -> combo 48 ns
    | CacheSubsectorAssign ns          -> combo 49 ns
    | Norecurrence ns                  -> combo 50 ns
    | Independent ns                   -> combo 51 ns
    | Temp ns                          -> combo 52 ns

    | PrefetchIteration i              -> catstr [mkstr 53; string_of_int i]
    | PrefetchIterationL2 i            -> catstr [mkstr 54; string_of_int i]
    | LoopBlocking i                   -> catstr [mkstr 55; string_of_int i]
    | Unroll i                         -> catstr [mkstr 56; string_of_int i]

    | CacheSectorSize is               -> catstr ((mkstr 57)::(List.map string_of_int is))

    | Mfunc i_opt                      -> catstr ((mkstr 58)::(opt_to_list_map string_of_int i_opt))
    | Striping i_opt                   -> catstr ((mkstr 59)::(opt_to_list_map string_of_int i_opt))
    | FissionPoint i_opt               -> catstr ((mkstr 60)::(opt_to_list_map string_of_int i_opt))
    | Xfill i_opt                      -> catstr ((mkstr 61)::(opt_to_list_map string_of_int i_opt))

    | Simd a_opt                       -> catstr ((mkstr 62)::(opt_to_list_map align_to_short_string a_opt))
    | Uxsimd a_opt                     -> catstr ((mkstr 63)::(opt_to_list_map align_to_short_string a_opt))

    | ArrayMerge(n_opt, ns)            -> catstr ((mkstr 64)::(string_opt_to_string n_opt)::ns)
    | PrefetchCacheLevel lv            -> combo 65 [num_or_name_to_string lv]
    | PrefetchRead(lv_opt, st_opt)     -> catstr ((mkstr 66)::((opt_to_list_map num_or_name_to_string lv_opt) @ (opt_to_list_map string_of_int st_opt)))
    | PrefetchWrite(lv_opt, st_opt)    -> catstr ((mkstr 67)::((opt_to_list_map num_or_name_to_string lv_opt) @ (opt_to_list_map string_of_int st_opt)))
    | PrefetchSequential s_opt         -> catstr ((mkstr 68)::(opt_to_list_map prefetch_spec_to_short_string s_opt))
    | RelOp op                         -> catstr [mkstr 69; IntrinsicOperator.to_short_string op]

    | LoopPartSimd                     -> mkstr 70
    | LoopNopartSimd                   -> mkstr 71
    | Shortloop i                      -> catstr [mkstr 72; string_of_int i]
    | Noshortloop                      -> mkstr 73
    | SimdListv s_opt                  -> catstr ((mkstr 74)::(opt_to_list_map listv_scope_to_short_string s_opt))
    | Unswitching                      -> mkstr 75

    | LoopPartParallel                 -> mkstr 76
    | LoopNopartParallel               -> mkstr 77
    | FirstPrivate ns                  -> combo 78 ns
    | LastPrivate ns                   -> combo 79 ns
    | TempPrivate ns                   -> combo 80 ns
    | ParallelCyclic i_opt             -> catstr ((mkstr 81)::(opt_to_list_map string_of_int i_opt))

end

module Dec = struct

  module Directive = struct
    include Labels.Dec.Directive

    let to_short_string = function
      | Alias(i, e)          -> combo 0 [i;e]
      | Assume               -> mkstr 1
      | Assume_aligned       -> mkstr 2
      | Attributes           -> mkstr 3
      | Declare              -> mkstr 4
      | Nodeclare            -> mkstr 5
      | Define n             -> combo 6 [n]
      | Undefine n           -> combo 7 [n]
      | DistributePoint      -> mkstr 8
      | Fixedformlinesize i  -> combo 9 [i]
      | Fma                  -> mkstr 10
      | Nofma                -> mkstr 11
      | Freeform             -> mkstr 12
      | Nofreeform           -> mkstr 13
      | Ident s              -> combo 14 [s]
      | If                   -> mkstr 15
      | IfDefined n          -> combo 16 [n]
      | Inline b             -> catstr [mkstr 17; (if b then mkstr 1 else mkstr 0)]
      | Forceinline b        -> catstr [mkstr 18; (if b then mkstr 1 else mkstr 0)]
      | Noinline             -> mkstr 19
      | Integer i            -> combo 20 [i]
      | Ivdep o              -> combo 21 [o]
      | Init_dep_fwd         -> mkstr 22
      | LoopCount il         -> combo 23 (List.map string_of_int il)
      | Message s            -> combo 24 [s]
      | Nofusion             -> mkstr 25
      | Objcomment s         -> combo 26 [s]
      | Optimize i           -> combo 27 [i]
      | Nooptimize           -> mkstr 28
      | Options ol           -> combo 29 ol
      | Pack i               -> combo 30 [i]
      | Parallel             -> mkstr 31
      | Noparallel           -> mkstr 32
      | Prefetch             -> mkstr 33
      | Noprefetch           -> mkstr 34
      | Psect n              -> combo 35 [n]
      | Real i               -> combo 36 [i]
      | Simd                 -> mkstr 37
      | Strict               -> mkstr 38
      | Nostrict             -> mkstr 39
      | Unroll i_opt         -> combo 40 [int_opt_to_string ~prefix:"" i_opt]
      | Nounroll             -> mkstr 41
      | Unroll_and_jam i_opt -> combo 42 [int_opt_to_string ~prefix:"" i_opt]
      | Nounroll_and_jam     -> mkstr 43
      | Vector               -> mkstr 44
      | Novector             -> mkstr 45
      | Elseif               -> mkstr 46
      | Else                 -> mkstr 47
      | Endif                -> mkstr 48
      | EndOptions           -> mkstr 49
      | Block_loop           -> mkstr 50
      | Noblock_loop         -> mkstr 51
      | Code_align i         -> combo 52 [string_of_int i]
  end

  module Clause = struct
    include Labels.Dec.Clause

    let to_short_string = function
      | Always          -> mkstr 0
      | Assert          -> mkstr 1
      | Aligned         -> mkstr 2
      | Unaligned       -> mkstr 3
      | Temporal        -> mkstr 4
      | Nontemporal     -> mkstr 5
      | Vecremainder    -> mkstr 6
      | Novecremainder  -> mkstr 7
      | Noassert        -> mkstr 8
      | Firstprivate    -> mkstr 9
      | Lastprivate     -> mkstr 10
      | Linear          -> mkstr 11
      | Private         -> mkstr 12
      | Reduction       -> mkstr 13
      | Vectorlength il -> combo 14 (List.map string_of_int il)
      | Vectorlengthfor -> mkstr 15
      | Num_threads     -> mkstr 16
      | Mask            -> mkstr 17
      | Nomask          -> mkstr 18
      | Processor p     -> combo 19 [p]
      | Uniform         -> mkstr 20
      | Profitable      -> mkstr 21
      | Cost            -> mkstr 22
      | Factor          -> mkstr 23
      | Level ll        -> combo 24 (List.map Labels.Dec.level_to_string ll)
  end

  module Attribute = struct
    include Labels.Dec.Attribute

    let to_short_string = function
      | Alias s                  -> combo 0 [s]
      | Align i                  -> combo 1 [string_of_int i]
      | Allocatable              -> mkstr 2
      | Array_null               -> mkstr 3
      | C                        -> mkstr 4
      | Code_align i             -> combo 5 [string_of_int i]
      | Concurrency_safe         -> mkstr 6
      | Cvf                      -> mkstr 7
      | Decorate                 -> mkstr 8
      | Default                  -> mkstr 9
      | Dllexport                -> mkstr 10
      | Dllimport                -> mkstr 11
      | Extern                   -> mkstr 12
      | Fastmem                  -> mkstr 13
      | Forceinline              -> mkstr 14
      | Ignore_loc               -> mkstr 15
      | Inline                   -> mkstr 16
      | Mixed_str_len_arg        -> mkstr 17
      | No_arg_check             -> mkstr 18
      | Noclone                  -> mkstr 19
      | Noinline                 -> mkstr 20
      | Offload n                -> combo 21 [n]
      | Optimization_parameter s -> combo 22 [s]
      | Reference                -> mkstr 23
      | Stdcall                  -> mkstr 24
      | Value                    -> mkstr 25
      | Varying                  -> mkstr 26
      | Vector                   -> mkstr 27

  end

  type t = Labels.Dec.t

  let to_string = Labels.Dec.to_string

  let to_simple_string = Labels.Dec.to_simple_string

  let to_tag = Labels.Dec.to_tag

  let get_name _ = raise Not_found

  let get_name_opt _ = None

  let to_short_string = function
    | Labels.Dec.VarExpr         -> mkstr 0
    | Labels.Dec.Align s         -> combo 1 [s]
    | Labels.Dec.Wrt             -> mkstr 2
    | Labels.Dec.Nowrt           -> mkstr 3
    | Labels.Dec.PrefetchHint    -> mkstr 4
    | Labels.Dec.PrefetchHintAll -> mkstr 5
    | Labels.Dec.Max i           -> combo 6 [string_of_int i]
    | Labels.Dec.Min i           -> combo 7 [string_of_int i]
    | Labels.Dec.Avg i           -> combo 8 [string_of_int i]

end

module Xlf = struct

  module Directive = struct
    include Labels.Xlf.Directive

    let high_or_low_to_short_string = function
      | VeryHigh -> mkstr 0
      | VeryLow  -> mkstr 1

    let source_to_short_string = function
      | Fixed i_opt -> catstr [mkstr 0; int_opt_to_string i_opt]
      | Free        -> mkstr 1
      | FreeF90     -> mkstr 2
      | FreeIBM     -> mkstr 3

    let to_short_string = function
      | Align i               -> combo 0 [i]
      | Assert                -> mkstr 1
      | BlockLoop             -> mkstr 2
      | Cncall                -> mkstr 3
      | Collapse              -> mkstr 4
      | Eject                 -> mkstr 5
      | ExecutionFrequency hl -> catstr [mkstr 6; high_or_low_to_short_string hl]
      | ExpectedValue n       -> combo 7 [n]
      | FunctraceXlfCatch     -> mkstr 8
      | FunctraceXlfEnter     -> mkstr 9
      | FunctraceXlfExit      -> mkstr 10
      | IgnoreTkr             -> mkstr 11
      | Independent           -> mkstr 12
      | Loopid n              -> combo 13 [n]
      | MemDelay c            -> combo 14 [c]
      | New                   -> mkstr 15
      | Nofunctrace           -> mkstr 16
      | Nosimd                -> mkstr 17
      | Novector              -> mkstr 18
      | Permutation           -> mkstr 19
      | Snapshot              -> mkstr 20
      | Sourceform s          -> catstr [mkstr 21; source_to_short_string s]
      | StreamUnroll          -> mkstr 22
      | Subscriptorder        -> mkstr 23
      | Unroll                -> mkstr 24
      | UnrollAndFuse         -> mkstr 25
      | Process               -> mkstr 26

  end

  module Assertion = struct
    include Labels.Xlf.Assertion

    let to_short_string = function
      | Itercnt    -> mkstr 0
      | Minitercnt -> mkstr 1
      | Maxitercnt -> mkstr 2
      | Nodeps     -> mkstr 3

  end

  type t = Labels.Xlf.t

  let to_string = Labels.Xlf.to_string

  let to_simple_string = Labels.Xlf.to_simple_string

  let to_tag = Labels.Xlf.to_tag

  let get_name = Labels.Xlf.get_name

  let get_name_opt = Labels.Xlf.get_name_opt

  let to_short_string = function
    | Labels.Xlf.ERROR                      -> mkstr 0
    | Labels.Xlf.CollapseArray n            -> combo 1 [n]
    | Labels.Xlf.SubscriptorderArray(n, il) -> combo 2 (n :: il)
    | Labels.Xlf.NewClause                  -> mkstr 3
    | Labels.Xlf.ReductionClause            -> mkstr 4
    | Labels.Xlf.Option n                   -> combo 5 [n]

end

module OmpClause = struct
  include Labels.OmpClause

  let data_sharing_attr_to_short_string = function
    | Private      -> mkstr 0
    | Firstprivate -> mkstr 1
    | Shared       -> mkstr 2
    | None_        -> mkstr 3

  let kind_to_short_string = function
    | Static  -> mkstr 0
    | Dynamic -> mkstr 1
    | Guided  -> mkstr 2
    | Auto    -> mkstr 3
    | Runtime -> mkstr 4

  let policy_to_short_string = function
    | Master -> mkstr 0
    | Close  -> mkstr 1
    | Spread -> mkstr 2

  let map_type_to_short_string = function
    | Alloc  -> mkstr 0
    | To     -> mkstr 1
    | From   -> mkstr 2
    | Tofrom -> mkstr 3

  let dependence_type_to_short_string = function
    | In    -> mkstr 0
    | Out   -> mkstr 1
    | Inout -> mkstr 2

  let to_short_string = function
    | If                -> mkstr 0
    | Num_threads       -> mkstr 1
    | Default _         -> mkstr 2
    | Lastprivate       -> mkstr 3
    | Copyin            -> mkstr 4
    | Reduction         -> mkstr 5
    | Collapse          -> mkstr 6
    | Ordered           -> mkstr 7
    | Copyprivate       -> mkstr 8
    | Nowait            -> mkstr 9
    | Final             -> mkstr 10
    | Untied            -> mkstr 11
    | Mergeable         -> mkstr 12
    | DataSharingAttr a -> catstr [mkstr 13; data_sharing_attr_to_simple_string a]
    | Schedule k        -> catstr [mkstr 14; kind_to_simple_string k]

    | Proc_bind p       -> catstr [mkstr 15; policy_to_short_string p]
    | Linear b          -> catstr [mkstr 16; if b then mkstr 1 else mkstr 0]
    | Map t_opt         -> catstr ((mkstr 17)::(opt_to_list_map map_type_to_simple_string t_opt))
    | Safelen           -> mkstr 18
    | Simdlen           -> mkstr 19
    | Aligned b         -> catstr [mkstr 20; if b then mkstr 1 else mkstr 0]
    | Uniform           -> mkstr 21
    | Inbranch          -> mkstr 22
    | Notinbranch       -> mkstr 23
    | Depend t          -> catstr [mkstr 24; dependence_type_to_short_string t]
    | Device            -> mkstr 25
    | Dist_schedule k   -> catstr [mkstr 26; kind_to_simple_string k]
    | Initializer       -> mkstr 27
    | Num_teams         -> mkstr 28
    | Thread_limit      -> mkstr 29

    | ERROR -> mkstr 30
end

module OmpDirective = struct
  include Labels.OmpDirective

  let atomic_sub_to_short_string = function
    | Read    -> mkstr 0
    | Write   -> mkstr 1
    | Capture -> mkstr 2
    | Update  -> mkstr 3

  let construct_type_to_short_string = function
    | C_parallel  -> mkstr 0
    | C_sections  -> mkstr 1
    | C_do        -> mkstr 2
    | C_taskgroup -> mkstr 3

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | ERROR                -> mkstr 0
    | Barrier              -> mkstr 1
    | Do false             -> mkstr 2
    | Flush                -> mkstr 3
    | Master               -> mkstr 4
    | Ordered              -> mkstr 5
    | Parallel             -> mkstr 6
    | ParallelDo false     -> mkstr 7
    | ParallelSections     -> mkstr 8
    | ParallelWorkshare    -> mkstr 9
    | Section              -> mkstr 10
    | Sections             -> mkstr 11
    | Single               -> mkstr 12
    | Task                 -> mkstr 13
    | Taskwait             -> mkstr 14
    | Taskyield            -> mkstr 15
    | Threadprivate        -> mkstr 16
    | Workshare            -> mkstr 17
    | EndAtomic            -> mkstr 18
    | EndDo false          -> mkstr 19
    | EndMaster            -> mkstr 20
    | EndOrdered           -> mkstr 21
    | EndParallel          -> mkstr 22
    | EndSections          -> mkstr 23
    | EndSingle            -> mkstr 24
    | EndTask              -> mkstr 25
    | EndWorkshare         -> mkstr 26
    | EndParallelDo false  -> mkstr 27
    | EndParallelSections  -> mkstr 28
    | EndParallelWorkshare -> mkstr 29
    | Atomic(a_opt, false) -> catstr ((mkstr 30)::(opt_to_list_map atomic_sub_to_simple_string a_opt))
    | Critical n_opt       -> combo 31 (opt_to_list n_opt)
    | EndCritical n_opt    -> combo 32 (opt_to_list n_opt)

    | Do true              -> mkstr 33
    | EndDo true           -> mkstr 34
    | ParallelDo true      -> mkstr 35
    | EndParallelDo true   -> mkstr 36
    | Atomic(a_opt, true)  -> catstr ((mkstr 37)::(opt_to_list_map atomic_sub_to_simple_string a_opt))
    | Simd                 -> mkstr 38
    | EndSimd              -> mkstr 39
    | DeclareSimd n        -> combo 40 [n]
    | Target               -> mkstr 41
    | EndTarget            -> mkstr 42
    | TargetData           -> mkstr 43
    | EndTargetData        -> mkstr 44
    | TargetUpdate         -> mkstr 45
    | DeclareTarget        -> mkstr 46
    | Teams                -> mkstr 47
    | EndTeams             -> mkstr 48
    | Taskgroup            -> mkstr 49
    | EndTaskgroup         -> mkstr 50
    | Cancel c             -> catstr [mkstr 51; construct_type_to_short_string c]
    | CancellationPoint c  -> catstr [mkstr 52; construct_type_to_short_string c]
    | DeclareReduction     -> mkstr 53
    | TargetTeams          -> mkstr 54
    | EndTargetTeams       -> mkstr 55
    | Distribute true                         -> mkstr 56
    | EndDistribute true                      -> mkstr 57
    | DistributeParallelDo true               -> mkstr 58
    | EndDistributeParallelDo true            -> mkstr 59
    | TeamsDistribute true                    -> mkstr 60
    | EndTeamsDistribute true                 -> mkstr 61
    | TargetTeamsDistribute true              -> mkstr 62
    | EndTargetTeamsDistribute true           -> mkstr 63
    | TeamsDistributeParallelDo true          -> mkstr 64
    | EndTeamsDistributeParallelDo true       -> mkstr 65
    | TargetTeamsDistributeParallelDo true    -> mkstr 66
    | EndTargetTeamsDistributeParallelDo true -> mkstr 67
    | Distribute false                         -> mkstr 68
    | EndDistribute false                      -> mkstr 69
    | DistributeParallelDo false               -> mkstr 70
    | EndDistributeParallelDo false            -> mkstr 71
    | TeamsDistribute false                    -> mkstr 72
    | EndTeamsDistribute false                 -> mkstr 73
    | TargetTeamsDistribute false              -> mkstr 74
    | EndTargetTeamsDistribute false           -> mkstr 75
    | TeamsDistributeParallelDo false          -> mkstr 76
    | EndTeamsDistributeParallelDo false       -> mkstr 77
    | TargetTeamsDistributeParallelDo false    -> mkstr 78
    | EndTargetTeamsDistributeParallelDo false -> mkstr 79

end

module OmpConstruct = struct
  include Labels.OmpConstruct

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
      | Atomic(a_opt, false) -> catstr ((mkstr 0)::(opt_to_list_map OmpDirective.atomic_sub_to_simple_string a_opt))
      | Critical n_opt    -> combo 1 (opt_to_list n_opt)
      | Do false          -> mkstr 2
      | Master            -> mkstr 3
      | Ordered           -> mkstr 4
      | Parallel          -> mkstr 5
      | Sections          -> mkstr 6
      | Single            -> mkstr 7
      | Task              -> mkstr 8
      | Workshare         -> mkstr 9
      | ParallelDo false  -> mkstr 10
      | ParallelSections  -> mkstr 11
      | ParallelWorkshare -> mkstr 12

      | Atomic(a_opt, true) -> catstr ((mkstr 13)::(opt_to_list_map OmpDirective.atomic_sub_to_simple_string a_opt))
      | Do true           -> mkstr 14
      | ParallelDo true   -> mkstr 15
      | Simd              -> mkstr 16
      | Target            -> mkstr 17
      | TargetData        -> mkstr 18
      | Teams             -> mkstr 19
      | TargetTeams       -> mkstr 20
      | Taskgroup         -> mkstr 21
      | Distribute true                      -> mkstr 23
      | DistributeParallelDo true            -> mkstr 24
      | TeamsDistribute true                 -> mkstr 25
      | TargetTeamsDistribute true           -> mkstr 26
      | TeamsDistributeParallelDo true       -> mkstr 27
      | TargetTeamsDistributeParallelDo true -> mkstr 28
      | Distribute false                      -> mkstr 30
      | DistributeParallelDo false            -> mkstr 31
      | TeamsDistribute false                 -> mkstr 32
      | TargetTeamsDistribute false           -> mkstr 33
      | TeamsDistributeParallelDo false       -> mkstr 34
      | TargetTeamsDistributeParallelDo false -> mkstr 35

end

module AccClause = struct
  include Labels.AccClause

  let to_short_string = function
    | Async              -> mkstr 0
    | Auto               -> mkstr 1
    | Bind               -> mkstr 2
    | Collapse           -> mkstr 3
    | Copy               -> mkstr 4
    | Copyin             -> mkstr 5
    | Copyout            -> mkstr 6
    | Create             -> mkstr 7
    | DefaultNone        -> mkstr 8
    | DefaultPresent     -> mkstr 9
    | Delete             -> mkstr 10
    | Device             -> mkstr 11
    | Deviceptr          -> mkstr 12
    | Device_resident    -> mkstr 13
    | Device_type        -> mkstr 14
    | Device_typeAny     -> mkstr 15
    | Dtype              -> mkstr 16
    | DtypeAny           -> mkstr 17
    | Firstprivate       -> mkstr 18
    | Gang               -> mkstr 19
    | Host               -> mkstr 20
    | If                 -> mkstr 21
    | Independent        -> mkstr 22
    | Link               -> mkstr 23
    | Nohost             -> mkstr 24
    | Num_gangs          -> mkstr 25
    | Num_workers        -> mkstr 26
    | Pcopy              -> mkstr 27
    | Pcopyin            -> mkstr 28
    | Pcopyout           -> mkstr 29
    | Pcreate            -> mkstr 30
    | Present            -> mkstr 31
    | Present_or_copy    -> mkstr 32
    | Present_or_copyin  -> mkstr 33
    | Present_or_copyout -> mkstr 34
    | Present_or_create  -> mkstr 35
    | Private            -> mkstr 36
    | Reduction          -> mkstr 37
    | Self               -> mkstr 38
    | Seq                -> mkstr 39
    | Tile               -> mkstr 40
    | Use_device         -> mkstr 41
    | Vector             -> mkstr 42
    | Vector_length      -> mkstr 43
    | Wait               -> mkstr 44
    | Worker             -> mkstr 45

end

module AccDirective = struct
  include Labels.AccDirective

  let atomic_sub_to_short_string = function
    | Read    -> mkstr 0
    | Write   -> mkstr 1
    | Capture -> mkstr 2
    | Update  -> mkstr 3

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
      | ERROR           -> mkstr 0
      | Atomic a_opt    -> catstr ((mkstr 1)::(opt_to_list_map atomic_sub_to_simple_string a_opt))
      | Parallel        -> mkstr 2
      | Kernels         -> mkstr 3
      | Data            -> mkstr 4
      | EnterData       -> mkstr 5
      | ExitData        -> mkstr 6
      | Host_data       -> mkstr 7
      | Loop            -> mkstr 8
      | Cache           -> mkstr 9
      | Update          -> mkstr 10
      | Wait            -> mkstr 11
      | Routine n_opt   -> combo 12 (opt_to_list n_opt)
      | Declare         -> mkstr 13
      | EndAtomic       -> mkstr 14
      | EndParallel     -> mkstr 15
      | EndKernels      -> mkstr 16
      | EndData         -> mkstr 17
      | EndHost_data    -> mkstr 18
      | ParallelLoop    -> mkstr 19
      | KernelsLoop     -> mkstr 20
      | EndParallelLoop -> mkstr 21
      | EndKernelsLoop  -> mkstr 22

end

module AccConstruct = struct
  include Labels.AccConstruct

  let to_short_string ?(ignore_identifiers_flag=false) =
    let _ = ignore_identifiers_flag in
    (*let combo = combo ~ignore_identifiers_flag in*) function
      | Atomic a_opt -> catstr ((mkstr 0)::(opt_to_list_map AccDirective.atomic_sub_to_simple_string a_opt))
      | Parallel     -> mkstr 1
      | Kernels      -> mkstr 2
      | Data         -> mkstr 3
      | Host_data    -> mkstr 4
      | ParallelLoop -> mkstr 5
      | KernelsLoop  -> mkstr 6
      | Loop         -> mkstr 7

end

module LindaCall = struct
  include Labels.LindaCall

  let to_short_string = function
    | In   -> mkstr 0
    | Inp  -> mkstr 1
    | Rd   -> mkstr 2
    | Rdp  -> mkstr 3
    | Out  -> mkstr 4
    | Eval -> mkstr 5

end

module TypeSpec = struct
  include Labels.TypeSpec

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Character         -> mkstr 0
    | Complex           -> mkstr 1
    | DoublePrecision   -> mkstr 2
    | Integer           -> mkstr 3
    | Logical           -> mkstr 4
    | Real              -> mkstr 5
    | Byte              -> mkstr 6
    | DoubleComplex     -> mkstr 7
    | Type n            -> combo 8 [n]
    | Derived n         -> combo 9 [n]

    | PpMacroTypeSpec n -> combo 10 [n]

    | Class n           -> combo 11 [n]

end

module GenericSpec = struct
  include Labels.GenericSpec

  let record_kind_to_short_string = function
    | RK_formatted   -> mkstr 1
    | RK_unformatted -> mkstr 2
    | RK_weird n     -> combo 3 [n]

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Assignment           -> mkstr 0
    | Name n               -> combo 1 [n]
    | DefinedOperator op   -> catstr [mkstr 2; DefinedOperator.to_short_string op]
    | IntrinsicOperator op -> catstr [mkstr 3; IntrinsicOperator.to_short_string op]
    | Read k               -> catstr [mkstr 4; record_kind_to_short_string k]
    | Write k              -> catstr [mkstr 5; record_kind_to_short_string k]

end

module IoControlSpec = struct
  include Labels.IoControlSpec

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Unit             -> mkstr 0
    | Fmt              -> mkstr 1
    | Rec              -> mkstr 2
    | Iostat           -> mkstr 3
    | Size             -> mkstr 4
    | Advance          -> mkstr 5
    | Nml n            -> combo 6 [n]
    | Err lab          -> combo 7 [lab]
    | End lab          -> combo 8 [lab]
    | Eor lab          -> combo 9 [lab]
    | Iomsg            -> mkstr 10
    | Pos              -> mkstr 11
    | PreconnectedUnit -> mkstr 12

    | Asynchronous     -> mkstr 13
    | Blank            -> mkstr 14
    | Decimal          -> mkstr 15
    | Delim            -> mkstr 16
    | Id               -> mkstr 17
    | Pad              -> mkstr 18
    | Round            -> mkstr 19
    | Sign             -> mkstr 20

    | Num              -> mkstr 21

end

module InquireSpec = struct
  include Labels.InquireSpec

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Unit            -> mkstr 0
    | File            -> mkstr 1
    | Iostat          -> mkstr 2
    | Exist           -> mkstr 3
    | Opened          -> mkstr 4
    | Number          -> mkstr 5
    | Named           -> mkstr 6
    | Name            -> mkstr 7
    | Access          -> mkstr 8
    | Sequential      -> mkstr 9
    | Direct          -> mkstr 10
    | Form            -> mkstr 11
    | Formatted       -> mkstr 12
    | Unformatted     -> mkstr 13
    | Recl            -> mkstr 14
    | Nextrec         -> mkstr 15
    | Blank           -> mkstr 16
    | Position        -> mkstr 17
    | Action          -> mkstr 18
    | Read            -> mkstr 19
    | Write           -> mkstr 20
    | Readwrite       -> mkstr 21
    | Delim           -> mkstr 22
    | Pad             -> mkstr 23
    | Err lab         -> combo 24 [lab]
    | Iomsg           -> mkstr 25
    | Pos             -> mkstr 26

    | Binary          -> mkstr 27
    | Blocksize       -> mkstr 28
    | Buffered        -> mkstr 29
    | Convert         -> mkstr 30
    | Carriagecontrol -> mkstr 31
    | Defaultfile     -> mkstr 32
    | Iofocus         -> mkstr 33
    | Mode            -> mkstr 34
    | Organization    -> mkstr 35
    | Recordsize      -> mkstr 36
    | Recordtype      -> mkstr 37
    | Share           -> mkstr 38

    | Asynchronous -> mkstr 39
    | Decimal      -> mkstr 40
    | Encoding     -> mkstr 41
    | Id           -> mkstr 42
    | Pending      -> mkstr 43
    | Round        -> mkstr 44
    | Sign         -> mkstr 45
    | Size         -> mkstr 46
    | Stream       -> mkstr 47

    | Asynch       -> mkstr 48
    | Strid        -> mkstr 49

end

module ConnectSpec = struct
  include Labels.ConnectSpec

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Unit            -> mkstr 0
    | Iostat          -> mkstr 1
    | File            -> mkstr 2
    | Status          -> mkstr 3
    | Access          -> mkstr 4
    | Form            -> mkstr 5
    | Recl            -> mkstr 6
    | Blank           -> mkstr 7
    | Position        -> mkstr 8
    | Action          -> mkstr 9
    | Delim           -> mkstr 10
    | Pad             -> mkstr 11
    | Err lab         -> combo 12 [lab]
    | Iomsg           -> mkstr 13

    | Associatevariable -> mkstr 14
    | Blocksize         -> mkstr 15
    | Buffercount       -> mkstr 16
    | Buffered          -> mkstr 17
    | Carriagecontrol   -> mkstr 18
    | Convert           -> mkstr 19
    | Defaultfile       -> mkstr 20
    | Dispose           -> mkstr 21
    | Iofocus           -> mkstr 22
    | Maxrec            -> mkstr 23
    | Mode              -> mkstr 24
    | Name              -> mkstr 25
    | Organization      -> mkstr 26
    | Readonly          -> mkstr 27
    | Recordsize        -> mkstr 28
    | Recordtype        -> mkstr 29
    | Share             -> mkstr 30
    | Shared            -> mkstr 31
    | Title             -> mkstr 32
    | Useropen          -> mkstr 33
    | Type              -> mkstr 34

    | Asynchronous -> mkstr 35
    | Decimal      -> mkstr 36
    | Encoding     -> mkstr 37
    | Newunit      -> mkstr 38
    | Round        -> mkstr 39
    | Sign         -> mkstr 40

    | Asynch       -> mkstr 41

end

module CloseSpec = struct
  include Labels.CloseSpec

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Unit    -> mkstr 0
    | Iostat  -> mkstr 1
    | Status  -> mkstr 2
    | Err lab -> combo 3 [lab]
    | Iomsg   -> mkstr 4

    | Dispose -> mkstr 5
    | Type    -> mkstr 6

end

module PositionSpec = struct
  include Labels.PositionSpec

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Unit        -> mkstr 0
    | Iostat      -> mkstr 1
    | Err lab     -> combo 2 [lab]
    | Iomsg       -> mkstr 3

end

module Format = struct
  include Labels.Format

  let to_short_string ?(ignore_identifiers_flag=false) =
    let combo = combo ~ignore_identifiers_flag in function
    | Expr         -> mkstr 0
    | ListDirected -> mkstr 1
    | Label lab    -> combo 2 [lab]

end

module PrefixSpec = struct
  include Labels.PrefixSpec

  let to_short_string = function
    | Recursive  -> mkstr 0
    | Pure       -> mkstr 1
    | Elemental  -> mkstr 2
    | TypeSpec t -> catstr [mkstr 3; TypeSpec.to_short_string t]
    | Impure     -> mkstr 4
    | Module     -> mkstr 5
    | Attributes a -> combo 6 [a]
end

module CaseSelector = struct
  include Labels.CaseSelector

  let to_short_string = function
    | CaseValueRangeList -> mkstr 0
    | Default            -> mkstr 1

end

module CaseValueRange = struct
  include Labels.CaseValueRange

  let to_short_string = function
    | Value      -> mkstr 0
    | Lower      -> mkstr 1
    | Upper      -> mkstr 2
    | LowerUpper -> mkstr 3

end

module ControlEditDesc = struct
  include Labels.ControlEditDesc

  let to_short_string = function
    | Terminate             -> mkstr 0
    | PositionEditDesc s    -> mkstr_str 1 s
    | SignEditDesc s        -> mkstr_str 3 s
    | BlankInterpEditDesc s -> mkstr_str 5 s
    | ScaleFactor i         -> catstr [mkstr 7; string_of_int i]
    | EndOfRecord i_opt     -> catstr ((mkstr 8)::(opt_to_list_map string_of_int i_opt))
    | Unknown s             -> mkstr_str 9 s

end

module FormatItem = struct
  include Labels.FormatItem

  let special_edit_desc_to_short_string = function
    | Dollar    -> mkstr 0
    | Backslash -> mkstr 1
    | Plus      -> mkstr 2
    | Zero      -> mkstr 3
    | One       -> mkstr 4
    | Blank     -> mkstr 5

  let to_short_string = function
    | DataEditDesc(i_opt, s)       -> catstr ((mkstr_str 0 s)::(opt_to_list_map string_of_int i_opt))
    | ControlEditDesc c            -> catstr [mkstr 2; ControlEditDesc.to_short_string c]
    | CharStringEditDesc s         -> mkstr_str 3 s
    | FormatItemList i_opt         -> catstr ((mkstr 5)::(opt_to_list_map string_of_int i_opt))
    | SpecialEditDesc sd           -> catstr [mkstr 6; special_edit_desc_to_short_string sd]
    | VariableFormatDesc(i_opt, s) -> catstr ((mkstr_str 7 s)::(opt_to_list_map string_of_int i_opt))
    | Macro(i_opt, id)             -> catstr ((mkstr_str 9 id)::(opt_to_list_map string_of_int i_opt))

end

module WaitSpec = struct
  include Labels.WaitSpec

  let to_short_string = function
    | End lab     -> combo 0 [lab]
    | Eor lab     -> combo 1 [lab]
    | Err lab     -> combo 2 [lab]
    | Id          -> mkstr 3
    | Iomsg       -> mkstr 4
    | Iostat      -> mkstr 5
    | Unit        -> mkstr 6

end

module FlushSpec = struct
  include Labels.FlushSpec

  let to_short_string = function
    | Err lab     -> combo 0 [lab]
    | Iomsg       -> mkstr 1
    | Iostat      -> mkstr 2
    | Unit        -> mkstr 3

end

module BindingAttr = struct
  include Labels.BindingAttr

  let to_short_string = function
    | Pass n         -> combo 0 [n]
    | Nopass         -> mkstr 1
    | NonOverridable -> mkstr 2
    | Deferred       -> mkstr 3
    | Private        -> mkstr 4
    | Public         -> mkstr 5

end

module ProcComponentAttrSpec = struct
  include Labels.ProcComponentAttrSpec

  let to_short_string = function
    | Pass n  -> combo 0 [n]
    | Pointer -> mkstr 1
    | Nopass  -> mkstr 2
    | Private -> mkstr 3
    | Public  -> mkstr 4

end

module ProcAttrSpec = struct
  include Labels.ProcAttrSpec

  let to_short_string = function
    | Public      -> mkstr 0
    | Private     -> mkstr 1
    | Bind        -> mkstr 2
    | Intent i    -> combo 3 [IntentSpec.to_short_string i]
    | Optional    -> mkstr 4
    | Pointer     -> mkstr 5
    | Protected   -> mkstr 6
    | Save        -> mkstr 7
    | Weird n     -> combo 8 [n]

end





include Label


let to_short_string ?(ignore_identifiers_flag=false) =
  let combo2 = combo2 ~ignore_identifiers_flag in function
  | DUMMY                             -> mkstr2 0
  | EMPTY                             -> mkstr2 1
  | ERROR _                           -> mkstr2 2
  | OCL                               -> mkstr2 3
  | Program                           -> mkstr2 4
  | Block                             -> mkstr2 5
  | InterfaceBlock n_opt              -> combo2 6 (opt_to_list n_opt)
  | InterfaceBody                     -> mkstr2 7
  | CaseConstruct                     -> mkstr2 8
  | DoConstruct v_opt                 -> combo2 9 (opt_to_list v_opt)
  | ForallConstruct                   -> mkstr2 10
  | IfConstruct                       -> mkstr2 11
  | WhereConstruct                    -> mkstr2 12
  | DerivedTypeDef n                  -> combo2 13 [n]
  | ArrayElement n                    -> combo2 14 [n]
  | ArraySection n                    -> combo2 15 [n]
  | StructureComponent n              -> combo2 16 [n]
  | Substring                         -> mkstr2 17
  | SectionSubscriptList n            -> combo2 18 [n]
  | SubscriptTriplet                  -> mkstr2 19
  | FirstSubscript                    -> mkstr2 20
  | SecondSubscript                   -> mkstr2 21
  | Stride                            -> mkstr2 22
  | SubstringRange                    -> mkstr2 23
  | StartingPoint                     -> mkstr2 24
  | EndingPoint                       -> mkstr2 25
  | PartRef                           -> mkstr2 26
  | ParenExpr                         -> mkstr2 27
  | ArrayConstructor                  -> mkstr2 28
  | LoopControl v                     -> combo2 29 [v]
  | LoopControlWhile                  -> mkstr2 30
  | Rename                            -> mkstr2 31
  | OnlyList                          -> mkstr2 32
  | KindSelector                      -> mkstr2 33
  | CharSelector                      -> mkstr2 34
  | LengthSelector                    -> mkstr2 35
  | LengthSelectorOverride            -> mkstr2 36
(*  | CharLenParamValueAsterisk         -> mkstr2 37 *)
  | TypeParamValueAsterisk            -> mkstr2 37
  | TypeParamValueColon               -> mkstr2 38

  | ExplicitShapeSpec                 -> mkstr2 39
  | AssumedShapeSpec                  -> mkstr2 40
  | DeferredShapeSpec                 -> mkstr2 41
(*| AssumedSizeSpec                   -> mkstr2 41 *)
(*
  | ComponentAttrSpecPointer          -> mkstr2 42
  | ComponentAttrSpecDimension        -> mkstr2 43
*)
  | ComponentAttrSpecs                -> mkstr2 44

  | AttrSpecs                         -> mkstr2 47
  | InputItemList                     -> mkstr2 48
  | OutputItemList                    -> mkstr2 49
  | IoLength                          -> mkstr2 50
  | IoImpliedDo                       -> mkstr2 51
  | EquivalenceSet                    -> mkstr2 52
  | DataStmtSet                       -> mkstr2 53
  | DataStmtValue                     -> mkstr2 54
(*  | NullInit                          -> mkstr2 55*)
  | DataImpliedDo                     -> mkstr2 56
  | DataIDoObject                     -> mkstr2 57
  | DataIDoObjectList                 -> mkstr2 58
  | DataStmtObjectList                -> mkstr2 59
  | DataStmtValueList                 -> mkstr2 60
  | Prefix                            -> mkstr2 61
  | DummyArgNameList n                -> combo2 62 [n]
  | DummyArgList n                    -> combo2 63 [n]
  | ActualArgSpecList n               -> combo2 64 [n]
  | AlternateReturnIndicator          -> mkstr2 65
  | ForallHeader                      -> mkstr2 66
  | ImplicitSpec                      -> mkstr2 67
  | FormatSpecification               -> mkstr2 68
  | AcImpliedDo                       -> mkstr2 69


  | PartName n                        -> combo2 71 [n]
  | Name n                            -> combo2 72 [n]
  | VariableName n                    -> combo2 73 [n]
  | FunctionReference n               -> combo2 74 [n]
  | StructureConstructor n            -> combo2 75 [n]
  | ComponentDecl n                   -> combo2 76 [n]
  | EntityDecl n                      -> combo2 77 [n]
  | CommonBlockObject n               -> combo2 78 [n]
  | NamedConstantDef n                -> combo2 79 [n]
  | IoImpliedDoControl n              -> combo2 80 [n]
  | Array n                           -> combo2 81 [n]
  | NamelistGroup n                   -> combo2 82 [n]
  | ObjectName n                      -> combo2 83 [n]
  | Result n                          -> combo2 84 [n]
  | ForallTripletSpec n               -> combo2 85 [n]
  | AcImpliedDoControl n              -> combo2 86 [n]

  | AltReturnSpec lab                 -> combo2 87 [lab]
  | Label lab                         -> combo2 89 [lab]

  | ActualArgSpec n_opt               -> combo2 90 (opt_to_list n_opt)
  | CommonSpec n_opt                  -> combo2 91 (opt_to_list n_opt)

  | ArraySpec i                       -> combo2 92 [string_of_int i]
  | ExplicitShapeArray i          -> combo2 93 [string_of_int i]
  | AssumedShapeArray i           -> combo2 94 [string_of_int i]
  | DeferredShapeArray i          -> combo2 95 [string_of_int i]
  | AssumedSizeArray i            -> combo2 96 [string_of_int i]
  | ComponentArraySpec i              -> combo2 97 [string_of_int i]
  | ExplicitShapeComponentArray i -> combo2 98 [string_of_int i]
  | DeferredShapeComponentArray i -> combo2 99 [string_of_int i]

  | Stmt s                            -> catstr [mkstr2 100; Stmt.to_short_string s]
  | PpDirective d                     -> catstr [mkstr2 101; PpDirective.to_short_string d]
  | OclDirective d                    -> catstr [mkstr2 102; OclDirective.to_short_string d]
  | ProgramUnit pu                    -> catstr [mkstr2 103; ProgramUnit.to_short_string pu]
  | TypeSpec t                        -> catstr [mkstr2 104; TypeSpec.to_short_string t]
  | Ambiguous a                       -> catstr [mkstr2 105; Ambiguous.to_short_string a]
  | Constant c                        -> catstr [mkstr2 106; Constant.to_short_string c]
  | GenericSpec g                     -> catstr [mkstr2 107; GenericSpec.to_short_string g]
  | IntrinsicOperator op              -> catstr [mkstr2 108; IntrinsicOperator.to_short_string op]
  | DefinedOperator op                -> catstr [mkstr2 109; DefinedOperator.to_short_string op]
  | AttrSpec a                        -> catstr [mkstr2 110; AttrSpec.to_short_string a]
  | StopCode c                        -> catstr [mkstr2 111; Constant.to_short_string c]
  | Format f                          -> catstr [mkstr2 112; Format.to_short_string f]
  | PrefixSpec p                      -> catstr [mkstr2 114; PrefixSpec.to_short_string p]
  | CaseSelector sel                  -> catstr [mkstr2 115; CaseSelector.to_short_string sel]
  | CaseValueRange r                  -> catstr [mkstr2 116; CaseValueRange.to_short_string r]
  | FormatItem i                      -> catstr [mkstr2 117; FormatItem.to_short_string i]
  | AccessSpec spec                   -> catstr [mkstr2 118; AccessSpec.to_short_string spec]
  | InquireSpec spec                  -> catstr [mkstr2 119; InquireSpec.to_short_string spec]
  | CloseSpec spec                    -> catstr [mkstr2 120; CloseSpec.to_short_string spec]
  | ConnectSpec spec                  -> catstr [mkstr2 121; ConnectSpec.to_short_string spec]
  | PositionSpec spec                 -> catstr [mkstr2 122; PositionSpec.to_short_string spec]
  | IoControlSpec spec                -> catstr [mkstr2 123; IoControlSpec.to_short_string spec]
  | IntentSpec spec                   -> catstr [mkstr2 124; IntentSpec.to_short_string spec]

  | Include s                         -> mkstr2_str 127 s

  | LetterSpec(l, l_opt)              -> catstr ((mkstr2 129)::l::(opt_to_list l_opt))

  | OmpClause c              -> catstr [mkstr2 130; OmpClause.to_short_string c]
  | OmpDirective d           -> catstr [mkstr2 131; OmpDirective.to_short_string d]
  | OMP                      -> mkstr2 132
  | CommonBlockName n        -> combo2 133 [n]
  | IntrinsicProcedureName n -> combo2 134 [n]

  | LindaCall lc             -> catstr [mkstr2 135; LindaCall.to_short_string lc]
  | LindaFormal              -> mkstr2 136
  | LindaActual              -> mkstr2 137
  | LindaLength              -> mkstr2 138
  | LindaTypeof              -> mkstr2 139

  | SpecificationPart        -> mkstr2 140
  | ExecutionPart            -> mkstr2 141
  | SubprogramPart           -> mkstr2 142
  | ImplicitPart             -> mkstr2 143

  | Variable                 -> mkstr2 144

  | InternalSubprogram is    -> catstr [mkstr2 145; InternalSubprogram.to_short_string is]
  | ModuleSubprogram is      -> catstr [mkstr2 146; ModuleSubprogram.to_short_string is]

  | XlfDirective d           -> catstr [mkstr2 147; Xlf.Directive.to_short_string d]
  | XlfAssertion a           -> catstr [mkstr2 148; Xlf.Assertion.to_short_string a]
  | XlfMisc x                -> catstr [mkstr2 149; Xlf.to_short_string x]
  | XLF                      -> mkstr2 150

  | StructureDecl n_opt      -> combo2 152 (opt_to_list n_opt)
  | UnionDecl                -> mkstr2 153
  | MapDecl                  -> mkstr2 154
  | RecordDecl n             -> combo2 155 [n]
  | RecordFieldRef n         -> combo2 156 [n]

  | EntityName n             -> combo2 157 [n]
  | DummyArgName n           -> combo2 158 [n]

  | LanguageBindingSpec      -> mkstr2 159
  | Suffix                   -> mkstr2 160

  | Fragment                 -> mkstr2 161

  | TypeAttrSpec spec        -> catstr [mkstr2 162; TypeAttrSpec.to_short_string spec]

  | InitializationExpr                -> mkstr2 163
  | InitializationNull                -> mkstr2 164
  | InitializationTarget              -> mkstr2 165
  | InitializationOldStyle            -> mkstr2 166

  | StatVariable                      -> mkstr2 167
  | ErrmsgVariable                    -> mkstr2 168
  | SourceExpr                        -> mkstr2 169
  | MoldExpr                          -> mkstr2 170

  | ModuleNatureIntrinsic    -> mkstr2 171
  | ModuleNatureNonIntrinsic -> mkstr2 172

  | PpMacroId n              -> combo2 173 [n]
  | PpMacroExpr n            -> combo2 174 [n]
  | PpMacroVariable n        -> combo2 175 [n]

  | PpBranch                 -> mkstr2 176
  | PpBranchDo               -> mkstr2 177
  | PpBranchForall           -> mkstr2 178
  | PpBranchIf               -> mkstr2 179
  | PpBranchSelect           -> mkstr2 180
  | PpBranchWhere            -> mkstr2 181

  | PpBranchEndDo            -> mkstr2 182
  | PpBranchEndForall        -> mkstr2 183
  | PpBranchEndIf            -> mkstr2 184
  | PpBranchEndSelect        -> mkstr2 185
  | PpBranchEndWhere         -> mkstr2 186

  | PpSectionIf s            -> combo2 187 [s]
  | PpSectionIfdef s         -> combo2 188 [s]
  | PpSectionIfndef s        -> combo2 189 [s]
  | PpSectionElif s          -> combo2 190 [s]
  | PpSectionElse            -> mkstr2 191

  | IfThenBlock              -> mkstr2 192
  | ElseIfBlock              -> mkstr2 193
  | ElseBlock                -> mkstr2 194

  | OmpConstruct c           -> catstr [mkstr2 195; OmpConstruct.to_short_string c]

  | CrayPointerSpec          -> mkstr2 196

  | CaseBlock                -> mkstr2 197

  | IoItemList               -> mkstr2 198

  | Allocation n             -> combo2 199 [n]
  | AllocateShapeSpec        -> mkstr2 200
  | AllocateShapeSpecList    -> mkstr2 201

  | PpBranchDerivedType          -> mkstr2 202
  | PpBranchEndType              -> mkstr2 203
  | SelectTypeConstruct          -> mkstr2 204
  | AssociateConstruct           -> mkstr2 205
  | BlockConstruct               -> mkstr2 206
  | CriticalConstruct            -> mkstr2 207
  | LoopControlConcurrent        -> mkstr2 208
  | AssumedRankArray             -> mkstr2 209
  | WaitSpec sp                  -> catstr [mkstr2 210; WaitSpec.to_short_string sp]
  | FlushSpec sp                 -> catstr [mkstr2 211; FlushSpec.to_short_string sp]
  | BindingAttr a                -> catstr [mkstr2 212; BindingAttr.to_short_string a]
  | ProcComponentAttrSpec sp     -> catstr [mkstr2 213; ProcComponentAttrSpec.to_short_string sp]
  | ProcAttrSpec sp              -> catstr [mkstr2 214; ProcAttrSpec.to_short_string sp]
  | ExternalName n               -> combo2 215 [n]
  | TypeBoundProcDecl(n, n_opt)  -> catstr ((mkstr2 216)::n::(opt_to_list n_opt))
  | TypeBoundProcedurePart       -> mkstr2 217
  | ProcedureDesignator n        -> combo2 218 [n]
  | ProcDecl n                   -> combo2 219 [n]
  | TypeGuardBlock               -> mkstr2 220
  | Association n                -> combo2 221 [n]
  | DeferredCoshapeSpec          -> mkstr2 222
  | ExplicitCoshapeSpec          -> mkstr2 223
(*  | ExplicitCoshapeSpecUpper     -> mkstr2 224*)
  | DeferredCoshapeCoarray       -> mkstr2 225
  | ExplicitCoshapeCoarray       -> mkstr2 226
  | CodimensionDecl n            -> combo2 227 [n]
  | Enumerator n                 -> combo2 228 [n]
  | EnumDef                      -> mkstr2 229
  | BoundsSpec                   -> mkstr2 230
  | BoundsRemapping              -> mkstr2 231
  | BoundsSpecList               -> mkstr2 232
  | BoundsRemappingList          -> mkstr2 233
  | DataPointerObject n          -> combo2 234 [n]
  | AllocateCoshapeSpec          -> mkstr2 235
(*  | AllocateCoshapeSpecUpper     -> mkstr2 236*)
  | AllocateCoarraySpec          -> mkstr2 237

  | WEIRD s                      -> combo2 238 [s]
  | AcquiredLock                 -> mkstr2 239
  | ImageSelector                -> mkstr2 240
  | AllImages                    -> mkstr2 241
  | WhereBlock                   -> mkstr2 242
  | SelectiveOp                  -> mkstr2 243

  | PpBranchFunction      -> mkstr2 244
  | PpBranchEndFunction   -> mkstr2 245
  | PpBranchSubroutine    -> mkstr2 244
  | PpBranchEndSubroutine -> mkstr2 245
  | PpBranchPu            -> mkstr2 246
  | PpBranchEndPu         -> mkstr2 247

  | DefineFileSpec        -> mkstr2 248
  | Options s             -> mkstr2_str 249 s

  | ApolloPointerSpec     -> mkstr2 251

  | PpMacroEntityDecl n -> combo2 252 [n]
  | PpMacroObject n     -> combo2 253 [n]

  | AccClause c              -> catstr [mkstr2 254; AccClause.to_short_string c]
  | AccDirective d           -> catstr [mkstr2 255; AccDirective.to_short_string d]
  | ACC                      -> mkstr2 256
  | AccConstruct c           -> catstr [mkstr2 257; AccConstruct.to_short_string c]

  | DecDirective d           -> catstr [mkstr2 258; Dec.Directive.to_short_string d]
  | DecClause c              -> catstr [mkstr2 259; Dec.Clause.to_short_string c]
  | DecAttribute a           -> catstr [mkstr2 260; Dec.Attribute.to_short_string a]
  | DecMisc x                -> catstr [mkstr2 261; Dec.to_short_string x]
  | DEC                      -> mkstr2 262

  | DoBlock                  -> mkstr2 263

  | FunctionStmtHead n   -> combo2 264 [n]
  | SubroutineStmtHead n -> combo2 265 [n]

  | ProcName n -> combo2 266 [n]

let strip lab = lab (* not yet *)

let anonymize2 = anonymize ~more:true

let anonymize3 = anonymize ~more:true


(*
type annotation = string option

let null_annotation = None

let annotation_to_string = function
  | None -> "<none>"
  | Some x -> x
*)

module Annotation = struct
  type spec =
    | Require of string list
    | Provide of string list
    | Spec of Pinfo.Name.Spec.t

  type t = spec list

  let null = ([] : t)

  let mkrequire ns = Require ns
  let mkprovide ns = Provide ns
  let mkspec nspec = Spec nspec

  let spec_to_string = function
    | Require ns -> Printf.sprintf "require %s" (Xlist.to_string (fun x -> x) ", " ns)
    | Provide ns -> Printf.sprintf "provide %s" (Xlist.to_string (fun x -> x) ", " ns)
    | Spec nspec -> Pinfo.Name.Spec.to_string nspec

  let to_string l = Xlist.to_string spec_to_string "\n" l

  let from_specs (l : spec list) = (l : t)

  let add_spec (a : t) (s : spec) = (s :: a : t)

  let iter f (a : t) =
    List.iter f a

end (* of module Annotation *)

type annotation = Annotation.t
let null_annotation = Annotation.null
let annotation_to_string = Annotation.to_string


let is_hunk_boundary _ _ = false (* not yet *)

(* These labels are collapsible whether they are leaves or not. *)
let forced_to_be_collapsible (*lab*)_ =
  false


let is_collapse_target options lab =
  if options#no_collapse_flag then
    false
  else
    match lab with
    | PpDirective _
    | OclDirective _
    | OmpClause _
    | OmpDirective _
    | OmpConstruct _
    | LindaCall _
    | ProgramUnit _
    | InternalSubprogram _
    | ModuleSubprogram _
    | Stmt _
    | CaseConstruct
    | DoConstruct _
    | ForallConstruct
    | IfConstruct
    | WhereConstruct
    | SelectTypeConstruct
    | AssociateConstruct
    | BlockConstruct
    | CriticalConstruct

    | DerivedTypeDef _
    | InterfaceBlock _
    | SpecificationPart
    | ExecutionPart
    | SubprogramPart
    | ImplicitPart
    | Block
    | LoopControl _
    | LoopControlWhile
    | LoopControlConcurrent
    | OnlyList
    | ComponentDecl _
    | Prefix
    | Suffix
    | EntityDecl _
    | DummyArgNameList _
    | DummyArgList _
    | ActualArgSpecList _
    | ExplicitShapeSpec
    | AssumedShapeSpec
    | DeferredShapeSpec
    | ArraySpec _
    | ExplicitShapeArray _
    | AssumedShapeArray _
    | DeferredShapeArray _
    | AssumedSizeArray _
    | ComponentArraySpec _
    | ExplicitShapeComponentArray _
    | DeferredShapeComponentArray _

    | StructureDecl _
    | UnionDecl
    | MapDecl
    | TypeBoundProcDecl _
    | EnumDef
    | CodimensionDecl _

(*    | TypeGuardBlock*)
    | Association _
    | BoundsSpec
    | BoundsRemapping
    | BoundsSpecList
    | BoundsRemappingList

(* expr *)
    | VariableName _
    | Constant _
    | DefinedOperator _
    | IntrinsicOperator _
    | FunctionReference _
    | ArrayConstructor
    | StructureConstructor _
    | ArrayElement _
    | ArraySection _
    | StructureComponent _
    | Substring
    | ParenExpr

    | Ambiguous _

      -> true

    | _ -> false


let is_to_be_notified = function
  | PpDirective _
  | OclDirective _
  | OmpDirective _
  | OmpConstruct _
  | LindaCall _
  | ProgramUnit _
  | InternalSubprogram _
  | ModuleSubprogram _
  | Stmt _
  | CaseConstruct
  | DoConstruct _
  | ForallConstruct
  | IfConstruct
  | WhereConstruct
  | SelectTypeConstruct
  | AssociateConstruct
  | BlockConstruct
  | CriticalConstruct
  | DerivedTypeDef _
  | InterfaceBlock _
  | EnumDef
    -> true
  | _ -> false

let is_partition = function
  | ProgramUnit _
    -> true
  | _ -> false

let is_sequence = function
  | Program
  | Block
  | InterfaceBody
  | SpecificationPart
  | ExecutionPart
  | SubprogramPart
  | ImplicitPart
  | Fragment
  | TypeBoundProcedurePart
    -> true
  | _ -> false

let is_ntuple = function
  (* not yet *)
  | _ -> false


let is_boundary = function
  | Program
  | ProgramUnit _
  | InternalSubprogram _
  | ModuleSubprogram _
  | DerivedTypeDef _
  | InterfaceBlock _
  | Fragment
  | EnumDef
    -> true
  | _ -> false


let is_primary = function
  | Constant _
  | Name _
  | FunctionReference _
  | ArrayConstructor
  | StructureConstructor _
  | ArrayElement _
  | ArraySection _
  | StructureComponent _
  | Substring
  | ParenExpr
  | RecordFieldRef _
    -> true
  | _ -> false

let is_expr = function
  | DefinedOperator _
  | IntrinsicOperator _
    -> true
  | lab -> is_primary lab

let is_op = function
  | DefinedOperator _
  | IntrinsicOperator _
    -> true
  | _ -> false

let is_scope_creating = function (* not yet *)
  | _ -> false

let is_compatible ?(weak=false) _ _ = ignore weak; false

let is_order_insensitive = function
  | _ -> false

let quasi_eq _ _ = false

let relabel_allowed = function
  | Stmt _, Stmt _
  | IfConstruct, CaseConstruct | CaseConstruct, IfConstruct
  | IfConstruct, WhereConstruct | WhereConstruct, IfConstruct
  | DoConstruct _, ForallConstruct | ForallConstruct, DoConstruct _
  | LoopControl _, LoopControlWhile | LoopControlWhile, LoopControl _
  | LoopControl _, LoopControlConcurrent | LoopControlConcurrent, LoopControl _
  | ExecutionPart, Block | Block, ExecutionPart (* only for mapping children *)
    -> true
  | l1, l2 ->
      (is_expr l1 && is_expr l2) ||
      (anonymize2 l1 = anonymize2 l2)

let move_disallowed _ = false

let is_common _ = false

let get_ident_use = function
  | Name n -> n
  | _ -> ""

let to_char (*lab*)_ = '0'

let has_names lab =
  try
    ignore (get_names lab);
    true
  with
    Not_found -> false

let has_a_name lab =
  try
    ignore (get_name lab);
    true
  with
    Not_found -> false

let is_named lab =
  has_a_name lab || has_names lab

let is_named_orig lab =
  match lab with
  | Stmt s -> Stmt.is_named_orig s

  | SectionSubscriptList _
  | DummyArgNameList _
  | DummyArgList _
  | ActualArgSpecList _
  | ArrayElement _
  | ArraySection _
  | StructureComponent _
    -> false

  | _ -> is_named lab


let to_elem_data = Astml.to_elem_data lang_prefix to_tag

let of_elem_data (*name*)_ (*attrs*)_ _ = DUMMY (* not yet *)



let getlab nd = (Obj.obj nd#data#_label : t)



let cannot_be_keyroot nd =
  match getlab nd with
  | Program
  | ProgramUnit _
  | InternalSubprogram _
  | ModuleSubprogram _
  | ExecutionPart
    -> true
  | _ -> false


let is_int_literal = function
  | Constant (Constant.IntLiteralConstant _) -> true
  | _ -> false

let is_real_literal = function
  | Constant (Constant.RealLiteralConstant _) -> true
  | _ -> false

let is_string_literal = function
  | Constant (Constant.CharLiteralConstant _) -> true
  | _ -> false

let is_phantom = function
  | Block
  | DoBlock
  | WhereBlock
  | TypeGuardBlock
  | CaseBlock
  | IfThenBlock
  | ElseIfBlock
  | ElseBlock
  | SpecificationPart
  | ExecutionPart
  | ImplicitPart
    -> true
  | _ -> false

let is_special _ = false

let is_pp_directive = function
  | PpDirective _ -> true
  | _ -> false

let is_pp_define = function
  | PpDirective {PpDirective.pp_label=PpDirective.Define _;_} -> true
  | _ -> false

let is_pp_include = function
  | PpDirective
      {PpDirective.pp_label=PpDirective.Include _;_} -> true
  | _ -> false

let get_pp_include_path = function
  | PpDirective
      {PpDirective.pp_label=PpDirective.Include h;_} -> HeaderFile.to_path h
  | _ -> raise Not_found

let is_ocl_directive = function
  | OclDirective _ -> true
  | _ -> false

let is_omp_clause = function
  | OmpClause _ -> true
  | _ -> false

let is_omp_directive = function
  | OmpDirective _ -> true
  | _ -> false

let is_omp_construct = function
  | OmpConstruct _ -> true
  | _ -> false

let is_acc_clause = function
  | AccClause _ -> true
  | _ -> false

let is_acc_directive = function
  | AccDirective _ -> true
  | _ -> false

let is_acc_construct = function
  | AccConstruct _ -> true
  | _ -> false

let is_dec_clause = function
  | DecClause _ -> true
  | _ -> false

let is_dec_directive = function
  | DecDirective _ -> true
  | _ -> false

let is_program_unit = function
  | ProgramUnit _ -> true
  | _ -> false

let is_program = function
  | Program -> true
  | _ -> false

let is_fragment = function
  | Fragment -> true
  | _ -> false

let is_execution_part = function
  | ExecutionPart -> true
  | _ -> false

let is_subprogram_part = function
  | SubprogramPart -> true
  | _ -> false

let is_external_subprogram = function
  | ProgramUnit
      (ProgramUnit.FunctionSubprogram _ |
      ProgramUnit.SubroutineSubprogram _) -> true
  | _ -> false

let is_main_program = function
  | ProgramUnit (ProgramUnit.MainProgram _) -> true
  | _ -> false

let is_function = function
  | ProgramUnit (ProgramUnit.FunctionSubprogram _)
  | InternalSubprogram (InternalSubprogram.FunctionSubprogram _)
  | ModuleSubprogram (ModuleSubprogram.FunctionSubprogram _)
    -> true
  | _ -> false

let is_ext_function = function
  | ProgramUnit (ProgramUnit.FunctionSubprogram _)
    -> true
  | _ -> false

let is_int_function = function
  | InternalSubprogram (InternalSubprogram.FunctionSubprogram _)
    -> true
  | _ -> false

let is_mod_function = function
  | ModuleSubprogram (ModuleSubprogram.FunctionSubprogram _)
    -> true
  | _ -> false

let is_subroutine = function
  | ProgramUnit (ProgramUnit.SubroutineSubprogram _)
  | InternalSubprogram (InternalSubprogram.SubroutineSubprogram _)
  | ModuleSubprogram (ModuleSubprogram.SubroutineSubprogram _)
    -> true
  | _ -> false

let is_ext_subroutine = function
  | ProgramUnit (ProgramUnit.SubroutineSubprogram _)
    -> true
  | _ -> false

let is_int_subroutine = function
  | InternalSubprogram (InternalSubprogram.SubroutineSubprogram _)
    -> true
  | _ -> false

let is_mod_subroutine = function
  | ModuleSubprogram (ModuleSubprogram.SubroutineSubprogram _)
    -> true
  | _ -> false

let is_subprogram = function
  | ProgramUnit
      (ProgramUnit.SubroutineSubprogram _|ProgramUnit.FunctionSubprogram _)
  | InternalSubprogram
      (InternalSubprogram.SubroutineSubprogram _|InternalSubprogram.FunctionSubprogram _)
  | ModuleSubprogram _
    -> true
  | _ -> false

let is_program_unit_or_fragment = function
  | ProgramUnit _
  | Fragment -> true
  | _ -> false

let is_program_unit_or_subprogram = function
  | ProgramUnit _
  | InternalSubprogram
      (InternalSubprogram.SubroutineSubprogram _|InternalSubprogram.FunctionSubprogram _)
  | ModuleSubprogram
      (ModuleSubprogram.SubroutineSubprogram _|ModuleSubprogram.FunctionSubprogram _)
    -> true
  | _ -> false

let is_module = function
  | ProgramUnit (ProgramUnit.Module _) -> true
  | _ -> false

let is_block_data = function
  | ProgramUnit (ProgramUnit.BlockData _) -> true
  | _ -> false

let is_case_construct = function
  | CaseConstruct -> true
  | _ -> false

let is_do_construct = function
  | DoConstruct _ -> true
  | _ -> false

let is_forall_construct = function
  | ForallConstruct -> true
  | _ -> false

let is_if_construct = function
  | IfConstruct -> true
  | _ -> false

let is_where_construct = function
  | WhereConstruct -> true
  | _ -> false

let is_select_type_construct = function
  | SelectTypeConstruct -> true
  | _ -> false

let is_associate_construct = function
  | AssociateConstruct -> true
  | _ -> false

let is_block_construct = function
  | BlockConstruct -> true
  | _ -> false

let is_critical_construct = function
  | CriticalConstruct -> true
  | _ -> false

let is_derived_type_def = function
  | DerivedTypeDef _ -> true
  | _ -> false

let is_interface_block = function
  | InterfaceBlock _ -> true
  | _ -> false

let is_block = function
  | Block -> true
  | _ -> false

let is_ambiguous = function
  | Ambiguous _ -> true
  | _ -> false

let is_array_access = function
  | ArrayElement _
  | ArraySection _
  | Ambiguous (Ambiguous.ArrayAccess _) -> true
  | _ -> false

let is_if_then_block = function
  | IfThenBlock -> true
  | _ -> false

let is_else_block = function
  | ElseBlock -> true
  | _ -> false

let is_else_if_block = function
  | ElseIfBlock -> true
  | _ -> false

let is_where_block = function
  | WhereBlock -> true
  | _ -> false

let is_case_block = function
  | CaseBlock -> true
  | _ -> false

let is_type_guard_block = function
  | TypeGuardBlock -> true
  | _ -> false

let is_do_block = function
  | DoBlock -> true
  | _ -> false

let is_pp_branch = function
  | PpBranch -> true
  | _ -> false

let is_pp_branch_do = function
  | PpBranchDo -> true
  | _ -> false

let is_pp_branch_if = function
  | PpBranchIf -> true
  | _ -> false

let is_pp_branch_forall = function
  | PpBranchForall -> true
  | _ -> false

let is_pp_branch_where = function
  | PpBranchWhere -> true
  | _ -> false

let is_pp_branch_select = function
  | PpBranchSelect -> true
  | _ -> false

let is_pp_branch_end_do = function
  | PpBranchEndDo -> true
  | _ -> false

let is_pp_branch_end_if = function
  | PpBranchEndIf -> true
  | _ -> false

let is_pp_branch_end_forall = function
  | PpBranchEndForall -> true
  | _ -> false

let is_pp_branch_end_where = function
  | PpBranchEndWhere -> true
  | _ -> false

let is_pp_branch_end_select = function
  | PpBranchEndSelect -> true
  | _ -> false

let is_pp_section_ifdef = function
  | PpSectionIfdef _ -> true
  | _ -> false

let is_pp_section_ifndef = function
  | PpSectionIfndef _ -> true
  | _ -> false

let is_pp_section_if = function
  | PpSectionIf _ -> true
  | _ -> false

let is_pp_section_elif = function
  | PpSectionElif _ -> true
  | _ -> false

let is_pp_section_else = function
  | PpSectionElse -> true
  | _ -> false

let is_container_unit = function
  | AccConstruct _
  | CaseBlock
  | ElseBlock
  | ElseIfBlock
  | IfThenBlock
  | TypeGuardBlock
  | WhereBlock
  | PpSectionIf _
  | PpSectionElif _
  | PpSectionElse
  | PpSectionIfdef _
  | PpSectionIfndef _
  | AssociateConstruct
  | BlockConstruct
  | CaseConstruct
  | IfConstruct
  | SelectTypeConstruct
  | WhereConstruct
  | CriticalConstruct
  | DoConstruct _
  | ForallConstruct
  | DoBlock
  | ExecutionPart
  | OmpConstruct _
  | PpBranch
  | PpBranchDo
  | PpBranchIf
  | PpBranchForall
  | PpBranchWhere
  | PpBranchSelect
  | PpBranchEndDo
  | PpBranchEndIf
  | PpBranchEndForall
  | PpBranchEndWhere
  | PpBranchEndSelect
    -> true

  | _ -> false
