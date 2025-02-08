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

(* token.ml *)

module Xlist = Diffast_misc.Xlist
module Parserlib_base = Langs_common.Parserlib_base
module Astloc = Langs_common.Astloc
module Layeredloc = Langs_common.Layeredloc

module Loc = Astloc
module LLoc = Layeredloc
module H   = Labels.HeaderFile
module PPD = Labels.PpDirective
module DL = Common.DirectiveLine

open Tokens_

let sprintf = Printf.sprintf

let spec_to_string = Ast.Partial.spec_to_string
let nd_to_string = Printer.to_string

let rec rawtoken_to_string = function

  | PROGRAM_UNIT(spec, _)           -> sprintf "PROGRAM_UNIT(%s)" (spec_to_string spec)
  | SPEC_PART_CONSTRUCT(spec, _)    -> sprintf "SPEC_PART_CONSTRUCT(%s)" (spec_to_string spec)
  | EXEC_PART_CONSTRUCT(spec, _)    -> sprintf "EXEC_PART_CONSTRUCT(%s)" (spec_to_string spec)
  | SUBPROGRAM(spec, _)             -> sprintf "SUBPROGRAM(%s)" (spec_to_string spec)
  | INTERFACE_SPEC(spec, _)         -> sprintf "INTERFACE_SPEC(%s)" (spec_to_string spec)
  | CASE_BLOCK(spec, _)             -> sprintf "CASE_BLOCK(%s)" (spec_to_string spec)
  | DATA_STMT_SET(spec, nd)         -> sprintf "DATA_STMT_SET(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | STMT(spec, nd)                  -> sprintf "STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | ACTION_STMT(spec, nd)           -> sprintf "ACTION_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | VARIABLE(spec, nd)              -> sprintf "VARIABLE(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | EXPR(spec, nd)                  -> sprintf "EXPR(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | TYPE_SPEC(spec, nd)             -> sprintf "TYPE_SPEC(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | DERIVED_TYPE_DEF_PART(spec, nd) -> sprintf "DERIVED_TYPE_DEF_PART(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | ONLY_(spec, nd)                 -> sprintf "ONLY_(%s):\n%s" (spec_to_string spec) (nd_to_string nd)

  | DO_STMT(spec, nd)               -> sprintf "DO_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | FORALL_CONSTRUCT_STMT(spec, nd) -> sprintf "FORALL_CONSTRUCT_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | IF_THEN_STMT(spec, nd)          -> sprintf "IF_THEN_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | SELECT_CASE_STMT(spec, nd)      -> sprintf "SELECT_CASE_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | WHERE_CONSTRUCT_STMT(spec, nd)  -> sprintf "WHERE_CONSTRUCT_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | DERIVED_TYPE_STMT(spec, nd)     -> sprintf "DERIVED_TYPE_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)

  | END_DO_STMT(spec, nd)           -> sprintf "END_DO_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | END_FORALL_STMT(spec, nd)       -> sprintf "END_FORALL_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | END_IF_STMT(spec, nd)           -> sprintf "END_IF_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | END_SELECT_STMT(spec, nd)       -> sprintf "END_SELECT_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | END_WHERE_STMT(spec, nd)        -> sprintf "END_WHERE_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | END_TYPE_STMT(spec, nd)         -> sprintf "END_TYPE_STMT(%s):\n%s" (spec_to_string spec) (nd_to_string nd)

  | FUNCTION_HEAD(spec, nd)         -> sprintf "FUNCTION_HEAD(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | FUNCTION_STMT_HEAD(spec, nd)    -> sprintf "FUNCTION_STMT_HEAD(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | SUBROUTINE_HEAD(spec, nd)       -> sprintf "SUBROUTINE_HEAD(%s):\n%s" (spec_to_string spec) (nd_to_string nd)
  | SUBROUTINE_STMT_HEAD(spec, nd)  -> sprintf "SUBROUTINE_STMT_HEAD(%s):\n%s" (spec_to_string spec) (nd_to_string nd)

  | PU_TAIL(spec, nd)               -> sprintf "PU_TAIL(%s):\n%s" (spec_to_string spec) (nd_to_string nd)

  | PP_IDENTIFIER s -> "PP_IDENTIFIER:"^s

  | PP_UNDERSCORE s -> "PP_UNDERSCORE:"^s

  | PP_MACRO_CONST s      -> "PP_MACRO_CONST:"^s
(*  | PP_MACRO_CONST_CHAR s -> "PP_MACRO_CONST_CHAR:"^s
  | PP_MACRO_CONST_INT s  -> "PP_MACRO_CONST_INT:"^s*)
  | PP_MACRO_NAME(s, e)   -> "PP_MACRO_NAME:"^s^(if e = "" then "" else ":"^e)
  | PP_MACRO_VARIABLE s   -> "PP_MACRO_VARIABLE:"^s
  | PP_MACRO_EXPR s       -> "PP_MACRO_EXPR:"^s
  | PP_MACRO_STMT s       -> "PP_MACRO_STMT:"^s
  | PP_MACRO_TYPE_SPEC s  -> "PP_MACRO_TYPE_SPEC:"^s
  | PP_MACRO_WRITE s      -> "PP_MACRO_WRITE:"^s
  | PP_MACRO_READ_WRITE s -> "PP_MACRO_READ_WRITE:"^s
  | PP_MACRO_READ_PRINT s -> "PP_MACRO_READ_PRINT:"^s


  | PP_MACRO_ID(kind, s)    -> "PP_MACRO_ID:"^(Macro.kind_to_string kind)^":"^s
  | PP_MACRO_ID_RW(kind, s) -> "PP_MACRO_ID_RW:"^(Macro.kind_to_string kind)^":"^s
  | PP_MACRO_APPL(s, sl)    -> sprintf "PP_MACRO_APPL:%s(%s)" s (String.concat "," sl)

  | PP_DEFINE__IDENT__BODY(i, b) -> "PP_DEFINE__IDENT__BODY:"^i^":"^(Macro.body_to_string b)
  | PP_INCLUDE__FILE h           -> "PP_INCLUDE__FILE:"^(H.to_string h)

  | PP_BRANCH b -> "PP_BRANCH:"^(PPD.branch_to_string b)
(*
  | PP_IF__COND c                -> "PP_IF__COND:"^c
  | PP_ELIF__COND c              -> "PP_ELIF__COND:"^c
  | PP_IFDEF__IDENT i            -> "PP_IFDEF__IDENT:"^i
  | PP_IFNDEF__IDENT i           -> "PP_IFNDEF__IDENT:"^i
*)
  | PP_ELSE              -> "PP_ELSE"
  | PP_ENDIF             -> "PP_ENDIF"

  | PP_UNDEF__IDENT i            -> "PP_UNDEF__IDENT:"^i

  | PP_ISSUE__MESG m             -> "PP_ISSUE__MESG:"^(PPD.message_to_string m)
(*
  | PP_ERROR__MESG m             -> "PP_ERROR__MESG:"^m
  | PP_WARNING__MESG m           -> "PP_WARNING__MESG:"^m
*)
  | PP_UNKNOWN__REST(d, r)       -> "PP_UNKNOWN__REST:"^d^":"^r

  | PP_INCLUDE           -> "PP_INCLUDE"
  | PP_DEFINE            -> "PP_DEFINE"
  | PP_UNDEF             -> "PP_UNDEF"
  | PP_IF                -> "PP_IF"
  | PP_IFDEF             -> "PP_IFDEF"
  | PP_IFNDEF            -> "PP_IFNDEF"
  | PP_ELIF              -> "PP_ELSIF"

  | PP_ERROR             -> "PP_ERROR"
  | PP_WARNING           -> "PP_WARNING"

  | PP_UNKNOWN           -> "PP_UNKNOWN"

  | PP_AND               -> "PP_AND"
  | PP_OR                -> "PP_OR"
  | PP_CONCAT            -> "PP_CONCAT"

  | OCL_ARRAY_FUSION           -> "OCL_ARRAY_FUSION"
  | OCL_END_ARRAY_FUSION       -> "OCL_END_ARRAY_FUSION"
  | OCL_ARRAY_MERGE            -> "OCL_ARRAY_MERGE"
  | OCL_ARRAY_SUBSCRIPT        -> "OCL_ARRAY_SUBSCRIPT"
  | OCL_EVAL                   -> "OCL_EVAL"
  | OCL_NOEVAL                 -> "OCL_NOEVAL"
  | OCL_FLTLD                  -> "OCL_FLTLD"
  | OCL_NOFLTLD                -> "OCL_NOFLTLD"
  | OCL_FP_RELAXED             -> "OCL_FP_RELAXED"
  | OCL_NOFP_RELAXED           -> "OCL_NOFP_RELAXED"
  | OCL_LOOP_INTERCHANGE       -> "OCL_LOOP_INTERCHANGE"
  | OCL_LOOP_NOINTERCHANGE     -> "OCL_LOOP_NOINTERCHANGE"
  | OCL_MFUNC                  -> "OCL_MFUNC"
  | OCL_NOMFUNC                -> "OCL_NOMFUNC"
  | OCL_NOARRAYPAD             -> "OCL_NOARRAYPAD"
  | OCL_LOOP_NOFUSION          -> "OCL_LOOP_NOFUSION"
  | OCL_PREEX                  -> "OCL_PREEX"
  | OCL_NOPREEX                -> "OCL_NOPREEX"
  | OCL_PREFETCH               -> "OCL_PREFETCH"
  | OCL_NOPREFETCH             -> "OCL_NOPREFETCH"
  | OCL_PREFETCH_CACHE_LEVEL   -> "OCL_PREFETCH_CACHE_LEVEL"
  | OCL_PREFETCH_INFER         -> "OCL_PREFETCH_INFER"
  | OCL_PREFETCH_NOINFER       -> "OCL_PREFETCH_NOINFER"
  | OCL_PREFETCH_ITERATION     -> "OCL_PREFETCH_ITERATION"
  | OCL_PREFETCH_ITERATION_L2  -> "OCL_PREFETCH_ITERATION_L2"
  | OCL_PREFETCH_READ          -> "OCL_PREFETCH_READ"
  | OCL_PREFETCH_WRITE         -> "OCL_PREFETCH_WRITE"
  | OCL_STRIPING               -> "OCL_STRIPING"
  | OCL_NOSTRIPING             -> "OCL_NOSTRIPING"
  | OCL_SWP                    -> "OCL_SWP"
  | OCL_NOSWP                  -> "OCL_NOSWP"
  | OCL_LOOP_BLOCKING          -> "OCL_LOOP_BLOCKING"
  | OCL_UNROLL                 -> "OCL_UNROLL"
  | OCL_NOUNROLL               -> "OCL_NOUNROLL"
  | OCL_NOVREC                 -> "OCL_NOVREC"
  | OCL_SIMD                   -> "OCL_SIMD"
  | OCL_NOSIMD                 -> "OCL_NOSIMD"
  | OCL_CACHE_SECTOR_SIZE      -> "OCL_CACHE_SECTOR_SIZE"
  | OCL_END_CACHE_SECTOR_SIZE  -> "OCL_END_CACHE_SECTOR_SIZE"
  | OCL_CACHE_SUBSECTOR_ASSIGN -> "OCL_CACHE_SUBSECTOR_ASSIGN"
  | OCL_END_CACHE_SUBSECTOR    -> "OCL_END_CACHE_SUBSECTOR"
  | OCL_FISSION_POINT          -> "OCL_FISSION_POINT"
  | OCL_LOOP_NOFISSION         -> "OCL_LOOP_NOFISSION"
  | OCL_XFILL                  -> "OCL_XFILL"
  | OCL_NOXFILL                -> "OCL_NOXFILL"
  | OCL_PREFETCH_SEQUENTIAL    -> "OCL_PREFETCH_SEQUENTIAL"
  | OCL_PREFETCH_STRONG        -> "OCL_PREFETCH_STRONG"
  | OCL_PREFETCH_NOSTRONG      -> "OCL_PREFETCH_NOSTRONG"
  | OCL_PREFETCH_STRONG_L2     -> "OCL_PREFETCH_STRONG_L2"
  | OCL_PREFETCH_NOSTRONG_L2   -> "OCL_PREFETCH_NOSTRONG_L2"
  | OCL_FP_CONTRACT            -> "OCL_FP_CONTRACT"
  | OCL_NOFP_CONTRACT          -> "OCL_NOFP_CONTRACT"
  | OCL_LOOP_NOBLOCKING        -> "OCL_LOOP_NOBLOCKING"
  | OCL_NORECURRENCE           -> "OCL_NORECURRENCE"
  | OCL_UXSIMD                 -> "OCL_UXSIMD"
  | OCL_NOUXSIMD               -> "OCL_NOUXSIMD"

  | OCL_ARRAY_PRIVATE          -> "OCL_ARRAY_PRIVATE"
  | OCL_NOARRAY_PRIVATE        -> "OCL_NOARRAY_PRIVATE"
  | OCL_INDEPENDENT            -> "OCL_INDEPENDENT"
  | OCL_NOALIAS                -> "OCL_NOALIAS"
  | OCL_SERIAL                 -> "OCL_SERIAL"
  | OCL_PARALLEL               -> "OCL_PARALLEL"
  | OCL_PARALLEL_STRONG        -> "OCL_PARALLEL_STRONG"
  | OCL_REDUCTION              -> "OCL_REDUCTION"
  | OCL_NOREDUCTION            -> "OCL_NOREDUCTION"
  | OCL_TEMP                   -> "OCL_TEMP"

  | OCL_LOOP_PART_SIMD         -> "OCL_LOOP_PART_SIMD"
  | OCL_LOOP_NOPART_SIMD       -> "OCL_LOOP_NOPART_SIMD"
  | OCL_SHORTLOOP              -> "OCL_SHORTLOOP"
  | OCL_NOSHORTLOOP            -> "OCL_NOSHORTLOOP"
  | OCL_SIMD_LISTV             -> "OCL_SIMD_LISTV"
  | OCL_UNSWITCHING            -> "OCL_UNSWITCHING"
  | OCL_LOOP_PART_PARALLEL     -> "OCL_LOOP_PART_PARALLEL"
  | OCL_LOOP_NOPART_PARALLEL   -> "OCL_LOOP_NOPART_PARALLEL"
  | OCL_FIRST_PRIVATE          -> "OCL_FIRST_PRIVATE"
  | OCL_LAST_PRIVATE           -> "OCL_LAST_PRIVATE"
  | OCL_TEMP_PRIVATE           -> "OCL_TEMP_PRIVATE"
  | OCL_PARALLEL_CYCLIC        -> "OCL_PARALLEL_CYCLIC"
  | OCL_ALIGNED                -> "OCL_ALIGNED"
  | OCL_UNALIGNED              -> "OCL_UNALIGNED"
  | OCL_LEVEL                  -> "OCL_LEVEL"
  | OCL_STRONG                 -> "OCL_STRONG"
  | OCL_AUTO                   -> "OCL_AUTO"
  | OCL_SOFT                   -> "OCL_SOFT"
  | OCL_ALL                    -> "OCL_ALL"
  | OCL_THEN                   -> "OCL_THEN"
  | OCL_ELSE                   -> "OCL_ELSE"

  (*| RAWOCL s                   -> "RAWOCL:"^s*)
  | OCL _                      -> "OCL"


  | OMP_AUTO                   -> "OMP_AUTO"
  | OMP_ATOMIC                 -> "OMP_ATOMIC"
  | OMP_BARRIER                -> "OMP_BARRIER"
  | OMP_CAPTURE                -> "OMP_CAPTURE"
  | OMP_COLLAPSE               -> "OMP_COLLAPSE"
  | OMP_COPYIN                 -> "OMP_COPYIN"
  | OMP_COPYPRIVATE            -> "OMP_COPYPRIVATE"
  | OMP_CRITICAL               -> "OMP_CRITICAL"
  | OMP_DEFAULT                -> "OMP_DEFAULT"
  | OMP_DO                     -> "OMP_DO"
  | OMP_DYNAMIC                -> "OMP_DYNAMIC"
  | OMP_END                    -> "OMP_END"
  | OMP_FINAL                  -> "OMP_FINAL"
  | OMP_FIRSTPRIVATE           -> "OMP_FIRSTPRIVATE"
  | OMP_FLUSH                  -> "OMP_FLUSH"
  | OMP_GUIDED                 -> "OMP_GUIDED"
  | OMP_IF                     -> "OMP_IF"
  | OMP_LASTPRIVATE            -> "OMP_LASTPRIVATE"
  | OMP_MASTER                 -> "OMP_MASTER"
  | OMP_MERGEABLE              -> "OMP_MERGEABLE"
  | OMP_NONE                   -> "OMP_NONE"
  | OMP_NOWAIT                 -> "OMP_NOWAIT"
  | OMP_NUM_THREADS            -> "OMP_NUM_THREADS"
  | OMP_ORDERED                -> "OMP_ORDERED"
  | OMP_PARALLEL               -> "OMP_PARALLEL"
  | OMP_PRIVATE                -> "OMP_PRIVATE"
  | OMP_READ                   -> "OMP_READ"
  | OMP_REDUCTION              -> "OMP_REDUCTION"
  | OMP_RUNTIME                -> "OMP_RUNTIME"
  | OMP_SCHEDULE               -> "OMP_SCHEDULE"
  | OMP_SECTION                -> "OMP_SECTION"
  | OMP_SECTIONS               -> "OMP_SECTIONS"
  | OMP_SHARED                 -> "OMP_SHARED"
  | OMP_SINGLE                 -> "OMP_SINGLE"
  | OMP_STATIC                 -> "OMP_STATIC"
  | OMP_TASK                   -> "OMP_TASK"
  | OMP_TASKWAIT               -> "OMP_TASKWAIT"
  | OMP_TASKYIELD              -> "OMP_TASKYIELD"
  | OMP_THREADPRIVATE          -> "OMP_THREADPRIVATE"
  | OMP_UNTIED                 -> "OMP_UNTIED"
  | OMP_UPDATE                 -> "OMP_UPDATE"
  | OMP_WORKSHARE              -> "OMP_WORKSHARE"
  | OMP_WRITE                  -> "OMP_WRITE"

  | OMP_END_ATOMIC             -> "OMP_END_ATOMIC"
  | OMP_END_CRITICAL           -> "OMP_END_CRITICAL"
  | OMP_END_DO                 -> "OMP_END_DO"
  | OMP_END_MASTER             -> "OMP_END_MASTER"
  | OMP_END_ORDERED            -> "OMP_END_ORDERED"
  | OMP_END_PARALLEL           -> "OMP_END_PARALLEL"
  | OMP_END_SECTIONS           -> "OMP_END_SECTIONS"
  | OMP_END_SINGLE             -> "OMP_END_SINGLE"
  | OMP_END_TASK               -> "OMP_END_TASK"
  | OMP_END_WORKSHARE          -> "OMP_END_WORKSHARE"
  | OMP_PARALLEL_DO            -> "OMP_PARALLEL_DO"
  | OMP_PARALLEL_SECTIONS      -> "OMP_PARALLEL_SECTIONS"
  | OMP_PARALLEL_WORKSHARE     -> "OMP_PARALLEL_WORKSHARE"
  | OMP_END_PARALLEL_DO        -> "OMP_END_PARALLEL_DO"
  | OMP_END_PARALLEL_SECTIONS  -> "OMP_END_PARALLEL_SECTIONS"
  | OMP_END_PARALLEL_WORKSHARE -> "OMP_END_PARALLEL_WORKSHARE"

  (* for OpenMP 4.0 *)
  | OMP_ALIGNED                                      -> "OMP_ALIGNED"
  | OMP_ALLOC                                        -> "OMP_ALLOC"
  | OMP_CANCEL                                       -> "OMP_CANCEL"
  | OMP_CANCELLATION_POINT                           -> "OMP_CANCELLATION_POINT"
  | OMP_CLOSE                                        -> "OMP_CLOSE"
  | OMP_DECLARE_REDUCTION                            -> "OMP_DECLARE_REDUCTION"
  | OMP_DECLARE_SIMD                                 -> "OMP_DECLARE_SIMD"
  | OMP_DECLARE_TARGET                               -> "OMP_DECLARE_TARGET"
  | OMP_DEPEND                                       -> "OMP_DEPEND"
  | OMP_DEVICE                                       -> "OMP_DEVICE"
  | OMP_DIST_SCHEDULE                                -> "OMP_DIST_SCHEDULE"
  | OMP_DISTRIBUTE                                   -> "OMP_DISTRIBUTE"
  | OMP_DISTRIBUTE_PARALLEL_DO                       -> "OMP_DISTRIBUTE_PARALLEL_DO"
  | OMP_DISTRIBUTE_PARALLEL_DO_SIMD                  -> "OMP_DISTRIBUTE_PARALLEL_DO_SIMD"
  | OMP_DISTRIBUTE_SIMD                              -> "OMP_DISTRIBUTE_SIMD"
  | OMP_DO_SIMD                                      -> "OMP_DO_SIMD"
  | OMP_END_DISTRIBUTE                               -> "OMP_END_DISTRIBUTE"
  | OMP_END_DISTRIBUTE_PARALLEL_DO                   -> "OMP_END_DISTRIBUTE_PARALLEL_DO"
  | OMP_END_DISTRIBUTE_PARALLEL_DO_SIMD              -> "OMP_END_DISTRIBUTE_PARALLEL_DO_SIMD"
  | OMP_END_DISTRIBUTE_SIMD                          -> "OMP_END_DISTRIBUTE_SIMD"
  | OMP_END_DO_SIMD                                  -> "OMP_END_DO_SIMD"
  | OMP_END_PARALLEL_DO_SIMD                         -> "OMP_END_PARALLEL_DO_SIMD"
  | OMP_END_SIMD                                     -> "OMP_END_SIMD"
  | OMP_END_TARGET                                   -> "OMP_END_TARGET"
  | OMP_END_TARGET_DATA                              -> "OMP_END_TARGET_DATA"
  | OMP_END_TARGET_TEAMS                             -> "OMP_END_TARGET_TEAMS"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE                  -> "OMP_END_TARGET_TEAMS_DISTRIBUTE"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO      -> "OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD -> "OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_SIMD             -> "OMP_END_TARGET_TEAMS_DISTRIBUTE_SIMD"
  | OMP_END_TASKGROUP                                -> "OMP_END_TASKGROUP"
  | OMP_END_TEAMS                                    -> "OMP_END_TEAMS"
  | OMP_END_TEAMS_DISTRIBUTE                         -> "OMP_END_TEAMS_DISTRIBUTE"
  | OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO             -> "OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO"
  | OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD        -> "OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD"
  | OMP_END_TEAMS_DISTRIBUTE_SIMD                    -> "OMP_END_TEAMS_DISTRIBUTE_SIMD"
  | OMP_FROM                                         -> "OMP_FROM"
  | OMP_IN                                           -> "OMP_IN"
  | OMP_INBRANCH                                     -> "OMP_INBRANCH"
  | OMP_INITIALIZER                                  -> "OMP_INITIALIZER"
  | OMP_INOUT                                        -> "OMP_INOUT"
  | OMP_LINEAR                                       -> "OMP_LINEAR"
  | OMP_MAP                                          -> "OMP_MAP"
  | OMP_NOTINBRANCH                                  -> "OMP_NOTINBRANCH"
  | OMP_NUM_TEAMS                                    -> "OMP_NUM_TEAMS"
  | OMP_OUT                                          -> "OMP_OUT"
  | OMP_PARALLEL_DO_SIMD                             -> "OMP_PARALLEL_DO_SIMD"
  | OMP_PROC_BIND                                    -> "OMP_PROC_BIND"
  | OMP_SAFELEN                                      -> "OMP_SAFELEN"
  | OMP_SEQ_CST                                      -> "OMP_SEQ_CST"
  | OMP_SIMD                                         -> "OMP_SIMD"
  | OMP_SIMDLEN                                      -> "OMP_SIMDLEN"
  | OMP_SPREAD                                       -> "OMP_SPREAD"
  | OMP_TARGET                                       -> "OMP_TARGET"
  | OMP_TARGET_DATA                                  -> "OMP_TARGET_DATA"
  | OMP_TARGET_TEAMS                                 -> "OMP_TARGET_TEAMS"
  | OMP_TARGET_TEAMS_DISTRIBUTE                      -> "OMP_TARGET_TEAMS_DISTRIBUTE"
  | OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO          -> "OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO"
  | OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD     -> "OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD"
  | OMP_TARGET_TEAMS_DISTRIBUTE_SIMD                 -> "OMP_TARGET_TEAMS_DISTRIBUTE_SIMD"
  | OMP_TARGET_UPDATE                                -> "OMP_TARGET_UPDATE"
  | OMP_TASKGROUP                                    -> "OMP_TASKGROUP"
  | OMP_TEAMS                                        -> "OMP_TEAMS"
  | OMP_TEAMS_DISTRIBUTE                             -> "OMP_TEAMS_DISTRIBUTE"
  | OMP_TEAMS_DISTRIBUTE_PARALLEL_DO                 -> "OMP_TEAMS_DISTRIBUTE_PARALLEL_DO"
  | OMP_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD            -> "OMP_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD"
  | OMP_TEAMS_DISTRIBUTE_SIMD                        -> "OMP_TEAMS_DISTRIBUTE_SIMD"
  | OMP_THREAD_LIMIT                                 -> "OMP_THREAD_LIMIT"
  | OMP_TO                                           -> "OMP_TO"
  | OMP_TOFROM                                       -> "OMP_TOFROM"
  | OMP_UNIFORM                                      -> "OMP_UNIFORM"

  | RAW {DL.tag=tag; DL.line=l; DL.fixed_cont=fxc; DL.free_cont=frc; _} ->
      sprintf "RAW%s:%s[fixed_cont:%B,free_cont:%B]" (DL.tag_to_string tag) l fxc frc

  | OMP _                      -> "OMP"

  | ACC_ATOMIC            -> "ACC_ATOMIC"
  | ACC_CACHE             -> "ACC_CACHE"
  | ACC_DATA              -> "ACC_DATA"
  | ACC_DECLARE           -> "ACC_DECLARE"
  | ACC_END               -> "ACC_END"
  | ACC_ENTER             -> "ACC_ENTER"
  | ACC_EXIT              -> "ACC_EXIT"
  | ACC_HOST_DATA         -> "ACC_HOST_DATA"
  | ACC_KERNELS           -> "ACC_KERNELS"
  | ACC_LOOP              -> "ACC_LOOP"
  | ACC_PARALLEL          -> "ACC_PARALLEL"
  | ACC_ROUTINE           -> "ACC_ROUTINE"
  | ACC_UPDATE            -> "ACC_UPDATE"
  | ACC_WAIT              -> "ACC_WAIT"

  | ACC_ASYNC              -> "ACC_ASYNC"
  | ACC_AUTO               -> "ACC_AUTO"
  | ACC_BIND               -> "ACC_BIND"
  | ACC_CAPTURE            -> "ACC_CAPTURE"
  | ACC_COLLAPSE           -> "ACC_COLLAPSE"
  | ACC_COPY               -> "ACC_COPY"
  | ACC_COPYIN             -> "ACC_COPYIN"
  | ACC_COPYOUT            -> "ACC_COPYOUT"
  | ACC_CREATE             -> "ACC_CREATE"
  | ACC_DEFAULT            -> "ACC_DEFAULT"
  | ACC_DELETE             -> "ACC_DELETE"
  | ACC_DEVICE             -> "ACC_DEVICE"
  | ACC_DEVICEPTR          -> "ACC_DEVICEPTR"
  | ACC_DEVICE_RESIDENT    -> "ACC_DEVICE_RESIDENT"
  | ACC_DEVICE_TYPE        -> "ACC_DEVICE_TYPE"
  | ACC_DTYPE              -> "ACC_DTYPE"
  | ACC_FIRSTPRIVATE       -> "ACC_FIRSTPRIVATE"
  | ACC_GANG               -> "ACC_GANG"
  | ACC_HOST               -> "ACC_HOST"
  | ACC_IF                 -> "ACC_IF"
  | ACC_INDEPENDENT        -> "ACC_INDEPENDENT"
  | ACC_LINK               -> "ACC_LINK"
  | ACC_NOHOST             -> "ACC_NOHOST"
  | ACC_NONE               -> "ACC_NONE"
  | ACC_NUM_GANGS          -> "ACC_NUM_GANGS"
  | ACC_NUM_WORKERS        -> "ACC_NUM_WORKERS"
  | ACC_PCOPY              -> "ACC_PCOPY"
  | ACC_PCOPYIN            -> "ACC_PCOPYIN"
  | ACC_PCOPYOUT           -> "ACC_PCOPYOUT"
  | ACC_PCREATE            -> "ACC_PCREATE"
  | ACC_PRESENT            -> "ACC_PRESENT"
  | ACC_PRESENT_OR_COPY    -> "ACC_PRESENT_OR_COPY"
  | ACC_PRESENT_OR_COPYIN  -> "ACC_PRESENT_OR_COPYIN"
  | ACC_PRESENT_OR_COPYOUT -> "ACC_PRESENT_OR_COPYOUT"
  | ACC_PRESENT_OR_CREATE  -> "ACC_PRESENT_OR_CREATE"
  | ACC_PRIVATE            -> "ACC_PRIVATE"
  | ACC_READ               -> "ACC_READ"
  | ACC_REDUCTION          -> "ACC_REDUCTION"
  | ACC_SELF               -> "ACC_SELF"
  | ACC_SEQ                -> "ACC_SEQ"
  | ACC_TILE               -> "ACC_TILE"
  | ACC_USE_DEVICE         -> "ACC_USE_DEVICE"
  | ACC_VECTOR             -> "ACC_VECTOR"
  | ACC_VECTOR_LENGTH      -> "ACC_VECTOR_LENGTH"
  | ACC_WORKER             -> "ACC_WORKER"
  | ACC_WRITE              -> "ACC_WRITE"

  | ACC _ -> "ACC"

  | XLF_ALIGN               -> "XLF_ALIGN"
  | XLF_ASSERT              -> "XLF_ASSERT"
  | XLF_BLOCK_LOOP          -> "XLF_BLOCK_LOOP"
  | XLF_CNCALL              -> "XLF_CNCALL"
  | XLF_COLLAPSE            -> "XLF_COLLAPSE"
  | XLF_EJECT               -> "XLF_EJECT"
  | XLF_EXECUTION_FREQUENCY -> "XLF_EXECUTION_FREQUENCY"
  | XLF_EXPECTED_VALUE      -> "XLF_EXPECTED_VALUE"
  | XLF_FUNCTRACE_XLF_CATCH -> "XLF_FUNCTRACE_XLF_CATCH"
  | XLF_FUNCTRACE_XLF_ENTER -> "XLF_FUNCTRACE_XLF_ENTER"
  | XLF_FUNCTRACE_XLF_EXIT  -> "XLF_FUNCTRACE_XLF_EXIT"
  | XLF_IGNORE_TKR          -> "XLF_IGNORE_TKR"
  | XLF_INDEPENDENT         -> "XLF_INDEPENDENT"
  | XLF_LOOPID              -> "XLF_LOOPID"
  | XLF_MEM_DELAY           -> "XLF_MEM_DELAY"
  | XLF_NEW                 -> "XLF_NEW"
  | XLF_NOFUNCTRACE         -> "XLF_NOFUNCTRACE"
  | XLF_NOSIMD              -> "XLF_NOSIMD"
  | XLF_NOVECTOR            -> "XLF_NOVECTOR"
  | XLF_PERMUTATION         -> "XLF_PERMUTATION"
  | XLF_SNAPSHOT            -> "XLF_SNAPSHOT"
  | XLF_SOURCEFORM          -> "XLF_SOURCEFORM"
  | XLF_STREAM_UNROLL       -> "XLF_STREAM_UNROLL"
  | XLF_SUBSCRIPTORDER      -> "XLF_SUBSCRIPTORDER"
  | XLF_UNROLL              -> "XLF_UNROLL"
  | XLF_UNROLL_AND_FUSE     -> "XLF_UNROLL_AND_FUSE"
  | XLF_PROCESS             -> "XLF_PROCESS"

  | XLF_ITERCNT    -> "XLF_ITERCNT"
  | XLF_MINITERCNT -> "XLF_MINITERCNT"
  | XLF_MAXITERCNT -> "XLF_MAXITERCNT"
  | XLF_NODEPS     -> "XLF_NODEPS"
  | XLF_REDUCTION  -> "XLF_REDUCTION"
(*
  | XLF_MAX       -> "XLF_MAX"
  | XLF_MIN       -> "XLF_MIN"
  | XLF_IAND      -> "XLF_IAND"
  | XLF_IEOR      -> "XLF_IEOR"
*)
  | XLF_FIXED     -> "XLF_FIXED"
  | XLF_FREE      -> "XLF_FREE"
  | XLF_F90       -> "XLF_F90"
  | XLF_IBM       -> "XLF_IBM"

  | XLF_VERY_HIGH -> "XLF_VERY_HIGH"
  | XLF_VERY_LOW  -> "XLF_VERY_LOW"

  (*| RAWXLF(t, s, _, _) -> "RAWXLF:"^t^":"^s*)
  | XLF _              -> "XLF"

  | DEC_ALIAS             -> "DEC_ALIAS"
  | DEC_ASSUME            -> "DEC_ASSUME"
  | DEC_ASSUME_ALIGNED    -> "DEC_ASSUME_ALIGNED"
  | DEC_ATTRIBUTES        -> "DEC_ATTRIBUTES"
  | DEC_BLOCK_LOOP        -> "DEC_BLOCK_LOOP"
  | DEC_NOBLOCK_LOOP      -> "DEC_NOBLOCK_LOOP"
  | DEC_CODE_ALIGN        -> "DEC_CODE_ALIGN"
  | DEC_DECLARE           -> "DEC_DECLARE"
  | DEC_NODECLARE         -> "DEC_NODECLARE"
  | DEC_DEFINE            -> "DEC_DEFINE"
  | DEC_UNDEFINE          -> "DEC_UNDEFINE"
  | DEC_DISTRIBUTE        -> "DEC_DISTRIBUTE"
  | DEC_POINT             -> "DEC_POINT"
  | DEC_FIXEDFORMLINESIZE -> "DEC_FIXEDFORMLINESIZE"
  | DEC_FMA               -> "DEC_FMA"
  | DEC_NOFMA             -> "DEC_NOFMA"
  | DEC_FREEFORM          -> "DEC_FREEFORM"
  | DEC_NOFREEFORM        -> "DEC_NOFREEFORM"
  | DEC_IDENT             -> "DEC_IDENT"
  | DEC_IF                -> "DEC_IF"
  | DEC_DEFINED           -> "DEC_DEFINED"
  | DEC_INLINE            -> "DEC_INLINE"
  | DEC_FORCEINLINE       -> "DEC_FORCEINLINE"
  | DEC_NOINLINE          -> "DEC_NOINLINE"
  | DEC_INTEGER           -> "DEC_INTEGER"
  | DEC_IVDEP             -> "DEC_IVDEP"
  | DEC_INIT_DEP_FWD      -> "DEC_INIT_DEP_FWD"
  | DEC_LOOP              -> "DEC_LOOP"
  | DEC_COUNT             -> "DEC_COUNT"
  | DEC_MESSAGE           -> "DEC_MESSAGE"
  | DEC_NOFUSION          -> "DEC_NOFUSION"
  | DEC_OBJCOMMENT        -> "DEC_OBJCOMMENT"
  | DEC_OPTIMIZE          -> "DEC_OPTIMIZE"
  | DEC_NOOPTIMIZE        -> "DEC_NOOPTIMIZE"
  | DEC_OPTIONS           -> "DEC_OPTIONS"
  | DEC_PACK              -> "DEC_PACK"
  | DEC_PARALLEL          -> "DEC_PARALLEL"
  | DEC_NOPARALLEL        -> "DEC_NOPARALLEL"
  | DEC_PREFETCH          -> "DEC_PREFETCH"
  | DEC_NOPREFETCH        -> "DEC_NOPREFETCH"
  | DEC_PSECT             -> "DEC_PSECT"
  | DEC_REAL              -> "DEC_REAL"
  | DEC_SIMD              -> "DEC_SIMD"
  | DEC_STRICT            -> "DEC_STRICT"
  | DEC_NOSTRICT          -> "DEC_NOSTRICT"
  | DEC_UNROLL            -> "DEC_UNROLL"
  | DEC_NOUNROLL          -> "DEC_NOUNROLL"
  | DEC_UNROLL_AND_JAM    -> "DEC_UNROLL_AND_JAM"
  | DEC_NOUNROLL_AND_JAM  -> "DEC_NOUNROLL_AND_JAM"
  | DEC_VECTOR            -> "DEC_VECTOR"
  | DEC_NOVECTOR          -> "DEC_NOVECTOR"

  | DEC_DISTRIBUTEPOINT   -> "DEC_DISTRIBUTEPOINT"
  | DEC_LOOPCOUNT         -> "DEC_LOOPCOUNT"
  | DEC_IFDEFINED         -> "DEC_IFDEFINED"
  | DEC_ELSEIF            -> "DEC_ELSEIF"
  | DEC_ELSE              -> "DEC_ELSE"
  | DEC_ENDIF             -> "DEC_ENDIF"

  | DEC_ALWAYS            -> "DEC_ALWAYS"
  | DEC_ASSERT            -> "DEC_ASSERT"
  | DEC_ALIGNED           -> "DEC_ALIGNED"
  | DEC_UNALIGNED         -> "DEC_UNALIGNED"
  | DEC_TEMPORAL          -> "DEC_TEMPORAL"
  | DEC_NONTEMPORAL       -> "DEC_NONTEMPORAL"
  | DEC_VECREMAINDER      -> "DEC_VECREMAINDER"
  | DEC_NOVECREMAINDER    -> "DEC_NOVECREMAINDER"
  | DEC_NOASSERT          -> "DEC_NOASSERT"
  | DEC_FIRSTPRIVATE      -> "DEC_FIRSTPRIVATE"
  | DEC_LASTPRIVATE       -> "DEC_LASTPRIVATE"
  | DEC_LINEAR            -> "DEC_LINEAR"
  | DEC_PRIVATE           -> "DEC_PRIVATE"
  | DEC_REDUCTION         -> "DEC_REDUCTION"
  | DEC_VECTORLENGTH      -> "DEC_VECTORLENGTH"
  | DEC_VECTORLENGTHFOR   -> "DEC_VECTORLENGTHFOR"
  | DEC_NUM_THREADS       -> "DEC_NUM_THREADS"
  | DEC_END               -> "DEC_END"
  | DEC_ENDOPTIONS        -> "DEC_ENDOPTIONS"

  | DEC_ALIGN             -> "DEC_ALIGN"
  | DEC_NOALIGN           -> "DEC_NOALIGN"
  | DEC_WRT               -> "DEC_WRT"
  | DEC_NOWRT             -> "DEC_NOWRT"
  | DEC_WARN              -> "DEC_WARN"
  | DEC_OFFLOAD_ATTRIBUTE_TARGET -> "DEC_OFFLOAD_ATTRIBUTE_TARGET"
  | DEC_ALIGNMENT         -> "DEC_ALIGNMENT"
  | DEC_NOALIGNMENT       -> "DEC_NOALIGNMENT"
  | DEC_RECURSIVE         -> "DEC_RECURSIVE"

  | DEC_MASK      -> "DEC_MASK"
  | DEC_NOMASK    -> "DEC_NOMASK"
  | DEC_PROCESSOR -> "DEC_PROCESSOR"
  | DEC_UNIFORM   -> "DEC_UNIFORM"

  | DEC_FACTOR -> "DEC_FACTOR"
  | DEC_LEVEL  -> "DEC_LEVEL"

  (*| RAWDEC(p, s) -> "RAWDEC:"^p^":"^s*)
  | DEC _        -> "DEC"

  | LINDA_TYPEOF _ -> "LINDA_TYPEOF"



(*
  | LBRACE                       -> "LBRACE"
  | RBRACE                       -> "RBRACE"
*)

  | EXCLAM                 -> "EXCLAM"
  | DOLLAR                 -> "DOLLAR"
  | BACKSLASH              -> "BACKSLASH"
  | QUESTION               -> "QUESTION"

  | PERCENT                -> "PERCENT"
  | AMP                    -> "AMP"

  | LPAREN                  -> "LPAREN"
  | LPAREN__IMPLICIT        -> "LPAREN__IMPLICIT"
  | LPAREN__GO_TO           -> "LPAREN__GO_TO"
  | LPAREN__io_control_spec -> "LPAREN__io_control_spec"
  | LPAREN__position_spec   -> "LPAREN__position_spec"
  | LPAREN__flush_spec      -> "LPAREN__flush_spec"

  | RPAREN                  -> "RPAREN"

  | LBRACKET               -> "LBRACKET"
  | RBRACKET               -> "RBRACKET"

  | STAR                   -> "STAR"
  | SLASH                  -> "SLASH"
  | PLUS                   -> "PLUS"
  | MINUS                  -> "MINUS"
  | UPLUS                  -> "UPLUS"
  | UMINUS                 -> "UMINUS"

  | COMMA                  -> "COMMA"
  | COMMA__SLASH           -> "COMMA__SLASH"
  | DOT                    -> "DOT"
  | COLON                  -> "COLON"
  | SEMICOLON              -> "SEMICOLON"

  | LT                     -> "LT"
  | EQ                     -> "EQ"
  | GT                     -> "GT"

  | VFE_BEGIN s -> "VFE_BEGIN"^(if s = "" then "" else ":"^s) (* Variable Format Expr *)
  | VFE_END s   -> "VFE_END"^(if s = "" then "" else ":"^s)   (* Variable Format Expr *)

  | STAR_STAR              -> "STAR_STAR"

  | LT_EQ        -> "LT_EQ"
  | GT_EQ        -> "GT_EQ"
  | EQ_EQ        -> "EQ_EQ"

  | EQ_GT        -> "EQ_GT"


  | COLON_COLON  -> "COLON_COLON"

  | SLASH_SLASH  -> "SLASH_SLASH"

  | SLASH_EQ     -> "SLASH_EQ"

  | LPAREN_SLASH -> "LPAREN_SLASH"

  | SLASH_RPAREN -> "SLASH_RPAREN"


  | IDENTIFIER s -> "IDENTIFIER:"^s

  | COMPOSITE_IDENTIFIER(b, s, ol) ->
      sprintf "COMPOSITE_IDENTIFIER[%s|%s](force_decomposition=%B)"
        s (Xlist.to_string (fun o -> rawtoken_to_string (Obj.obj o)) ";" ol) b

  | CONTINUED_IDENTIFIER s -> "CONTINUED_IDENTIFIER:"^s

  | INT_LITERAL s     -> "INT_LITERAL:"^s
  | REAL_LITERAL s    -> "REAL_LITERAL:"^s
  | BOZ_LITERAL s     -> "BOZ_LITERAL:"^s
  | LOGICAL_LITERAL s -> "LOGICAL_LITERAL:"^s
  | CHAR_LITERAL s    -> "CHAR_LITERAL:"^s
(*  | COMPLEX_LITERAL(r, i) -> "COMPLEX_LITERAL:"^r^":"^i *)

  | DEFINED_OP s -> "DEFINED_OP:"^s

  | DATA_EDIT_DESC s        -> "DATA_EDIT_DESC:"^s
  | KP_DESC s               -> "KP_DESC:"^s
  | POSITION_EDIT_DESC s    -> "POSITION_EDIT_DESC:"^s
  | HOLLERITH(s, b)         -> sprintf "HOLLERITH:%s(partial=%B)" s b

  | LABEL s -> "LABEL:"^s

  | LETTER s -> "LETTER:"^s

  | CONSTRUCT_NAME s        -> "CONSTRUCT_NAME:"^s
(*
  | DO_CONSTRUCT_NAME s     -> "DO_CONSTRUCT_NAME:"^s
  | IF_CONSTRUCT_NAME s     -> "IF_CONSTRUCT_NAME:"^s
  | WHERE_CONSTRUCT_NAME s  -> "WHERE_CONSTRUCT_NAME:"^s
  | FORALL_CONSTRUCT_NAME s -> "FORALL_CONSTRUCT_NAME:"^s
  | CASE_CONSTRUCT_NAME s   -> "CASE_CONSTRUCT_NAME:"^s
  | SELECT_CONSTRUCT_NAME s -> "SELECT_CONSTRUCT_NAME:"^s
  | ASSOCIATE_CONSTRUCT_NAME s -> "ASSOCIATE_CONSTRUCT_NAME:"^s
*)

(* dotted identifiers *)
  | D_EQ    -> "D_EQ"
  | D_NE    -> "D_NE"
  | D_GT    -> "D_GT"
  | D_GE    -> "D_GE"
  | D_LT    -> "D_LT"
  | D_LE    -> "D_LE"
  | D_NOT   -> "D_NOT"
  | D_AND   -> "D_AND"
  | D_OR    -> "D_OR"
  | D_EQV   -> "D_EQV"
  | D_NEQV  -> "D_NEQV"
(*
  | D_TRUE  -> "D_TRUE"
  | D_FALSE -> "D_FALSE"
*)

(* keywords *)
  | ABSTRACT _         -> "ABSTRACT"     (* F2003*)
  | ALLOCATABLE _      -> "ALLOCATABLE"
  | ALLOCATE _         -> "ALLOCATE"
  | ASSIGN _           -> "ASSIGN"       (* F90 *)
  | ASSIGNMENT _       -> "ASSIGNMENT"
  | ASSOCIATE _        -> "ASSOCIATE"    (* F2003*)
  | ASYNCHRONOUS _     -> "ASYNCHRONOUS" (* F2003*)
  | BACKSPACE _        -> "BACKSPACE"
  | BIND _             -> "BIND"         (* F2003*)
  | BLOCK _            -> "BLOCK"        (* F2008 *)
  | BLOCK_DATA _       -> "BLOCK_DATA"
  | BYTE _             -> "BYTE"
  | CALL _             -> "CALL"
  | CASE _             -> "CASE"
  | CHARACTER _        -> "CHARACTER"
  | CLASS _            -> "CLASS"
  | CLOSE _            -> "CLOSE"
  | CODIMENSION _      -> "CODIMENSION"
  | COMMON _           -> "COMMON"
(*  | COMPLEX _          -> "COMPLEX"*)
  | CONCURRENT _       -> "CONCURRENT"
  | CONTAINS _         -> "CONTAINS"
  | CONTINUE _         -> "CONTINUE"
  | CRITICAL _         -> "CRITICAL"
  | CYCLE _            -> "CYCLE"
  | DATA _             -> "DATA"
  | DEALLOCATE _       -> "DEALLOCATE"
  | DEFAULT _          -> "DEFAULT"
  | DIMENSION _        -> "DIMENSION"
  | DO _               -> "DO"
  | DOUBLE _           -> "DOUBLE"
  | DOUBLE_PRECISION _ -> "DOUBLE_PRECISION"
  | DOUBLE_COMPLEX   _ -> "DOUBLE_COMPLEX"
(*  | ELEMENTAL _        -> "ELEMENTAL"*)
  | ELSE _             -> "ELSE"
  | ELSE_IF _          -> "ELSE_IF"
  | ELSEWHERE _        -> "ELSEWHERE"
  | END _              -> "END"
  | END_ASSOCIATE _    -> "END_ASSOCIATE"
  | END_BLOCK _        -> "END_BLOCK"
  | END_BLOCK_DATA _   -> "END_BLOCK_DATA"
  | END_CRITICAL _     -> "END_CRITICAL"
  | END_DO _           -> "END_DO"
  | END_ENUM _         -> "END_ENUM"    (* F2003 *)
  | END_FILE _         -> "END_FILE"
  | END_FORALL _       -> "END_FORALL"
(*  | END_FUNCTION _     -> "END_FUNCTION"*)
  | END_IF _           -> "END_IF"
  | END_INTERFACE _    -> "END_INTERFACE"
  | END_MODULE _       -> "END_MODULE"
  | END_PROCEDURE _    -> "END_PROCEDURE"
  | END_PROGRAM _      -> "END_PROGRAM"
  | END_SELECT _       -> "END_SELECT"
  | END_SUBMODULE _    -> "END_SUBMODULE" (* F2008 *)
  | END_SUBPROGRAM s   -> sprintf "END_SUBPROGRAM(%s)" s
(*  | END_SUBROUTINE _   -> "END_SUBROUTINE"*)
  | END_TYPE _         -> "END_TYPE"
  | END_WHERE _        -> "END_WHERE"
  | ENTRY _            -> "ENTRY"
  | ENUM _             -> "ENUM"          (* F2003 *)
  | ENUMERATOR _       -> "ENUMMERATOR"   (* F2003 *)
(*  | ERRMSG _           -> "ERRMSG"        (* F2003 *)*)
  | ERROR _            -> "ERROR"         (* F2008 *)
  | EQUIVALENCE _      -> "EQUIVALENCE"
  | EXIT _             -> "EXIT"
  | EXTENDS _          -> "EXTENDS"       (* F2003 *)
(*  | EXTERNAL _         -> "EXTERNAL"*)
  | FLUSH _            -> "FLUSH"         (* F2003 *)
  | FORALL _           -> "FORALL"
  | FORMAT _           -> "FORMAT"
  | FUNCTION _         -> "FUNCTION"
  | GENERIC _          -> "GENERIC"       (* F2003 *)
  | GO_TO _            -> "GO_TO"
  | ID _               -> "ID"            (* F2003 *)
  | IF _               -> "IF"
  | IMPLICIT _         -> "IMPLICIT"
  | IMPORT _           -> "IMPORT"        (* F2003 *)
(*  | IMPURE _           -> "IMPURE"        (* F2008 *)*)
(*
  | IN _               -> "IN"
  | IN_OUT _           -> "IN_OUT"
*)
  | INQUIRE _          -> "INQUIRE"
(*  | INTEGER _          -> "INTEGER"*)
  | INTENT _           -> "INTENT"
  | INTENT_SPEC s      -> "INTENT_SPEC:"^s
  | INTERFACE _        -> "INTERFACE"
  | INTRINSIC _        -> "INTRINSIC"
  | KIND _             -> "KIND"
  | KINDED_TYPE_SPEC s -> "KINDED_TYPE_SPEC:"^s
  | LEN _              -> "LEN"
  | LOCK _             -> "LOCK"
(*  | LOGICAL _          -> "LOGICAL"*)
  | MODULE _           -> "MODULE"
(*  | MOLD _             -> "MOLD"      (* F2008 *)*)
  | ALLOC_OPT_EXPR s   -> "ALLOC_OPT_EXPR:"^s (* MOLD or SOURCE *)
  | NAMELIST _         -> "NAMELIST"
  | NONE _             -> "NONE"
  | NON_INTRINSIC _    -> "NON_INTRINSIC" (* F2003 *)
  | NULL _             -> "NULL"
  | NULLIFY _          -> "NULLIFY"
  | ONLY _             -> "ONLY"
  | OPEN _             -> "OPEN"
  | OPERATOR _         -> "OPERATOR"
  | OPTIONAL _         -> "OPTIONAL"
(*  | OUT _              -> "OUT"*)
  | PARAMETER _        -> "PARAMETER"
  | PAUSE _            -> "PAUSE"     (* F90 *)
  | POINTER _          -> "POINTER"
  | PRECISION _        -> "PRECISION"
  | PREFIX_SPEC s      -> "PREFIX_SPEC:"^s
  | PRINT _            -> "PRINT"
  | PRIVATE _          -> "PRIVATE"
  | PROCEDURE _        -> "PROCEDURE"
  | PROGRAM _          -> "PROGRAM"
(*  | PROTECTED _        -> "PROTECTED" (* F2003 *)*)
  | PUBLIC _           -> "PUBLIC"
(*  | PURE _             -> "PURE"*)
  | READ _             -> "READ"
(*  | REAL _             -> "REAL"*)
(*  | RECURSIVE _        -> "RECURSIVE"*)
  | RESULT _           -> "RESULT"
  | RETURN _           -> "RETURN"
  | REWIND _           -> "REWIND"
  | SAVE _             -> "SAVE"
  | SELECT_CASE _      -> "SELECT_CASE"
  | SELECT_TYPE _      -> "SELECT_TYPE" (* F2003 *)
  | SEQUENCE _         -> "SEQUENCE"
(*  | SOURCE _           -> "SOURCE"   (* F2003 *)*)
(*  | STAT _             -> "STAT"*)
  | STOP _             -> "STOP"
  | SUBMODULE _        -> "SUBMODULE"  (* F2008 *)
  | SUBROUTINE _       -> "SUBROUTINE"
  | SYNC _             -> "SYNC"
  | TARGET _           -> "TARGET"
  | THEN _             -> "THEN"
  | TO _               -> "TO"       (* F90 *)
  | TYPE _             -> "TYPE"
  | USE _              -> "USE"
(*
  | VALUE _            -> "VALUE"    (* F2003 *)
  | VOLATILE _         -> "VOLATILE" (* F2003 *)
*)
  | WAIT _             -> "WAIT"     (* F2003 *)
  | WHERE _            -> "WHERE"
  | WHILE _            -> "WHILE"
  | WRITE _            -> "WRITE"
(*
  | ACCESS _   -> "ACCESS"
  | ACTION _   -> "ACTION"
  | BLANK _    -> "BLANK"
  | DELIM _    -> "DELIM"
  | FORM _     -> "FORM"
  | PAD _      -> "PAD"
  | POSITION _ -> "POSITION"
  | RECL _     -> "RECL"
*)
  | ERR _      -> "ERR"
  | FILE _     -> "FILE"
  | IOSTAT _   -> "IOSTAT"
  | IOMSG _    -> "IOMSG" (* F2003 *)
(*  | POS _      -> "POS"*)
  | STATUS _   -> "STATUS"
  | UNIT _     -> "UNIT"

  | FMT _     -> "FMT"
  | NML _     -> "NML"
(*
  | REC _     -> "REC"
  | ADVANCE _ -> "ADVANCE"
*)
  | SIZE _    -> "SIZE"
  | EOR _     -> "EOR"
(*
  | DIRECT _      -> "DIRECT"
  | EXIST _       -> "EXIST"
  | FORMATTED _   -> "FORMATTED"
  | NAMED _       -> "NAMED"
  | NEXTREC _     -> "NEXTREC"
  | NUMBER _      -> "NUMBER"
  | OPENED _      -> "OPENED"
  | READWRITE _   -> "READWRITE"
  | SEQUENTIAL _  -> "SEQUENTIAL"
  | UNFORMATTED _ -> "UNFORMATTED"
*)
  | NAME_ _       -> "NAME"
  | IOLENGTH _    -> "IOLENGTH"


  | CONNECT_SPEC s -> "CONNECT_SPEC:"^s
  | INQUIRE_SPEC s -> "INQUIRE_SPEC:"^s
  | IOCTL_SPEC s   -> "IOCTL_SPEC:"^s

  | CONNECT_INQUIRE_IOCTL_SPEC s -> "CONNECT_INQUIRE_IOCTL_SPEC:"^s
  | CONNECT_INQUIRE_SPEC s       -> "CONNECT_INQUIRE_SPEC:"^s
  | INQUIRE_IOCTL_SPEC s         -> "INQUIRE_IOCTL_SPEC:"^s

(* Compaq Fortran *)
(*
  | AUTOMATIC s       -> "AUTOMATIC"
  | STATIC s          -> "STATIC"
*)
  | OPTIONS__OPTS s   -> "OPTIONS__OPTS:"^s
  | ACCEPT _          -> "ACCEPT"
  | REWRITE _         -> "REWRITE"
  | DELETE _          -> "DELETE"
  | UNLOCK _          -> "UNLOCK"
  | DEFINE_FILE       -> "DEFINE_FILE"
  | ENCODE _          -> "ENCODE"
  | DECODE _          -> "DECODE"
  | FIND _            -> "FIND"
  | VIRTUAL _         -> "VIRTUAL"
  | STRUCTURE _       -> "STRUCTURE"
  | END_STRUCTURE _   -> "END_STRUCTURE"
  | RECORD _          -> "RECORD"
  | UNION _           -> "UNION"
  | END_UNION _       -> "END_UNION"
  | MAP _             -> "MAP"
  | END_MAP _         -> "END_MAP"

  | INTEL_CLOSE_CONNECT_SPEC s   -> "INTEL_CLOSE_CONNECT_SPEC:"^s
(*
  | INTEL_CONNECT_SPEC s         -> "INTEL_CONNECT_SPEC:"^s
  | INTEL_CONNECT_INQUIRE_SPEC s -> "INTEL_CONNECT_INQUIRE_SPEC:"^s
  | INTEL_INQUIRE_SPEC s         -> "INTEL_INQUIRE_SPEC:"^s
*)


  | PASS _            -> "PASS"            (* F2003 *)
  | NOPASS _          -> "NOPASS"          (* F2003 *)
  | NON_OVERRIDABLE _ -> "NON_OVERRIDABLE" (* F2003 *)
  | DEFERRED _        -> "DEFERRED"        (* F2003 *)

  | FINAL _ -> "FINAL" (* F2003 *)

  | TYPE_IS _       -> "TYPE_IS"       (* F2003 *)
  | CLASS_IS _      -> "CLASS_IS"      (* F2003 *)
  | CLASS_DEFAULT _ -> "CLASS_DEFAULT" (* F2003 *)

  | EOL -> "EOL"

  | EOF o_opt -> "EOF"^(Common.opt_to_string (fun _ -> "(EOL pending)") o_opt)

  | EOP -> "EOP"

  | NOTHING -> "NOTHING"

  | MARKER -> "MARKER"
  | PP_MARKER -> "PP_MARKER"

  | END_FRAGMENT -> "END_FRAGMENT"

  | INCLUDE__FILE s -> "INCLUDE__FILE:"^s

  | SIMPLE_ATTR s -> "SIMPLE_ATTR:"^s

(*
  | _ -> "<impossible>"
*)


let rawtoken_size = function

  | ERROR _ -> 0

  | PROGRAM_UNIT(spec, _)
  | SPEC_PART_CONSTRUCT(spec, _)
  | EXEC_PART_CONSTRUCT(spec, _)
  | SUBPROGRAM(spec, _)
  | INTERFACE_SPEC(spec, _)
  | CASE_BLOCK(spec, _)
  | DATA_STMT_SET(spec, _)
  | STMT(spec, _)
  | ACTION_STMT(spec, _)
  | VARIABLE(spec, _)
  | EXPR(spec, _)
  | TYPE_SPEC(spec, _)
  | DERIVED_TYPE_DEF_PART(spec, _)
  | ONLY_(spec, _)
    -> spec.Ast.Partial.length

  | DO_STMT(spec, _)
  | FORALL_CONSTRUCT_STMT(spec, _)
  | IF_THEN_STMT(spec, _)
  | SELECT_CASE_STMT(spec, _)
  | WHERE_CONSTRUCT_STMT(spec, _)
  | DERIVED_TYPE_STMT(spec, _)

  | END_DO_STMT(spec, _)
  | END_FORALL_STMT(spec, _)
  | END_IF_STMT(spec, _)
  | END_SELECT_STMT(spec, _)
  | END_WHERE_STMT(spec, _)
  | END_TYPE_STMT(spec, _)

  | FUNCTION_HEAD(spec, _)
  | FUNCTION_STMT_HEAD(spec, _)
  | SUBROUTINE_HEAD(spec, _)
  | SUBROUTINE_STMT_HEAD(spec, _)
  | PU_TAIL(spec, _)

    -> spec.Ast.Partial.length


  | PP_IDENTIFIER s      -> String.length s

  | PP_UNDERSCORE s      -> String.length s

  | PP_MACRO_CONST s
(*  | PP_MACRO_CONST_CHAR s
  | PP_MACRO_CONST_INT s*)
  | PP_MACRO_NAME(s, _)
  | PP_MACRO_VARIABLE s
  | PP_MACRO_EXPR s
  | PP_MACRO_STMT s
  | PP_MACRO_TYPE_SPEC s
  | PP_MACRO_WRITE s
  | PP_MACRO_READ_WRITE s
  | PP_MACRO_READ_PRINT s -> String.length s


  | PP_MACRO_ID(_, s)    -> String.length s
  | PP_MACRO_ID_RW(_, s) -> String.length s
  | PP_MACRO_APPL(s, sl) -> (String.length s) + (List.fold_left (fun sum s -> sum + (String.length s)) 0 sl) + 1 + (List.length sl)


  | PP_DEFINE__IDENT__BODY(i, b) -> 7 + (String.length i) + (Macro.body_length b)
  | PP_INCLUDE__FILE h           -> 8 + (H.length h)
  | PP_BRANCH b                  -> PPD.length_of_branch b
(*
  | PP_IF__COND c                -> 3 + (String.length c)
  | PP_ELIF__COND c              -> 5 + (String.length c)
  | PP_IFDEF__IDENT i            -> 6 + (String.length i)
  | PP_IFNDEF__IDENT i           -> 7 + (String.length i)
*)
  | PP_ELSE              -> 5
  | PP_ENDIF             -> 6

  | PP_UNDEF__IDENT i            -> 6 + (String.length i)

  | PP_ISSUE__MESG m             -> PPD.length_of_message m
(*
  | PP_ERROR__MESG m             -> 6 + (String.length m)
  | PP_WARNING__MESG m           -> 8 + (String.length m)
*)
  | PP_UNKNOWN__REST(d, r)       -> (String.length d) + (String.length r)

  | PP_INCLUDE           -> 8
  | PP_DEFINE            -> 7
  | PP_UNDEF             -> 6
  | PP_IF                -> 3
  | PP_IFDEF             -> 6
  | PP_IFNDEF            -> 7
  | PP_ELIF              -> 5

  | PP_ERROR             -> 6
  | PP_WARNING           -> 8

  | PP_UNKNOWN           -> 0

  | PP_AND
  | PP_OR
  | PP_CONCAT
    -> 2


  | OCL_ARRAY_FUSION           -> 12
  | OCL_END_ARRAY_FUSION       -> 16
  | OCL_ARRAY_MERGE            -> 11
  | OCL_ARRAY_SUBSCRIPT        -> 15
  | OCL_EVAL                   -> 4
  | OCL_NOEVAL                 -> 6
  | OCL_FLTLD                  -> 5
  | OCL_NOFLTLD                -> 7
  | OCL_FP_RELAXED             -> 10
  | OCL_NOFP_RELAXED           -> 12
  | OCL_LOOP_INTERCHANGE       -> 16
  | OCL_LOOP_NOINTERCHANGE     -> 18
  | OCL_MFUNC                  -> 5
  | OCL_NOMFUNC                -> 7
  | OCL_NOARRAYPAD             -> 10
  | OCL_LOOP_NOFUSION          -> 13
  | OCL_PREEX                  -> 5
  | OCL_NOPREEX                -> 7
  | OCL_PREFETCH               -> 8
  | OCL_NOPREFETCH             -> 10
  | OCL_PREFETCH_CACHE_LEVEL   -> 20
  | OCL_PREFETCH_INFER         -> 14
  | OCL_PREFETCH_NOINFER       -> 16
  | OCL_PREFETCH_ITERATION     -> 18
  | OCL_PREFETCH_ITERATION_L2  -> 21
  | OCL_PREFETCH_READ          -> 13
  | OCL_PREFETCH_WRITE         -> 14
  | OCL_STRIPING               -> 8
  | OCL_NOSTRIPING             -> 10
  | OCL_SWP                    -> 3
  | OCL_NOSWP                  -> 5
  | OCL_LOOP_BLOCKING          -> 13
  | OCL_UNROLL                 -> 6
  | OCL_NOUNROLL               -> 8
  | OCL_NOVREC                 -> 6
  | OCL_SIMD                   -> 4
  | OCL_NOSIMD                 -> 6
  | OCL_CACHE_SECTOR_SIZE      -> 17
  | OCL_END_CACHE_SECTOR_SIZE  -> 21
  | OCL_CACHE_SUBSECTOR_ASSIGN -> 22
  | OCL_END_CACHE_SUBSECTOR    -> 19
  | OCL_FISSION_POINT          -> 13
  | OCL_LOOP_NOFISSION         -> 14
  | OCL_XFILL                  -> 5
  | OCL_NOXFILL                -> 7
  | OCL_PREFETCH_SEQUENTIAL    -> 19
  | OCL_PREFETCH_STRONG        -> 15
  | OCL_PREFETCH_NOSTRONG      -> 17
  | OCL_PREFETCH_STRONG_L2     -> 18
  | OCL_PREFETCH_NOSTRONG_L2   -> 20
  | OCL_FP_CONTRACT            -> 11
  | OCL_NOFP_CONTRACT          -> 13
  | OCL_LOOP_NOBLOCKING        -> 15
  | OCL_NORECURRENCE           -> 12
  | OCL_UXSIMD                 -> 6
  | OCL_NOUXSIMD               -> 8
  | OCL_ARRAY_PRIVATE          -> 13
  | OCL_NOARRAY_PRIVATE        -> 15
  | OCL_INDEPENDENT            -> 11
  | OCL_NOALIAS                -> 7
  | OCL_SERIAL                 -> 6
  | OCL_PARALLEL               -> 8
  | OCL_PARALLEL_STRONG        -> 15
  | OCL_REDUCTION              -> 9
  | OCL_NOREDUCTION            -> 11
  | OCL_TEMP                   -> 4

  | OCL_LOOP_PART_SIMD         -> 14
  | OCL_LOOP_NOPART_SIMD       -> 16
  | OCL_SHORTLOOP              -> 9
  | OCL_NOSHORTLOOP            -> 11
  | OCL_SIMD_LISTV             -> 10
  | OCL_UNSWITCHING            -> 11
  | OCL_LOOP_PART_PARALLEL     -> 18
  | OCL_LOOP_NOPART_PARALLEL   -> 20
  | OCL_FIRST_PRIVATE          -> 13
  | OCL_LAST_PRIVATE           -> 12
  | OCL_TEMP_PRIVATE           -> 12
  | OCL_PARALLEL_CYCLIC        -> 15

  | OCL_ALIGNED                -> 7
  | OCL_UNALIGNED              -> 9
  | OCL_LEVEL                  -> 6
  | OCL_STRONG                 -> 6
  | OCL_AUTO                   -> 4
  | OCL_SOFT                   -> 4
  | OCL_ALL                    -> 3
  | OCL_THEN                   -> 4
  | OCL_ELSE                   -> 4


  (*| RAWOCL s                   -> String.length s*)
  | OCL _                      -> 0

  | OMP_AUTO                   -> 4
  | OMP_ATOMIC                 -> 6
  | OMP_BARRIER                -> 7
  | OMP_CAPTURE                -> 7
  | OMP_COLLAPSE               -> 8
  | OMP_COPYIN                 -> 6
  | OMP_COPYPRIVATE            -> 11
  | OMP_CRITICAL               -> 8
  | OMP_DEFAULT                -> 7
  | OMP_DO                     -> 2
  | OMP_DYNAMIC                -> 7
  | OMP_END                    -> 3
  | OMP_FINAL                  -> 5
  | OMP_FIRSTPRIVATE           -> 12
  | OMP_FLUSH                  -> 4
  | OMP_GUIDED                 -> 6
  | OMP_IF                     -> 2
  | OMP_LASTPRIVATE            -> 11
  | OMP_MASTER                 -> 6
  | OMP_MERGEABLE              -> 9
  | OMP_NONE                   -> 4
  | OMP_NOWAIT                 -> 6
  | OMP_NUM_THREADS            -> 11
  | OMP_ORDERED                -> 7
  | OMP_PARALLEL               -> 8
  | OMP_PRIVATE                -> 7
  | OMP_READ                   -> 4
  | OMP_REDUCTION              -> 9
  | OMP_RUNTIME                -> 7
  | OMP_SCHEDULE               -> 8
  | OMP_SECTION                -> 7
  | OMP_SECTIONS               -> 8
  | OMP_SHARED                 -> 6
  | OMP_SINGLE                 -> 6
  | OMP_STATIC                 -> 6
  | OMP_TASK                   -> 4
  | OMP_TASKWAIT               -> 8
  | OMP_TASKYIELD              -> 9
  | OMP_THREADPRIVATE          -> 13
  | OMP_UNTIED                 -> 6
  | OMP_UPDATE                 -> 6
  | OMP_WORKSHARE              -> 9
  | OMP_WRITE                  -> 5
  | OMP_END_ATOMIC             -> 9
  | OMP_END_CRITICAL           -> 11
  | OMP_END_DO                 -> 5
  | OMP_END_MASTER             -> 9
  | OMP_END_ORDERED            -> 10
  | OMP_END_PARALLEL           -> 11
  | OMP_END_SECTIONS           -> 11
  | OMP_END_SINGLE             -> 9
  | OMP_END_TASK               -> 7
  | OMP_END_WORKSHARE          -> 12
  | OMP_PARALLEL_DO            -> 10
  | OMP_PARALLEL_SECTIONS      -> 16
  | OMP_PARALLEL_WORKSHARE     -> 17
  | OMP_END_PARALLEL_DO        -> 13
  | OMP_END_PARALLEL_SECTIONS  -> 19
  | OMP_END_PARALLEL_WORKSHARE -> 20

  (* for OpenMP 4.0 *)
  | OMP_ALIGNED                                      -> 7
  | OMP_ALLOC                                        -> 5
  | OMP_CANCEL                                       -> 6
  | OMP_CANCELLATION_POINT                           -> 17
  | OMP_CLOSE                                        -> 5
  | OMP_DECLARE_REDUCTION                            -> 16
  | OMP_DECLARE_SIMD                                 -> 11
  | OMP_DECLARE_TARGET                               -> 13
  | OMP_DEPEND                                       -> 6
  | OMP_DEVICE                                       -> 6
  | OMP_DIST_SCHEDULE                                -> 13
  | OMP_DISTRIBUTE                                   -> 10
  | OMP_DISTRIBUTE_PARALLEL_DO                       -> 20
  | OMP_DISTRIBUTE_PARALLEL_DO_SIMD                  -> 24
  | OMP_DISTRIBUTE_SIMD                              -> 14
  | OMP_DO_SIMD                                      -> 6
  | OMP_END_DISTRIBUTE                               -> 13
  | OMP_END_DISTRIBUTE_PARALLEL_DO                   -> 23
  | OMP_END_DISTRIBUTE_PARALLEL_DO_SIMD              -> 27
  | OMP_END_DISTRIBUTE_SIMD                          -> 17
  | OMP_END_DO_SIMD                                  -> 9
  | OMP_END_PARALLEL_DO_SIMD                         -> 17
  | OMP_END_SIMD                                     -> 7
  | OMP_END_TARGET                                   -> 9
  | OMP_END_TARGET_DATA                              -> 13
  | OMP_END_TARGET_TEAMS                             -> 14
  | OMP_END_TARGET_TEAMS_DISTRIBUTE                  -> 24
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO      -> 34
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD -> 38
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_SIMD             -> 27
  | OMP_END_TASKGROUP                                -> 12
  | OMP_END_TEAMS                                    -> 8
  | OMP_END_TEAMS_DISTRIBUTE                         -> 18
  | OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO             -> 28
  | OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD        -> 32
  | OMP_END_TEAMS_DISTRIBUTE_SIMD                    -> 22
  | OMP_FROM                                         -> 4
  | OMP_IN                                           -> 2
  | OMP_INBRANCH                                     -> 8
  | OMP_INITIALIZER                                  -> 11
  | OMP_INOUT                                        -> 5
  | OMP_LINEAR                                       -> 6
  | OMP_MAP                                          -> 3
  | OMP_NOTINBRANCH                                  -> 11
  | OMP_NUM_TEAMS                                    -> 9
  | OMP_OUT                                          -> 3
  | OMP_PARALLEL_DO_SIMD                             -> 14
  | OMP_PROC_BIND                                    -> 9
  | OMP_SAFELEN                                      -> 7
  | OMP_SEQ_CST                                      -> 7
  | OMP_SIMD                                         -> 4
  | OMP_SIMDLEN                                      -> 7
  | OMP_SPREAD                                       -> 6
  | OMP_TARGET                                       -> 6
  | OMP_TARGET_DATA                                  -> 10
  | OMP_TARGET_TEAMS                                 -> 11
  | OMP_TARGET_TEAMS_DISTRIBUTE                      -> 22
  | OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO          -> 34
  | OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD     -> 39
  | OMP_TARGET_TEAMS_DISTRIBUTE_SIMD                 -> 27
  | OMP_TARGET_UPDATE                                -> 12
  | OMP_TASKGROUP                                    -> 9
  | OMP_TEAMS                                        -> 5
  | OMP_TEAMS_DISTRIBUTE                             -> 16
  | OMP_TEAMS_DISTRIBUTE_PARALLEL_DO                 -> 28
  | OMP_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD            -> 33
  | OMP_TEAMS_DISTRIBUTE_SIMD                        -> 21
  | OMP_THREAD_LIMIT                                 -> 12
  | OMP_TO                                           -> 2
  | OMP_TOFROM                                       -> 6
  | OMP_UNIFORM                                      -> 7

  | RAW {DL.line=l;_} -> String.length l
  | OMP _           -> 0

  | ACC_ATOMIC             -> 6
  | ACC_CACHE              -> 5
  | ACC_DATA               -> 4
  | ACC_DECLARE            -> 7
  | ACC_END                -> 3
  | ACC_ENTER              -> 5
  | ACC_EXIT               -> 4
  | ACC_HOST_DATA          -> 9
  | ACC_KERNELS            -> 7
  | ACC_LOOP               -> 4
  | ACC_PARALLEL           -> 8
  | ACC_ROUTINE            -> 7
  | ACC_UPDATE             -> 6
  | ACC_WAIT               -> 4

  | ACC_ASYNC              -> 5
  | ACC_AUTO               -> 4
  | ACC_BIND               -> 4
  | ACC_CAPTURE            -> 7
  | ACC_COLLAPSE           -> 8
  | ACC_COPY               -> 4
  | ACC_COPYIN             -> 6
  | ACC_COPYOUT            -> 7
  | ACC_CREATE             -> 6
  | ACC_DEFAULT            -> 7
  | ACC_DELETE             -> 6
  | ACC_DEVICE             -> 6
  | ACC_DEVICEPTR          -> 9
  | ACC_DEVICE_RESIDENT    -> 15
  | ACC_DEVICE_TYPE        -> 11
  | ACC_DTYPE              -> 5
  | ACC_FIRSTPRIVATE       -> 12
  | ACC_GANG               -> 4
  | ACC_HOST               -> 4
  | ACC_IF                 -> 2
  | ACC_INDEPENDENT        -> 11
  | ACC_LINK               -> 4
  | ACC_NOHOST             -> 6
  | ACC_NONE               -> 4
  | ACC_NUM_GANGS          -> 9
  | ACC_NUM_WORKERS        -> 11
  | ACC_PCOPY              -> 5
  | ACC_PCOPYIN            -> 7
  | ACC_PCOPYOUT           -> 8
  | ACC_PCREATE            -> 7
  | ACC_PRESENT            -> 7
  | ACC_PRESENT_OR_COPY    -> 15
  | ACC_PRESENT_OR_COPYIN  -> 17
  | ACC_PRESENT_OR_COPYOUT -> 18
  | ACC_PRESENT_OR_CREATE  -> 17
  | ACC_PRIVATE            -> 7
  | ACC_READ               -> 4
  | ACC_REDUCTION          -> 9
  | ACC_SELF               -> 4
  | ACC_SEQ                -> 3
  | ACC_TILE               -> 4
  | ACC_USE_DEVICE         -> 10
  | ACC_VECTOR             -> 6
  | ACC_VECTOR_LENGTH      -> 13
  | ACC_WORKER             -> 6
  | ACC_WRITE              -> 5

  | ACC _ -> 0

  | XLF_ALIGN               -> 5
  | XLF_ASSERT              -> 6
  | XLF_BLOCK_LOOP          -> 10
  | XLF_CNCALL              -> 6
  | XLF_COLLAPSE            -> 8
  | XLF_EJECT               -> 5
  | XLF_EXECUTION_FREQUENCY -> 19
  | XLF_EXPECTED_VALUE      -> 14
  | XLF_FUNCTRACE_XLF_CATCH -> 19
  | XLF_FUNCTRACE_XLF_ENTER -> 19
  | XLF_FUNCTRACE_XLF_EXIT  -> 18
  | XLF_IGNORE_TKR          -> 10
  | XLF_INDEPENDENT         -> 11
  | XLF_LOOPID              -> 6
  | XLF_MEM_DELAY           -> 9
  | XLF_NEW                 -> 3
  | XLF_NOFUNCTRACE         -> 11
  | XLF_NOSIMD              -> 6
  | XLF_NOVECTOR            -> 8
  | XLF_PERMUTATION         -> 11
  | XLF_SNAPSHOT            -> 8
  | XLF_SOURCEFORM          -> 10
  | XLF_STREAM_UNROLL       -> 13
  | XLF_SUBSCRIPTORDER      -> 14
  | XLF_UNROLL              -> 6
  | XLF_UNROLL_AND_FUSE     -> 15
  | XLF_PROCESS             -> 8

  | XLF_ITERCNT    -> 7
  | XLF_MINITERCNT -> 10
  | XLF_MAXITERCNT -> 10
  | XLF_NODEPS     -> 6
  | XLF_REDUCTION  -> 9
(*
  | XLF_MAX       -> 3
  | XLF_MIN       -> 3
  | XLF_IAND      -> 4
  | XLF_IEOR      -> 4
*)
  | XLF_FIXED     -> 4
  | XLF_FREE      -> 4
  | XLF_F90       -> 3
  | XLF_IBM       -> 3

  | XLF_VERY_HIGH -> 9
  | XLF_VERY_LOW -> 8

  (*| RAWXLF(t, s, _, _) -> String.length s*)
  | XLF _    -> 0

  | DEC_ALIAS -> 5
  | DEC_ASSUME -> 6
  | DEC_ASSUME_ALIGNED -> 14
  | DEC_ATTRIBUTES -> 10
  | DEC_BLOCK_LOOP -> 10
  | DEC_NOBLOCK_LOOP -> 12
  | DEC_CODE_ALIGN -> 10
  | DEC_DECLARE -> 7
  | DEC_NODECLARE -> 9
  | DEC_DEFINE -> 6
  | DEC_UNDEFINE -> 8
  | DEC_DISTRIBUTE -> 10
  | DEC_POINT -> 5
  | DEC_FIXEDFORMLINESIZE -> 17
  | DEC_FMA -> 3
  | DEC_NOFMA -> 5
  | DEC_FREEFORM -> 8
  | DEC_NOFREEFORM -> 10
  | DEC_IDENT -> 5
  | DEC_IF -> 2
  | DEC_DEFINED -> 7
  | DEC_INLINE -> 6
  | DEC_FORCEINLINE -> 11
  | DEC_NOINLINE -> 8
  | DEC_INTEGER -> 7
  | DEC_IVDEP -> 5
  | DEC_INIT_DEP_FWD -> 12
  | DEC_LOOP -> 4
  | DEC_COUNT -> 5
  | DEC_MESSAGE -> 7
  | DEC_NOFUSION -> 8
  | DEC_OBJCOMMENT -> 10
  | DEC_OPTIMIZE -> 8
  | DEC_NOOPTIMIZE -> 10
  | DEC_OPTIONS -> 7
  | DEC_PACK -> 4
  | DEC_PARALLEL -> 8
  | DEC_NOPARALLEL -> 10
  | DEC_PREFETCH -> 8
  | DEC_NOPREFETCH -> 10
  | DEC_PSECT -> 5
  | DEC_REAL -> 4
  | DEC_SIMD -> 4
  | DEC_STRICT -> 6
  | DEC_NOSTRICT -> 8
  | DEC_UNROLL -> 6
  | DEC_NOUNROLL -> 8
  | DEC_UNROLL_AND_JAM -> 14
  | DEC_NOUNROLL_AND_JAM -> 16
  | DEC_VECTOR -> 6
  | DEC_NOVECTOR -> 8

  | DEC_DISTRIBUTEPOINT -> 15
  | DEC_LOOPCOUNT       -> 9
  | DEC_IFDEFINED       -> 9
  | DEC_ELSEIF          -> 6
  | DEC_ELSE            -> 4
  | DEC_ENDIF           -> 5

  | DEC_ALWAYS            -> 6
  | DEC_ASSERT            -> 6
  | DEC_ALIGNED           -> 7
  | DEC_UNALIGNED         -> 9
  | DEC_TEMPORAL          -> 8
  | DEC_NONTEMPORAL       -> 11
  | DEC_VECREMAINDER      -> 12
  | DEC_NOVECREMAINDER    -> 14
  | DEC_NOASSERT          -> 8
  | DEC_FIRSTPRIVATE      -> 12
  | DEC_LASTPRIVATE       -> 11
  | DEC_LINEAR            -> 6
  | DEC_PRIVATE           -> 7
  | DEC_REDUCTION         -> 9
  | DEC_VECTORLENGTH      -> 12
  | DEC_VECTORLENGTHFOR   -> 15
  | DEC_NUM_THREADS       -> 11
  | DEC_ALIGN             -> 5
  | DEC_WRT               -> 3
  | DEC_NOWRT             -> 5
  | DEC_END               -> 3
  | DEC_ENDOPTIONS        -> 10
  | DEC_NOALIGN           -> 7
  | DEC_WARN              -> 4
  | DEC_OFFLOAD_ATTRIBUTE_TARGET -> 24
  | DEC_ALIGNMENT         -> 9
  | DEC_NOALIGNMENT       -> 11
  | DEC_RECURSIVE         -> 9

  | DEC_MASK      -> 4
  | DEC_NOMASK    -> 6
  | DEC_PROCESSOR -> 9
  | DEC_UNIFORM   -> 7

  | DEC_FACTOR -> 6
  | DEC_LEVEL -> 5

  (*| RAWDEC(p, s) -> String.length s*)
  | DEC _ -> 0

  | LINDA_TYPEOF s -> String.length s

(* Compaq Fortran *)
(*
  | AUTOMATIC s
  | STATIC s
*)
  | ACCEPT s
  | REWRITE s
  | DELETE s
  | UNLOCK s
(*  | DEFINE_FILE s*)
  | ENCODE s
  | DECODE s
  | FIND s
  | VIRTUAL s
  | STRUCTURE s
  | END_STRUCTURE s
  | RECORD s
  | UNION s
  | END_UNION s
  | MAP s
  | END_MAP s
    -> String.length s

  | OPTIONS__OPTS _ -> 0
  | DEFINE_FILE -> 11

(*
  | LBRACE
  | RBRACE
*)

  | EXCLAM
  | DOLLAR
  | BACKSLASH
  | QUESTION

  | PERCENT
  | AMP
  | LPAREN
  | LPAREN__IMPLICIT
  | LPAREN__GO_TO
  | LPAREN__io_control_spec
  | LPAREN__position_spec
  | LPAREN__flush_spec

  | RPAREN

  | LBRACKET
  | RBRACKET

  | STAR
  | SLASH
  | PLUS
  | MINUS
  | UPLUS
  | UMINUS

  | COMMA
  | COMMA__SLASH
  | DOT
  | COLON
  | SEMICOLON

  | LT
  | EQ
  | GT        -> 1

  | VFE_BEGIN s -> (String.length s) + 1 (* '<' *)
  | VFE_END s   -> (String.length s) + 1 (* '>' *)

  | LT_EQ
  | GT_EQ
  | EQ_EQ
  | EQ_GT

  | STAR_STAR

  | COLON_COLON
  | SLASH_SLASH

  | LPAREN_SLASH

  | SLASH_RPAREN

  | SLASH_EQ     -> 2

  | IDENTIFIER s -> String.length s

  | COMPOSITE_IDENTIFIER(_, s, _) -> String.length s

  | CONTINUED_IDENTIFIER s -> String.length s

  | INT_LITERAL s
  | REAL_LITERAL s
  | BOZ_LITERAL s
  | LOGICAL_LITERAL s
  | CHAR_LITERAL s    -> String.length s

(*  | COMPLEX_LITERAL(r, i) -> (String.length r) + (String.length i) + 3 *)

  | DEFINED_OP s -> String.length s

  | DATA_EDIT_DESC s
  | KP_DESC s
  | POSITION_EDIT_DESC s
  | HOLLERITH(s, _)          -> String.length s

  | LABEL s -> String.length s

  | LETTER s -> String.length s

  | CONSTRUCT_NAME s -> String.length s
(*
  | DO_CONSTRUCT_NAME s
  | IF_CONSTRUCT_NAME s
  | WHERE_CONSTRUCT_NAME s
  | FORALL_CONSTRUCT_NAME s
  | CASE_CONSTRUCT_NAME s
  | SELECT_CONSTRUCT_NAME s
  | ASSOCIATE_CONSTRUCT_NAME s
    -> String.length s
*)

(* dotted identifiers *)
  | D_EQ
  | D_NE
  | D_GT
  | D_GE
  | D_LT
  | D_LE    -> 4
  | D_NOT
  | D_AND   -> 5
  | D_OR    -> 4
  | D_EQV   -> 5
  | D_NEQV  -> 6
(*
  | D_TRUE  -> 6
  | D_FALSE -> 7
*)

(* keywords *)
  | ABSTRACT s
  | ALLOCATABLE s
  | ALLOCATE s
  | ASSIGN s
  | ASSIGNMENT s
  | ASSOCIATE s
  | ASYNCHRONOUS s
  | BACKSPACE s
  | BIND s
  | BLOCK s
  | BLOCK_DATA s
  | BYTE s
  | CALL s
  | CASE s
  | CHARACTER s
  | CLASS s
  | CLOSE s
  | CODIMENSION s
  | COMMON s
(*  | COMPLEX s*)
  | CONCURRENT s
  | CONTAINS s
  | CONTINUE s
  | CRITICAL s
  | CYCLE s
  | DATA s
  | DEALLOCATE s
  | DEFAULT s
  | DIMENSION s
  | DO s
  | DOUBLE s
  | DOUBLE_PRECISION s
  | DOUBLE_COMPLEX s
(*  | ELEMENTAL s*)
  | ELSE s
  | ELSE_IF s
  | ELSEWHERE s
  | END s
  | END_ASSOCIATE s
  | END_BLOCK s
  | END_BLOCK_DATA s
  | END_CRITICAL s
  | END_DO s
  | END_ENUM s
  | END_FILE s
  | END_FORALL s
(*  | END_FUNCTION s*)
  | END_IF s
  | END_INTERFACE s
  | END_MODULE s
  | END_PROCEDURE s
  | END_PROGRAM s
  | END_SELECT s
  | END_SUBMODULE s
  | END_SUBPROGRAM s
(*  | END_SUBROUTINE s*)
  | END_TYPE s
  | END_WHERE s
  | ENTRY s
  | ENUM s
  | ENUMERATOR s
(*  | ERRMSG s*)
  | EQUIVALENCE s
  | EXIT s
  | EXTENDS s
(*  | EXTERNAL s*)
  | FLUSH s
  | FORALL s
  | FORMAT s
  | FUNCTION s
  | GENERIC s
  | GO_TO s
  | ID s
  | IF s
  | IMPLICIT s
  | IMPORT s
(*  | IMPURE s*)
(*
  | IN s
  | IN_OUT s
*)
  | INQUIRE s
(*  | INTEGER s*)
  | INTENT s
  | INTENT_SPEC s
  | INTERFACE s
  | INTRINSIC s
  | KIND s
  | KINDED_TYPE_SPEC s
  | LEN s
  | LOCK s
(*  | LOGICAL s*)
  | MODULE s
(*  | MOLD s*)
  | ALLOC_OPT_EXPR s
  | NAMELIST s
  | NONE s
  | NON_INTRINSIC s
  | NULL s
  | NULLIFY s
  | ONLY s
  | OPEN s
  | OPERATOR s
  | OPTIONAL s
(*  | OUT s*)
  | PARAMETER s
  | PAUSE s
  | POINTER s
  | PRECISION s
  | PREFIX_SPEC s
  | PRINT s
  | PRIVATE s
  | PROCEDURE s
  | PROGRAM s
(*  | PROTECTED s*)
  | PUBLIC s
(*  | PURE s*)
  | READ s
(*  | REAL s*)
(*  | RECURSIVE s*)
  | RESULT s
  | RETURN s
  | REWIND s
  | SAVE s
  | SELECT_CASE s
  | SELECT_TYPE s
  | SEQUENCE s
(*  | SOURCE s*)
(*  | STAT s*)
  | STOP s
  | SUBMODULE s
  | SUBROUTINE s
  | SYNC s
  | TARGET s
  | THEN s
  | TO s
  | TYPE s
  | USE s
(*
  | VALUE s
  | VOLATILE s
*)
  | WAIT s
  | WHERE s
  | WHILE s
  | WRITE s
(*
  | ACCESS s
  | ACTION s
  | BLANK s
  | DELIM s
  | FORM s
  | PAD s
  | POSITION s
  | RECL s
*)
  | ERR s
  | FILE s
  | IOSTAT s
  | IOMSG s
(*  | POS s *)
  | STATUS s
  | UNIT s

  | FMT s
  | NML s
(*
  | REC s
  | ADVANCE s
*)
  | SIZE s
  | EOR s
(*
  | DIRECT s
  | EXIST s
  | FORMATTED s
  | NAMED s
  | NEXTREC s
  | NUMBER s
  | OPENED s
  | READWRITE s
  | SEQUENTIAL s
  | UNFORMATTED s
*)
  | NAME_ s
  | IOLENGTH s

  | CONNECT_SPEC s
  | INQUIRE_SPEC s
  | IOCTL_SPEC s

  | CONNECT_INQUIRE_IOCTL_SPEC s
  | CONNECT_INQUIRE_SPEC s
  | INQUIRE_IOCTL_SPEC s

  | INTEL_CLOSE_CONNECT_SPEC s
(*
  | INTEL_CONNECT_SPEC s
  | INTEL_CONNECT_INQUIRE_SPEC s
  | INTEL_INQUIRE_SPEC s
*)
    -> String.length s

  | PASS s
  | NOPASS s
  | NON_OVERRIDABLE s
  | DEFERRED s        -> String.length s

  | FINAL s -> String.length s

  | TYPE_IS s
  | CLASS_IS s
  | CLASS_DEFAULT s -> String.length s


  | EOL -> 0

  | EOF _ -> 0

  | EOP -> 0

  | NOTHING -> 0

  | MARKER -> 0
  | PP_MARKER -> 0

  | END_FRAGMENT -> 0

  | INCLUDE__FILE _ -> 0

  | SIMPLE_ATTR s -> String.length s

(*
  | _ -> "<impossible>"
*)



let rawtoken_to_rep = function

  | ERROR msg             -> sprintf "<error:%s>" msg

  | PROGRAM_UNIT _        -> "PROGRAM_UNIT"
  | SPEC_PART_CONSTRUCT _ -> "SPEC_PART_CONSTRUCT"
  | EXEC_PART_CONSTRUCT _ -> "EXEC_PART_CONSTRUCT"
  | SUBPROGRAM _          -> "SUBPROGRAM"
  | INTERFACE_SPEC _      -> "INTERFACE_SPEC"
  | CASE_BLOCK _          -> "CASE_BLOCK"
  | DATA_STMT_SET _       -> "DATA_STMT_SET"
  | ACTION_STMT _         -> "ACTION_STMT"
  | STMT _                -> "STMT"
  | VARIABLE _            -> "VARIABLE"
  | EXPR _                -> "EXPR"
  | TYPE_SPEC _           -> "TYPE_SPEC"
  | DERIVED_TYPE_DEF_PART _ -> "DERIVED_TYPE_DEF_PART"
  | ONLY_ _                 -> "ONLY_"

  | DO_STMT _               -> "DO_STMT"
  | FORALL_CONSTRUCT_STMT _ -> "FORALL_CONSTRUCT_STMT"
  | IF_THEN_STMT _          -> "IF_THEN_STMT"
  | SELECT_CASE_STMT _      -> "SELECT_CASE_STMT"
  | WHERE_CONSTRUCT_STMT _  -> "WHERE_CONSTRUCT_STMT"
  | DERIVED_TYPE_STMT _     -> "DERIVED_TYPE_STMT"

  | END_DO_STMT _           -> "END_DO_STMT"
  | END_FORALL_STMT _       -> "END_FORALL_STMT"
  | END_IF_STMT _           -> "END_IF_STMT"
  | END_SELECT_STMT _       -> "END_SELECT_STMT"
  | END_WHERE_STMT _        -> "END_WHERE_STMT"
  | END_TYPE_STMT _         -> "END_TYPE_STMT"

  | FUNCTION_HEAD _         -> "FUNCTION_HEAD"
  | FUNCTION_STMT_HEAD _    -> "FUNCTION_STMT_HEAD"
  | SUBROUTINE_HEAD _       -> "SUBROUTINE_HEAD"
  | SUBROUTINE_STMT_HEAD _  -> "SUBROUTINE_STMT_HEAD"

  | PU_TAIL _               -> "PU_TAIL"

  | PP_IDENTIFIER s -> s

  | PP_UNDERSCORE s -> s

  | PP_MACRO_CONST s      -> s
(*  | PP_MACRO_CONST_CHAR s -> s
  | PP_MACRO_CONST_INT s  -> s*)
  | PP_MACRO_NAME(s, _)   -> s
  | PP_MACRO_VARIABLE s   -> s
  | PP_MACRO_EXPR s       -> s
  | PP_MACRO_STMT s       -> s
  | PP_MACRO_TYPE_SPEC s  -> s
  | PP_MACRO_WRITE s      -> s
  | PP_MACRO_READ_WRITE s -> s
  | PP_MACRO_READ_PRINT s -> s


  | PP_MACRO_ID(_, s)    -> s
  | PP_MACRO_ID_RW(_, s) -> s
  | PP_MACRO_APPL(s, sl) -> sprintf "%s(%s)" s (String.concat "," sl)


  | PP_DEFINE__IDENT__BODY(i, b) -> sprintf "#define %s %s" i (Macro.body_to_rep b)
  | PP_INCLUDE__FILE h           -> "#include "^(H.to_rep h)
  | PP_BRANCH b -> PPD.branch_to_simple_string b
(*
  | PP_IF__COND c                -> "#if "^c
  | PP_ELIF__COND c              -> "#elif "^c
  | PP_IFDEF__IDENT i            -> "#ifdef "^i
  | PP_IFNDEF__IDENT i           -> "#ifndef "^i
*)
  | PP_ELSE              -> "#else"
  | PP_ENDIF             -> "#endif"

  | PP_UNDEF__IDENT i            -> "#undef "^i

  | PP_ISSUE__MESG m             -> PPD.message_to_simple_string m
(*
  | PP_ERROR__MESG m             -> "#error "^m
  | PP_WARNING__MESG m           -> "#warning "^m
*)
  | PP_UNKNOWN__REST(d, r)       -> d^" "^r

  | PP_INCLUDE           -> "#include"
  | PP_DEFINE            -> "#define"
  | PP_UNDEF             -> "#undef"
  | PP_IF                -> "#if"
  | PP_IFDEF             -> "#ifdef"
  | PP_IFNDEF            -> "#ifndef"
  | PP_ELIF              -> "#elif"

  | PP_ERROR             -> "#error"
  | PP_WARNING           -> "#warning"

  | PP_UNKNOWN           -> "#<unknown>"

  | PP_AND               -> "&&"
  | PP_OR                -> "||"
  | PP_CONCAT            -> "##"

  | OCL_ARRAY_FUSION           -> "ARRAY_FUSION"
  | OCL_END_ARRAY_FUSION       -> "END_ARRAY_FUSION"
  | OCL_ARRAY_MERGE            -> "ARRAY_MERGE"
  | OCL_ARRAY_SUBSCRIPT        -> "ARRAY_SUBSCRIPT"
  | OCL_EVAL                   -> "EVAL"
  | OCL_NOEVAL                 -> "NOEVAL"
  | OCL_FLTLD                  -> "FLTLD"
  | OCL_NOFLTLD                -> "NOFLTLD"
  | OCL_FP_RELAXED             -> "FP_RELAXED"
  | OCL_NOFP_RELAXED           -> "NOFP_RELAXED"
  | OCL_LOOP_INTERCHANGE       -> "LOOP_INTERCHANGE"
  | OCL_LOOP_NOINTERCHANGE     -> "LOOP_NOINTERCHANGE"
  | OCL_MFUNC                  -> "MFUNC"
  | OCL_NOMFUNC                -> "NOMFUNC"
  | OCL_NOARRAYPAD             -> "NOARRAYPAD"
  | OCL_LOOP_NOFUSION          -> "LOOP_NOFUSION"
  | OCL_PREEX                  -> "PREEX"
  | OCL_NOPREEX                -> "NOPREEX"
  | OCL_PREFETCH               -> "PREFETCH"
  | OCL_NOPREFETCH             -> "NOPREFETCH"
  | OCL_PREFETCH_CACHE_LEVEL   -> "PREFETCH_CACHE_LEVEL"
  | OCL_PREFETCH_INFER         -> "PREFETCH_INFER"
  | OCL_PREFETCH_NOINFER       -> "PREFETCH_NOINFER"
  | OCL_PREFETCH_ITERATION     -> "PREFETCH_ITERATION"
  | OCL_PREFETCH_ITERATION_L2  -> "PREFETCH_ITERATION_L2"
  | OCL_PREFETCH_READ          -> "PREFETCH_READ"
  | OCL_PREFETCH_WRITE         -> "PREFETCH_WRITE"
  | OCL_STRIPING               -> "STRIPING"
  | OCL_NOSTRIPING             -> "NOSTRIPING"
  | OCL_SWP                    -> "SWP"
  | OCL_NOSWP                  -> "NOSWP"
  | OCL_LOOP_BLOCKING          -> "LOOP_BLOCKING"
  | OCL_UNROLL                 -> "UNROLL"
  | OCL_NOUNROLL               -> "NOUNROLL"
  | OCL_NOVREC                 -> "NOVREC"
  | OCL_SIMD                   -> "SIMD"
  | OCL_NOSIMD                 -> "NOSIMD"
  | OCL_CACHE_SECTOR_SIZE      -> "CACHE_SECTOR_SIZE"
  | OCL_END_CACHE_SECTOR_SIZE  -> "END_CACHE_SECTOR_SIZE"
  | OCL_CACHE_SUBSECTOR_ASSIGN -> "CACHE_SUBSECTOR_ASSIGN"
  | OCL_END_CACHE_SUBSECTOR    -> "END_CACHE_SUBSECTOR"
  | OCL_FISSION_POINT          -> "FISSION_POINT"
  | OCL_LOOP_NOFISSION         -> "LOOP_NOFISSION"
  | OCL_XFILL                  -> "XFILL"
  | OCL_NOXFILL                -> "NOXFILL"
  | OCL_PREFETCH_SEQUENTIAL    -> "PREFETCH_SEQUENTIAL"
  | OCL_PREFETCH_STRONG        -> "PREFETCH_STRONG"
  | OCL_PREFETCH_NOSTRONG      -> "PREFETCH_NOSTRONG"
  | OCL_PREFETCH_STRONG_L2     -> "PREFETCH_STRONG_L2"
  | OCL_PREFETCH_NOSTRONG_L2   -> "PREFETCH_NOSTRONG_L2"
  | OCL_FP_CONTRACT            -> "FP_CONTRACT"
  | OCL_NOFP_CONTRACT          -> "NOFP_CONTRACT"
  | OCL_LOOP_NOBLOCKING        -> "LOOP_NOBLOCKING"
  | OCL_NORECURRENCE           -> "NORECURRENCE"
  | OCL_UXSIMD                 -> "UXSIMD"
  | OCL_NOUXSIMD               -> "NOUXSIMD"
  | OCL_ARRAY_PRIVATE          -> "ARRAY_PRIVATE"
  | OCL_NOARRAY_PRIVATE        -> "NOARRAY_PRIVATE"
  | OCL_INDEPENDENT            -> "INDEPENDENT"
  | OCL_NOALIAS                -> "NOALIAS"
  | OCL_SERIAL                 -> "SERIAL"
  | OCL_PARALLEL               -> "PARALLEL"
  | OCL_PARALLEL_STRONG        -> "PARALLEL_STRONG"
  | OCL_REDUCTION              -> "REDUCTION"
  | OCL_NOREDUCTION            -> "NOREDUCTION"
  | OCL_TEMP                   -> "TEMP"
  | OCL_LOOP_PART_SIMD         -> "LOOP_PART_SIMD"
  | OCL_LOOP_NOPART_SIMD       -> "LOOP_NOPART_SIMD"
  | OCL_SHORTLOOP              -> "SHORTLOOP"
  | OCL_NOSHORTLOOP            -> "NOSHORTLOOP"
  | OCL_SIMD_LISTV             -> "SIMD_LISTV"
  | OCL_UNSWITCHING            -> "UNSWITCHING"
  | OCL_LOOP_PART_PARALLEL     -> "LOOP_PART_PARALLEL"
  | OCL_LOOP_NOPART_PARALLEL   -> "LOOP_NOPART_PARALLEL"
  | OCL_FIRST_PRIVATE          -> "FIRST_PRIVATE"
  | OCL_LAST_PRIVATE           -> "LAST_PRIVATE"
  | OCL_TEMP_PRIVATE           -> "TEMP_PRIVATE"
  | OCL_PARALLEL_CYCLIC        -> "PARALLEL_CYCLIC"

  | OCL_ALIGNED                -> "ALIGNED"
  | OCL_UNALIGNED              -> "UNALIGNED"
  | OCL_LEVEL                  -> "LEVEL"
  | OCL_STRONG                 -> "STRONG"
  | OCL_AUTO                   -> "AUTO"
  | OCL_SOFT                   -> "SOFT"
  | OCL_ALL                    -> "ALL"
  | OCL_THEN                   -> "THEN"
  | OCL_ELSE                   -> "ELSE"

  (*| RAWOCL s                   -> "!OCL"^s*)
  | OCL _                      -> "OCL"

  | OMP_AUTO                   -> "auto"
  | OMP_ATOMIC                 -> "atomic"
  | OMP_BARRIER                -> "barrier"
  | OMP_CAPTURE                -> "capture"
  | OMP_COLLAPSE               -> "collapse"
  | OMP_COPYIN                 -> "copyin"
  | OMP_COPYPRIVATE            -> "copyprivate"
  | OMP_CRITICAL               -> "critical"
  | OMP_DEFAULT                -> "default"
  | OMP_DO                     -> "do"
  | OMP_DYNAMIC                -> "dynamic"
  | OMP_END                    -> "end"
  | OMP_FINAL                  -> "final"
  | OMP_FIRSTPRIVATE           -> "firstprivate"
  | OMP_FLUSH                  -> "flush"
  | OMP_GUIDED                 -> "guided"
  | OMP_IF                     -> "if"
  | OMP_LASTPRIVATE            -> "lastprivate"
  | OMP_MASTER                 -> "master"
  | OMP_MERGEABLE              -> "mergeable"
  | OMP_NONE                   -> "none"
  | OMP_NOWAIT                 -> "nowait"
  | OMP_NUM_THREADS            -> "num_threads"
  | OMP_ORDERED                -> "ordered"
  | OMP_PARALLEL               -> "parallel"
  | OMP_PRIVATE                -> "private"
  | OMP_READ                   -> "read"
  | OMP_REDUCTION              -> "reduction"
  | OMP_RUNTIME                -> "runtime"
  | OMP_SCHEDULE               -> "schedule"
  | OMP_SECTION                -> "section"
  | OMP_SECTIONS               -> "sections"
  | OMP_SHARED                 -> "shared"
  | OMP_SINGLE                 -> "single"
  | OMP_STATIC                 -> "static"
  | OMP_TASK                   -> "task"
  | OMP_TASKWAIT               -> "taskwait"
  | OMP_TASKYIELD              -> "taskyield"
  | OMP_THREADPRIVATE          -> "threadprivate"
  | OMP_UNTIED                 -> "united"
  | OMP_UPDATE                 -> "update"
  | OMP_WORKSHARE              -> "workshare"
  | OMP_WRITE                  -> "write"
  | OMP_END_ATOMIC             -> "end atomic"
  | OMP_END_CRITICAL           -> "end critical"
  | OMP_END_DO                 -> "end do"
  | OMP_END_MASTER             -> "end master"
  | OMP_END_ORDERED            -> "end ordered"
  | OMP_END_PARALLEL           -> "end parallel"
  | OMP_END_SECTIONS           -> "end sections"
  | OMP_END_SINGLE             -> "end single"
  | OMP_END_TASK               -> "end task"
  | OMP_END_WORKSHARE          -> "end workshare"
  | OMP_PARALLEL_DO            -> "parallel do"
  | OMP_PARALLEL_SECTIONS      -> "parallel sections"
  | OMP_PARALLEL_WORKSHARE     -> "parallel workshare"
  | OMP_END_PARALLEL_DO        -> "end parallel do"
  | OMP_END_PARALLEL_SECTIONS  -> "end parallel sections"
  | OMP_END_PARALLEL_WORKSHARE -> "end parallel workshare"

  (* OpenMP 4.0 *)
  | OMP_ALIGNED                                      -> "aligned"
  | OMP_ALLOC                                        -> "alloc"
  | OMP_CANCEL                                       -> "cancel"
  | OMP_CANCELLATION_POINT                           -> "cancellation point"
  | OMP_CLOSE                                        -> "close"
  | OMP_DECLARE_REDUCTION                            -> "declare reduction"
  | OMP_DECLARE_SIMD                                 -> "declare simd"
  | OMP_DECLARE_TARGET                               -> "declare target"
  | OMP_DEPEND                                       -> "depend"
  | OMP_DEVICE                                       -> "device"
  | OMP_DIST_SCHEDULE                                -> "dist_schedule"
  | OMP_DISTRIBUTE                                   -> "distribute"
  | OMP_DISTRIBUTE_PARALLEL_DO                       -> "distribute parallel do"
  | OMP_DISTRIBUTE_PARALLEL_DO_SIMD                  -> "distribute parallel do simd"
  | OMP_DISTRIBUTE_SIMD                              -> "distribute simd"
  | OMP_DO_SIMD                                      -> "do simd"
  | OMP_END_DISTRIBUTE                               -> "end distribute"
  | OMP_END_DISTRIBUTE_PARALLEL_DO                   -> "end distribute parallel do"
  | OMP_END_DISTRIBUTE_PARALLEL_DO_SIMD              -> "end distribute parallel do simd"
  | OMP_END_DISTRIBUTE_SIMD                          -> "end distribute simd"
  | OMP_END_DO_SIMD                                  -> "end do simd"
  | OMP_END_PARALLEL_DO_SIMD                         -> "end parallel do simd"
  | OMP_END_SIMD                                     -> "end simd"
  | OMP_END_TARGET                                   -> "end target"
  | OMP_END_TARGET_DATA                              -> "end target data"
  | OMP_END_TARGET_TEAMS                             -> "end target teams"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE                  -> "end target teams distribute"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO      -> "end target teams distribute parallel do"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD -> "end target teams distribute parallel do simd"
  | OMP_END_TARGET_TEAMS_DISTRIBUTE_SIMD             -> "end target teams distribute simd"
  | OMP_END_TASKGROUP                                -> "end taskgroup"
  | OMP_END_TEAMS                                    -> "end teams"
  | OMP_END_TEAMS_DISTRIBUTE                         -> "end teams distribute"
  | OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO             -> "end teams distribute parallel do"
  | OMP_END_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD        -> "end teams distribute parallel do simd"
  | OMP_END_TEAMS_DISTRIBUTE_SIMD                    -> "end teams distribute simd"
  | OMP_FROM                                         -> "from"
  | OMP_IN                                           -> "in"
  | OMP_INBRANCH                                     -> "inbranch"
  | OMP_INITIALIZER                                  -> "initializer"
  | OMP_INOUT                                        -> "inout"
  | OMP_LINEAR                                       -> "linear"
  | OMP_MAP                                          -> "map"
  | OMP_NOTINBRANCH                                  -> "notinbranch"
  | OMP_NUM_TEAMS                                    -> "num_teams"
  | OMP_OUT                                          -> "out"
  | OMP_PARALLEL_DO_SIMD                             -> "parallel do simd"
  | OMP_PROC_BIND                                    -> "proc_bind"
  | OMP_SAFELEN                                      -> "safelen"
  | OMP_SEQ_CST                                      -> "seq_cst"
  | OMP_SIMD                                         -> "simd"
  | OMP_SIMDLEN                                      -> "simdlen"
  | OMP_SPREAD                                       -> "spread"
  | OMP_TARGET                                       -> "target"
  | OMP_TARGET_DATA                                  -> "target data"
  | OMP_TARGET_TEAMS                                 -> "target teams"
  | OMP_TARGET_TEAMS_DISTRIBUTE                      -> "target teams distribute"
  | OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO          -> "target teams distribute parallel do"
  | OMP_TARGET_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD     -> "target teams distribute parallel do simd"
  | OMP_TARGET_TEAMS_DISTRIBUTE_SIMD                 -> "target teams distribute simd"
  | OMP_TARGET_UPDATE                                -> "target update"
  | OMP_TASKGROUP                                    -> "taskgroup"
  | OMP_TEAMS                                        -> "teams"
  | OMP_TEAMS_DISTRIBUTE                             -> "teams distribute"
  | OMP_TEAMS_DISTRIBUTE_PARALLEL_DO                 -> "teams distribute parallel do"
  | OMP_TEAMS_DISTRIBUTE_PARALLEL_DO_SIMD            -> "teams distribute parallel do simd"
  | OMP_TEAMS_DISTRIBUTE_SIMD                        -> "teams distribute simd"
  | OMP_THREAD_LIMIT                                 -> "thread_limit"
  | OMP_TO                                           -> "to"
  | OMP_TOFROM                                       -> "tofrom"
  | OMP_UNIFORM                                      -> "uniform"

  | RAW {DL.head=h;DL.line=l;_} -> h^l
  | OMP _ -> "OMP"

  | ACC_ATOMIC             -> "atomic"
  | ACC_CACHE              -> "cache"
  | ACC_DATA               -> "data"
  | ACC_DECLARE            -> "declare"
  | ACC_END                -> "end"
  | ACC_ENTER              -> "enter"
  | ACC_EXIT               -> "exit"
  | ACC_HOST_DATA          -> "host_data"
  | ACC_KERNELS            -> "kernels"
  | ACC_LOOP               -> "loop"
  | ACC_PARALLEL           -> "parallel"
  | ACC_ROUTINE            -> "routine"
  | ACC_UPDATE             -> "update"
  | ACC_WAIT               -> "wait"

  | ACC_ASYNC              -> "async"
  | ACC_AUTO               -> "auto"
  | ACC_BIND               -> "bind"
  | ACC_CAPTURE            -> "capture"
  | ACC_COLLAPSE           -> "collapse"
  | ACC_COPY               -> "copy"
  | ACC_COPYIN             -> "copyin"
  | ACC_COPYOUT            -> "copyout"
  | ACC_CREATE             -> "create"
  | ACC_DEFAULT            -> "default"
  | ACC_DELETE             -> "delete"
  | ACC_DEVICE             -> "device"
  | ACC_DEVICEPTR          -> "deviceptr"
  | ACC_DEVICE_RESIDENT    -> "device_resident"
  | ACC_DEVICE_TYPE        -> "device_type"
  | ACC_DTYPE              -> "dtype"
  | ACC_FIRSTPRIVATE       -> "firstprivate"
  | ACC_GANG               -> "gang"
  | ACC_HOST               -> "host"
  | ACC_IF                 -> "if"
  | ACC_INDEPENDENT        -> "independent"
  | ACC_LINK               -> "link"
  | ACC_NOHOST             -> "nohost"
  | ACC_NONE               -> "none"
  | ACC_NUM_GANGS          -> "num_gangs"
  | ACC_NUM_WORKERS        -> "num_workers"
  | ACC_PCOPY              -> "pcopy"
  | ACC_PCOPYIN            -> "pcopyin"
  | ACC_PCOPYOUT           -> "pcopyout"
  | ACC_PCREATE            -> "pcreate"
  | ACC_PRESENT            -> "present"
  | ACC_PRESENT_OR_COPY    -> "present_or_copy"
  | ACC_PRESENT_OR_COPYIN  -> "present_or_copyin"
  | ACC_PRESENT_OR_COPYOUT -> "present_or_copyout"
  | ACC_PRESENT_OR_CREATE  -> "present_or_create"
  | ACC_PRIVATE            -> "private"
  | ACC_READ               -> "read"
  | ACC_REDUCTION          -> "reduction"
  | ACC_SELF               -> "self"
  | ACC_SEQ                -> "seq"
  | ACC_TILE               -> "tile"
  | ACC_USE_DEVICE         -> "use_device"
  | ACC_VECTOR             -> "vector"
  | ACC_VECTOR_LENGTH      -> "vector_length"
  | ACC_WORKER             -> "worker"
  | ACC_WRITE              -> "write"

  | ACC _ -> "ACC"

  | XLF_ALIGN               -> "ALIGN"
  | XLF_ASSERT              -> "ASSERT"
  | XLF_BLOCK_LOOP          -> "BLOCK_LOOP"
  | XLF_CNCALL              -> "CNCALL"
  | XLF_COLLAPSE            -> "COLLAPSE"
  | XLF_EJECT               -> "EJECT"
  | XLF_EXECUTION_FREQUENCY -> "EXECUTION_FREQUENCY"
  | XLF_EXPECTED_VALUE      -> "EXPECTED_VALUE"
  | XLF_FUNCTRACE_XLF_CATCH -> "FUNCTRACE_XLF_CATCH"
  | XLF_FUNCTRACE_XLF_ENTER -> "FUNCTRACE_XLF_ENTER"
  | XLF_FUNCTRACE_XLF_EXIT  -> "FUNCTRACE_XLF_EXIT"
  | XLF_IGNORE_TKR          -> "IGNORE_TKR"
  | XLF_INDEPENDENT         -> "INDEPENDENT"
  | XLF_LOOPID              -> "LOOPID"
  | XLF_MEM_DELAY           -> "MEM_DELAY"
  | XLF_NEW                 -> "NEW"
  | XLF_NOFUNCTRACE         -> "NOFUNCTRACE"
  | XLF_NOSIMD              -> "NOSIMD"
  | XLF_NOVECTOR            -> "NOVECTOR"
  | XLF_PERMUTATION         -> "PERMUTATION"
  | XLF_SNAPSHOT            -> "SNAPSHOT"
  | XLF_SOURCEFORM          -> "SOURCEFORM"
  | XLF_STREAM_UNROLL       -> "STREAM_UNROLL"
  | XLF_SUBSCRIPTORDER      -> "SUBSCRIPTORDER"
  | XLF_UNROLL              -> "UNROLL"
  | XLF_UNROLL_AND_FUSE     -> "UNROLL_AND_FUSE"
  | XLF_PROCESS             -> "@PROCESS"

  | XLF_ITERCNT    -> "ITERCNT"
  | XLF_MINITERCNT -> "MINITERCNT"
  | XLF_MAXITERCNT -> "MAXITERCNT"
  | XLF_NODEPS     -> "NODEPS"
  | XLF_REDUCTION  -> "REDUCTION"
(*
  | XLF_MAX       -> "MAX"
  | XLF_MIN       -> "MIN"
  | XLF_IAND      -> "IAND"
  | XLF_IEOR      -> "IEOR"
*)
  | XLF_FIXED     -> "FIXED"
  | XLF_FREE      -> "FREE"
  | XLF_F90       -> "F90"
  | XLF_IBM       -> "IBM"

  | XLF_VERY_HIGH -> "VERY_HIGH"
  | XLF_VERY_LOW -> "VERY_LOW"

  (*| RAWXLF(t, s, _, _) -> sprintf "!%s %s" t s*)
  | XLF _    -> "XLF"


  | DEC_ALIAS             -> "ALIAS"
  | DEC_ASSUME            -> "ASSUME"
  | DEC_ASSUME_ALIGNED    -> "ASSUME_ALIGNED"
  | DEC_ATTRIBUTES        -> "ATTRIBUTES"
  | DEC_BLOCK_LOOP        -> "BLOCK_LOOP"
  | DEC_NOBLOCK_LOOP      -> "NOBLOCK_LOOP"
  | DEC_CODE_ALIGN        -> "CODE_ALIGN"
  | DEC_DECLARE           -> "DECLARE"
  | DEC_NODECLARE         -> "NODECLARE"
  | DEC_DEFINE            -> "DEFINE"
  | DEC_UNDEFINE          -> "UNDEFINE"
  | DEC_DISTRIBUTE        -> "DISTRIBUTE"
  | DEC_POINT             -> "POINT"
  | DEC_FIXEDFORMLINESIZE -> "FIXEDFORMLINESIZE"
  | DEC_FMA               -> "FMA"
  | DEC_NOFMA             -> "NOFMA"
  | DEC_FREEFORM          -> "FREEFORM"
  | DEC_NOFREEFORM        -> "NOFREEFORM"
  | DEC_IDENT             -> "IDENT"
  | DEC_IF                -> "IF"
  | DEC_DEFINED           -> "DEFINED"
  | DEC_INLINE            -> "INLINE"
  | DEC_FORCEINLINE       -> "FORCEINLINE"
  | DEC_NOINLINE          -> "NOINLINE"
  | DEC_INTEGER           -> "INTEGER"
  | DEC_IVDEP             -> "IVDEP"
  | DEC_INIT_DEP_FWD      -> "INIT_DEP_FWD"
  | DEC_LOOP              -> "LOOP"
  | DEC_COUNT             -> "COUNT"
  | DEC_MESSAGE           -> "MESSAGE"
  | DEC_NOFUSION          -> "NOFUSION"
  | DEC_OBJCOMMENT        -> "OBJCOMMENT"
  | DEC_OPTIMIZE          -> "OPTIMIZE"
  | DEC_NOOPTIMIZE        -> "NOOPTIMIZE"
  | DEC_OPTIONS           -> "OPTIONS"
  | DEC_PACK              -> "PACK"
  | DEC_PARALLEL          -> "PARALLEL"
  | DEC_NOPARALLEL        -> "NOPARALLEL"
  | DEC_PREFETCH          -> "PREFETCH"
  | DEC_NOPREFETCH        -> "NOPREFETCH"
  | DEC_PSECT             -> "PSECT"
  | DEC_REAL              -> "REAL"
  | DEC_SIMD              -> "SIMD"
  | DEC_STRICT            -> "STRICT"
  | DEC_NOSTRICT          -> "NOSTRICT"
  | DEC_UNROLL            -> "UNROLL"
  | DEC_NOUNROLL          -> "NOUNROLL"
  | DEC_UNROLL_AND_JAM    -> "UNROLL_AND_JAM"
  | DEC_NOUNROLL_AND_JAM  -> "NOUNROLL_AND_JAM"
  | DEC_VECTOR            -> "VECTOR"
  | DEC_NOVECTOR          -> "NOVECTOR"

  | DEC_DISTRIBUTEPOINT   -> "DISTRIBUTEPOINT"
  | DEC_LOOPCOUNT         -> "LOOPCOUNT"
  | DEC_IFDEFINED         -> "IFDEFINED"
  | DEC_ELSEIF            -> "ELSEIF"
  | DEC_ELSE              -> "ELSE"
  | DEC_ENDIF             -> "ENDIF"

  | DEC_ALWAYS            -> "ALWAYS"
  | DEC_ASSERT            -> "ASSERT"
  | DEC_ALIGNED           -> "ALIGNED"
  | DEC_UNALIGNED         -> "UNALIGNED"
  | DEC_TEMPORAL          -> "TEMPORAL"
  | DEC_NONTEMPORAL       -> "NONTEMPORAL"
  | DEC_VECREMAINDER      -> "VECREMAINDER"
  | DEC_NOVECREMAINDER    -> "NOVECREMAINDER"
  | DEC_NOASSERT          -> "NOASSERT"
  | DEC_FIRSTPRIVATE      -> "FIRSTPRIVATE"
  | DEC_LASTPRIVATE       -> "LASTPRIVATE"
  | DEC_LINEAR            -> "LINEAR"
  | DEC_PRIVATE           -> "PRIVATE"
  | DEC_REDUCTION         -> "REDUCTION"
  | DEC_VECTORLENGTH      -> "VECTORLENGTH"
  | DEC_VECTORLENGTHFOR   -> "VECTORLENGTHFOR"
  | DEC_NUM_THREADS       -> "NUM_THREADS"
  | DEC_END               -> "END"
  | DEC_ENDOPTIONS        -> "ENDOPTIONS"

  | DEC_ALIGN             -> "ALIGN"
  | DEC_NOALIGN           -> "NOALIGN"
  | DEC_WRT               -> "WRT"
  | DEC_NOWRT             -> "NOWRT"
  | DEC_WARN              -> "WARN"
  | DEC_OFFLOAD_ATTRIBUTE_TARGET -> "OFFLOAD_ATTRIBUTE_TARGET"
  | DEC_ALIGNMENT         -> "ALIGNMENT"
  | DEC_NOALIGNMENT       -> "NOALIGNMENT"
  | DEC_RECURSIVE         -> "RECURSIVE"

  | DEC_MASK      -> "MASK"
  | DEC_NOMASK    -> "NOMASK"
  | DEC_PROCESSOR -> "PROCESSOR"
  | DEC_UNIFORM   -> "UNIFORM"

  | DEC_FACTOR -> "FACTOR"
  | DEC_LEVEL  -> "LEVEL"

  (*| RAWDEC(p, s) -> sprintf "!%s %s" p s*)
  | DEC _ -> "DEC"

  | LINDA_TYPEOF s             -> s

(* Compaq Fortran *)
(*
  | AUTOMATIC s
  | STATIC s
*)
  | ACCEPT s
  | REWRITE s
  | DELETE s
  | UNLOCK s
(*  | DEFINE_FILE s*)
  | ENCODE s
  | DECODE s
  | FIND s
  | VIRTUAL s
  | STRUCTURE s
  | END_STRUCTURE s
  | RECORD s
  | UNION s
  | END_UNION s
  | MAP s
  | END_MAP s
    -> s

  | OPTIONS__OPTS s -> "options "^s
  | DEFINE_FILE -> "define file"

(*
  | LBRACE                     -> "{"
  | RBRACE                     -> "}"
*)

  | EXCLAM    -> "!"
  | DOLLAR    -> "$"
  | BACKSLASH -> "\\"
  | QUESTION  -> "?"

  | PERCENT                -> "%"
  | AMP                    -> "&"

  | LPAREN                  -> "("
  | LPAREN__IMPLICIT        -> "("
  | LPAREN__GO_TO           -> "("
  | LPAREN__io_control_spec -> "("
  | LPAREN__position_spec   -> "("
  | LPAREN__flush_spec      -> "("

  | RPAREN                  -> ")"

  | LBRACKET               -> "["
  | RBRACKET               -> "]"

  | STAR                   -> "*"
  | SLASH                  -> "/"
  | PLUS                   -> "+"
  | MINUS                  -> "-"
  | UPLUS                  -> "+"
  | UMINUS                 -> "-"

  | COMMA                  -> ","
  | COMMA__SLASH           -> ","
  | DOT                    -> "."
  | COLON                  -> ":"
  | SEMICOLON              -> ";"

  | LT                     -> "<"
  | EQ                     -> "="
  | GT                     -> ">"

  | VFE_BEGIN s -> s^"<"
  | VFE_END s   -> ">"^s

  | STAR_STAR              -> "**"

  | LT_EQ        -> "<="
  | GT_EQ        -> ">="
  | EQ_EQ        -> "=="

  | EQ_GT        -> "=>"

  | COLON_COLON  -> "::"

  | SLASH_SLASH  -> "//"

  | SLASH_EQ     -> "/="

  | LPAREN_SLASH -> "(/"

  | SLASH_RPAREN -> "/)"

  | IDENTIFIER s -> s

  | COMPOSITE_IDENTIFIER(_, _, ol) -> (Xlist.to_string (fun o -> rawtoken_to_string (Obj.obj o)) " " ol)

  | CONTINUED_IDENTIFIER s -> s

  | INT_LITERAL s     -> s
  | REAL_LITERAL s    -> s
  | BOZ_LITERAL s     -> s
  | LOGICAL_LITERAL s -> s
  | CHAR_LITERAL s    -> s
(*  | COMPLEX_LITERAL(r,i) -> sprintf "(%s,%s)" r i *)


  | DEFINED_OP s -> s

  | DATA_EDIT_DESC s        -> s
  | KP_DESC s               -> s
  | POSITION_EDIT_DESC s    -> s
  | HOLLERITH(s, _)         -> s

  | LABEL s -> s

  | LETTER s -> s

  | CONSTRUCT_NAME s -> s
(*
  | DO_CONSTRUCT_NAME s
  | IF_CONSTRUCT_NAME s
  | WHERE_CONSTRUCT_NAME s
  | FORALL_CONSTRUCT_NAME s
  | CASE_CONSTRUCT_NAME s
  | SELECT_CONSTRUCT_NAME s
  | ASSOCIATE_CONSTRUCT_NAME s
    -> s
*)

(* dotted identifiers *)
  | D_EQ    -> ".eq."
  | D_NE    -> ".ne."
  | D_GT    -> ".gt."
  | D_GE    -> ".ge."
  | D_LT    -> ".lt."
  | D_LE    -> ".le."
  | D_NOT   -> ".not."
  | D_AND   -> ".and."
  | D_OR    -> ".or."
  | D_EQV   -> ".eqv."
  | D_NEQV  -> ".neqv."
(*
  | D_TRUE  -> ".true."
  | D_FALSE -> ".false."
*)

(* keywords *)
  | ABSTRACT s
  | ALLOCATABLE s
  | ALLOCATE s
  | ASSIGN s
  | ASSIGNMENT s
  | ASSOCIATE s
  | ASYNCHRONOUS s
  | BACKSPACE s
  | BIND s
  | BLOCK s
  | BLOCK_DATA s
  | BYTE s
  | CALL s
  | CASE s
  | CHARACTER s
  | CLASS s
  | CLOSE s
  | CODIMENSION s
  | COMMON s
(*  | COMPLEX s*)
  | CONCURRENT s
  | CONTAINS s
  | CONTINUE s
  | CRITICAL s
  | CYCLE s
  | DATA s
  | DEALLOCATE s
  | DEFAULT s
  | DIMENSION s
  | DO s
  | DOUBLE s
  | DOUBLE_PRECISION s
  | DOUBLE_COMPLEX s
(*  | ELEMENTAL s*)
  | ELSE s
  | ELSE_IF s
  | ELSEWHERE s
  | END s
  | END_ASSOCIATE s
  | END_BLOCK s
  | END_BLOCK_DATA s
  | END_CRITICAL s
  | END_DO s
  | END_ENUM s
  | END_FILE s
  | END_FORALL s
(*  | END_FUNCTION s*)
  | END_IF s
  | END_INTERFACE s
  | END_MODULE s
  | END_PROCEDURE s
  | END_PROGRAM s
  | END_SELECT s
  | END_SUBMODULE s
  | END_SUBPROGRAM s
(*  | END_SUBROUTINE s*)
  | END_TYPE s
  | END_WHERE s
  | ENTRY s
  | ENUM s
  | ENUMERATOR s
(*  | ERRMSG s*)
  | EQUIVALENCE s
  | EXIT s
  | EXTENDS s
(*  | EXTERNAL s*)
  | FLUSH s
  | FORALL s
  | FORMAT s
  | FUNCTION s
  | GENERIC s
  | GO_TO s
  | ID s
  | IF s
  | IMPLICIT s
  | IMPORT s
(*  | IMPURE s*)
(*
  | IN s
  | IN_OUT s
*)
  | INQUIRE s
(*  | INTEGER s*)
  | INTENT s
  | INTENT_SPEC s
  | INTERFACE s
  | INTRINSIC s
  | KIND s
  | KINDED_TYPE_SPEC s
  | LEN s
  | LOCK s
(*  | LOGICAL s*)
  | MODULE s
(*  | MOLD s*)
  | ALLOC_OPT_EXPR s
  | NAMELIST s
  | NONE s
  | NON_INTRINSIC s
  | NULL s
  | NULLIFY s
  | ONLY s
  | OPEN s
  | OPERATOR s
  | OPTIONAL s
(*  | OUT s*)
  | PARAMETER s
  | PAUSE s
  | POINTER s
  | PRECISION s
  | PREFIX_SPEC s
  | PRINT s
  | PRIVATE s
  | PROCEDURE s
  | PROGRAM s
(*  | PROTECTED s*)
  | PUBLIC s
(*  | PURE s*)
  | READ s
(*  | REAL s*)
(*  | RECURSIVE s*)
  | RESULT s
  | RETURN s
  | REWIND s
  | SAVE s
  | SELECT_CASE s
  | SELECT_TYPE s
  | SEQUENCE s
(*  | SOURCE s*)
(*  | STAT s*)
  | STOP s
  | SUBMODULE s
  | SUBROUTINE s
  | SYNC s
  | TARGET s
  | THEN s
  | TO s
  | TYPE s
  | USE s
(*
  | VALUE s
  | VOLATILE s
*)
  | WAIT s
  | WHERE s
  | WHILE s
  | WRITE s
(*
  | ACCESS s
  | ACTION s
  | BLANK s
  | DELIM s
  | FORM s
  | PAD s
  | POSITION s
  | RECL s
*)
  | ERR s
  | FILE s
  | IOSTAT s
  | IOMSG s
(*  | POS s*)
  | STATUS s
  | UNIT s

  | FMT s
  | NML s
(*
  | REC s
  | ADVANCE s
*)
  | SIZE s
  | EOR s
(*
  | DIRECT s
  | EXIST s
  | FORMATTED s
  | NAMED s
  | NEXTREC s
  | NUMBER s
  | OPENED s
  | READWRITE s
  | SEQUENTIAL s
  | UNFORMATTED s
*)
  | NAME_ s
  | IOLENGTH s

  | CONNECT_SPEC s
  | INQUIRE_SPEC s
  | IOCTL_SPEC s

  | CONNECT_INQUIRE_IOCTL_SPEC s
  | CONNECT_INQUIRE_SPEC s
  | INQUIRE_IOCTL_SPEC s

  | INTEL_CLOSE_CONNECT_SPEC s
(*
  | INTEL_CONNECT_SPEC s
  | INTEL_CONNECT_INQUIRE_SPEC s
  | INTEL_INQUIRE_SPEC s
*)
    -> s

  | PASS s
  | NOPASS s
  | NON_OVERRIDABLE s
  | DEFERRED s        -> s

  | FINAL s -> s

  | TYPE_IS s
  | CLASS_IS s
  | CLASS_DEFAULT s -> s

  | EOL -> "EOL"

  | EOF o_opt -> "EOF"^(Common.opt_to_string (fun _ -> "(EOL pending)") o_opt)

  | EOP -> "EOP"

  | NOTHING -> "NOTHING"

  | MARKER -> "MARKER"
  | PP_MARKER -> "PP_MARKER"

  | END_FRAGMENT -> "END_FRAGMENT"

  | INCLUDE__FILE s -> "include "^s

  | SIMPLE_ATTR s -> s

(*
  | _ -> "<impossible>"
*)


let get_keyword ?(elsef=fun _ -> raise Not_found) = function
  | ABSTRACT s
  | ALLOCATABLE s
  | ALLOCATE s
  | ASSIGN s
  | ASSIGNMENT s
  | ASSOCIATE s
  | ASYNCHRONOUS s
  | BACKSPACE s
  | BIND s
  | BLOCK s
  | BLOCK_DATA s
  | BYTE s
  | CALL s
  | CASE s
  | CHARACTER s
  | CLASS s
  | CLOSE s
  | CODIMENSION s
  | COMMON s
(*  | COMPLEX s*)
  | CONCURRENT s
  | CONTAINS s
  | CONTINUE s
  | CRITICAL s
  | CYCLE s
  | DATA s
  | DEALLOCATE s
  | DEFAULT s
  | DEFERRED s
  | DIMENSION s
  | DO s
  | DOUBLE s
  | DOUBLE_PRECISION s
  | DOUBLE_COMPLEX s
(*  | ELEMENTAL s*)
  | ELSE s
  | ELSE_IF s
  | ELSEWHERE s
  | END s
  | END_ASSOCIATE s
  | END_BLOCK s
  | END_BLOCK_DATA s
  | END_CRITICAL s
  | END_DO s
  | END_ENUM s
  | END_FILE s
  | END_FORALL s
(*  | END_FUNCTION s*)
  | END_IF s
  | END_INTERFACE s
  | END_MODULE s
  | END_PROCEDURE s
  | END_PROGRAM s
  | END_SELECT s
  | END_SUBMODULE s
  | END_SUBPROGRAM s
(*  | END_SUBROUTINE s*)
  | END_TYPE s
  | END_WHERE s
  | ENTRY s
  | ENUM s
  | ENUMERATOR s
(*  | ERRMSG s*)
  | EQUIVALENCE s
  | EXIT s
  | EXTENDS s
(*  | EXTERNAL s*)
  | FINAL s
  | FLUSH s
  | FORALL s
  | FORMAT s
  | FUNCTION s
  | GENERIC s
  | GO_TO s
  | ID s
  | IF s
  | IMPLICIT s
  | IMPORT s
(*  | IMPURE s*)
(*
  | IN s
  | IN_OUT s
*)
  | INQUIRE s
(*  | INTEGER s*)
  | INTENT s
  | INTENT_SPEC s
  | INTERFACE s
  | INTRINSIC s
  | KIND s
  | KINDED_TYPE_SPEC s
  | LEN s
  | LOCK s
(*  | LOGICAL s*)
  | MODULE s
(*  | MOLD s*)
  | ALLOC_OPT_EXPR s
  | NAMELIST s
  | NONE s
  | NON_INTRINSIC s
  | NON_OVERRIDABLE s
  | NOPASS s
  | NULL s
  | NULLIFY s
  | ONLY s
  | OPEN s
  | OPERATOR s
  | OPTIONAL s
(*  | OUT s*)
  | PARAMETER s
  | PASS s
  | PAUSE s
  | POINTER s
  | PRECISION s
  | PREFIX_SPEC s
  | PRINT s
  | PRIVATE s
  | PROCEDURE s
  | PROGRAM s
(*  | PROTECTED s*)
  | PUBLIC s
(*  | PURE s*)
  | READ s
(*  | REAL s*)
(*  | RECURSIVE s*)
  | RESULT s
  | RETURN s
  | REWIND s
  | SAVE s
  | SELECT_CASE s
  | SELECT_TYPE s
  | SEQUENCE s
(*  | SOURCE s*)
(*  | STAT s*)
  | STOP s
  | SUBMODULE s
  | SUBROUTINE s
  | SYNC s
  | TARGET s
  | THEN s
  | TO s
  | TYPE s
  | USE s
(*
  | VALUE s
  | VOLATILE s
*)
  | WAIT s
  | WHERE s
  | WHILE s
  | WRITE s

  | SIMPLE_ATTR s
(*
  | AUTOMATIC s
  | STATIC s
*)
  | ACCEPT s
  | REWRITE s
  | DELETE s
  | UNLOCK s
(*  | DEFINE_FILE s*)
  | ENCODE s
  | DECODE s
  | FIND s
  | VIRTUAL s
  | STRUCTURE s
  | END_STRUCTURE s
  | RECORD s
  | UNION s
  | END_UNION s
  | MAP s
  | END_MAP s
    -> s

  | DEFINE_FILE -> "define file"

  | t -> elsef t

let is_keyword ?(elsef=fun _ -> raise Not_found) x =
  try
    let _ = get_keyword ~elsef x in
    true
  with
    Not_found -> false



let is_action_stmt_kw = function
  | ALLOCATE _
  | BACKSPACE _
  | CALL _
  | CLOSE _
  | CONTINUE _
  | CYCLE _
  | DEALLOCATE _
  | END_FILE _
(*  | END_FUNCTION _*)
  | END_PROGRAM _
  | END_SUBMODULE _
  | END_SUBPROGRAM _
(*  | END_SUBROUTINE _*)
  | EXIT _
  | FORALL _
  | GO_TO _
  | IF _
  | INQUIRE _
  | NULLIFY _
  | OPEN _
  | PRINT _
  | READ _
  | RETURN _
  | REWIND _
  | STOP _
  | SYNC _
  | WHERE _
  | WRITE _
    -> true
  | _ -> false


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

  let loc_of_nd nd =
    nd#lloc#to_loc ?cache:(Some (Some env#fname_ext_cache)) ()

  let of_program_unit spec nd =
    (PROGRAM_UNIT(spec, nd), loc_of_nd nd)

  let of_spec_part_construct spec nd =
    (SPEC_PART_CONSTRUCT(spec, nd), loc_of_nd nd)

  let of_exec_part_construct spec nd =
    (EXEC_PART_CONSTRUCT(spec, nd), loc_of_nd nd)

  let of_subprogram spec nd =
    (SUBPROGRAM(spec, nd), loc_of_nd nd)

  let of_interface_spec spec nd =
    (INTERFACE_SPEC(spec, nd), loc_of_nd nd)

  let of_case_block spec nd =
    (CASE_BLOCK(spec, nd), loc_of_nd nd)

  let of_data_stmt_set spec nd =
    (DATA_STMT_SET(spec, nd), loc_of_nd nd)

  let of_variable spec nd =
    (VARIABLE(spec, nd), loc_of_nd nd)

  let of_expr spec nd =
    (EXPR(spec, nd), loc_of_nd nd)

  let of_stmt spec nd =
    (STMT(spec, nd), loc_of_nd nd)

  let of_select_case_stmt spec nd =
    (SELECT_CASE_STMT(spec, nd), loc_of_nd nd)

  let of_action_stmt spec nd =
    (ACTION_STMT(spec, nd), loc_of_nd nd)

  let of_type_spec spec nd =
    (TYPE_SPEC(spec, nd), loc_of_nd nd)

  let of_derived_type_def_part spec nd =
    (DERIVED_TYPE_DEF_PART(spec, nd), loc_of_nd nd)

  let of_only spec nd =
    (ONLY_(spec, nd), loc_of_nd nd)

  let of_function_head spec nd =
    (FUNCTION_HEAD(spec, nd), loc_of_nd nd)

  let of_function_stmt_head spec nd =
    (FUNCTION_STMT_HEAD(spec, nd), loc_of_nd nd)

  let of_subroutine_head spec nd =
    (SUBROUTINE_HEAD(spec, nd), loc_of_nd nd)

  let of_subroutine_stmt_head spec nd =
    (SUBROUTINE_STMT_HEAD(spec, nd), loc_of_nd nd)

  let of_pu_tail spec nd =
    (PU_TAIL(spec, nd), loc_of_nd nd)

  let is_include = function
    | INCLUDE__FILE _ -> true
    | _ -> false

  let is_pp_directive = function
    | PP_DEFINE__IDENT__BODY _
    | PP_INCLUDE__FILE _
    | PP_BRANCH _
(*
    | PP_IF__COND _
    | PP_ELIF__COND _
    | PP_IFDEF__IDENT _
    | PP_IFNDEF__IDENT _
*)
    | PP_ELSE
    | PP_ENDIF

    | PP_UNDEF__IDENT _

    | PP_ISSUE__MESG _
(*
    | PP_ERROR__MESG _
    | PP_WARNING__MESG _
*)
    | PP_UNKNOWN__REST _

    | PP_INCLUDE
    | PP_DEFINE
    | PP_UNDEF
    | PP_IFDEF
    | PP_IFNDEF
    | PP_IF
    | PP_ELIF

    | PP_ERROR
    | PP_WARNING

    | PP_UNKNOWN

      -> true

    | _ -> false

  let is_directive = function
    | OMP _
    | ACC _
    | XLF _
    | OCL _
    | DEC _
      -> true
    | _ -> false


  let size = function
  | PROGRAM_UNIT(spec, _)
  | SPEC_PART_CONSTRUCT(spec, _)
  | EXEC_PART_CONSTRUCT(spec, _)
  | SUBPROGRAM(spec, _)
  | INTERFACE_SPEC(spec, _)
  | CASE_BLOCK(spec, _)
  | DATA_STMT_SET(spec, _)
  | STMT(spec, _)
  | ACTION_STMT(spec, _)
  | VARIABLE(spec, _)
  | EXPR(spec, _)
  | TYPE_SPEC(spec, _)
  | DERIVED_TYPE_DEF_PART(spec, _)
  | ONLY_(spec, _)
    -> spec.Ast.Partial.length

  | _ -> 1



end (* of functor Token.F *)
