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

open Label_common

type atomic_sub =
  | Read
  | Write
  | Capture
  | Update

let atomic_sub_to_string = function
  | Read    -> "Read"
  | Write   -> "Write"
  | Capture -> "Capture"
  | Update  -> "Update"

let atomic_sub_to_simple_string = function
  | Read    -> "read"
  | Write   -> "write"
  | Capture -> "capture"
  | Update  -> "update"

let simd_to_string b = if b then "Simd" else ""

let simd_to_simple_string b = if b then " simd" else ""

let seq_cst_to_string b = if b then ".SeqCst" else ""

let seq_cst_to_simple_string b = if b then " seq_cst" else ""

type construct_type =
  | C_parallel
  | C_sections
  | C_do
  | C_taskgroup

let construct_type_to_string = function
  | C_parallel  -> "C_parallel"
  | C_sections  -> "C_sections"
  | C_do        -> "C_do"
  | C_taskgroup -> "C_taskgroup"

let construct_type_to_string_ = function
  | C_parallel  -> "Parallel"
  | C_sections  -> "Sections"
  | C_do        -> "Do"
  | C_taskgroup -> "Taskgroup"

let construct_type_to_simple_string = function
  | C_parallel  -> "parallel"
  | C_sections  -> "sections"
  | C_do        -> "do"
  | C_taskgroup -> "taskgroup"

type t =
  | ERROR
  | Atomic of atomic_sub option * bool (* seq_cst *)
  | Barrier
  | Critical of name option
  | Do of bool (* simd or not *)
  | Flush
  | Master
  | Ordered
  | Parallel
  | ParallelDo of bool (* simd or not *)
  | ParallelSections
  | ParallelWorkshare
  | Section
  | Sections
  | Single
  | Task
  | Taskwait
  | Taskyield
  | Threadprivate
  | Workshare
  | EndAtomic
  | EndCritical of name option
  | EndDo of bool (* simd or not *)
  | EndMaster
  | EndOrdered
  | EndParallel
  | EndSections
  | EndSingle
  | EndTask
  | EndWorkshare
  | EndParallelDo of bool (* simd or not *)
  | EndParallelSections
  | EndParallelWorkshare
(* 4.0 *)
  | Simd         
  | EndSimd
  | DeclareSimd of name
  | Target
  | EndTarget
  | TargetData
  | EndTargetData
  | TargetUpdate
  | DeclareTarget
  | Teams
  | EndTeams
  | Distribute of bool (* simd or not *)
  | EndDistribute of bool (* simd or not *)
  | DistributeParallelDo of bool (* simd or not *)
  | EndDistributeParallelDo of bool (* simd or not *)
  | TargetTeams
  | EndTargetTeams
  | TeamsDistribute of bool (* simd or not *)
  | EndTeamsDistribute of bool (* simd or not *)
  | TargetTeamsDistribute of bool (* simd or not *)
  | EndTargetTeamsDistribute of bool (* simd or not *)
  | TeamsDistributeParallelDo of bool (* simd or not *)
  | EndTeamsDistributeParallelDo of bool (* simd or not *)
  | TargetTeamsDistributeParallelDo of bool (* simd or not *)
  | EndTargetTeamsDistributeParallelDo of bool (* simd or not *)
  | Taskgroup
  | EndTaskgroup
  | Cancel of construct_type
  | CancellationPoint of construct_type
  | DeclareReduction

let to_string = function
  | ERROR                -> "ERROR"
  | Atomic(a_opt, seq_cst) -> "Atomic"^(opt_to_string atomic_sub_to_string ~prefix:"." a_opt)^(seq_cst_to_string seq_cst)
  | Barrier              -> "Barrier"
  | Critical n_opt       -> "Critical"^(string_opt_to_string ~prefix:":" n_opt)
  | Do simd              -> "Do"^(simd_to_string simd)
  | Flush                -> "Flush"
  | Master               -> "Master"
  | Ordered              -> "Ordered"
  | Parallel             -> "Parallel"
  | ParallelDo simd      -> "ParallelDo"^(simd_to_string simd)
  | ParallelSections     -> "ParallelSections"
  | ParallelWorkshare    -> "ParallelWorkshare"
  | Section              -> "Section"
  | Sections             -> "Sections"
  | Single               -> "Single"
  | Task                 -> "Task"
  | Taskwait             -> "Taskwait"
  | Taskyield            -> "Taskyield"
  | Threadprivate        -> "Threadprivate"
  | Workshare            -> "Workshare"
  | EndAtomic            -> "EndAtomic"
  | EndCritical n_opt    -> "EndCritical"^(string_opt_to_string ~prefix:":" n_opt)
  | EndDo simd           -> "EndDo"^(simd_to_string simd)
  | EndMaster            -> "EndMaster"
  | EndOrdered           -> "EndOrdered"
  | EndParallel          -> "EndParallel"
  | EndSections          -> "EndSections"
  | EndSingle            -> "EndSingle"
  | EndTask              -> "EndTask"
  | EndWorkshare         -> "EndWorkshare"
  | EndParallelDo simd   -> "EndParallelDo"^(simd_to_string simd)
  | EndParallelSections  -> "EndParallelSections"
  | EndParallelWorkshare -> "EndParallelWordshare"
(* 4.0 *)
  | Simd                 -> "Simd"
  | EndSimd              -> "EndSimd"
  | DeclareSimd n        -> "DeclareSimd:"^n
  | Target               -> "Target"
  | EndTarget            -> "EndTarget"
  | TargetData           -> "TargetData"
  | EndTargetData        -> "EndTargetData"
  | TargetUpdate         -> "TargetUpdate"
  | DeclareTarget        -> "DeclareTarget"
  | Teams                -> "Teams"
  | EndTeams             -> "EndTeams"
  | Distribute simd      -> "Distribute"^(simd_to_string simd)
  | EndDistribute simd   -> "EndDistribute"^(simd_to_string simd)
  | DistributeParallelDo simd               -> "DistributeParallelDo"^(simd_to_string simd)
  | EndDistributeParallelDo simd            -> "EndDistributeParallelDo"^(simd_to_string simd)
  | TargetTeams                             -> "TargetTeams"
  | EndTargetTeams                          -> "EndTargetTeams"
  | TeamsDistribute simd                    -> "TeamsDistribute"^(simd_to_string simd)
  | EndTeamsDistribute simd                 -> "EndTeamsDistribute"^(simd_to_string simd)
  | TargetTeamsDistribute simd              -> "TargetTeamsDistribute"^(simd_to_string simd)
  | EndTargetTeamsDistribute simd           -> "EndTargetTeamsDistribute"^(simd_to_string simd)
  | TeamsDistributeParallelDo simd          -> "TeamsDistributeParallelDo"^(simd_to_string simd)
  | EndTeamsDistributeParallelDo simd       -> "EndTeamsDistributeParallelDo"^(simd_to_string simd)
  | TargetTeamsDistributeParallelDo simd    -> "TargetTeamsDistributeParallelDo"^(simd_to_string simd)
  | EndTargetTeamsDistributeParallelDo simd -> "EndTargetTeamsDistributeParallelDo"^(simd_to_string simd)
  | Taskgroup           -> "Taskgroup"
  | EndTaskgroup        -> "EndTaskgroup"
  | Cancel c            -> "Cancel:"^(construct_type_to_string c)
  | CancellationPoint c -> "CancellationPoint:"^(construct_type_to_string c)
  | DeclareReduction    -> "DeclareReduction"


let to_simple_string = function
  | ERROR                -> "<error>"
  | Atomic(a_opt, seq_cst) -> "atomic"^(opt_to_string atomic_sub_to_simple_string ~prefix:" " a_opt)^(seq_cst_to_simple_string seq_cst)
  | Barrier              -> "barrier"
  | Critical n_opt       -> "critical"^(string_opt_to_string ~prefix:" (" ~suffix:")" n_opt)
  | Do simd              -> "do"^(simd_to_simple_string simd)
  | Flush                -> "flush"
  | Master               -> "master"
  | Ordered              -> "ordered"
  | Parallel             -> "parallel"
  | ParallelDo simd      -> "parallel do"^(simd_to_simple_string simd)
  | ParallelSections     -> "parallel sections"
  | ParallelWorkshare    -> "parallel workshare"
  | Section              -> "section"
  | Sections             -> "sections"
  | Single               -> "single"
  | Task                 -> "task"
  | Taskwait             -> "taskwait"
  | Taskyield            -> "taskyield"
  | Threadprivate        -> "threadprivate"
  | Workshare            -> "workshare"
  | EndAtomic            -> "end atomic"
  | EndCritical n_opt    -> "end critical"^(string_opt_to_string ~prefix:" (" ~suffix:")" n_opt)
  | EndDo simd           -> "end do"^(simd_to_simple_string simd)
  | EndMaster            -> "end master"
  | EndOrdered           -> "end ordered"
  | EndParallel          -> "end parallel"
  | EndSections          -> "end sections"
  | EndSingle            -> "end single"
  | EndTask              -> "end task"
  | EndWorkshare         -> "end workshare"
  | EndParallelDo simd   -> "end parallel do"^(simd_to_simple_string simd)
  | EndParallelSections  -> "end parallel sections"
  | EndParallelWorkshare -> "end parallel wordshare"
(* 4.0 *)
  | Simd                 -> "simd"
  | EndSimd              -> "end simd"
  | DeclareSimd n        -> "declare simd ("^n^")"
  | Target               -> "target"
  | EndTarget            -> "end target"
  | TargetData           -> "target data"
  | EndTargetData        -> "end target data"
  | TargetUpdate         -> "target update"
  | DeclareTarget        -> "declare target"
  | Teams                -> "teams"
  | EndTeams             -> "end teams"
  | Distribute simd      -> "distribute"^(simd_to_simple_string simd)
  | EndDistribute simd   -> "end distribute"^(simd_to_simple_string simd)
  | DistributeParallelDo simd               -> "distribute parallel do"^(simd_to_simple_string simd)
  | EndDistributeParallelDo simd            -> "end distribute parallel do"^(simd_to_simple_string simd)
  | TargetTeams                             -> "target teams"
  | EndTargetTeams                          -> "end target teams"
  | TeamsDistribute simd                    -> "teams distribute"^(simd_to_simple_string simd)
  | EndTeamsDistribute simd                 -> "end teams distribute"^(simd_to_simple_string simd)
  | TargetTeamsDistribute simd              -> "target teams distribute"^(simd_to_simple_string simd)
  | EndTargetTeamsDistribute simd           -> "end target teams distribute"^(simd_to_simple_string simd)
  | TeamsDistributeParallelDo simd          -> "teams distribute parallel do"^(simd_to_simple_string simd)
  | EndTeamsDistributeParallelDo simd       -> "end teams distribute parallel do"^(simd_to_simple_string simd)
  | TargetTeamsDistributeParallelDo simd    -> "target teams distribute parallel do"^(simd_to_simple_string simd)
  | EndTargetTeamsDistributeParallelDo simd -> "end target teams distribute parallel do"^(simd_to_simple_string simd)
  | Taskgroup           -> "taskgroup"
  | EndTaskgroup        -> "end taskgroup"
  | Cancel c            -> "cancel "^(construct_type_to_simple_string c)
  | CancellationPoint c -> "cancellation point "^(construct_type_to_simple_string c)
  | DeclareReduction    -> "declare reduction"


let to_tag = function
  | ERROR                -> "ERROR", []
  | Atomic(a_opt, seq_cst) -> "OmpAtomic"^(opt_to_string atomic_sub_to_string a_opt)^(seq_cst_to_string seq_cst), []
  | Barrier              -> "OmpBarrier", []
  | Critical n_opt       -> "OmpCritical", (string_opt_to_attr name_attr_name n_opt)
  | Do simd              -> "OmpDo"^(simd_to_string simd), []
  | Flush                -> "OmpFlush", []
  | Master               -> "OmpMaster", []
  | Ordered              -> "OmpOrdered", []
  | Parallel             -> "OmpParallel", []
  | ParallelDo simd      -> "OmpParallelDo"^(simd_to_string simd), []
  | ParallelSections     -> "OmpParallelSections", []
  | ParallelWorkshare    -> "OmpParallelWorkshare", []
  | Section              -> "OmpSection", []
  | Sections             -> "OmpSections", []
  | Single               -> "OmpSingle", []
  | Task                 -> "OmpTask", []
  | Taskwait             -> "OmpTaskwait", []
  | Taskyield            -> "OmpTaskyield", []
  | Threadprivate        -> "OmpThreadprivate", []
  | Workshare            -> "OmpWorkshare", []
  | EndAtomic            -> "OmpEndAtomic", []
  | EndCritical n_opt    -> "OmpEndCritical", (string_opt_to_attr name_attr_name n_opt)
  | EndDo simd           -> "OmpEndDo"^(simd_to_string simd), []
  | EndMaster            -> "OmpEndMaster", []
  | EndOrdered           -> "OmpEndOrdered", []
  | EndParallel          -> "OmpEndParallel", []
  | EndSections          -> "OmpEndSections", []
  | EndSingle            -> "OmpEndSingle", []
  | EndTask              -> "OmpEndTask", []
  | EndWorkshare         -> "OmpEndWorkshare", []
  | EndParallelDo simd   -> "OmpEndParallelDo"^(simd_to_string simd), []
  | EndParallelSections  -> "OmpEndParallelSections", []
  | EndParallelWorkshare -> "OmpEndParallelWordshare", []
(* 4.0 *)
  | Simd                 -> "OmpSimd", []
  | EndSimd              -> "OmpEndSimd", []
  | DeclareSimd n        -> "OmpDeclareSimd", [name_attr_name,n]
  | Target               -> "OmpTarget", []
  | EndTarget            -> "OmpEndTarget", []
  | TargetData           -> "OmpTargetData", []
  | EndTargetData        -> "OmpEndTargetData", []
  | TargetUpdate         -> "OmpTargetUpdate", []
  | DeclareTarget        -> "OmpDeclareTarget", []
  | Teams                -> "OmpTeams", []
  | EndTeams             -> "OmpEndTeams", []
  | Distribute simd      -> "OmpDistribute"^(simd_to_string simd), []
  | EndDistribute simd   -> "OmpEndDistribute"^(simd_to_string simd), []
  | DistributeParallelDo simd               -> "OmpDistributeParallelDo"^(simd_to_string simd), []
  | EndDistributeParallelDo simd            -> "OmpEndDistributeParallelDo"^(simd_to_string simd), []
  | TargetTeams                             -> "OmpTargetTeams", []
  | EndTargetTeams                          -> "OmpEndTargetTeams", []
  | TeamsDistribute simd                    -> "OmpTeamsDistribute"^(simd_to_string simd), []
  | EndTeamsDistribute simd                 -> "OmpEndTeamsDistribute"^(simd_to_string simd), []
  | TargetTeamsDistribute simd              -> "OmpTargetTeamsDistribute"^(simd_to_string simd), []
  | EndTargetTeamsDistribute simd           -> "OmpEndTargetTeamsDistribute"^(simd_to_string simd), []
  | TeamsDistributeParallelDo simd          -> "OmpTeamsDistributeParallelDo"^(simd_to_string simd), []
  | EndTeamsDistributeParallelDo simd       -> "OmpEndTeamsDistributeParallelDo"^(simd_to_string simd), []
  | TargetTeamsDistributeParallelDo simd    -> "OmpTargetTeamsDistributeParallelDo"^(simd_to_string simd), []
  | EndTargetTeamsDistributeParallelDo simd -> "OmpEndTargetTeamsDistributeParallelDo"^(simd_to_string simd), []
  | Taskgroup           -> "OmpTaskgroup", []
  | EndTaskgroup        -> "OmpEndTaskgroup", []
  | Cancel c            -> "OmpCancel", ["type",construct_type_to_string_ c]
  | CancellationPoint c -> "OmpCancellationPoint", ["type",construct_type_to_string_ c]
  | DeclareReduction    -> "OmpDeclareReduction", []


let get_name = function
  | Critical n_opt
  | EndCritical n_opt -> 
      begin
        match n_opt with
        | Some n -> n
        | _ -> raise Not_found
      end
  | _ -> raise Not_found

let get_name_opt = function
  | Critical n_opt 
  | EndCritical n_opt
    -> n_opt
  | _ -> None

let is_specification_part = function
  | ERROR
  | DeclareSimd _
  | DeclareTarget
  | Threadprivate
  | DeclareReduction
    -> true

  | _ -> false

let is_execution_part = function
  | ERROR
  | Atomic _
  | EndAtomic
  | Critical _
  | EndCritical _
  | Do _
  | EndDo _
  | Master
  | EndMaster
  | Ordered
  | EndOrdered
  | Parallel
  | EndParallel
  | Sections
  | Section
  | EndSections
  | Single
  | EndSingle
  | Task
  | EndTask
  | Workshare
  | EndWorkshare
  | ParallelDo _
  | EndParallelDo _
  | ParallelSections
  | EndParallelSections
  | ParallelWorkshare
  | EndParallelWorkshare
  | Simd
  | EndSimd
  | Target
  | EndTarget
  | Teams
  | EndTeams
  | Distribute _
  | EndDistribute _
  | DistributeParallelDo _
  | EndDistributeParallelDo _
  | TargetTeams
  | EndTargetTeams
  | TeamsDistribute _
  | EndTeamsDistribute _
  | TargetTeamsDistribute _
  | EndTargetTeamsDistribute _
  | TeamsDistributeParallelDo _
  | EndTeamsDistributeParallelDo _
  | TargetTeamsDistributeParallelDo _
  | EndTargetTeamsDistributeParallelDo _
  | Taskgroup
  | EndTaskgroup

  | Barrier
  | Flush
  | Taskwait
  | Taskyield
  | TargetData
  | EndTargetData
  | TargetUpdate
  | Cancel _
  | CancellationPoint _
    -> true

  | _ -> false

let anonymize = function
  | Atomic(_, _)  -> Atomic(None, false)
  | Critical _    -> Critical None
  | EndCritical _ -> EndCritical None
  | l -> l

