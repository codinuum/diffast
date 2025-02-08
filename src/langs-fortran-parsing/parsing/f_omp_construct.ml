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


module D = F_omp_directive


open Label_common

type t =
  | Atomic of D.atomic_sub option * bool
  | Critical of name option
  | Do of bool
  | Master
  | Ordered
  | Parallel
  | Sections
  | Single
  | Task
  | Workshare
  | ParallelDo of bool
  | ParallelSections
  | ParallelWorkshare
(* 4.0 *)
  | Simd
  | Target
  | TargetData
  | Teams
  | Distribute of bool
  | DistributeParallelDo of bool
  | TargetTeams
  | TeamsDistribute of bool
  | TargetTeamsDistribute of bool
  | TeamsDistributeParallelDo of bool
  | TargetTeamsDistributeParallelDo of bool
  | Taskgroup

let to_string = function
  | Atomic(a_opt, seq_cst) -> "Atomic"^(opt_to_string D.atomic_sub_to_string ~prefix:"." a_opt)^(D.seq_cst_to_string seq_cst)
  | Critical n_opt    -> "Critical"^(string_opt_to_string ~prefix:":" n_opt)
  | Do simd           -> "Do"^(D.simd_to_string simd)
  | Master            -> "Master"
  | Ordered           -> "Ordered"
  | Parallel          -> "Parallel"
  | Sections          -> "Sections"
  | Single            -> "Single"
  | Task              -> "Task"
  | Workshare         -> "Workshare"
  | ParallelDo simd   -> "ParallelDo"^(D.simd_to_string simd)
  | ParallelSections  -> "ParallelSections"
  | ParallelWorkshare -> "ParallelWorkshare"
  | Simd                            -> "Simd"
  | Target                          -> "Target"
  | TargetData                      -> "TargetData"
  | Teams                           -> "Teams"
  | Distribute simd                 -> "Distribute"^(D.simd_to_string simd)
  | DistributeParallelDo simd       -> "DistributeParallelDo"^(D.simd_to_string simd)
  | TargetTeams                     -> "TargetTeams"
  | TeamsDistribute simd            -> "TeamsDistribute"^(D.simd_to_string simd)
  | TargetTeamsDistribute simd      -> "TargetTeamsDistribute"^(D.simd_to_string simd)
  | TeamsDistributeParallelDo simd  -> "TeamsDistributeParallelDo"^(D.simd_to_string simd)
  | TargetTeamsDistributeParallelDo simd -> "TargetTeamsDistributeParallelDo"^(D.simd_to_string simd)
  | Taskgroup                       -> "Taskgroup"

let to_simple_string = function
  | Atomic(a_opt, seq_cst) -> "<atomic"^(opt_to_string D.atomic_sub_to_simple_string ~prefix:" " a_opt)^(D.seq_cst_to_simple_string seq_cst)^">"
  | Critical n_opt    -> "<critical"^(string_opt_to_string ~prefix:" (" ~suffix:")" n_opt)^">"
  | Do simd           -> "<do"^(D.simd_to_simple_string simd)^">"
  | Master            -> "<master>"
  | Ordered           -> "<ordered>"
  | Parallel          -> "<parallel>"
  | Sections          -> "<sections>"
  | Single            -> "<single>"
  | Task              -> "<task>"
  | Workshare         -> "<workshare>"
  | ParallelDo simd   -> "<parallel do"^(D.simd_to_simple_string simd)^">"
  | ParallelSections  -> "<parallel sections>"
  | ParallelWorkshare -> "<parallel workshare>"
  | Simd                            -> "<simd>"
  | Target                          -> "<target>"
  | TargetData                      -> "<target data>"
  | Teams                           -> "<teams>"
  | Distribute simd                 -> "<distribute"^(D.simd_to_simple_string simd)^">"
  | DistributeParallelDo simd       -> "<distribute parallel do"^(D.simd_to_simple_string simd)^">"
  | TargetTeams                     -> "<target teams>"
  | TeamsDistribute simd            -> "<teams distribute"^(D.simd_to_simple_string simd)^">"
  | TargetTeamsDistribute simd      -> "<target teams distribute"^(D.simd_to_simple_string simd)^">"
  | TeamsDistributeParallelDo simd  -> "<teams distribute parallel do"^(D.simd_to_simple_string simd)^">"
  | TargetTeamsDistributeParallelDo simd -> "<target teams distribute parallel do"^(D.simd_to_simple_string simd)^">"
  | Taskgroup                       -> "<taskgroup>"

let to_tag = function
  | Atomic(a_opt, seq_cst)               -> "OmpAtomic"^(opt_to_string D.atomic_sub_to_string a_opt)^"Construct", ["seq_cst",if seq_cst then "true" else "false"]
  | Critical n_opt                       -> "OmpCriticalConstruct", (string_opt_to_attr name_attr_name n_opt)
  | Do simd                              -> "OmpDo"^(D.simd_to_string simd)^"Construct", []
  | Master                               -> "OmpMasterConstruct", []
  | Ordered                              -> "OmpOrderedConstruct", []
  | Parallel                             -> "OmpParallelConstruct", []
  | Sections                             -> "OmpSectionsConstruct", []
  | Single                               -> "OmpSingleConstruct", []
  | Task                                 -> "OmpTaskConstruct", []
  | Workshare                            -> "OmpWorkshareConstruct", []
  | ParallelDo simd                      -> "OmpParallelDo"^(D.simd_to_string simd)^"Construct", []
  | ParallelSections                     -> "OmpParallelSectionsConstruct", []
  | ParallelWorkshare                    -> "OmpParallelWorkshareConstruct", []
  | Simd                                 -> "OmpSimdConstruct", []
  | Target                               -> "OmpTargetConstruct", []
  | TargetData                           -> "OmpTargetDataConstruct", []
  | Teams                                -> "OmpTeamsConstruct", []
  | Distribute simd                      -> "OmpDistribute"^(D.simd_to_string simd)^"Construct", []
  | DistributeParallelDo simd            -> "OmpDistributeParallelDo"^(D.simd_to_string simd)^"Construct", []
  | TargetTeams                          -> "OmpTargetTeamsConstruct", []
  | TeamsDistribute simd                 -> "OmpTeamsDistribute"^(D.simd_to_string simd)^"Construct", []
  | TargetTeamsDistribute simd           -> "OmpTargetTeamsDistribute"^(D.simd_to_string simd)^"Construct", []
  | TeamsDistributeParallelDo simd       -> "OmpTeamsDistributeParallelDo"^(D.simd_to_string simd)^"Construct", []
  | TargetTeamsDistributeParallelDo simd -> "OmpTargetTeamsDistributeParallelDo"^(D.simd_to_string simd)^"Construct", []
  | Taskgroup                            -> "OmpTaskgroupConstruct", []

let get_name = function
  | Critical n_opt ->
      begin
        match n_opt with
        | Some n -> n
        | _ -> raise Not_found
      end
  | _ -> raise Not_found

let get_name_opt = function
  | Critical n_opt 
    -> n_opt
  | _ -> None

let anonymize = function
  | Atomic(_, _) -> Atomic(None, false)
  | Critical _   -> Critical None
  | l -> l
