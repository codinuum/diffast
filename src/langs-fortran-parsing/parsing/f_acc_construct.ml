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


module D = F_acc_directive


open Label_common

type t =
  | Atomic of D.atomic_sub option
  | Parallel
  | Kernels
  | ParallelLoop
  | KernelsLoop
  | Data
  | Host_data
  | Loop

let to_string = function
  | Atomic a_opt -> "Atomic"^(opt_to_string D.atomic_sub_to_string ~prefix:"." a_opt)
  | Parallel     -> "Parallel"
  | Kernels      -> "Kernels"
  | Data         -> "Data"
  | Host_data    -> "Host_data"
  | ParallelLoop -> "ParallelLoop"
  | KernelsLoop  -> "KernelsLoop"
  | Loop         -> "Loop"

let to_simple_string = function
  | Atomic a_opt -> "<atomic"^(opt_to_string D.atomic_sub_to_simple_string ~prefix:" " a_opt)^">"
  | Parallel     -> "<parallel>"
  | Kernels      -> "<kernels>"
  | Data         -> "<data>"
  | Host_data    -> "<host_data>"
  | ParallelLoop -> "<parallel-loop>"
  | KernelsLoop  -> "<kernels-loop>"
  | Loop         -> "<loop>"

let to_tag = function
  | Atomic a_opt -> "AccAtomicConstruct"^(opt_to_string D.atomic_sub_to_string a_opt), []
  | Parallel     -> "AccParallelConstruct", []
  | Kernels      -> "AccKernelsConstruct", []
  | Data         -> "AccDataConstruct", []
  | Host_data    -> "AccHost_dataConstruct", []
  | ParallelLoop -> "AccParallelLoopConstruct", []
  | KernelsLoop  -> "AccKernelsLoopConstruct", []
  | Loop         -> "AccLoopConstruct", []

let anonymize = function
  | Atomic _ -> Atomic None
  | l -> l

