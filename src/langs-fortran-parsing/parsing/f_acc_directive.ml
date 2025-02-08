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

type t =
  | ERROR
  | Atomic of atomic_sub option
  | Parallel
  | Kernels
  | ParallelLoop
  | KernelsLoop
  | Data
  | EnterData
  | ExitData
  | Host_data
  | Loop
  | Cache
  | Update
  | Wait
  | Routine of name option
  | Declare
  | EndAtomic
  | EndParallel
  | EndKernels
  | EndParallelLoop
  | EndKernelsLoop
  | EndData
  | EndHost_data

let to_string = function
  | ERROR           -> "ERROR"
  | Atomic a_opt    -> "Atomic"^(opt_to_string atomic_sub_to_string ~prefix:"." a_opt)
  | Parallel        -> "Parallel"
  | Kernels         -> "Kernels"
  | ParallelLoop    -> "ParallelLoop"
  | KernelsLoop     -> "KernelsLoop"
  | Data            -> "Data"
  | EnterData       -> "EnterData"
  | ExitData        -> "ExitData"
  | Host_data       -> "Host_data"
  | Loop            -> "Loop"
  | Cache           -> "Cache"
  | Update          -> "Update"
  | Wait            -> "Wait"
  | Routine n_opt   -> "Routine"^(string_opt_to_string ~prefix:":" n_opt)
  | Declare         -> "Declare"
  | EndAtomic       -> "EndAtomic"
  | EndParallel     -> "EndParallel"
  | EndKernels      -> "EndKernels"
  | EndParallelLoop -> "EndParallelLoop"
  | EndKernelsLoop  -> "EndKernelsLoop"
  | EndData         -> "EndData"
  | EndHost_data    -> "EndHost_data"


let to_simple_string = function
  | ERROR           -> "<error>"
  | Atomic a_opt    -> "atomic"^(opt_to_string atomic_sub_to_simple_string ~prefix:" " a_opt)
  | Parallel        -> "parallel"
  | Kernels         -> "kernels"
  | ParallelLoop    -> "parallel loop"
  | KernelsLoop     -> "kernels loop"
  | Data            -> "data"
  | EnterData       -> "enter data"
  | ExitData        -> "exit data"
  | Host_data       -> "host_data"
  | Loop            -> "loop"
  | Cache           -> "cache"
  | Update          -> "update"
  | Wait            -> "wait"
  | Routine n_opt   -> "routine"^(string_opt_to_string ~prefix:" (" ~suffix:")" n_opt)
  | Declare         -> "declare"
  | EndAtomic       -> "end atomic"
  | EndParallel     -> "end parallel"
  | EndKernels      -> "end kernels"
  | EndParallelLoop -> "end parallel loop"
  | EndKernelsLoop  -> "end kernels loop"
  | EndData         -> "end data"
  | EndHost_data    -> "end host_data"

let to_tag = function
  | ERROR           -> "ERROR", []
  | Atomic a_opt    -> "AccAtomic"^(opt_to_string atomic_sub_to_string a_opt), []
  | Parallel        -> "AccParallel", []
  | Kernels         -> "AccKernels", []
  | ParallelLoop    -> "AccParallelLoop", []
  | KernelsLoop     -> "AccKernelsLoop", []
  | Data            -> "AccData", []
  | EnterData       -> "AccEnterData", []
  | ExitData        -> "AccExitData", []
  | Host_data       -> "AccHost_data", []
  | Loop            -> "AccLoop", []
  | Cache           -> "AccCache", []
  | Update          -> "AccUpdate", []
  | Wait            -> "AccWait", []
  | Routine n_opt   -> "AccRoutine", (string_opt_to_attr name_attr_name n_opt)
  | Declare         -> "AccDeclare", []
  | EndAtomic       -> "AccEndAtomic", []
  | EndParallel     -> "AccEndParallel", []
  | EndParallelLoop -> "AccEndParallelLoop", []
  | EndKernelsLoop  -> "AccEndKernelsLoop", []
  | EndKernels      -> "AccEndKernels", []
  | EndData         -> "AccEndData", []
  | EndHost_data    -> "AccEndHost_data", []


let get_name = function
  | Routine n_opt ->
      begin
        match n_opt with
        | Some n -> n
        | _ -> raise Not_found
      end
  | _ -> raise Not_found

let get_name_opt = function
  | Routine n_opt
    -> n_opt
  | _ -> None

let is_specification_part = function
  | ERROR
  | Declare
  | Routine _
    -> true
  | _ -> false

let is_execution_part = function
  | ERROR
  | Atomic _
  | Parallel
  | Kernels
  | ParallelLoop
  | KernelsLoop
  | Data
  | EnterData
  | ExitData
  | Host_data
  | Loop
  | Cache
  | Update
  | Wait
  | EndAtomic
  | EndParallel
  | EndKernels
  | EndParallelLoop
  | EndKernelsLoop
  | EndData
  | EndHost_data
    -> true
  | _ -> false

let anonymize = function
  | Atomic _  -> Atomic None
  | Routine _ -> Routine None
  | l -> l

