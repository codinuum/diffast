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



module Assertion = struct
  type t =
    | Itercnt
    | Minitercnt
    | Maxitercnt
    | Nodeps

  let to_string = function
    | Itercnt    -> "Itercnt"
    | Minitercnt -> "Minitercnt"
    | Maxitercnt -> "Maxitercnt"
    | Nodeps     -> "Nodeps"

  let to_simple_string = function
    | Itercnt    -> "ITERCNT"
    | Minitercnt -> "MINITERCNT"
    | Maxitercnt -> "MAXITERCNT"
    | Nodeps     -> "NODEPS"

  let to_tag = function
    | Itercnt    -> "XlfItercnt", []
    | Minitercnt -> "XlfMinitercnt", []
    | Maxitercnt -> "XlfMaxitercnt", []
    | Nodeps     -> "XlfNodeps", []

end

module Directive = struct

  type source =
    | Fixed of int option
    | Free
    | FreeF90
    | FreeIBM

  let source_to_string = function
    | Fixed i_opt -> "Fixed"^(opt_to_string string_of_int ~prefix:":" i_opt)
    | Free        -> "Free"
    | FreeF90     -> "Free(F90)"
    | FreeIBM     -> "Free(IBM)"

  type high_or_low =
    | VeryHigh
    | VeryLow

  let high_or_low_to_string = function
    | VeryHigh -> "VeryHigh"
    | VeryLow  -> "VeryLow"

  let high_or_low_to_simple_string = function
    | VeryHigh -> "VERY_HIGH"
    | VeryLow  -> "VERY_LOW"


  type t =
    | Align of string
    | Assert          
    | BlockLoop
    | Cncall          
    | Collapse
    | Eject
    | ExecutionFrequency of high_or_low
    | ExpectedValue of name
    | FunctraceXlfCatch
    | FunctraceXlfEnter
    | FunctraceXlfExit
    | IgnoreTkr
    | Independent
    | Loopid of name
    | MemDelay of string
    | New
    | Nofunctrace
    | Nosimd
    | Novector
    | Permutation
    | Snapshot
    | Sourceform of source
    | StreamUnroll
    | Subscriptorder
    | Unroll
    | UnrollAndFuse

    | Process

  let to_string = function
    | Align i               -> "Align:"^i
    | Assert                -> "Assert"
    | BlockLoop             -> "BlockLoop"
    | Cncall                -> "Cncall"
    | Collapse              -> "Collapse"
    | Eject                 -> "Eject"
    | ExecutionFrequency hl -> "ExecutionFrequency:"^(high_or_low_to_string hl)
    | ExpectedValue n       -> "ExpectedValue:"^n
    | FunctraceXlfCatch     -> "FunctraceXlfCatch"
    | FunctraceXlfEnter     -> "FunctraceXlfEnter"
    | FunctraceXlfExit      -> "FunctraceXlfExit"
    | IgnoreTkr             -> "IgnoreTkr"
    | Independent           -> "Independent"
    | Loopid n              -> "Loopid:"^n
    | MemDelay c            -> "MemDelay:"^c
    | New                   -> "New"
    | Nofunctrace           -> "Nofunctrace"
    | Nosimd                -> "Nosimd"
    | Novector              -> "Novector"
    | Permutation           -> "Permutation"
    | Snapshot              -> "Snapshot"
    | Sourceform s          -> "Sourceform:"^(source_to_string s)
    | StreamUnroll          -> "StreamUnroll"
    | Subscriptorder        -> "Subscriptorder"
    | Unroll                -> "Unroll"
    | UnrollAndFuse         -> "UnrollAndFuse"

    | Process               -> "Process"

  let to_simple_string = function
    | Align i               -> "ALIGN("^i^")"
    | Assert                -> "ASSERT"
    | BlockLoop             -> "BLOCK_LOOP"
    | Cncall                -> "CNCALL"
    | Collapse              -> "COLLAPSE"
    | Eject                 -> "EJECT"
    | ExecutionFrequency hl -> Printf.sprintf "EXECUTION_FREQUENCY(%s)" (high_or_low_to_simple_string hl)
    | ExpectedValue n       -> Printf.sprintf "EXPECTED_VALUE(%s)" n
    | FunctraceXlfCatch     -> "FUNCTRACE_XLF_CATCH"
    | FunctraceXlfEnter     -> "FUNCTRACE_XLF_ENTER"
    | FunctraceXlfExit      -> "FUNCTRACE_XLF_EXIT"
    | IgnoreTkr             -> "IGNORE_TKR"
    | Independent           -> "INDEPENDENT"
    | Loopid n              -> "LOOPID:"^n
    | MemDelay c            -> "MEM_DELAY("^c^")"
    | New                   -> "NEW"
    | Nofunctrace           -> "NOFUNCTRACE"
    | Nosimd                -> "NOSIMD"
    | Novector              -> "NOVECTOR"
    | Permutation           -> "PERMUTATION"
    | Snapshot              -> "SNAPSHOT"
    | Sourceform s          -> "SOURCEFORM("^(source_to_string s)^")"
    | StreamUnroll          -> "STREAM_UNROLL"
    | Subscriptorder        -> "SUBSCRIPTORDER"
    | Unroll                -> "UNROLL"
    | UnrollAndFuse         -> "UNROLL_AND_FUSE"

    | Process               -> "@PROCESS"

  let to_tag = function
    | Align i               -> "XlfAlign", ["boundary",i]
    | Assert                -> "XlfAssert", []
    | BlockLoop             -> "XlfBlockLoop", []
    | Cncall                -> "XlfCncall", []
    | Collapse              -> "XlfCollapse", []
    | Eject                 -> "XlfEject", []
    | ExecutionFrequency hl -> "XlfExecutionFrequency", ["freq",high_or_low_to_string hl]
    | ExpectedValue n       -> "XlfExpectedValue", [name_attr_name,n]
    | FunctraceXlfCatch     -> "XlfFunctraceXlfCatch", []
    | FunctraceXlfEnter     -> "XlfFunctraceXlfEnter", []
    | FunctraceXlfExit      -> "XlfFunctraceXlfExit", []
    | IgnoreTkr             -> "XlfIgnoreTkr", []
    | Independent           -> "XlfIndependent", []
    | Loopid n              -> "XlfLoopid", [name_attr_name,n]
    | MemDelay c            -> "XlfMemDelay", ["cycle",c]
    | New                   -> "XlfNew", []
    | Nofunctrace           -> "XlfNofunctrace", []
    | Nosimd                -> "XlfNosimd", []
    | Novector              -> "XlfNovector", []
    | Permutation           -> "XlfPermutation", []
    | Snapshot              -> "XlfSnapshot", []
    | Sourceform s          -> "XlfSourceform", ["source",(source_to_string s)]
    | StreamUnroll          -> "XlfStreamUnroll", []
    | Subscriptorder        -> "XlfSubscriptorder", []
    | Unroll                -> "XlfUnroll", []
    | UnrollAndFuse         -> "XlfUnrollAndFuse", []

    | Process               -> "XlfProcess", []

  let get_name = function
    | Loopid n        
    | ExpectedValue n
      -> n
    | _ -> raise Not_found

  let get_name_opt = function
    | Loopid n 
    | ExpectedValue n
      -> Some n       
    | _ -> None

  let is_specification_part = function
    | Align _
    | Collapse
    | Eject
    | ExpectedValue _
    | Process
    | Subscriptorder
    | Sourceform _
      -> true
    | _ -> false

  let is_execution_part = function
    | Assert
    | BlockLoop
    | Cncall
    | Eject
    | ExecutionFrequency _
    | IgnoreTkr
    | Independent
    | Loopid _
    | MemDelay _
    | New
    | Nosimd
    | Novector
    | Permutation
    | Snapshot
    | Sourceform _
    | StreamUnroll
    | Unroll
    | UnrollAndFuse
    | Process
      -> true
    | _ -> false


  let anonymize = function
    | Align _              -> Align ""
    | ExecutionFrequency _ -> ExecutionFrequency VeryLow
    | ExpectedValue _      -> ExpectedValue ""
    | Loopid _             -> Loopid ""
    | MemDelay _           -> MemDelay ""
    | Sourceform _         -> Sourceform FreeF90
    | l -> l

end (* of module Xlf.Directive *)


type t =
  | ERROR 

  | CollapseArray of name
  | SubscriptorderArray of name * string list
  | NewClause
  | ReductionClause
  | Option of name

let to_string = function
  | ERROR                      -> "ERROR"

  | CollapseArray n            -> "CollapseArray:"^n
  | SubscriptorderArray(n, il) -> "SubscriptorderArray:"^n^":"^(String.concat ";" il)
  | NewClause                  -> "NewClause"
  | ReductionClause            -> "ReductionClause"
  | Option n                   -> "Option:"^n

let to_simple_string = function
  | ERROR                      -> "<error>"

  | CollapseArray n            -> n
  | SubscriptorderArray(n, il) -> Printf.sprintf "%s(%s)" n (String.concat "," il)
  | NewClause                  -> "<new-clause>"
  | ReductionClause            -> "<reduction-clause>"
  | Option n                   -> n

let to_tag = function
  | ERROR                      -> "ERROR", []

  | CollapseArray n            -> "XlfCollapseArray", [name_attr_name,n]
  | SubscriptorderArray(n, il) -> "XlfSubscriptorderArray", [name_attr_name,n;"subscriptorder_numbers",String.concat ";" il]
  | NewClause                  -> "XlfNewClause", []
  | ReductionClause            -> "XlfReductionClause", []
  | Option n                   -> "XlfOption", [name_attr_name,n]

let get_name = function
  | CollapseArray n
  | SubscriptorderArray(n, _) 
  | Option n                 
    -> n

  | _ -> raise Not_found

let get_name_opt = function
  | CollapseArray n 
  | SubscriptorderArray(n, _) 
  | Option n                 
    -> Some n
  | _ -> None

let anonymize = function
  | CollapseArray _           -> CollapseArray ""
  | SubscriptorderArray(_, _) -> SubscriptorderArray("", [])
  | Option _                  -> Option ""
  | l -> l

