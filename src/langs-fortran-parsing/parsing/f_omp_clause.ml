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

type data_sharing_attr =
  | Private
  | Firstprivate
  | Shared
  | None_

let data_sharing_attr_to_string = function
  | Private      -> "Private"
  | Firstprivate -> "Firstprivate"
  | Shared       -> "Shared"
  | None_        -> "None"

let data_sharing_attr_to_simple_string = function
  | Private      -> "private"
  | Firstprivate -> "firstprivate"
  | Shared       -> "shared"
  | None_        -> "none"

let data_sharing_attr_to_tag = function
  | Private      -> "OmpPrivate", []
  | Firstprivate -> "OmpFirstprivate", []
  | Shared       -> "OmpShared", []
  | None_        -> invalid_arg "Label.OmpClause.data_sharing_attr_to_tag"

type kind =
  | Static
  | Dynamic
  | Guided
  | Auto
  | Runtime

let kind_to_string = function
  | Static  -> "Static"
  | Dynamic -> "Dynamic"
  | Guided  -> "Guided"
  | Auto    -> "Auto"
  | Runtime -> "Runtime"

let kind_to_simple_string = function
  | Static  -> "static"
  | Dynamic -> "dynamic"
  | Guided  -> "guided"
  | Auto    -> "auto"
  | Runtime -> "runtime"

type policy = 
  | Master
  | Close
  | Spread

let policy_to_string = function
  | Master -> "Master"
  | Close  -> "Close"
  | Spread -> "Spread"

let policy_to_simple_string = function
  | Master -> "master"
  | Close  -> "close"
  | Spread -> "spread"

type map_type =
  | Alloc
  | To
  | From
  | Tofrom

let map_type_to_string = function
  | Alloc  -> "Alloc"
  | To     -> "To"
  | From   -> "From"
  | Tofrom -> "Tofrom"

let map_type_to_simple_string = function
  | Alloc  -> "alloc"
  | To     -> "to"
  | From   -> "from"
  | Tofrom -> "tofrom"

type dependence_type =
  | In
  | Out
  | Inout

let dependence_type_to_string = function
  | In    -> "In"
  | Out   -> "Out"
  | Inout -> "Inout"

let dependence_type_to_simple_string = function
  | In    -> "in"
  | Out   -> "out"
  | Inout -> "inout"

type t =
  | ERROR
  | If
  | Num_threads
  | Default of data_sharing_attr
  | DataSharingAttr of data_sharing_attr
  | Lastprivate
  | Copyin
  | Reduction
  | Schedule of kind
  | Collapse
  | Ordered
  | Copyprivate
  | Nowait
  | Final
  | Untied
  | Mergeable
(* 4.0 *)
  | Proc_bind of policy     
  | Linear of bool (* with step or not *)
  | Map of map_type option 
  | Safelen                
  | Simdlen                
  | Aligned of bool (* with alignment or not *)
  | Uniform                
  | Inbranch               
  | Notinbranch            
  | Depend of dependence_type
  | Device
  | Dist_schedule of kind
  | Initializer
  | Num_teams
  | Thread_limit

let to_string = function
  | ERROR             -> "ERROR"
  | If                -> "If"
  | Num_threads       -> "Num_threads"
  | Default a         -> "Default:"^(data_sharing_attr_to_string a)
  | DataSharingAttr a -> data_sharing_attr_to_string a
  | Lastprivate       -> "Lastprivate"
  | Copyin            -> "Copyin"
  | Reduction         -> "Reduction"
  | Schedule k        -> "Schedule:"^(kind_to_string k)
  | Collapse          -> "Collapse"
  | Ordered           -> "Ordered"
  | Copyprivate       -> "Copyprivate"
  | Nowait            -> "Nowait"
  | Final             -> "Final"
  | Untied            -> "Untied"
  | Mergeable         -> "Mergeable"
  | Proc_bind p       -> "Proc_bind:"^(policy_to_string p)
  | Linear b          -> Printf.sprintf "Linear:%B" b
  | Map t_opt         -> "Map"^(opt_to_string map_type_to_string ~prefix:":" t_opt)
  | Safelen           -> "Safelen"
  | Simdlen           -> "Simdlen"
  | Aligned b         -> Printf.sprintf "Aligned:%B" b
  | Uniform           -> "Uniform"
  | Inbranch          -> "Inbranch"
  | Notinbranch       -> "Notinbranch"
  | Depend t          -> "Depend:"^(dependence_type_to_string t)
  | Device            -> "Device"
  | Dist_schedule k   -> "Dist_schedule:"^(kind_to_string k)
  | Initializer       -> "Initializer"
  | Num_teams         -> "Num_teams"
  | Thread_limit      -> "Thread_limit"

let to_simple_string = function
  | ERROR             -> "<error>"
  | If                -> "if"
  | Num_threads       -> "num_threads"
  | Default a         -> "default("^(data_sharing_attr_to_simple_string a)^")"
  | DataSharingAttr a -> data_sharing_attr_to_simple_string a
  | Lastprivate       -> "lastprivate"
  | Copyin            -> "copyin"
  | Reduction         -> "reduction"
  | Schedule k        -> "schedule("^(kind_to_string k)^")"
  | Collapse          -> "collapse"
  | Ordered           -> "ordered"
  | Copyprivate       -> "copyprivate"
  | Nowait            -> "nowait"
  | Final             -> "final"
  | Untied            -> "untied"
  | Mergeable         -> "mergeable"
  | Proc_bind p       -> "proc_bind("^(policy_to_simple_string p)^")"
  | Linear b          -> "linear"^(if b then ":" else "")
  | Map t_opt         -> "map"^(opt_to_string map_type_to_simple_string ~prefix:"(" ~suffix:")" t_opt)
  | Safelen           -> "safelen"
  | Simdlen           -> "simdlen"
  | Aligned b         -> "aligned"^(if b then ":" else "")
  | Uniform           -> "uniform"
  | Inbranch          -> "inbranch"
  | Notinbranch       -> "notinbranch"
  | Depend t          -> "depend("^(dependence_type_to_simple_string t)^")"
  | Device            -> "device"
  | Dist_schedule k   -> "dist_schedule("^(kind_to_string k)^")"
  | Initializer       -> "initializer"
  | Num_teams         -> "num_teams"
  | Thread_limit      -> "thread_limit"

let to_tag = function
  | ERROR             -> "ERROR", []
  | If                -> "OmpIf", []
  | Num_threads       -> "OmpNum_threads", []
  | Default a         -> "OmpDefault", ["attr",data_sharing_attr_to_string a]
  | DataSharingAttr a -> data_sharing_attr_to_tag a
  | Lastprivate       -> "OmpLastprivate", []
  | Copyin            -> "OmpCopyin", []
  | Reduction         -> "OmpReduction", []
  | Schedule k        -> "OmpSchedule", ["kind",kind_to_string k]
  | Collapse          -> "OmpCollapse", []
  | Ordered           -> "OmpOrdered", []
  | Copyprivate       -> "OmpCopyprivate", []
  | Nowait            -> "OmpNowait", []
  | Final             -> "OmpFinal", []
  | Untied            -> "OmpUntied", []
  | Mergeable         -> "OmpMergeable", []
  | Proc_bind p       -> "OmpProc_bind", ["policy",policy_to_string p]
  | Linear b          -> "OmpLinear", ["step",string_of_bool b]
  | Map t_opt         -> "OmpMap", (opt_to_attr map_type_to_string "type" t_opt)
  | Safelen           -> "OmpSafelen", []
  | Simdlen           -> "OmpSimdlen", []
  | Aligned b         -> "OmpAligned", ["alignment",string_of_bool b]
  | Uniform           -> "OmpUniform", []
  | Inbranch          -> "OmpInbranch", []
  | Notinbranch       -> "OmpNotinbranch", []
  | Depend t          -> "OmpDepend", ["type",dependence_type_to_string t]
  | Device            -> "OmpDevice", []
  | Dist_schedule k   -> "OmpDist_schedule", ["kind",kind_to_string k]
  | Initializer       -> "OmpInitializer", []
  | Num_teams         -> "OmpNum_teams", []
  | Thread_limit      -> "OmpThread_limit", []

let anonymize = function
  | Default _         -> Default None_
  | Schedule _        -> Schedule Auto
  | Map _             -> Map None
  | Dist_schedule _   -> Dist_schedule Auto
  | Linear _          -> Linear false
  | Aligned _         -> Aligned false
  | l -> l
