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

module Xlist = Diffast_misc.Xlist

open Label_common

type num_or_name = NNnum of int | NNname of name

let num_or_name_to_string = function
  | NNnum i   -> string_of_int i
  | NNname n  -> n

type align = Aaligned | Aunaligned

let align_to_string = function
  | Aaligned   -> "ALIGNED"
  | Aunaligned -> "UNALIGNED"

type prefetch_spec = Pauto | Psoft

let prefetch_spec_to_string = function
  | Pauto -> "AUTO"
  | Psoft -> "SOFT"

type listv_scope =
  | Sall
  | Sthen
  | Selse

let listv_scope_to_string = function
  | Sall  -> "ALL"
  | Sthen -> "THEN"
  | Selse -> "ELSE"

type t =
  | ERROR

  | ArrayFusion
  | EndArrayFusion
  | ArrayMerge of name option * name list
  | ArraySubscript of name list
  | Eval 
  | Noeval
  | Fltld
  | Nofltld
  | FpRelaxed
  | NofpRelaxed
  | LoopInterchange of name list
  | LoopNointerchange
  | Mfunc of int option
  | Nomfunc
  | Noarraypad of name
  | LoopNofusion
  | Preex
  | Nopreex
  | Prefetch
  | Noprefetch
  | PrefetchCacheLevel of num_or_name
  | PrefetchInfer
  | PrefetchNoinfer
  | PrefetchIteration of int
  | PrefetchIterationL2 of int
  | PrefetchRead of num_or_name option * int option
  | PrefetchWrite of num_or_name option * int option
  | Striping of int option
  | Nostriping
  | Swp
  | Noswp
  | LoopBlocking of int
  | Unroll of int
  | UnrollFull

  | Nounroll
  | Novrec of name list
  | Simd of align option
  | Nosimd
  | CacheSectorSize of int list
  | EndCacheSectorSize
  | CacheSubsectorAssign of name list
  | EndCacheSubsector
  | FissionPoint of int option
  | LoopNofission
  | Xfill of int option
  | Noxfill
  | PrefetchSequential of prefetch_spec option
  | PrefetchStrong
  | PrefetchNostrong
  | PrefetchStrongL2
  | PrefetchNostrongL2
  | FpContract
  | NofpContract
  | LoopNoblocking
  | Norecurrence of name list
  | Uxsimd of align option
  | Nouxsimd

  | ArrayPrivate
  | NoarrayPrivate
  | Independent of name list
  | Noalias
  | Serial
  | Parallel
  | ParallelStrong
  | Reduction
  | Noreduction
  | Temp of name list
  | RelOp of F_intrinsic_operator.t

  | LoopPartParallel
  | LoopNopartParallel
  | LoopPartSimd
  | LoopNopartSimd
  | Shortloop of int
  | Noshortloop
  | SimdListv of listv_scope option
  | Unswitching
  | FirstPrivate of name list
  | LastPrivate of name list
  | TempPrivate of name list
  | ParallelCyclic of int option

let lv_opt_st_opt_to_string lv_opt st_opt =
  let lvstr =
    match lv_opt with
    | Some lv -> ":level="^(num_or_name_to_string lv)
    | None -> ""
  in
  let ststr =
    match st_opt with
    | Some st -> ":strong="^(string_of_int st)
    | None -> ""
  in
  lvstr^ststr


let lv_opt_st_opt_to_string_simple lv_opt st_opt =
  let mklvs lv = "level="^(num_or_name_to_string lv) in
  let mksts st = "strong="^(string_of_int st) in
  match lv_opt, st_opt with
  | Some lv, Some st -> Printf.sprintf "(%s,%s)" (mklvs lv) (mksts st)
  | Some lv, None    -> Printf.sprintf "(%s)" (mklvs lv)
  | None,    Some st -> Printf.sprintf "(%s)" (mksts st)
  | _ -> ""


let to_string = function
  | ERROR                            -> "ERROR"

  | ArrayFusion                      -> "ArrayFusion"
  | EndArrayFusion                   -> "EndArrayFusion"
  | ArrayMerge(n_opt, ns)            -> "ArrayMerge"^(string_opt_to_string ~prefix:":" n_opt)^":"^(Xlist.to_string (fun x -> x) ":" ns)
  | ArraySubscript ns                -> "ArraySubscirpt:"^(Xlist.to_string (fun x -> x) ":" ns)
  | Eval                             -> "Eval"
  | Noeval                           -> "Noeval"
  | Fltld                            -> "Fltld"
  | Nofltld                          -> "Nofltld"
  | FpRelaxed                        -> "FpRelaxed"
  | NofpRelaxed                      -> "NofpRelaxed"
  | LoopInterchange ns               -> "LoopInterchange:"^(Xlist.to_string (fun x -> x) ":" ns)
  | LoopNointerchange                -> "LoopNointerchange"
  | Mfunc i_opt                      -> "Mfunc"^(int_opt_to_string ~prefix:":" i_opt)
  | Nomfunc                          -> "Nomfunc"
  | Noarraypad n                     -> "Noarraypad:"^n
  | LoopNofusion                     -> "LoopNofusion"
  | Preex                            -> "Preex"
  | Nopreex                          -> "Nopreex"
  | Prefetch                         -> "Prefetch"
  | Noprefetch                       -> "Noprefetch"
  | PrefetchCacheLevel lv            -> "PrefetchCacheLevel:"^(num_or_name_to_string lv)
  | PrefetchInfer                    -> "PrefetchInfer"
  | PrefetchNoinfer                  -> "PrefetchNoinfer"
  | PrefetchIteration i              -> "PrefetchIteration:"^(string_of_int i)
  | PrefetchIterationL2 i            -> "PrefetchIterationL2:"^(string_of_int i)
  | PrefetchRead(lv_opt, st_opt)     -> "PrefetchRead:"^(lv_opt_st_opt_to_string lv_opt st_opt)
  | PrefetchWrite(lv_opt, st_opt)    -> "PrefetchWrite:"^(lv_opt_st_opt_to_string lv_opt st_opt)
  | Striping i_opt                   -> "Striping"^(int_opt_to_string ~prefix:":" i_opt)
  | Nostriping                       -> "Nostriping"
  | Swp                              -> "Swp"
  | Noswp                            -> "Noswp"
  | LoopBlocking i                   -> "LoopBlocking:"^(string_of_int i)
  | Unroll i                         -> "Unroll:"^(string_of_int i)
  | UnrollFull                       -> "UnrollFull"
  | Nounroll                         -> "Nounroll"
  | Novrec ns                        -> "Novrec:"^(Xlist.to_string (fun x -> x) ":" ns)
  | Simd a_opt                       -> "Simd"^(opt_to_string align_to_string ~prefix:":" a_opt)
  | Nosimd                           -> "Nosimd"
  | CacheSectorSize is               -> "CacheSectorSize:"^(Xlist.to_string string_of_int ":" is)
  | EndCacheSectorSize               -> "EndCacheSectorSize"
  | CacheSubsectorAssign ns          -> "CacheSubsectorAssign:"^(Xlist.to_string (fun x -> x) ":" ns)
  | EndCacheSubsector                -> "EndCacheSubsector"
  | FissionPoint i_opt               -> "FissionPoint"^(int_opt_to_string ~prefix:":" i_opt)
  | LoopNofission                    -> "LoopNofission"
  | Xfill i_opt                      -> "Xfill"^(int_opt_to_string ~prefix:":" i_opt)
  | Noxfill                          -> "Noxfill"
  | PrefetchSequential s_opt         -> "PrefetchSequential"^(opt_to_string prefetch_spec_to_string ~prefix:":" s_opt)
  | PrefetchStrong                   -> "PrefetchStrong"
  | PrefetchNostrong                 -> "PrefetchNostrong"
  | PrefetchStrongL2                 -> "PrefetchStrongL2"
  | PrefetchNostrongL2               -> "PrefetchNostrongL2"
  | FpContract                       -> "FpContract"
  | NofpContract                     -> "NofpContract"
  | LoopNoblocking                   -> "LoopNoblocking"
  | Norecurrence ns                  -> "Norecurrence:"^(Xlist.to_string (fun x -> x) ":" ns)
  | Uxsimd a_opt                     -> "Uxsimd:"^(opt_to_string align_to_string ~prefix:":" a_opt)
  | Nouxsimd                         -> "Nouxsimd"

  | ArrayPrivate                     -> "ArrayPrivate"
  | NoarrayPrivate                   -> "NoarrayPrivate"
  | Independent ns                   -> "Independent:"^(Xlist.to_string (fun x -> x) ":" ns)
  | Noalias                          -> "Noalias"
  | Serial                           -> "Serial"
  | Parallel                         -> "Parallel"
  | ParallelStrong                   -> "ParallelStrong"
  | Reduction                        -> "Reduction"
  | Noreduction                      -> "Noreduction"
  | Temp ns                          -> "Temp:"^(Xlist.to_string (fun x -> x) ":" ns)
  | RelOp op                         -> "RelOp."^(F_intrinsic_operator.to_string op)

  | LoopPartParallel                 -> "LoopPartParallel"
  | LoopNopartParallel               -> "LoopNopartParallel"
  | LoopPartSimd                     -> "LoopPartSimd"
  | LoopNopartSimd                   -> "LoopNopartSimd"
  | Shortloop i                      -> "Shortloop:"^(string_of_int i)
  | Noshortloop                      -> "Noshortloop"
  | SimdListv s_opt                  -> "SimdListv"^(opt_to_string listv_scope_to_string ~prefix:":" s_opt)
  | Unswitching                      -> "Unswitching"
  | FirstPrivate ns                  -> "FirstPrivate"^(Xlist.to_string (fun x -> x) ":" ns)
  | LastPrivate ns                   -> "LastPrivate"^(Xlist.to_string (fun x -> x) ":" ns)
  | TempPrivate ns                   -> "TempPrivate"^(Xlist.to_string (fun x -> x) ":" ns)
  | ParallelCyclic i_opt             -> "ParallelCyclic"^(int_opt_to_string ~prefix:":" i_opt)

let to_simple_string = function
  | ERROR                            -> "<error>"

  | ArrayFusion                      -> "!OCL ARRAY_FUSION"
  | EndArrayFusion                   -> "!OCL END_ARRAY_FUSION"
  | ArrayMerge(n_opt, ns)            -> "!OCL ARRAY_MERGE("^(string_opt_to_string ~suffix:":" n_opt)^(Xlist.to_string (fun x -> x) "," ns)^")"
  | ArraySubscript ns                -> "!OCL ARRAY_SUBSCRIPT("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | Eval                             -> "!OCL EVAL"
  | Noeval                           -> "!OCL NOEVAL"
  | Fltld                            -> "!OCL FLTLD"
  | Nofltld                          -> "!OCL NOFLTLD"
  | FpRelaxed                        -> "!OCL FP_RELAXED"
  | NofpRelaxed                      -> "!OCL NOFP_RELAXED"
  | LoopInterchange ns               -> "!OCL LOOP_INTERCHANGE("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | LoopNointerchange                -> "!OCL LOOP_NOINTERCHANGE"
  | Mfunc i_opt                      -> "!OCL MFUNC"^(int_opt_to_string ~prefix:"(" ~suffix:")" i_opt)
  | Nomfunc                          -> "!OCL NOMFUNC"
  | Noarraypad n                     -> "!OCL NOARRAYPAD("^n^")"
  | LoopNofusion                     -> "!OCL LOOP_NOFUSION"
  | Preex                            -> "!OCL PREEX"
  | Nopreex                          -> "!OCL NOPREEX"
  | Prefetch                         -> "!OCL PREFETCH"
  | Noprefetch                       -> "!OCL NOPREFETCH"
  | PrefetchCacheLevel lv            -> "!OCL PREFETCH_CACHE_LEVEL("^(num_or_name_to_string lv)^")"
  | PrefetchInfer                    -> "!OCL PREFETCH_INFER"
  | PrefetchNoinfer                  -> "!OCL PREFETCH_NOINFER"
  | PrefetchIteration i              -> "!OCL PREFETCH_ITERATION("^(string_of_int i)^")"
  | PrefetchIterationL2 i            -> "!OCL PREFETCH_ITERATION_L2("^(string_of_int i)^")"
  | PrefetchRead(lv_opt, st_opt)     -> "!OCL PREFETCH_READ"^(lv_opt_st_opt_to_string_simple lv_opt st_opt)
  | PrefetchWrite(lv_opt, st_opt)    -> "!OCL PREFETCH_WRITE"^(lv_opt_st_opt_to_string_simple lv_opt st_opt)
  | Striping i_opt                   -> "!OCL STRIPING"^(int_opt_to_string ~prefix:"(" ~suffix:")" i_opt)
  | Nostriping                       -> "!OCL NOSTRIPING"
  | Swp                              -> "!OCL SWP"
  | Noswp                            -> "!OCL NOSWP"
  | LoopBlocking i                   -> "!OCL LOOP_BLOCKING("^(string_of_int i)^")"
  | Unroll i                         -> "!OCL UNROLL("^(string_of_int i)^")"
  | UnrollFull                       -> "!OCL UNROLL_FULL"
  | Nounroll                         -> "!OCL NOUNROLL"
  | Novrec ns                        -> "!OCL NOVREC("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | Simd a_opt                       -> "!OCL SIMD"^(opt_to_string align_to_string ~prefix:"(" ~suffix:")" a_opt)
  | Nosimd                           -> "!OCL NOSIMD"
  | CacheSectorSize is               -> "!OCL CACHE_SECTOR_SIZE("^(Xlist.to_string string_of_int "," is)^")"
  | EndCacheSectorSize               -> "!OCL END_CACHE_SECTOR_SIZE"
  | CacheSubsectorAssign ns          -> "!OCL CACHE_SUBSECTOR_ASSIGN("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | EndCacheSubsector                -> "!OCL END_CACHE_SUBSECTOR"
  | FissionPoint i_opt               -> "!OCL FISSION_POINT"^(int_opt_to_string ~prefix:"(" ~suffix:")" i_opt)
  | LoopNofission                    -> "!OCL LOOP_NOFISSION"
  | Xfill i_opt                      -> "!OCL XFILL"^(int_opt_to_string ~prefix:"(" ~suffix:")" i_opt)
  | Noxfill                          -> "!OCL NOXFILL"
  | PrefetchSequential s_opt         -> "!OCL PREFETCH_SEQUENTIAL"^(opt_to_string prefetch_spec_to_string ~prefix:"(" ~suffix:")" s_opt)
  | PrefetchStrong                   -> "!OCL PREFETCH_STRONG"
  | PrefetchNostrong                 -> "!OCL PREFETCH_NOSTRONG"
  | PrefetchStrongL2                 -> "!OCL PREFETCH_STRONG_L2"
  | PrefetchNostrongL2               -> "!OCL PREFETCH_NOSTRONG_L2"
  | FpContract                       -> "!OCL FP_CONTRACT"
  | NofpContract                     -> "!OCL NOFP_CONTRACT"
  | LoopNoblocking                   -> "!OCL LOOP_NOBLOCKING"
  | Norecurrence ns                  -> "!OCL NORECURRENCE("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | Uxsimd a_opt                     -> "!OCL UXSIMD"^(opt_to_string align_to_string ~prefix:"(" ~suffix:")" a_opt)
  | Nouxsimd                         -> "!OCL NOUXSIMD"

  | ArrayPrivate                     -> "!OCL ARRAY_PRIVATE"
  | NoarrayPrivate                   -> "!OCL NOARRAY_PRIVATE"
  | Independent ns                   -> "!OCL INDEPENDENT("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | Noalias                          -> "!OCL NOALIAS"
  | Serial                           -> "!OCL SERIAL"
  | Parallel                         -> "!OCL PARALLEL"
  | ParallelStrong                   -> "!OCL PARALLEL_STRONG"
  | Reduction                        -> "!OCL REDUCTION"
  | Noreduction                      -> "!OCL NOREDUCTION"
  | Temp ns                          -> "!OCL TEMP("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | RelOp op                         -> "!OCL "^(F_intrinsic_operator.to_simple_string op)

  | LoopPartParallel                 -> "!OCL LOOP_PART_PARALLEL"
  | LoopNopartParallel               -> "!OCL LOOP_NOPART_PARALLEL"
  | LoopPartSimd                     -> "!OCL LOOP_PART_SIMD"
  | LoopNopartSimd                   -> "!OCL LOOP_NOPART_SIMD"
  | Shortloop i                      -> "!OCL SHORTLOOP("^(string_of_int i)^")"
  | Noshortloop                      -> "!OCL NOSHORTLOOP"
  | SimdListv s_opt                  -> "!OCL SIMD_LISTV"^(opt_to_string listv_scope_to_string ~prefix:"(" ~suffix:")" s_opt)
  | Unswitching                      -> "!OCL UNSWITCHING"
  | FirstPrivate ns                  -> "!OCL FIRST_PRIVATE("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | LastPrivate ns                   -> "!OCL LAST_PRIVATE("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | TempPrivate ns                   -> "!OCL TEMP_PRIVATE("^(Xlist.to_string (fun x -> x) "," ns)^")"
  | ParallelCyclic i_opt             -> "!OCL PARALLEL_CYCLIC"^(int_opt_to_string ~prefix:"(" ~suffix:")" i_opt)


let to_tag = function
  | ERROR                            -> "ERROR", []

  | ArrayFusion                      -> "OclArrayFusion", []
  | EndArrayFusion                   -> "OclEndArrayFusion", []
  | ArrayMerge(n_opt, ns)            -> "OclArrayMerge", (string_opt_to_attr "base" n_opt) @ (name_list_to_attr "array" ns)
  | ArraySubscript ns                -> "OclArraySubscirpt", (name_list_to_attr "array" ns)
  | Eval                             -> "OclEval", []
  | Noeval                           -> "OclNoeval", []
  | Fltld                            -> "OclFltld", []
  | Nofltld                          -> "OclNofltld", []
  | FpRelaxed                        -> "OclFpRelaxed", []
  | NofpRelaxed                      -> "OclNofpRelaxed", []
  | LoopInterchange ns               -> "OclLoopInterchange", (name_list_to_attr "var" ns)
  | LoopNointerchange                -> "OclLoopNointerchange", []
  | Mfunc i_opt                      -> "OclMfunc", (int_opt_to_attr "level" i_opt)
  | Nomfunc                          -> "OclNomfunc", []
  | Noarraypad n                     -> "OclNoarraypad", ["array",n]
  | LoopNofusion                     -> "OclLoopNofusion", []
  | Preex                            -> "OclPreex", []
  | Nopreex                          -> "OclNopreex", []
  | Prefetch                         -> "OclPrefetch", []
  | Noprefetch                       -> "OclNoprefetch", []
  | PrefetchCacheLevel lv            -> "OclPrefetchCacheLevel", ["level",num_or_name_to_string lv]
  | PrefetchInfer                    -> "OclPrefetchInfer", []
  | PrefetchNoinfer                  -> "OclPrefetchNoinfer", []
  | PrefetchIteration i              -> "OclPrefetchIteration", ["m",string_of_int i]
  | PrefetchIterationL2 i            -> "OclPrefetchIterationL2", ["m",string_of_int i]
  | PrefetchRead(lv_opt, st_opt)     -> "OclPrefetchRead", (opt_to_attr num_or_name_to_string "level" lv_opt) @ (int_opt_to_attr "strong" st_opt)
  | PrefetchWrite(lv_opt, st_opt)    -> "OclPrefetchWrite", (opt_to_attr num_or_name_to_string "level" lv_opt) @ (int_opt_to_attr "strong" st_opt)
  | Striping i_opt                   -> "OclStriping", (int_opt_to_attr "m" i_opt)
  | Nostriping                       -> "OclNostriping", []
  | Swp                              -> "OclSwp", []
  | Noswp                            -> "OclNoswp", []
  | LoopBlocking i                   -> "OclLoopBlocking", ["m",string_of_int i]
  | Unroll i                         -> "OclUnroll", ["m",string_of_int i]
  | UnrollFull                       -> "OclUnrollFull", []
  | Nounroll                         -> "OclNounroll", []
  | Novrec ns                        -> "OclNovrec", (name_list_to_attr "array" ns)
  | Simd a_opt                       -> "OclSimd", ["align",opt_to_string align_to_string a_opt]
  | Nosimd                           -> "OclNosimd", []
  | CacheSectorSize is               -> "OclCacheSectorSize", (int_list_to_attr "n" is)
  | EndCacheSectorSize               -> "OclEndCacheSectorSize", []
  | CacheSubsectorAssign ns          -> "OclCacheSubsectorAssign", (name_list_to_attr "array" ns)
  | EndCacheSubsector                -> "OclEndCacheSubsector", []
  | FissionPoint i_opt               -> "OclFissionPoint", (int_opt_to_attr "n" i_opt)
  | LoopNofission                    -> "OclLoopNofission", []
  | Xfill i_opt                      -> "OclXfill", (int_opt_to_attr "n" i_opt)
  | Noxfill                          -> "OclNoxfill", []
  | PrefetchSequential s_opt         -> "OclPrefetchSequential", (opt_to_attr prefetch_spec_to_string "arg" s_opt)
  | PrefetchStrong                   -> "OclPrefetchStrong", []
  | PrefetchNostrong                 -> "OclPrefetchNostrong", []
  | PrefetchStrongL2                 -> "OclPrefetchStrongL2", []
  | PrefetchNostrongL2               -> "OclPrefetchNostrongL2", []
  | FpContract                       -> "OclFpContract", []
  | NofpContract                     -> "OclNofpContract", []
  | LoopNoblocking                   -> "OclLoopNoblocking", []
  | Norecurrence ns                  -> "OclNorecurrence", (name_list_to_attr "array" ns)
  | Uxsimd a_opt                     -> "OclUxsimd", (opt_to_attr align_to_string "align" a_opt)
  | Nouxsimd                         -> "OclNouxsimd", []

  | ArrayPrivate                     -> "OclArrayPrivate", []
  | NoarrayPrivate                   -> "OclNoarrayPrivate", []
  | Independent ns                   -> "OclIndependent", (name_list_to_attr "e" ns)
  | Noalias                          -> "OclNoalias", []
  | Serial                           -> "OclSerial", []
  | Parallel                         -> "OclParallel", []
  | ParallelStrong                   -> "OclParallelStrong", []
  | Reduction                        -> "OclReduction", []
  | Noreduction                      -> "OclNoreduction", []
  | Temp ns                          -> "OclTemp", (name_list_to_attr "var" ns)
  | RelOp op                         -> "OclRelOp", ["op",F_intrinsic_operator.to_string op]

  | LoopPartParallel                 -> "LoopPartParallel", []
  | LoopNopartParallel               -> "LoopNopartParallel", []
  | LoopPartSimd                     -> "OclLoopPartSimd", []
  | LoopNopartSimd                   -> "OclLoopNopartSimd", []
  | Shortloop i                      -> "OclShortloop", ["n",string_of_int i]
  | Noshortloop                      -> "OclNoshortloop", []
  | SimdListv s_opt                  -> "OclSimdListv", (opt_to_attr listv_scope_to_string "scope" s_opt)
  | Unswitching                      -> "OclUnswitching", []
  | FirstPrivate ns                  -> "FirstPrivate", (name_list_to_attr "var" ns)
  | LastPrivate ns                   -> "LastPrivate", (name_list_to_attr "var" ns)
  | TempPrivate ns                   -> "TempPrivate", (name_list_to_attr "var" ns)
  | ParallelCyclic i_opt             -> "ParallelCyclic", (int_opt_to_attr "size" i_opt)

let get_names = function
  | ArrayMerge(n_opt, ns)   -> (opt_to_list n_opt) @ ns
  | ArraySubscript ns                
  | LoopInterchange ns     
  | Novrec ns               
  | CacheSubsectorAssign ns 
  | Norecurrence ns         
  | Independent ns          
  | Temp ns                 -> ns
  | Noarraypad n            -> [n]
  | _ -> raise Not_found

let get_names_opt = function
  | ArrayMerge(n_opt, ns)   -> Some ((opt_to_list n_opt) @ ns)
  | ArraySubscript ns                
  | LoopInterchange ns     
  | Novrec ns               
  | CacheSubsectorAssign ns 
  | Norecurrence ns         
  | Independent ns          
  | Temp ns                 -> Some ns
  | Noarraypad n            -> Some [n]                
  | _ -> None


exception Bad_ocl

let ocl_tuple_to_n_opt_names (nn_opt, nns) =
  let n_opt =
    match nn_opt with
    | Some (NNname n) -> Some n
    | _ -> None
  in
  n_opt, Xlist.filter_map (function NNname n -> Some n | _ -> None) nns

let ocl_tuple_to_names x = 
  let _, ns = ocl_tuple_to_n_opt_names x in
  ns

let ocl_tuple_to_name x = 
  let ns = ocl_tuple_to_names x in
  try
    List.hd ns
  with
    _ -> raise Bad_ocl

let ocl_tuple_opt_to_names t_opt = 
  match t_opt with
  | Some (nn_opt, nns) -> ocl_tuple_to_names (nn_opt, nns)
  | _ -> []


let ocl_tuple_to_nums (_, nns) =
  Xlist.filter_map (function NNnum i -> Some i | _ -> None) nns

let ocl_tuple_to_nn (_, nns) =
  match nns with
  | [] -> raise Bad_ocl
  | nn::_ -> nn

let ocl_tuple_to_num (nn_opt, nns) =
  let nums = ocl_tuple_to_nums (nn_opt, nns) in
  match nums with
  | [] -> raise Bad_ocl
  | i::_ -> i

let ocl_tuple_opt_to_num_opt t_opt = 
  try
    match t_opt with
    | Some (nn_opt, nns) -> Some (ocl_tuple_to_num (nn_opt, nns))
    | _ -> None
  with
    Bad_ocl -> None

let is_specification_part = function
  | ERROR

  | CacheSectorSize _
  | CacheSubsectorAssign _
  | EndCacheSectorSize
  | EndCacheSubsector
    -> true
  | _ -> false

let is_execution_part = function
  | ERROR

  | Noalias
  | ArrayFusion
  | EndArrayFusion
  | ArrayPrivate
  | NoarrayPrivate
  | CacheSectorSize _
  | EndCacheSectorSize
  | CacheSubsectorAssign _
  | EndCacheSubsector
  | Eval
  | Noeval
  | FirstPrivate _
  | LastPrivate _
  | FissionPoint _
  | Fltld
  | Nofltld
  | FpContract
  | NofpContract
  | FpRelaxed
  | NofpRelaxed
  | Independent _
  | LoopBlocking _
  | LoopNoblocking
  | LoopInterchange _
  | LoopNointerchange
  | LoopNofission
  | LoopNofusion
  | LoopPartParallel
  | LoopNopartParallel
  | LoopNopartSimd
  | LoopPartSimd
  | Mfunc _
  | Nomfunc
  | Novrec _
  | Norecurrence _
  | Parallel
  | ParallelCyclic _
  | ParallelStrong
  | Preex
  | Nopreex
  | Prefetch
  | Noprefetch
  | PrefetchCacheLevel _
  | PrefetchInfer
  | PrefetchNoinfer
  | PrefetchIteration _
  | PrefetchIterationL2 _
  | PrefetchRead _
  | PrefetchWrite _
  | PrefetchSequential _
  | PrefetchStrong
  | PrefetchNostrong
  | PrefetchStrongL2
  | PrefetchNostrongL2
  | Reduction
  | Noreduction
  | Serial
  | Shortloop _
  | Noshortloop
  | Simd _
  | Nosimd
  | SimdListv _
  | Striping _
  | Nostriping
  | Swp
  | Noswp
  | Temp _
  | TempPrivate _
  | Unroll _
  | Nounroll
  | UnrollFull
  | Unswitching
  | Uxsimd _
  | Xfill _
  | Noxfill
  | RelOp _
    -> true
  | _ -> false

let anonymize = function
  | Noarraypad _           -> Noarraypad ""
  | ArraySubscript _       -> ArraySubscript []
  | LoopInterchange _      -> LoopInterchange []
  | Novrec _               -> Novrec []
  | CacheSubsectorAssign _ -> CacheSubsectorAssign []
  | Norecurrence _         -> Norecurrence []
  | Independent _          -> Independent []
  | Temp _                 -> Temp []
  | PrefetchIteration _    -> PrefetchIteration 0
  | PrefetchIterationL2 _  -> PrefetchIterationL2 0
  | LoopBlocking _         -> LoopBlocking 0
  | Unroll _               -> Unroll 0
  | CacheSectorSize _      -> CacheSectorSize []
  | Mfunc _                -> Mfunc None
  | Striping _             -> Striping None
  | FissionPoint _         -> FissionPoint None
  | Xfill _                -> Xfill None
  | Simd _                 -> Simd None
  | Uxsimd _               -> Uxsimd None

  | ArrayMerge(_, _)     -> ArrayMerge(None, [])
  | PrefetchCacheLevel _ -> PrefetchCacheLevel (NNnum 0)
  | PrefetchRead(_, _)   -> PrefetchRead(None, None)
  | PrefetchWrite(_, _)  -> PrefetchWrite(None, None)
  | PrefetchSequential _ -> PrefetchSequential None

  | Shortloop _          -> Shortloop 0
  | SimdListv _          -> SimdListv None

  | FirstPrivate _       -> FirstPrivate []
  | LastPrivate _        -> LastPrivate []
  | TempPrivate _        -> TempPrivate []
  | ParallelCyclic _     -> ParallelCyclic None

  | l -> l

