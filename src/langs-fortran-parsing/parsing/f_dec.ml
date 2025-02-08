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

let level_to_string (i, j) = Printf.sprintf "%d:%d" i j

let level_list_to_string =
  Xlist.to_string level_to_string ","


module Directive = struct
  type t =
    | Alias of name * name
    | Assume
    | Assume_aligned
    | Attributes
    | Block_loop
    | Code_align of int
    | Declare
    | Define of name
    | DistributePoint
    | Else
    | Elseif
    | EndOptions
    | Endif
    | Fixedformlinesize of string
    | Fma
    | Forceinline of bool
    | Freeform
    | Ident of string
    | If
    | IfDefined of name
    | Init_dep_fwd
    | Inline of bool
    | Integer of string
    | Ivdep of string
    | LoopCount of int list
    | Message of string
    | Noblock_loop
    | Nodeclare
    | Nofma
    | Nofreeform
    | Nofusion
    | Noinline
    | Nooptimize
    | Noparallel
    | Noprefetch
    | Nostrict
    | Nounroll
    | Nounroll_and_jam
    | Novector
    | Objcomment of string
    | Optimize of string
    | Options of string list
    | Pack of string
    | Parallel
    | Prefetch
    | Psect of name
    | Real of string
    | Simd
    | Strict
    | Undefine of name
    | Unroll of int option
    | Unroll_and_jam of int option
    | Vector

  let to_string = function
    | Alias(i, e)          -> "Alias:"^i^":"^e
    | Assume               -> "Assume"
    | Assume_aligned       -> "Assume_aligned"
    | Attributes           -> "Attributes"
    | Block_loop           -> "Block_loop"
    | Noblock_loop         -> "Noblock_loop"
    | Code_align i         -> "Code_align:"^(string_of_int i)
    | Declare              -> "Declare"
    | Nodeclare            -> "Nodeclare"
    | Define n             -> "Define:"^n
    | Undefine n           -> "Undefine:"^n
    | DistributePoint      -> "DistributePoint"
    | Fixedformlinesize i  -> "Fixedformlinesize:"^i
    | Fma                  -> "Fma"
    | Nofma                -> "Nofma"
    | Freeform             -> "Freeform"
    | Nofreeform           -> "Nofreeform"
    | Ident s              -> "Ident:"^s
    | If                   -> "If"
    | IfDefined n          -> "IfDefined:"^n
    | Inline b             -> "Inline:"^(string_of_bool b)
    | Forceinline b        -> "Forceinline:"^(string_of_bool b)
    | Noinline             -> "Noinline"
    | Integer i            -> "Integer:"^i
    | Ivdep o              -> "Ivdep"^(if o = "" then "" else ":"^o)
    | Init_dep_fwd         -> "Init_dep_fwd"
    | LoopCount il         -> "LoopCount"^(int_list_to_string ~prefix:":" "," il)
    | Message s            -> "Message:"^s
    | Nofusion             -> "Nofusion"
    | Objcomment s         -> "Objcomment:"^s
    | Optimize i           -> "Optimize"^(if i = "" then "" else ":"^i)
    | Nooptimize           -> "Nooptimize"
    | Options ol           -> "Options:"^(string_list_to_string "" ol)
    | Pack i               -> "Pack"^(if i = "" then "" else ":"^i)
    | Parallel             -> "Parallel"
    | Noparallel           -> "Noparallel"
    | Prefetch             -> "Prefetch"
    | Noprefetch           -> "Noprefetch"
    | Psect n              -> "Psect:"^n
    | Real i               -> "Real:"^i
    | Simd                 -> "Simd"
    | Strict               -> "Strict"
    | Nostrict             -> "Nostrict"
    | Unroll i_opt         -> "Unroll"^(int_opt_to_string ~prefix:":" i_opt)
    | Nounroll             -> "Nounroll"
    | Unroll_and_jam i_opt -> "Unroll_and_jam"^(int_opt_to_string ~prefix:":" i_opt)
    | Nounroll_and_jam     -> "Nounroll_and_jam"
    | Vector               -> "Vector"
    | Novector             -> "Novector"

    | Elseif            -> "Elseif"
    | Else              -> "Else"
    | Endif             -> "Endif"
    | EndOptions        -> "EndOptions"

  let to_simple_string = function
    | Alias(i, e)          -> "ALIAS "^i^", "^e
    | Assume               -> "ASSUME"
    | Assume_aligned       -> "ASSUME_ALIGNED"
    | Attributes           -> "ATTRIBUTES"
    | Block_loop           -> "BLOCK_LOOP"
    | Noblock_loop         -> "NOBLOCK_LOOP"
    | Code_align i         -> "CODE_ALIGN:"^(string_of_int i)
    | Declare              -> "DECLARE"
    | Nodeclare            -> "NODECLARE"
    | Define n             -> "DEFINE "^n
    | Undefine n           -> "UNDEFINE "^n
    | DistributePoint      -> "DISTRIBUTE POINT"
    | Fixedformlinesize i  -> "FIXEDFORMLINESIZE:"^i
    | Fma                  -> "FMA"
    | Nofma                -> "NOFMA"
    | Freeform             -> "FREEFORM"
    | Nofreeform           -> "NOFREEFORM"
    | Ident s              -> "IDENT "^s
    | If                   -> "IF"
    | IfDefined n          -> "IF DEFINED "^n
    | Inline b             -> "INLINE"^(if b then " RECURSIVE" else "")
    | Forceinline b        -> "FORCEINLINE"^(if b then " RECURSIVE" else "")
    | Noinline             -> "NOINLINE"
    | Integer i            -> "INTEGER:"^i
    | Ivdep o              -> "IVDEP"^(if o = "" then "" else ":"^o)
    | Init_dep_fwd         -> "INIT_DEP_FWD"
    | LoopCount il         -> "LOOP COUNT"^(int_list_to_string ~prefix:"=" "," il)
    | Message s            -> "MESSAGE:"^s
    | Nofusion             -> "NOFUSION"
    | Objcomment s         -> "OBJCOMMENT LIB:"^s
    | Optimize i           -> "OPTIMIZE"^(if i = "" then "" else ":"^i)
    | Nooptimize           -> "NOOPTIMIZE"
    | Options ol           -> "OPTIONS "^(string_list_to_string "" ol)
    | Pack i               -> "PACK"^(if i = "" then "" else ":"^i)
    | Parallel             -> "PARALLEL"
    | Noparallel           -> "NOPARALLEL"
    | Prefetch             -> "PREFETCH"
    | Noprefetch           -> "NOPREFETCH"
    | Psect n              -> "PSECT /"^n^"/"
    | Real i               -> "REAL:"^i
    | Simd                 -> "SIMD"
    | Strict               -> "STRICT"
    | Nostrict             -> "NOSTRICT"
    | Unroll i_opt         -> "UNROLL"^(int_opt_to_string ~prefix:"=" i_opt)
    | Nounroll             -> "NOUNROLL"
    | Unroll_and_jam i_opt -> "UNROLL_AND_JAM"^(int_opt_to_string ~prefix:"=" i_opt)
    | Nounroll_and_jam     -> "NOUNROLL_AND_JAM"
    | Vector               -> "VECTOR"
    | Novector             -> "NOVECTOR"

    | Elseif            -> "ELSEIF"
    | Else              -> "ELSE"
    | Endif             -> "ENDIF"
    | EndOptions        -> "END OPTIONS"

  let to_tag = function
    | Alias(i, e)          -> "DecAlias", ["internal",i;"external",e]
    | Assume               -> "DecAssume", []
    | Assume_aligned       -> "DecAssume_aligned", []
    | Attributes           -> "DecAttributes", []
    | Block_loop           -> "DecBlock_loop", []
    | Noblock_loop         -> "DecNoblock_loop", []
    | Code_align i         -> "DecCode_align", ["value",string_of_int i]
    | Declare              -> "DecDeclare", []
    | Nodeclare            -> "DecNodeclare", []
    | Define n             -> "DecDefine", [name_attr_name,n]
    | Undefine n           -> "DecUndefine", [name_attr_name,n]
    | DistributePoint      -> "DecDistributePoint", []
    | Fixedformlinesize i  -> "DecFixedformlinesize", ["length",i]
    | Fma                  -> "DecFma", []
    | Nofma                -> "DecNofma", []
    | Freeform             -> "DecFreeform", []
    | Nofreeform           -> "DecNofreeform", []
    | Ident s              -> "DecIdent", ["ident",s]
    | If                   -> "DecIf", []
    | IfDefined n          -> "DecIfDefined", [name_attr_name,n]
    | Inline b             -> "DecInline", ["recursive", string_of_bool b]
    | Forceinline b        -> "DecForceinline", ["recursive", string_of_bool b]
    | Noinline             -> "DecNoinline", []
    | Integer i            -> "DecInteger", ["size",i]
    | Ivdep o              -> "DecIvdep", (if o = "" then [] else ["option",o])
    | Init_dep_fwd         -> "DecInit_dep_fwd", []
    | LoopCount il         -> "DecLoopCount", (list_to_attr string_of_int "count" il)
    | Message s            -> "DecMessage", ["message",s]
    | Nofusion             -> "DecNofusion", []
    | Objcomment s         -> "DecObjcomment", ["library",s]
    | Optimize i           -> "DecOptimize", (if i = "" then [] else ["level",i])
    | Nooptimize           -> "DecNooptimize", []
    | Options ol           -> "DecOptions", (list_to_attr (fun x -> x) "option" ol)
    | Pack i               -> "DecPack", (if i = "" then [] else ["align",i])
    | Parallel             -> "DecParallel", []
    | Noparallel           -> "DecNoparallel", []
    | Prefetch             -> "DecPrefetch", []
    | Noprefetch           -> "DecNoprefetch", []
    | Psect n              -> "DecPsect", [name_attr_name, n]
    | Real i               -> "DecReal", ["size",i]
    | Simd                 -> "DecSimd", []
    | Strict               -> "DecStrict", []
    | Nostrict             -> "DecNostrict", []
    | Unroll i_opt         -> "DecUnroll", (int_opt_to_attr "n" i_opt)
    | Nounroll             -> "DecNounroll", []
    | Unroll_and_jam i_opt -> "DecUnroll_and_jam", (int_opt_to_attr "n" i_opt)
    | Nounroll_and_jam     -> "DecNounroll_and_jam", []
    | Vector               -> "DecVector", []
    | Novector             -> "DecNovector", []

    | Elseif            -> "DecElseif", []
    | Else              -> "DecElse", []
    | Endif             -> "DecEndif", []
    | EndOptions        -> "DecEndOptions", []

  let get_name = function
    | Define n
    | Undefine n
    | IfDefined n
    | Psect n
      -> n
    | _ -> raise Not_found

  let get_name_opt = function
    | Define n
    | Undefine n
    | IfDefined n
    | Psect n
      -> Some n
    | _ -> None

  let is_specification_part = function
    | Alias _
    | Assume
    | Assume_aligned
    | Attributes
    | Declare
    | Nodeclare
    | Define _
    | Undefine _
    | Fixedformlinesize _
    | Fma
    | Nofma
    | Freeform
    | Nofreeform
    | Ident _
    | If
    | IfDefined _
    | Elseif
    | Else
    | Endif
    | EndOptions
    | Message _
    | Objcomment _
    | Optimize _
    | Nooptimize
    | Options _
    | Integer _
    | Pack _
    | Psect _
    | Real _
    | Strict
    | Nostrict
      -> true
    | _ -> false

  let is_execution_part = function
    | Alias _
    | Assume
    | Assume_aligned
    | Attributes
    | Block_loop
    | Noblock_loop
    | Code_align _
    | Declare
    | Nodeclare
    | Define _
    | Undefine _
    | DistributePoint
    | Fixedformlinesize _
    | Fma
    | Nofma
    (*| Freeform*)
    (*| Nofreeform*)
    (*| Ident _*)
    | If
    | IfDefined _
    | Elseif
    | Else
    | Endif
    | Inline _
    | Forceinline _
    | Noinline
    (*| Integer _*)
    | Ivdep _
    | Init_dep_fwd
    | LoopCount _
    | Message _
    | Nofusion
    (*| Objcomment _*)
    | Optimize _
    | Nooptimize
    (*| Options _*)
    (*| EndOptions*)
    (*| Pack _*)
    | Parallel
    | Noparallel
    | Prefetch
    | Noprefetch
    | Psect _
    (*| Real _*)
    | Simd
    | Strict
    | Nostrict
    | Unroll _
    | Nounroll
    | Unroll_and_jam _
    | Nounroll_and_jam
    | Vector
    | Novector
      -> true
    | _ -> false

  let anonymize = function
    | Alias(_, _)         -> Alias("", "")
    | Define _            -> Define ""
    | Undefine _          -> Undefine ""
    | Fixedformlinesize _ -> Fixedformlinesize ""
    | Ident _             -> Ident ""
    | IfDefined _         -> IfDefined ""
    | Inline _            -> Inline false
    | Forceinline _       -> Forceinline false
    | Integer _           -> Integer ""
    | Ivdep _             -> Ivdep ""
    | LoopCount _         -> LoopCount []
    | Message _           -> Message ""
    | Objcomment _        -> Objcomment ""
    | Optimize _          -> Optimize ""
    | Options _           -> Options []
    | Pack _              -> Pack ""
    | Psect _             -> Psect ""
    | Real _              -> Real ""
    | Unroll _            -> Unroll None
    | Unroll_and_jam _    -> Unroll_and_jam None
    | l -> l

end (* module Directive *)

module Clause = struct
  type t =
    | Always
    | Assert
    | Aligned
    | Unaligned
    | Temporal
    | Nontemporal
    | Vecremainder
    | Novecremainder
    | Noassert
    | Firstprivate
    | Lastprivate
    | Linear
    | Private
    | Reduction
    | Vectorlength of int list
    | Vectorlengthfor
    | Num_threads

    | Mask
    | Nomask
    | Processor of string
    | Uniform

    | Profitable
    | Cost

    | Factor
    | Level of (int * int) list

  let to_string = function
    | Always          -> "Always"
    | Assert          -> "Assert"
    | Aligned         -> "Aligned"
    | Unaligned       -> "Unaligned"
    | Temporal        -> "Temporal"
    | Nontemporal     -> "Nontemporal"
    | Vecremainder    -> "Vecremainder"
    | Novecremainder  -> "Novecremainder"
    | Noassert        -> "Noassert"
    | Firstprivate    -> "Firstprivate"
    | Lastprivate     -> "Lastprivate"
    | Linear          -> "Linear"
    | Private         -> "Private"
    | Reduction       -> "Reduction"
    | Vectorlength il -> "Vectorlength"^(int_list_to_string ~prefix:":" "," il)
    | Vectorlengthfor -> "Vectorlengthfor"
    | Num_threads     -> "Num_threads"

    | Mask            -> "Mask"
    | Nomask          -> "Nomask"
    | Processor p     -> "Processor:"^p
    | Uniform         -> "Uniform"

    | Profitable      -> "Profitable"
    | Cost            -> "Cost"

    | Factor          -> "Factor"
    | Level ll        -> "Level:"^(level_list_to_string ll)

  let to_simple_string = function
    | Always          -> "ALWAYS"
    | Assert          -> "ASSERT"
    | Aligned         -> "ALIGNED"
    | Unaligned       -> "UNALIGNED"
    | Temporal        -> "TEMPORAL"
    | Nontemporal     -> "NONTEMPORAL"
    | Vecremainder    -> "VECREMAINDER"
    | Novecremainder  -> "NOVECREMAINDER"
    | Noassert        -> "NOASSERT"
    | Firstprivate    -> "FIRSTPRIVATE"
    | Lastprivate     -> "LASTPRIVATE"
    | Linear          -> "LINEAR"
    | Private         -> "PRIVATE"
    | Reduction       -> "REDUCTION"
    | Vectorlength il -> "VECTORLENGTH ("^(int_list_to_string ~prefix:"" "," il)
    | Vectorlengthfor -> "VECTORLENGTHFOR"
    | Num_threads     -> "NUM_THREADS"

    | Mask            -> "MASK"
    | Nomask          -> "NOMASK"
    | Processor p     -> "PROCESSOR("^p^")"
    | Uniform         -> "UNIFORM"

    | Profitable      -> "PROFITABLE"
    | Cost            -> "COST"

    | Factor          -> "FACTOR"
    | Level ll        -> "LEVEL("^(level_list_to_string ll)^")"

  let to_tag = function
    | Always          -> "DecAlways", []
    | Assert          -> "DecAssert", []
    | Aligned         -> "DecAligned", []
    | Unaligned       -> "DecUnaligned", []
    | Temporal        -> "DecTemporal", []
    | Nontemporal     -> "DecNontemporal", []
    | Vecremainder    -> "DecVecremainder", []
    | Novecremainder  -> "DecNovecremainder", []
    | Noassert        -> "DecNoassert", []
    | Firstprivate    -> "DecFirstprivate", []
    | Lastprivate     -> "DecLastprivate", []
    | Linear          -> "DecLinear", []
    | Private         -> "DecPrivate", []
    | Reduction       -> "DecReduction", []
    | Vectorlength il -> "DecVectorlength", (list_to_attr string_of_int "length" il)
    | Vectorlengthfor -> "DecVectorlengthfor", []
    | Num_threads     -> "DecNum_threads", []

    | Mask            -> "DecMask", []
    | Nomask          -> "DecNomask", []
    | Processor p     -> "DecProcessor", ["processor",p]
    | Uniform         -> "DecUniform", []

    | Profitable      -> "DecProfitable", []
    | Cost            -> "DecCost", []

    | Factor          -> "Factor", []
    | Level ll        -> "Level", (list_to_attr level_to_string "level" ll)

  let anonymize = function
    | Vectorlength _ -> Vectorlength []
    | Processor _    -> Processor ""
    | Level _ -> Level []
    | l -> l

end (* module Clause *)

module Attribute = struct
  type t =
    | Alias of string
    | Align of int
    | Allocatable
    | Array_null
    | C
    | Code_align of int
    | Concurrency_safe
    | Cvf
    | Decorate
    | Default
    | Dllexport
    | Dllimport
    | Extern
    | Fastmem
    | Forceinline
    | Ignore_loc
    | Inline
    | Mixed_str_len_arg
    | No_arg_check
    | Noclone
    | Noinline
    | Offload of name
    | Optimization_parameter of string
    | Reference
    | Stdcall
    | Value
    | Varying
    | Vector

  let to_string = function
    | Alias s                  -> "Alias:"^s
    | Align i                  -> "Align:"^(string_of_int i)
    | Allocatable              -> "Allocatable"
    | Array_null               -> "Array_null"
    | C                        -> "C"
    | Code_align i             -> "Code_align:"^(string_of_int i)
    | Concurrency_safe         -> "Concurrency_safe"
    | Cvf                      -> "Cvf"
    | Decorate                 -> "Decorate"
    | Default                  -> "Default"
    | Dllexport                -> "Dllexport"
    | Dllimport                -> "Dllimport"
    | Extern                   -> "Extern"
    | Fastmem                  -> "Fastmem"
    | Forceinline              -> "Forceinline"
    | Ignore_loc               -> "Ignore_loc"
    | Inline                   -> "Inline"
    | Mixed_str_len_arg        -> "Mixed_str_len_arg"
    | No_arg_check             -> "No_arg_check"
    | Noclone                  -> "Noclone"
    | Noinline                 -> "Noinline"
    | Offload n                -> "Offload:"^n
    | Optimization_parameter s -> "Optimization_parameter:"^s
    | Reference                -> "Reference"
    | Stdcall                  -> "Stdcall"
    | Value                    -> "Value"
    | Varying                  -> "Varying"
    | Vector                   -> "Vector"

  let to_simple_string = function
    | Alias s                  -> "ALIAS:"^s
    | Align i                  -> "ALIGN:"^(string_of_int i)
    | Allocatable              -> "ALLOCATABLE"
    | Array_null               -> "ARRAY_NULL"
    | C                        -> "C"
    | Code_align i             -> "CODE_ALIGN:"^(string_of_int i)
    | Concurrency_safe         -> "CONCURRENCY_SAFE"
    | Cvf                      -> "CVF"
    | Decorate                 -> "DECORATE"
    | Default                  -> "DEFAULT"
    | Dllexport                -> "DLLEXPORT"
    | Dllimport                -> "DLLIMPORT"
    | Extern                   -> "EXTERN"
    | Fastmem                  -> "FASTMEM"
    | Forceinline              -> "FORCEINLINE"
    | Ignore_loc               -> "IGNORE_LOC"
    | Inline                   -> "INLINE"
    | Mixed_str_len_arg        -> "MIXED_STR_LEN_ARG"
    | No_arg_check             -> "NO_ARG_CHECK"
    | Noclone                  -> "NOCLONE"
    | Noinline                 -> "NOINLINE"
    | Offload n                -> "OFFLOAD:"^n
    | Optimization_parameter s -> "OPTIMIZATION_PARAMETER:"^s
    | Reference                -> "REFERENCE"
    | Stdcall                  -> "STDCALL"
    | Value                    -> "VALUE"
    | Varying                  -> "VARYING"
    | Vector                   -> "VECTOR"

  let to_tag = function
    | Alias s                  -> "DecAttributeAlias", [name_attr_name,s]
    | Align i                  -> "DecAttributeAlign", ["value",string_of_int i]
    | Allocatable              -> "DecAttributeAllocatable", []
    | Array_null               -> "DecAttributeArray_null", []
    | C                        -> "DecAttributeC", []
    | Code_align i             -> "DecAttributeCode_align", ["value",string_of_int i]
    | Concurrency_safe         -> "DecAttributeConcurrency_safe", []
    | Cvf                      -> "DecAttributeCvf", []
    | Decorate                 -> "DecAttributeDecorate", []
    | Default                  -> "DecAttributeDefault", []
    | Dllexport                -> "DecAttributeDllexport", []
    | Dllimport                -> "DecAttributeDllimport", []
    | Extern                   -> "DecAttributeExtern", []
    | Fastmem                  -> "DecAttributeFastmem", []
    | Forceinline              -> "DecAttributeForceinline", []
    | Ignore_loc               -> "DecAttributeIgnore_loc", []
    | Inline                   -> "DecAttributeInline", []
    | Mixed_str_len_arg        -> "DecAttributeMixed_str_len_arg", []
    | No_arg_check             -> "DecAttributeNo_arg_check", []
    | Noclone                  -> "DecAttributeNoclone", []
    | Noinline                 -> "DecAttributeNoinline", []
    | Offload n                -> "DecAttributeOffload", [name_attr_name,n]
    | Optimization_parameter s -> "DecAttributeOptimization_parameter", ["parameter",s]
    | Reference                -> "DecAttributeReference", []
    | Stdcall                  -> "DecAttributeStdcall", []
    | Value                    -> "DecAttributeValue", []
    | Varying                  -> "DecAttributeVarying", []
    | Vector                   -> "DecAttributeVector", []

  let get_name = function
    | Alias s   -> s
    | Offload n -> n
    | _ -> raise Not_found

  let get_name_opt = function
    | Alias s   -> Some s
    | Offload n -> Some n
    | _ -> None

  let anonymize = function
    | Alias _                  -> Alias ""
    | Align _                  -> Align 0
    | Code_align _             -> Code_align 0
    | Offload _                -> Offload ""
    | Optimization_parameter _ -> Optimization_parameter ""
    | l -> l

  let of_keyword kw =
    match String.lowercase_ascii kw with
    | "allocatable"            -> Allocatable
    | "array_null"             -> Array_null
    | "c"                      -> C
    | "concurrency_safe"       -> Concurrency_safe
    | "cvf"                    -> Cvf
    | "decorate"               -> Decorate
    | "default"                -> Default
    | "dllexport"              -> Dllexport
    | "dllimport"              -> Dllimport
    | "extern"                 -> Extern
    | "fastmem"                -> Fastmem
    | "forceinline"            -> Forceinline
    | "ignore_loc"             -> Ignore_loc
    | "mixed_str_len_arg"      -> Mixed_str_len_arg
    | "no_arg_check"           -> No_arg_check
    | "noclone"                -> Noclone
    | "reference"              -> Reference
    | "stdcall"                -> Stdcall
    | "value"                  -> Value
    | "varying"                -> Varying

    | _ -> failwith "F_dec.Attribute.of_keyword"

  let of_keyword_int kw _ =
    match String.lowercase_ascii kw with

    | _ -> failwith "F_dec.Attribute.of_keyword_int"

  let of_keyword_name kw n =
    match String.lowercase_ascii kw with
    | "offload"                -> Offload n

    | _ -> failwith "F_dec.Attribute.of_keyword_name"

  let of_keyword_string kw s =
    match String.lowercase_ascii kw with
    | "optimization_parameter" -> Optimization_parameter s

    | _ -> failwith "F_dec.Attribute.of_keyword_string"

end (* module Attribute *)

type t =
  | VarExpr
  | Align of string
  | Wrt
  | Nowrt
  | PrefetchHint
  | PrefetchHintAll
  | Max of int
  | Min of int
  | Avg of int

let to_string = function
  | VarExpr         -> "VarExpr"
  | Align s         -> "Align:"^s
  | Wrt             -> "Wrt"
  | Nowrt           -> "Nowrt"
  | PrefetchHint    -> "PrefetchHint"
  | PrefetchHintAll -> "PrefetchHintAll"
  | Max i           -> "Max:"^(string_of_int i)
  | Min i           -> "Min:"^(string_of_int i)
  | Avg i           -> "Avg:"^(string_of_int i)

let to_simple_string = function
  | VarExpr         -> "<var-expr>"
  | Align s         -> "ALIGN="^s
  | Wrt             -> "WRT"
  | Nowrt           -> "NOWRT"
  | PrefetchHint    -> "<prefetch-hint>"
  | PrefetchHintAll -> "<prefetch-hint-all>"
  | Max i           -> "MAX="^(string_of_int i)
  | Min i           -> "MIN="^(string_of_int i)
  | Avg i           -> "AVG="^(string_of_int i)

let to_tag = function
  | VarExpr         -> "DecVarExpr", []
  | Align s         -> "DecAlign", ["align",s]
  | Wrt             -> "DecWrt", []
  | Nowrt           -> "DecNowrt", []
  | PrefetchHint    -> "DecPrefetchHint", []
  | PrefetchHintAll -> "DecPrefetchHintAll", []
  | Max i           -> "DecMax", [value_attr_name, string_of_int i] 
  | Min i           -> "DecMin", [value_attr_name, string_of_int i] 
  | Avg i           -> "DecAvg", [value_attr_name, string_of_int i] 

let anonymize = function
  | Align _         -> Align ""
  | Max _           -> Max 0
  | Min _           -> Min 0
  | Avg _           -> Avg 0
  | l -> l
