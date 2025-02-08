(*
   Copyright 2012-2025 Codinuum Software Lab <https://codinuum.com>

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

open Common
open Label_common

type wirespec =
  | WS_NORMAL
  | WS_UNRESOLVED

let wirespec_to_string = function
  | WS_NORMAL     -> "NORMAL"
  | WS_UNRESOLVED -> "UNRESOLVED"

let wirespec_to_rep = function
  | WS_NORMAL     -> "wire"
  | WS_UNRESOLVED -> "uwire"

type gate =
  | BUFIF0
  | BUFIF1
  | CMOS
  | NMOS
  | PMOS
  | NOTIF0
  | NOTIF1
  | PULLDOWN
  | PULLUP
  | RCMOS
  | RNMOS
  | RPMOS
  | RTRAN
  | RTRANIF0
  | RTRANIF1
  | TRAN
  | TRANIF0
  | TRANIF1

let gate_to_string = function
  | BUFIF0       -> "BUFIF0"
  | BUFIF1       -> "BUFIF1"
  | CMOS         -> "CMOS"
  | NMOS         -> "NMOS"
  | PMOS         -> "PMOS"
  | NOTIF0       -> "NOTIF0"
  | NOTIF1       -> "NOTIF1"
  | RCMOS        -> "RCMOS"
  | RNMOS        -> "RNMOS"
  | RPMOS        -> "RPMOS"
  | PULLDOWN     -> "PULLDOWN"
  | PULLUP       -> "PULLUP"
  | RTRAN        -> "RTRAN"
  | RTRANIF0     -> "RTRANIF0"
  | RTRANIF1     -> "RTRANIF1"
  | TRAN         -> "TRAN"
  | TRANIF0      -> "TRANIF0"
  | TRANIF1      -> "TRANIF1"

let gate_to_rep = function
  | BUFIF0       -> "bufif0"
  | BUFIF1       -> "bufif1"
  | CMOS         -> "cmos"
  | NMOS         -> "nmos"
  | PMOS         -> "pmos"
  | NOTIF0       -> "notif0"
  | NOTIF1       -> "notif1"
  | RCMOS        -> "rcmos"
  | RNMOS        -> "rnmos"
  | RPMOS        -> "rpmos"
  | PULLDOWN     -> "pulldown"
  | PULLUP       -> "pullup"
  | RTRAN        -> "rtran"
  | RTRANIF0     -> "rtranif0"
  | RTRANIF1     -> "rtranif1"
  | TRAN         -> "tran"
  | TRANIF0      -> "tranif0"
  | TRANIF1      -> "tranif1"


module OverloadOperator = struct
  type t =
    | Add
    | Incr
    | Subt
    | Decr
    | Mult
    | Pow
    | Div
    | Mod
    | Eq
    | Neq
    | Lt
    | Le
    | Gt
    | Ge
    | Assign

  let to_string oo =
    let conv = function
      | Add    -> "Add"
      | Incr   -> "Incr"
      | Subt   -> "Subt"
      | Decr   -> "Decr"
      | Mult   -> "Mult"
      | Pow    -> "Pow"
      | Div    -> "Div"
      | Mod    -> "Mod"
      | Eq     -> "Eq"
      | Neq    -> "Neq"
      | Lt     -> "Lt"
      | Le     -> "Le"
      | Gt     -> "Gt"
      | Ge     -> "Ge"
      | Assign -> "Assign"
    in
    "OverloadOperator."^(conv oo)

  let to_simple_string = function
    | Add    -> "+"
    | Incr   -> "++"
    | Subt   -> "-"
    | Decr   -> "--"
    | Mult   -> "*"
    | Pow    -> "**"
    | Div    -> "/"
    | Mod    -> "%"
    | Eq     -> "=="
    | Neq    -> "!="
    | Lt     -> "<"
    | Le     -> "<="
    | Gt     -> ">"
    | Ge     -> ">="
    | Assign -> "="

  let to_tag oo =
    let tail = "OverloadOp" in
    let name =
      match oo with
      | Add    -> "Add"
      | Incr   -> "Incr"
      | Subt   -> "Subt"
      | Decr   -> "Decr"
      | Mult   -> "Mult"
      | Pow    -> "Pow"
      | Div    -> "Div"
      | Mod    -> "Mod"
      | Eq     -> "Eq"
      | Neq    -> "Neq"
      | Lt     -> "Lt"
      | Le     -> "Le"
      | Gt     -> "Gt"
      | Ge     -> "Ge"
      | Assign -> "Assign"
    in
    name^tail, []

  let to_tag_name oo =
    let n, _ = to_tag oo in
    n

end (* of module OverloadOperator *)


module AssignmentOperator = struct
  type t =
    | Eq
    | AddEq
    | SubtEq
    | MultEq
    | DivEq
    | ModEq
    | AndEq
    | OrEq
    | XorEq
    | ShiftLEq
    | ShiftREq
    | SShiftREq

  let to_string ao =
    let conv = function
      | Eq        -> "Eq"
      | AddEq     -> "AddEq"
      | SubtEq    -> "SubtEq"
      | MultEq    -> "MultEq"
      | DivEq     -> "DivEq"
      | ModEq     -> "ModEq"
      | AndEq     -> "AndEq"
      | OrEq      -> "OrEq"
      | XorEq     -> "XorEq"
      | ShiftLEq  -> "ShiftLEq"
      | ShiftREq  -> "ShiftREq"
      | SShiftREq -> "SShiftREq"
    in
    "AssignmentOperator."^(conv ao)

  let to_simple_string = function
    | Eq        -> "="
    | AddEq     -> "+="
    | SubtEq    -> "-="
    | MultEq    -> "*="
    | DivEq     -> "/="
    | ModEq     -> "%="
    | AndEq     -> "&="
    | OrEq      -> "|="
    | XorEq     -> "^="
    | ShiftLEq  -> "<<="
    | ShiftREq  -> ">>="
    | SShiftREq -> ">>>="

  let to_tag ao =
    let tail = "AssignOp" in
    let name =
      match ao with
      | Eq        -> "Eq"
      | AddEq     -> "AddEq"
      | SubtEq    -> "SubtEq"
      | MultEq    -> "MultEq"
      | DivEq     -> "DivEq"
      | ModEq     -> "ModEq"
      | AndEq     -> "AndEq"
      | OrEq      -> "OrEq"
      | XorEq     -> "XorEq"
      | ShiftLEq  -> "ShiftLEq"
      | ShiftREq  -> "ShiftREq"
      | SShiftREq -> "SShiftREq"
    in
    name^tail, []

  let to_tag_name ao =
    let n, _ = to_tag ao in
    n

end (* of module AssignmentOperator *)

module IncOrDecOperator = struct
  type t =
    | PreIncr
    | PreDecr
    | PostIncr
    | PostDecr

  let to_string ido =
    let conv = function
      | PreIncr  -> "PreIncr"
      | PreDecr  -> "PreDecr"
      | PostIncr -> "PostIncr"
      | PostDecr -> "PostDecr"
    in
    "IncOrDecOperator."^(conv ido)

  let to_simple_string = function
    | PreIncr  -> "++()"
    | PreDecr  -> "--()"
    | PostIncr -> "()++"
    | PostDecr -> "()--"

  let to_tag ido =
    let name =
      match ido with
      | PreIncr  -> "PreIncr"
      | PreDecr  -> "PreDecr"
      | PostIncr -> "PostIncr"
      | PostDecr -> "PostDecr"
    in
    name, []

  let to_tag_name ido =
    let n, _ = to_tag ido in
    n

end (* of module IncOrDecOperator *)

module UnaryOperator = struct
  type t =
    | Plus
    | Minus
    | Not
    | And
    | Neg
    | Or
    | Xor
    | Nand
    | Nor
    | Xnor
    | Inc
    | Dec

  let to_string uo =
    let conv = function
      | Plus  -> "Plus"
      | Minus -> "Minus"
      | Not   -> "Not"
      | And   -> "And"
      | Neg   -> "Neg"
      | Or    -> "Or"
      | Xor   -> "Xor"
      | Nand  -> "Nand"
      | Nor   -> "Nor"
      | Xnor  -> "Xnor"
      | Inc   -> "Inc"
      | Dec   -> "Dec"
    in
    "UnaryOperator."^(conv uo)

  let to_simple_string = function
    | Plus  -> "+"
    | Minus -> "-"
    | Not   -> "!"
    | And   -> "&"
    | Neg   -> "~"
    | Or    -> "|"
    | Xor   -> "^"
    | Nand  -> "~&"
    | Nor   -> "~|"
    | Xnor  -> "~^"
    | Inc   -> "++"
    | Dec   -> "--"

  let to_tag uo =
    let tail = "UnaryOp" in
    let name =
      match uo with
      | Plus  -> "Plus"
      | Minus -> "Minus"
      | Not   -> "Not"
      | And   -> "And"
      | Neg   -> "Neg"
      | Or    -> "Or"
      | Xor   -> "Xor"
      | Nand  -> "Nand"
      | Nor   -> "Nor"
      | Xnor  -> "Xnor"
      | Inc   -> "Inc"
      | Dec   -> "Dec"
    in
    name^tail, []

end (* of module UnaryOperator *)

module BinaryOperator = struct
  type t =
    | Add
    | Subt
    | Mult
    | Div
    | Mod
    | Eq
    | Neq
    | CaseEq
    | CaseNeq
    | WildEq
    | WildNeq
    | LogAnd
    | LogOr
    | Pow
    | Lt
    | Le
    | Gt
    | Ge
    | And
    | Or
    | Xor
    | Xnor
    | Nor
    | Nand
    | ShiftL
    | ShiftR
    | SShiftR
    | Constraint
    | LtMinusGt (* ? *)

  let to_string bo =
    let conv = function
      | Add        -> "Add"
      | Subt       -> "Subt"
      | Mult       -> "Mult"
      | Div        -> "Div"
      | Mod        -> "Mod"
      | Eq         -> "Eq"
      | Neq        -> "Neq"
      | CaseEq     -> "CaseEq"
      | CaseNeq    -> "CaseNeq"
      | WildEq     -> "WildEq"
      | WildNeq    -> "WildNeq"
      | LogAnd     -> "LogAnd"
      | LogOr      -> "LogOr"
      | Pow        -> "Pow"
      | Lt         -> "Lt"
      | Le         -> "Le"
      | Gt         -> "Gt"
      | Ge         -> "Ge"
      | And        -> "And"
      | Or         -> "Or"
      | Xor        -> "Xor"
      | Xnor       -> "Xnor"
      | Nor        -> "Nor"
      | Nand       -> "Nand"
      | ShiftL     -> "ShiftL"
      | ShiftR     -> "ShiftR"
      | SShiftR    -> "SShiftR"
      | Constraint -> "Constraint"
      | LtMinusGt  -> "LtMinusGt"
    in
    "BinaryOperator."^(conv bo)

  let to_simple_string = function
    | Add        -> "+"
    | Subt       -> "-"
    | Mult       -> "*"
    | Div        -> "/"
    | Mod        -> "%"
    | Eq         -> "=="
    | Neq        -> "!="
    | CaseEq     -> "==="
    | CaseNeq    -> "!=="
    | WildEq     -> "==?"
    | WildNeq    -> "!=?"
    | LogAnd     -> "&&"
    | LogOr      -> "||"
    | Pow        -> "**"
    | Lt         -> "<"
    | Le         -> "<="
    | Gt         -> ">"
    | Ge         -> ">="
    | And        -> "&"
    | Or         -> "|"
    | Xor        -> "^"
    | Xnor       -> "~^"
    | Nor        -> "~|"
    | Nand       -> "~&"
    | ShiftL     -> "<<"
    | ShiftR     -> ">>"
    | SShiftR    -> ">>>"
    | Constraint -> "->"
    | LtMinusGt  -> "<->"

  let to_tag bo =
    let tail = "BinaryOp" in
    let name =
      match bo with
      | Add        -> "Add"
      | Subt       -> "Subt"
      | Mult       -> "Mult"
      | Div        -> "Div"
      | Mod        -> "Mod"
      | Eq         -> "Eq"
      | Neq        -> "Neq"
      | CaseEq     -> "CaseEq"
      | CaseNeq    -> "CaseNeq"
      | WildEq     -> "WildEq"
      | WildNeq    -> "WildNeq"
      | LogAnd     -> "LogAnd"
      | LogOr      -> "LogOr"
      | Pow        -> "Pow"
      | Lt         -> "Lt"
      | Le         -> "Le"
      | Gt         -> "Gt"
      | Ge         -> "Ge"
      | And        -> "And"
      | Or         -> "Or"
      | Xor        -> "Xor"
      | Xnor       -> "Xnor"
      | Nor        -> "Nor"
      | Nand       -> "Nand"
      | ShiftL     -> "ShiftL"
      | ShiftR     -> "ShiftR"
      | SShiftR    -> "SShiftR"
      | Constraint -> "Constraint"
      | LtMinusGt  -> "LtMinusGt"
    in
    name^tail, []

end (* of module BinaryOperator *)

module TimingCheck = struct
  type t =
    | Setup
    | Hold
    | Recovery
    | Removal
    | Skew
    | Setuphold
    | Recrem
    | Timeskew
    | Fullskew
    | Period
    | Width
    | Nochange

    | Anonymous

  let to_string tc =
    let conv = function
      | Setup     -> "Setup"
      | Hold      -> "Hold"
      | Recovery  -> "Recovery"
      | Removal   -> "Removal"
      | Skew      -> "Skew"
      | Setuphold -> "SetupHold"
      | Recrem    -> "RecRem"
      | Timeskew  -> "TimeSkew"
      | Fullskew  -> "FullSkew"
      | Period    -> "Period"
      | Width     -> "Width"
      | Nochange  -> "NoChange"

      | Anonymous -> "<anonymous>"
    in
    "TimingCheck."^(conv tc)

  let to_simple_string = function
    | Setup     -> "$setup"
    | Hold      -> "$hold"
    | Recovery  -> "$recovery"
    | Removal   -> "$removal"
    | Skew      -> "$skew"
    | Setuphold -> "$setuphold"
    | Recrem    -> "$recrem"
    | Timeskew  -> "$timeskew"
    | Fullskew  -> "$fullskew"
    | Period    -> "$period"
    | Width     -> "$width"
    | Nochange  -> "$nochange"

    | Anonymous -> "<anonymous>"

  let get_name = to_simple_string

  let to_tag tc =
    let tail = "TimingCheck" in
    let name =
      match tc with
      | Setup     -> "Setup"
      | Hold      -> "Hold"
      | Recovery  -> "Recovery"
      | Removal   -> "Removal"
      | Skew      -> "Skew"
      | Setuphold -> "Setuphold"
      | Recrem    -> "Recrem"
      | Timeskew  -> "Timeskew"
      | Fullskew  -> "Fullskew"
      | Period    -> "Period"
      | Width     -> "Width"
      | Nochange  -> "Nochange"

      | Anonymous -> "Anonymous"
    in
    name^tail, []

end (* of module TimingCheck *)

module SystemTask = struct
  type t =
    | Error
    | Fatal
    | Info
    | Root
    | Unit
    | Warning

    | Anonymous

  let to_string st =
    let conv = function
      | Error   -> "Error"
      | Fatal   -> "Fatal"
      | Info    -> "Info"
      | Root    -> "Root"
      | Unit    -> "Unit"
      | Warning -> "Warning"
      | Anonymous -> "<anonymous>"
    in
    "SystemTask."^(conv st)

  let to_simple_string = function
    | Error   -> "$error"
    | Fatal   -> "$fatal"
    | Info    -> "$info"
    | Root    -> "$root"
    | Unit    -> "$unit"
    | Warning -> "$warning"
    | Anonymous -> "<anonymous>"

  let get_name = to_simple_string

  let to_tag st =
    let tail = "SystemTask" in
    let name =
      match st with
      | Error   -> "Error"
      | Fatal   -> "Fatal"
      | Info    -> "Info"
      | Root    -> "Root"
      | Unit    -> "Unit"
      | Warning -> "Warning"
      | Anonymous -> "Anonymous"
    in
    name^tail, []

  let to_id = function
    | Error  -> "$error"
    | Fatal   -> "$fatal"
    | Info    -> "$info"
    | Root    -> "$root"
    | Unit    -> "$unit"
    | Warning -> "$warning"
    | Anonymous -> "<anonymous>"

end (* of module SystemTask *)

module Qualifier = struct
  type t =
    | Protected
    | Local
    | Static
    | Virtual
    | PureVirtual
    | Rand
    | Randc
    | Automatic

  let to_string q =
    let conv = function
      | Protected   -> "Protected"
      | Local       -> "Local"
      | Static      -> "Static"
      | Virtual     -> "Virtual"
      | PureVirtual -> "PureVirtual"
      | Rand        -> "Rand"
      | Randc       -> "Randc"
      | Automatic   -> "Automatic"
    in
    "Qualifier."^(conv q)

  let to_simple_string = function
    | Protected   -> "protected"
    | Local       -> "local"
    | Static      -> "static"
    | Virtual     -> "virtual"
    | PureVirtual -> "pure virtual"
    | Rand        -> "rand"
    | Randc       -> "randc"
    | Automatic   -> "automatic"

  let to_tag q =
    let tail = "Qualifier" in
    let name =
      match q with
      | Protected   -> "Protected"
      | Local       -> "Local"
      | Static      -> "Static"
      | Virtual     -> "Virtual"
      | PureVirtual -> "PureVirtual"
      | Rand        -> "Rand"
      | Randc       -> "Randc"
      | Automatic   -> "Automatic"
    in
    name^tail, []

end (* of module Qualifier *)

module NetType = struct
  type t =
    | Supply0
    | Supply1
    | Tri
    | Tri0
    | Tri1
    | Triand
    | Trior
    | Trireg
    | Wand
    | Wire
    | Uwire
    | Wor

    | Anonymous

  let to_string nt =
    let conv = function
      | Supply0 -> "Supply0"
      | Supply1 -> "Supply1"
      | Tri     -> "Tri"
      | Tri0    -> "Tri0"
      | Tri1    -> "Tri1"
      | Triand  -> "Triand"
      | Trior   -> "Trior"
      | Trireg  -> "Trireg"
      | Wand    -> "Wand"
      | Wire    -> "Wire"
      | Uwire   -> "Wire"
      | Wor     -> "Wor"

      | Anonymous -> "<anonymous>"
    in
    "NetType."^(conv nt)

  let to_simple_string = function
    | Supply0 -> "supply0"
    | Supply1 -> "supply1"
    | Tri     -> "tri"
    | Tri0    -> "tri0"
    | Tri1    -> "tri1"
    | Triand  -> "triand"
    | Trior   -> "trior"
    | Trireg  -> "trireg"
    | Wand    -> "wand"
    | Wire    -> "wire"
    | Uwire   -> "uwire"
    | Wor     -> "wor"

    | Anonymous -> "<anonymous>"

  let to_tag nt =
    let tail = "NetType" in
    let name =
      match nt with
      | Supply0 -> "Supply0"
      | Supply1 -> "Supply1"
      | Tri     -> "Tri"
      | Tri0    -> "Tri0"
      | Tri1    -> "Tri1"
      | Triand  -> "Triand"
      | Trior   -> "Trior"
      | Trireg  -> "Trireg"
      | Wand    -> "Wand"
      | Wire    -> "Wire"
      | Uwire   -> "Uwire"
      | Wor     -> "Wor"

      | Anonymous -> "Anonymous"
    in
    name^tail, []

end (* of module NetType *)

module PortDirection = struct
  type t =
    | Input
    | Output
    | Inout
    | Ref
    | ConstRef

    | Anonymous

  let to_string pd =
    let conv = function
      | Input    -> "Input"
      | Output   -> "Output"
      | Inout    -> "Inout"
      | Ref      -> "Ref"
      | ConstRef -> "ConstRef"

      | Anonymous -> "<anonymous>"
    in
    "PortDirection."^(conv pd)

  let to_simple_string = function
    | Input    -> "input"
    | Output   -> "output"
    | Inout    -> "inout"
    | Ref      -> "ref"
    | ConstRef -> "const_ref"

    | Anonymous -> "<anonymous>"

  let to_tag pd =
    let tail = "PortDirection" in
    let name =
      match pd with
    | Input    -> "Input"
    | Output   -> "Output"
    | Inout    -> "Inout"
    | Ref      -> "Ref"
    | ConstRef -> "ConstRef"

    | Anonymous -> "Anonymous"
    in
    name^tail, []

end (* of module PortDirection *)

module Gate = struct
  type t =
    | Gate of gate
    | And
    | Buf
    | Nand
    | Nor
    | Not
    | Or
    | Xnor
    | Xor

    | Anonymous

  let to_string gate =
    let conv = function
    | Gate g -> "Gate:"^(gate_to_string g)
    | And  -> "And"
    | Buf  -> "Buf"
    | Nand -> "Nand"
    | Nor  -> "NOr"
    | Not  -> "not"
    | Or   -> "Or"
    | Xnor -> "XNOr"
    | Xor  -> "XOr"

    | Anonymous -> "<anonymous>"
    in
    "Gate."^(conv gate)

  let to_simple_string = function
    | Gate g -> gate_to_rep g
    | And  -> "and"
    | Buf  -> "buf"
    | Nand -> "nand"
    | Nor  -> "nor"
    | Not  -> "not"
    | Or   -> "or"
    | Xnor -> "xnor"
    | Xor  -> "xor"

    | Anonymous -> "<anonymous>"

  let gate_to_tag = function
    | BUFIF0       -> "Bufif0"
    | BUFIF1       -> "Bufif1"
    | CMOS         -> "Cmos"
    | NMOS         -> "Nmos"
    | PMOS         -> "Pmos"
    | NOTIF0       -> "Notif0"
    | NOTIF1       -> "Notif1"
    | RCMOS        -> "Rcmos"
    | RNMOS        -> "Rnmos"
    | RPMOS        -> "Rpmos"
    | PULLDOWN     -> "Pulldown"
    | PULLUP       -> "Pullup"
    | RTRAN        -> "Rtran"
    | RTRANIF0     -> "Rtranif0"
    | RTRANIF1     -> "Rtranif1"
    | TRAN         -> "Tran"
    | TRANIF0      -> "Tranif0"
    | TRANIF1      -> "Tranif1"

  let to_tag gate =
    let tail = "Gate" in
    let name =
      match gate with
    | Gate g -> gate_to_tag g
    | And  -> "And"
    | Buf  -> "Buf"
    | Nand -> "Nand"
    | Nor  -> "Nor"
    | Not  -> "Not"
    | Or   -> "Or"
    | Xnor -> "Xnor"
    | Xor  -> "Xor"

    | Anonymous -> "Anonymous"
    in
    name^tail, []

end (* of module Gate *)

module DataType = struct
  type t =
    | Byte
    | Shortint
    | Int
    | Longint
    | Integer
    | Time
    | Bit
    | Logic
    | Reg
    | Shortreal
    | Real
    | Realtime
    | Struct
    | Union
    | Enum
    | PsType of identifier
    | String
    | Chandle
    | Event
    | VirtualInterface of identifier
    | TypeReference
    | PsCovergroup of identifier
    | ClassScopeType of identifier
    | ClassType
    | Named of identifier
    | Implicit

  let to_string dt =
    let conv = function
    | Byte                -> "Byte"
    | Shortint            -> "Shortint"
    | Int                 -> "Int"
    | Longint             -> "Longint"
    | Integer             -> "Integer"
    | Time                -> "Time"
    | Bit                 -> "Bit"
    | Logic               -> "Logic"
    | Reg                 -> "Reg"
    | Shortreal           -> "Shortreal"
    | Real                -> "Real"
    | Realtime            -> "Realtime"
    | Struct              -> "Struct"
    | Union               -> "Union"
    | Enum                -> "Enum"
    | PsType id           -> "PsType:"^id
    | String              -> "String"
    | Chandle             -> "Chandle"
    | Event               -> "Event"
    | VirtualInterface id -> "VirtualInterface:"^id
    | TypeReference       -> "TypeReferenct"
    | PsCovergroup id     -> "PsCovergroup:"^id
    | ClassScopeType id   -> "ClassScopeType:"^id
    | ClassType           -> "ClassType"
    | Named id            -> "Named:"^id
    | Implicit            -> "Implicit"
    in
    "DataType."^(conv dt)

  let get_name = function
    | PsType id
    | VirtualInterface id
    | PsCovergroup id
    | ClassScopeType id
    | Named id            -> id
    | _                   -> raise Not_found

  let to_simple_string = function
    | Byte                -> "byte"
    | Shortint            -> "shortint"
    | Int                 -> "int"
    | Longint             -> "longint"
    | Integer             -> "integer"
    | Time                -> "time"
    | Bit                 -> "bit"
    | Logic               -> "logic"
    | Reg                 -> "reg"
    | Shortreal           -> "shortreal"
    | Real                -> "real"
    | Realtime            -> "realtime"
    | Struct              -> "struct"
    | Union               -> "union"
    | Enum                -> "enum"
    | PsType id           -> id
    | String              -> "string"
    | Chandle             -> "chandle"
    | Event               -> "event"
    | VirtualInterface id -> id
    | TypeReference       -> "<type_reference>"
    | PsCovergroup id     -> id
    | ClassScopeType id   -> id
    | ClassType           -> "<class_type>"
    | Named id            -> id
    | Implicit            -> "<implicit>"

  let to_tag dt =
    let tail = "DataType" in
    let name, attrs =
      match dt with
      | Byte                -> "Byte", []
      | Shortint            -> "Shortint", []
      | Int                 -> "Int", []
      | Longint             -> "Longint", []
      | Integer             -> "Integer", []
      | Time                -> "Time", []
      | Bit                 -> "Bit", []
      | Logic               -> "Logic", []
      | Reg                 -> "Reg", []
      | Shortreal           -> "Shortreal", []
      | Real                -> "Real", []
      | Realtime            -> "Realtime", []
      | Struct              -> "Struct", []
      | Union               -> "Union", []
      | Enum                -> "Enum", []
      | PsType id           -> "PsType", [ident_attr_name,id]
      | String              -> "String", []
      | Chandle             -> "Chandle", []
      | Event               -> "Event", []
      | VirtualInterface id -> "VirtualInterface", [ident_attr_name,id]
      | TypeReference       -> "TypeReference", []
      | PsCovergroup id     -> "PsCovergroup", [ident_attr_name,id]
      | ClassScopeType id   -> "ClassScopeType", [ident_attr_name,id]
      | ClassType           -> "ClassType", []
      | Named id            -> "Named", [ident_attr_name,id]
      | Implicit            -> "Implicit", []
    in
    name^tail, attrs

  let get_identifier = function
    | PsType id
    | VirtualInterface id
    | PsCovergroup id
    | ClassScopeType id
    | Named id -> id
    | _ -> raise Not_found

end (* of module DataType *)

module Expression = struct
  type t =
    | IntegralNumber of string
    | RealNumber of string
    | TimeNumber of string
    | Null
    | UOp of UnaryOperator.t
    | BOp of BinaryOperator.t
    | Cond
    | Paren
    | Tagged of identifier
    | Inside
    | Concat
    | EmptyQueue
    | Last
    | MinTypeMax
    | Cast
    | Constraint
    | ConstraintIf
    | ConstraintForeach
    | ConstraintSet
    | Stream
    | PreIncr
    | PreDecr
    | PostIncr
    | PostDecr
    | OperatorAssignment of AssignmentOperator.t
    | SystemFCall of identifier
    | SystemTCall of SystemTask.t
    | TfCall of identifier
    | MethodCall of identifier
    | ArrayMethodCallUnique
    | ArrayMethodCallAnd
    | ArrayMethodCallOr
    | ArrayMethodCallXor
    | CycleDelayConstRange
    | ConstantRange
    | ClassNew
    | ClassNewA

  let to_string e =
    let conv = function
      | IntegralNumber s      -> "IntegralNumber:"^s
      | RealNumber s          -> "RealNumber:"^s
      | TimeNumber s          -> "TimeNumber:"^s
      | Null                  -> "Null"
      | UOp uo                -> UnaryOperator.to_string uo
      | BOp bo                -> BinaryOperator.to_string bo
      | Cond                  -> "Cond"
      | Paren                 -> "Paren"
      | Tagged id             -> "Tagged:"^id
      | Inside                -> "Inside"
      | Concat                -> "Concat"
      | EmptyQueue            -> "EmptyQueue"
      | Last                  -> "Last"
      | MinTypeMax            -> "MinTypeMax"
      | Cast                  -> "Cast"
      | Constraint            -> "Constraint"
      | ConstraintIf          -> "ConstraintIf"
      | ConstraintForeach     -> "ConstraintForeach"
      | ConstraintSet         -> "ConstraintSet"
      | Stream                -> "Stream"
      | PreIncr               -> "PreIncr"
      | PreDecr               -> "PreDecr"
      | PostIncr              -> "PostIncr"
      | PostDecr              -> "PostDecr"
      | OperatorAssignment ao -> AssignmentOperator.to_string ao
      | SystemFCall id        -> "SystemFCall:"^id
      | SystemTCall st        -> SystemTask.to_string st
      | TfCall id             -> "TfCall:"^id
      | MethodCall id         -> "MethodCall:"^id
      | ArrayMethodCallUnique -> "ArrayMethodCallUnique"
      | ArrayMethodCallAnd    -> "ArrayMethodCallAnd"
      | ArrayMethodCallOr     -> "ArrayMethodCallOr"
      | ArrayMethodCallXor    -> "ArrayMethodCallXor"
      | CycleDelayConstRange  -> "CycleDelayConstRange"
      | ConstantRange         -> "ConstantRange"
      | ClassNew              -> "ClassNew"
      | ClassNewA             -> "ClassNewA"
    in
    "Expression."^(conv e)

  let to_simple_string = function
    | IntegralNumber s      -> s
    | RealNumber s          -> s
    | TimeNumber s          -> s
    | Null                  -> "null"
    | UOp uo                -> UnaryOperator.to_simple_string uo
    | BOp bo                -> BinaryOperator.to_simple_string bo
    | Cond                  -> "?:"
    | Paren                 -> "()"
    | Tagged id             -> "tagged:"^id
    | Inside                -> "inside"
    | Concat                -> "{{}}"
    | EmptyQueue            -> "{}"
    | Last                  -> "last"
    | MinTypeMax            -> "<min_type_max>"
    | Cast                  -> "cast"
    | Constraint            -> "->"
    | ConstraintIf          -> "if"
    | ConstraintForeach     -> "foreach"
    | ConstraintSet         -> "<constraint_set>"
    | Stream                -> "stream"
    | PreIncr               -> "++"
    | PreDecr               -> "--"
    | PostIncr              -> "++"
    | PostDecr              -> "--"
    | OperatorAssignment ao -> AssignmentOperator.to_simple_string ao
    | SystemFCall id        -> id
    | SystemTCall st        -> SystemTask.to_simple_string st
    | TfCall id             -> id
    | MethodCall id         -> "."^id
    | ArrayMethodCallUnique -> ".unique"
    | ArrayMethodCallAnd    -> ".and"
    | ArrayMethodCallOr     -> ".or"
    | ArrayMethodCallXor    -> ".xor"
    | CycleDelayConstRange  -> "<cycle_delay_const_range>"
    | ConstantRange         -> "<constant_range>"
    | ClassNew              -> "new"
    | ClassNewA             -> "new()"

  let get_name = function
    | Tagged id
    | SystemFCall id
    | TfCall id
    | MethodCall id         -> id
    | SystemTCall st        -> SystemTask.get_name st
    | _                     -> raise Not_found

  let get_value = function
    | IntegralNumber s
    | RealNumber s
    | TimeNumber s -> s
    | _ -> raise Not_found

  let to_tag e =
    let tail = "" in
    let name, attrs =
      match e with
      | IntegralNumber s      -> "IntegralNumber", [value_attr_name,XML.encode_string s]
      | RealNumber s          -> "RealNumber", [value_attr_name,XML.encode_string s]
      | TimeNumber s          -> "TimeNumber", [value_attr_name,XML.encode_string s]
      | Null                  -> "Null", []
      | UOp uo                -> UnaryOperator.to_tag uo
      | BOp bo                -> BinaryOperator.to_tag bo
      | Cond                  -> "Cond", []
      | Paren                 -> "Paren", []
      | Tagged id             -> "Tagged", [ident_attr_name,id]
      | Inside                -> "Inside", []
      | Concat                -> "Concat", []
      | EmptyQueue            -> "EmptyQueue", []
      | Last                  -> "Last", []
      | MinTypeMax            -> "MinTypeMax", []
      | Cast                  -> "Cast", []
      | Constraint            -> "Constraint", []
      | ConstraintIf          -> "ConstraintIf", []
      | ConstraintForeach     -> "ConstraintForeach", []
      | ConstraintSet         -> "ConstraintSet", []
      | Stream                -> "Stream", []
      | PreIncr               -> "PreIncr", []
      | PreDecr               -> "PreDecr", []
      | PostIncr              -> "PostIncr", []
      | PostDecr              -> "PostDecr", []
      | OperatorAssignment ao -> AssignmentOperator.to_tag ao
      | SystemFCall id        -> "System_f_call:", [ident_attr_name,id]
      | SystemTCall st        -> SystemTask.to_tag st
      | TfCall id             -> "TfCall", [ident_attr_name,id]
      | MethodCall id         -> "MethodCall", [ident_attr_name,id]
      | ArrayMethodCallUnique -> "ArrayMethodCallUnique", []
      | ArrayMethodCallAnd    -> "ArrayMethodCallAnd", []
      | ArrayMethodCallOr     -> "AarrayMethodCallOr", []
      | ArrayMethodCallXor    -> "ArrayMethodCallXor", []
      | CycleDelayConstRange  -> "CycleDelayConstRange", []
      | ConstantRange         -> "ConstantRange", []
      | ClassNew              -> "ClassNew", []
      | ClassNewA             -> "ClassNewA", []
    in
    name^tail, attrs

  let get_identifier = function
    | Tagged id
    | SystemFCall id
    | TfCall id
    | MethodCall id -> id
    | SystemTCall st -> SystemTask.to_id st
    | _ -> raise Not_found

end (* of module Expression *)

module EventExpression = struct
  type t =
    | Posedge
    | Negedge
    | Edge
    | Iff
    | Or
    | Multi

  let to_string ee =
    let conv = function
      | Posedge -> "Posedge"
      | Negedge -> "Negedge"
      | Edge    -> "Edge"
      | Iff     -> "Iff"
      | Or      -> "Or"
      | Multi   -> "Multi"
    in
    "EventExpression."^(conv ee)

  let to_simple_string = function
    | Posedge -> "posedge"
    | Negedge -> "negedge"
    | Edge    -> "edge"
    | Iff     -> "iff"
    | Or      -> "or"
    | Multi   -> "<multi>"

  let to_tag ee =
    let tail = "EventExpr" in
    let name =
      match ee with
      | Posedge -> "Posedge"
      | Negedge -> "Negedge"
      | Edge    -> "Edge"
      | Iff     -> "Iff"
      | Or      -> "Or"
      | Multi   -> "Multi"
    in
    name^tail, []

  let get_identifier = function
    | _ -> raise Not_found

end (* of module EventExpression *)

module PropertyExpression = struct
  type t =
    | Not
    | Strong
    | Weak
    | ImplicationOverlapped
    | ImplicationNonOverlapped
    | SharpMinusSharp
    | SharpEqSharp
    | Nexttime
    | S_nexttime
    | Always
    | S_always
    | Eventually
    | S_eventually
    | Until
    | S_until
    | Until_with
    | S_until_with
    | Implies
    | Iff
    | Accept_on
    | Sync_accept_on
    | Reject_on
    | Sync_reject_on
    | If
    | Case
    | Spec

  let to_string pe =
    let conv = function
      | Not                      -> "Not"
      | Strong                   -> "Strong"
      | Weak                     -> "Weak"
      | ImplicationOverlapped    -> "ImplicationOverlapped"
      | ImplicationNonOverlapped -> "ImplicationNonOverlapped"
      | SharpMinusSharp          -> "SharpMinusSharp"
      | SharpEqSharp             -> "SharpEqSharp"
      | Nexttime                 -> "Nexttime"
      | S_nexttime               -> "S_nexttime"
      | Always                   -> "Always"
      | S_always                 -> "S_always"
      | Eventually               -> "Eventually"
      | S_eventually             -> "S_eventually"
      | Until                    -> "Until"
      | S_until                  -> "S_until"
      | Until_with               -> "Until_with"
      | S_until_with             -> "S_UntilWith"
      | Implies                  -> "Implies"
      | Iff                      -> "Iff"
      | Accept_on                -> "Accept_on"
      | Sync_accept_on           -> "Sync_accept_on"
      | Reject_on                -> "Reject_on"
      | Sync_reject_on           -> "Sync_reject_on"
      | If                       -> "If"
      | Case                     -> "Case"
      | Spec                     -> "Spec"
    in
    "PropertyExpression."^(conv pe)

  let to_simple_string = function
    | Not                      -> "not"
    | Strong                   -> "strong"
    | Weak                     -> "weak"
    | ImplicationOverlapped    -> "|->"
    | ImplicationNonOverlapped -> "|=>"
    | SharpMinusSharp          -> "#-#"
    | SharpEqSharp             -> "#=#"
    | Nexttime                 -> "nexttime"
    | S_nexttime               -> "s_nexttime"
    | Always                   -> "always"
    | S_always                 -> "s_always"
    | Eventually               -> "eventually"
    | S_eventually             -> "s_eventually"
    | Until                    -> "until"
    | S_until                  -> "s_until"
    | Until_with               -> "until_with"
    | S_until_with             -> "s_until_with"
    | Implies                  -> "implies"
    | Iff                      -> "iff"
    | Accept_on                -> "accept_on"
    | Sync_accept_on           -> "sync_accept_on"
    | Reject_on                -> "reject_on"
    | Sync_reject_on           -> "sync_reject_on"
    | If                       -> "if"
    | Case                     -> "case"
    | Spec                     -> "<spec>"

  let to_tag pe =
    let tail = "PropertyExpr" in
    let name =
      match pe with
      | Not                      -> "Not"
      | Strong                   -> "Strong"
      | Weak                     -> "Weak"
      | ImplicationOverlapped    -> "ImplicationOverlapped"
      | ImplicationNonOverlapped -> "ImplicationNonOverlapped"
      | SharpMinusSharp          -> "SharpMinusSharp"
      | SharpEqSharp             -> "SharpEqSharp"
      | Nexttime                 -> "Nexttime"
      | S_nexttime               -> "S_nexttime"
      | Always                   -> "Always"
      | S_always                 -> "S_always"
      | Eventually               -> "Eventually"
      | S_eventually             -> "S_eventually"
      | Until                    -> "Until"
      | S_until                  -> "S_until"
      | Until_with               -> "Until_with"
      | S_until_with             -> "S_until_with"
      | Implies                  -> "Implies"
      | Iff                      -> "Iff"
      | Accept_on                -> "Accept_on"
      | Sync_accept_on           -> "Sync_accept_on"
      | Reject_on                -> "Reject_on"
      | Sync_reject_on           -> "Sync_reject_on"
      | If                       -> "If"
      | Case                     -> "Case"
      | Spec                     -> "Spec"
    in
    name^tail, []

  let get_identifier = function
    | _ -> raise Not_found

end (* of module PropertyExpression *)

module SequenceExpression = struct
  type t =
    | Concat
    | Repetition
    | OnMatch
    | And
    | Or
    | Intersect
    | First_match
    | Throughout
    | Within
    | Clocking

  let to_string se =
    let conv = function
      | Concat     -> "Concat"
      | Repetition -> "Repetition"
      | OnMatch   -> "OnMatch"
      | And        -> "And"
      | Or         -> "Or"
      | Intersect  -> "Intersect"
      | First_match -> "First_match"
      | Throughout -> "Throughout"
      | Within     -> "Within"
      | Clocking   -> "Clocking"
    in
    "SequenceExpression."^(conv se)

  let to_simple_string = function
    | Concat     -> "<concat>"
    | Repetition -> "<repetition>"
    | OnMatch    -> "<on_match>"
    | And        -> "and"
    | Or         -> "or"
    | Intersect  -> "intersect"
    | First_match -> "first_match"
    | Throughout -> "throughout"
    | Within     -> "within"
    | Clocking   -> "clocking"

  let to_tag se =
    let tail = "SequenceExpr" in
    let name =
      match se with
      | Concat      -> "Concat"
      | Repetition  -> "Repetition"
      | OnMatch    -> "OnMatch"
      | And         -> "And"
      | Or          -> "Or"
      | Intersect   -> "Intersect"
      | First_match -> "First_match"
      | Throughout  -> "Throughout"
      | Within      -> "Within"
      | Clocking    -> "Clocking"
    in
    name^tail, []

  let get_identifier = function
    | _ -> raise Not_found

end (* of module SequenceExpression *)

module JoinSpec = struct
type t =
  | NORMAL
  | ANY
  | NONE

let to_string = function
  | NORMAL -> "NORMAL"
  | ANY    -> "ANY"
  | NONE   -> "NONE"

let to_rep = function
  | NORMAL -> "join"
  | ANY    -> "join_any"
  | NONE   -> "join_none"

end

module Statement = struct
  type t =
    | Empty
    | OperatorAssignment of AssignmentOperator.t
    | Labeled of identifier
    | BlockingAssignment
    | NonBlockingAssignment
    | Assign
    | Deassign
    | Force
    | Release
    | Case
    | Casex
    | Casez
    | Conditional
    | IncOrDec
    | SubroutineCall
    | SubroutineCallVoid
    | Disable
    | DisableFork
    | EventTrigger
    | EventTriggerNonBlocking
    | Forever
    | Repeat
    | While
    | For
    | Do
    | Foreach
    | Return
    | Break
    | Continue
    | ParBlock of identifier * JoinSpec.t
    | ProceduralTimingControl
    | SeqBlock of identifier
    | Wait
    | WaitFork
    | WaitOrder
    | ProceduralAssertion
    | ClockingDrive
    | Randsequence of identifier
    | Randcase
    | ExpectProperty
    | Expr of Expression.t
    | PExpr of PropertyExpression.t

  let to_string stmt =
    let conv = function
    | Empty                   -> "Empty"
    | OperatorAssignment ao   -> AssignmentOperator.to_string ao
    | Labeled id              -> "Labeled:"^id
    | BlockingAssignment      -> "BlockingAssignment"
    | NonBlockingAssignment   -> "NonBlockingAssignment"
    | Assign                  -> "Assign"
    | Deassign                -> "Deassign"
    | Force                   -> "Force"
    | Release                 -> "Release"
    | Case                    -> "Case"
    | Casex                   -> "Casex"
    | Casez                   -> "Casez"
    | Conditional             -> "Conditional"
    | IncOrDec                -> "IncOrDec"
    | SubroutineCall          -> "SubroutineCall"
    | SubroutineCallVoid      -> "SubroutineCallVoid"
    | Disable                 -> "Disable"
    | DisableFork             -> "DisableFork"
    | EventTrigger            -> "EventTrigger"
    | EventTriggerNonBlocking -> "EventTriggerNonBlocking"
    | Forever                 -> "Forever"
    | Repeat                  -> "Repeat"
    | While                   -> "While"
    | For                     -> "For"
    | Do                      -> "Do"
    | Foreach                 -> "Foreach"
    | Return                  -> "Return"
    | Break                   -> "Break"
    | Continue                -> "Continue"
    | ParBlock(id, js)        -> "ParBlock:"^id^":"^(JoinSpec.to_string js)
    | ProceduralTimingControl -> "ProceduralTimingControl"
    | SeqBlock id             -> "SeqBlock:"^id
    | Wait                    -> "Wait"
    | WaitFork                -> "WaitFork"
    | WaitOrder               -> "WaitOrder"
    | ProceduralAssertion     -> "ProceduralAssertion"
    | ClockingDrive           -> "ClockingDrive"
    | Randsequence id         -> "Randsequence:"^id
    | Randcase                -> "Randcase"
    | ExpectProperty          -> "ExpectProperty"
    | Expr e                  -> Expression.to_string e
    | PExpr pe                -> PropertyExpression.to_string pe
    in
    "Statement."^(conv stmt)

  let get_name = function
    | Labeled id
    | ParBlock(id, _)
    | SeqBlock id
    | Randsequence id         -> id
    | Expr e                  -> Expression.get_name e
    | _                       -> raise Not_found

  let to_simple_string = function
    | Empty                   -> ";"
    | OperatorAssignment ao   -> AssignmentOperator.to_simple_string ao
    | Labeled id              -> id^":"
    | BlockingAssignment      -> "="
    | NonBlockingAssignment   -> "<="
    | Assign                  -> "assign"
    | Deassign                -> "deassign"
    | Force                   -> "force"
    | Release                 -> "release"
    | Case                    -> "case"
    | Casex                   -> "casex"
    | Casez                   -> "casez"
    | Conditional             -> "if"
    | IncOrDec                -> "<inc_or_dec>"
    | SubroutineCall          -> "<subroutine_call>"
    | SubroutineCallVoid      -> "<subroutine_call_void>"
    | Disable                 -> "disable"
    | DisableFork             -> "disable_fork"
    | EventTrigger            -> "->"
    | EventTriggerNonBlocking -> "->>"
    | Forever                 -> "forever"
    | Repeat                  -> "repeat"
    | While                   -> "while"
    | For                     -> "for"
    | Do                      -> "do"
    | Foreach                 -> "foreach"
    | Return                  -> "return"
    | Break                   -> "break"
    | Continue                -> "continue"
    | ParBlock(id, js)        -> "<par_block:"^id^":"^(JoinSpec.to_rep js)^">"
    | ProceduralTimingControl -> "<procedural_timing_control>"
    | SeqBlock id             -> "<seq_block:"^id^">"
    | Wait                    -> "wait"
    | WaitFork                -> "wait_fork"
    | WaitOrder               -> "wait_order"
    | ProceduralAssertion     -> "<procedural_assertion>"
    | ClockingDrive           -> "<clocking_drive>"
    | Randsequence id         -> "randsequence("^id^")"
    | Randcase                -> "randcase"
    | ExpectProperty          -> "expect"
    | Expr e                  -> Expression.to_simple_string e
    | PExpr pe                -> PropertyExpression.to_simple_string pe

  let to_tag stmt =
    let tail = "Stmt" in
    let name, attrs =
      match stmt with
      | Empty                   -> "Empty", []
      | OperatorAssignment ao   -> AssignmentOperator.to_tag ao
      | Labeled id              -> "Labeled", [label_attr_name,id]
      | BlockingAssignment      -> "BlockingAssignment", []
      | NonBlockingAssignment   -> "NonBlockingAssignment", []
      | Assign                  -> "Assign", []
      | Deassign                -> "Deassign", []
      | Force                   -> "Force", []
      | Release                 -> "Release", []
      | Case                    -> "Case", []
      | Casex                   -> "Casex", []
      | Casez                   -> "Casez", []
      | Conditional             -> "If", []
      | IncOrDec                -> "IncOrDec", []
      | SubroutineCall          -> "SubroutineCall", []
      | SubroutineCallVoid      -> "SubroutineCallVoid", []
      | Disable                 -> "Disable", []
      | DisableFork             -> "DisableFork", []
      | EventTrigger            -> "EventTrigger", []
      | EventTriggerNonBlocking -> "EventTriggerNonBlocking", []
      | Forever                 -> "Forever", []
      | Repeat                  -> "Repeat", []
      | While                   -> "While", []
      | For                     -> "For", []
      | Do                      -> "Do", []
      | Foreach                 -> "Foreach", []
      | Return                  -> "Return", []
      | Break                   -> "Break", []
      | Continue                -> "Continue", []
      | ParBlock(id, js)        -> "ParBlock", [ident_attr_name,id;"joinspec",JoinSpec.to_rep js]
      | ProceduralTimingControl -> "ProceduralTimingControl", []
      | SeqBlock id             -> "SeqBlock", [ident_attr_name,id]
      | Wait                    -> "Wait", []
      | WaitFork                -> "WaitFork", []
      | WaitOrder               -> "WaitOrder", []
      | ProceduralAssertion     -> "ProceduralAssertion", []
      | ClockingDrive           -> "ClockingDrive", []
      | Randsequence id         -> "Randsequence", [ident_attr_name,id]
      | Randcase                -> "Randcase", []
      | ExpectProperty          -> "ExpectProperty", []
      | Expr e                  -> Expression.to_tag e
      | PExpr pe                -> PropertyExpression.to_tag pe
    in
    name^tail, attrs

  let get_identifier = function
    | Labeled id
    | ParBlock(id, _)
    | SeqBlock id
    | Randsequence id -> id
    | Expr e -> Expression.get_identifier e
    | PExpr pe -> PropertyExpression.get_identifier pe
    | _ -> raise Not_found

end (* of module Statement *)

module CompilerDirective = struct
  type t =
    | Define of identifier
    | Undef of identifier
    | Undefineall
    | Include of string
    | SysInclude of string
    | Timescale of string * string
    | Error of string
    | Line of string * string * string
    | Resetall
    | Default_nettypeNone
    | Default_nettype
    | Pragma of identifier
    | Begin_keywords of string
    | End_keywords
    | Default_decay_time of string
    | Default_trireg_strength of string
    | Delay_mode_distributed
    | Delay_mode_path
    | Delay_mode_unit
    | Delay_mode_zero
    | Celldefine
    | Endcelldefine
    | Unconnected_drive
    | Nounconnected_drive

  let to_string cd =
    let conv = function
    | Define id               -> "Define:"^id
    | Undef id                -> "Undef:"^id
    | Undefineall             -> "Undefineall"
    | Include s               -> "Include:"^s
    | SysInclude s            -> "SysInclude:"^s
    | Timescale(s1, s2)       -> "Timescale:"^s1^":"^s2
    | Error s                 -> "Error:"^s
    | Line(n1, s, n2)         -> "Line:"^n1^":"^s^":"^n2
    | Resetall                -> "Resetall"
    | Default_nettypeNone     -> "Default_nettypeNone"
    | Default_nettype         -> "Default_nettype"
    | Pragma id               -> "Pragma:"^id
    | Begin_keywords s        -> "Begin_keywords:"^s
    | End_keywords            -> "End_keywords"
    | Default_decay_time s    -> "Default_decay_time:"^s
    | Default_trireg_strength s -> "Default_trireg_strength:"^s
    | Delay_mode_distributed    -> "Delay_mode_distributed"
    | Delay_mode_path           -> "Delay_mode_path"
    | Delay_mode_unit           -> "Delay_mode_unit"
    | Delay_mode_zero           -> "Delay_mode_zero"
    | Celldefine              -> "Celldfine"
    | Endcelldefine           -> "Endcelldefine"
    | Unconnected_drive        -> "Unconnected_drive"
    | Nounconnected_drive      -> "Nounconnected_drive"
    in
    "CompilerDirective."^(conv cd)

  let to_simple_string = function
    | Define id               -> "`define "^id
    | Undef id                -> "`undef "^id
    | Undefineall             -> "`undefineall"
    | Include s               -> "`include "^s
    | SysInclude s            -> "`include "^s
    | Timescale(s1, s2)       -> "`timescale "^s1^"/"^s2
    | Error s                 -> "`error "^s
    | Line(n1, s, n2)         -> "`line "^n1^" "^s^" "^n2
    | Resetall                -> "`resetall"
    | Default_nettypeNone      -> "`default_nettype none"
    | Default_nettype          -> "`default_nettype"
    | Pragma id               -> "`pragma "^id
    | Begin_keywords s         -> "`begin_keywords "^s
    | End_keywords             -> "`end_keywords"
    | Default_decay_time s      -> "`default_decay_time "^s
    | Default_trireg_strength s -> "`default_trireg_strength "^s
    | Delay_mode_distributed    -> "`delay_mode_distributed"
    | Delay_mode_path           -> "`delay_mode_path"
    | Delay_mode_unit           -> "`delay_mode_unit"
    | Delay_mode_zero           -> "`delay_mode_zero"
    | Celldefine              -> "`celldefine"
    | Endcelldefine           -> "`endcelldefine"
    | Unconnected_drive        -> "`unconnected_drive"
    | Nounconnected_drive      -> "`nounconnected_drive"

  let get_name = function
    | Define id
    | Undef id
    | Pragma id               -> id
    | _                       -> raise Not_found

  let to_tag cd =
    let tail = "Directive" in
    let name, attrs =
      match cd with
      | Define id                 -> "Define", [ident_attr_name,id]
      | Undef id                  -> "Undef", [ident_attr_name,id]
      | Undefineall               -> "Undefineall", []
      | Include s                 -> "Include", [path_attr_name,strlit_to_encoded_path s]
      | SysInclude s              -> "SysInclude", [path_attr_name,strlit_to_encoded_path s]
      | Timescale(s1, s2)         -> "Timescale", ["unit",s1;"precision",s2]
      | Error s                   -> "Error", ["message",XML.encode_string s]
      | Line(n1, s, n2)           -> "Line", ["line_number",n1;path_attr_name,strlit_to_encoded_path s;"level",n2]
      | Resetall                  -> "Resetall", []
      | Default_nettypeNone       -> "Default_nettypeNone", []
      | Default_nettype           -> "Default_nettype", []
      | Pragma id                 -> "Pragma", [ident_attr_name,id]
      | Begin_keywords s          -> "Begin_keywords", ["version",XML.encode_string s]
      | End_keywords              -> "End_keywords", []
      | Default_decay_time s      -> "Default_decay_time", ["time",s]
      | Default_trireg_strength s -> "Default_trireg_strength", ["strength",s]
      | Delay_mode_distributed    -> "Delay_mode_distributed", []
      | Delay_mode_path           -> "Delay_mode_path", []
      | Delay_mode_unit           -> "Delay_mode_unit", []
      | Delay_mode_zero           -> "Delay_mode_zero", []
      | Celldefine                -> "Celldefine", []
      | Endcelldefine             -> "Endcelldefine", []
      | Unconnected_drive         -> "Unconnected_drive", []
      | Nounconnected_drive       -> "Nounconnected_drive", []
    in
    name^tail, attrs

end (* of module CompilerDirective *)


module Strength = struct
  type t =
    | HIGHZ0
    | HIGHZ1
    | LARGE
    | MEDIUM
    | SMALL
    | PULL0
    | PULL1
    | STRONG0
    | STRONG1
    | WEAK0
    | WEAK1

    | Anonymous

  let to_string = function
    | HIGHZ0       -> "HIGHZ0"
    | HIGHZ1       -> "HIGHZ1"
    | LARGE        -> "LARGE"
    | MEDIUM       -> "MEDIUM"
    | SMALL        -> "SMALL"
    | PULL0        -> "PULL0"
    | PULL1        -> "PULL1"
    | STRONG0      -> "STRONG0"
    | STRONG1      -> "STRONG1"
    | WEAK0        -> "WEAK0"
    | WEAK1        -> "WEAK1"

    | Anonymous -> "<anonymous>"

  let to_rep = function
    | HIGHZ0       -> "highz0"
    | HIGHZ1       -> "highz1"
    | LARGE        -> "large"
    | MEDIUM       -> "medium"
    | SMALL        -> "small"
    | PULL0        -> "pull0"
    | PULL1        -> "pull1"
    | STRONG0      -> "strong0"
    | STRONG1      -> "strong1"
    | WEAK0        -> "weak0"
    | WEAK1        -> "weak1"

    | Anonymous -> "<anonymous>"

  let to_tag strength =
    let tail = "Strength" in
    let name =
      match strength with
      | HIGHZ0       -> "Highz0"
      | HIGHZ1       -> "Highz1"
      | LARGE        -> "Large"
      | MEDIUM       -> "Medium"
      | SMALL        -> "Small"
      | PULL0        -> "Pull0"
      | PULL1        -> "Pull1"
      | STRONG0      -> "Strong0"
      | STRONG1      -> "Strong1"
      | WEAK0        -> "Weak0"
      | WEAK1        -> "Weak1"

      | Anonymous -> "Anonymous"
    in
    name^tail, []

end

module SimpleImmediateAssertion = struct
  type t =
    | Assert
    | Assume
    | Cover

  let to_string sia =
    let conv = function
      | Assert -> "Assert"
      | Assume -> "Assume"
      | Cover  -> "Cover"
    in
    "SimpleImmediateAssertion."^(conv sia)

  let to_simple_string = function
    | Assert -> "assert"
    | Assume -> "assume"
    | Cover  -> "cover"

  let to_tag sia =
    let tail = "ImmediateAssertion" in
    let name =
      match sia with
      | Assert -> "Assert"
      | Assume -> "Assume"
      | Cover  -> "Cover"
    in
    name^tail, []

end

module DeferredImmediateAssertion = struct
  type t = (* strings are always "0" *)
    | Assert of string
    | Assume of string
    | Cover of string

    | Anonymous

  let to_string dia =
    let conv = function
      | Assert s -> "Assert:"^s
      | Assume s -> "Assume:"^s
      | Cover  s -> "Cover:"^s

      | Anonymous -> "<anonymous>"
    in
    "DeferredImmediateAssertion."^(conv dia)

  let to_simple_string = function
    | Assert s -> "assert "^s
    | Assume s -> "assume "^s
    | Cover s  -> "cover "^s

    | Anonymous -> "<anonymous>"

  let to_tag dia =
    let tail = "DeferredImmediateAssertion" in
    let name =
      match dia with
      | Assert _ -> "Assert"
      | Assume _ -> "Assume"
      | Cover _  -> "Cover"

      | Anonymous -> "Anonymous"
    in
    name^tail, []

end

module ConcurrentAssertion = struct
  type t =
    | AssertProp
    | AssumeProp
    | CoverProp
    | CoverSeq
    | RestrictProp

  let to_string ca =
    let conv = function
      | AssertProp   -> "AssertProp"
      | AssumeProp   -> "AssumeProp"
      | CoverProp    -> "CoverProp"
      | CoverSeq     -> "CoverSeq"
      | RestrictProp -> "RestrictProp"
    in
    "ConcurrentAssertion."^(conv ca)

  let to_simple_string = function
    | AssertProp   -> "assert property"
    | AssumeProp   -> "assume property"
    | CoverProp    -> "cover property"
    | CoverSeq     -> "cover sequence"
    | RestrictProp -> "restrict property"

  let to_tag ca =
    let tail = "ConcurrentAssertion" in
    let name =
      match ca with
      | AssertProp   -> "AssertProp"
      | AssumeProp   -> "AssumeProp"
      | CoverProp    -> "CoverProp"
      | CoverSeq     -> "CoverSeq"
      | RestrictProp -> "RestrictProp"
    in
    name^tail, []

end


module ModuleSpec = struct
  type t =
    | NORMAL
    | MACRO

  let to_string = function
    | NORMAL    -> "NORMAL"
    | MACRO     -> "MACRO"

  let to_rep = function
    | NORMAL    -> "module"
    | MACRO     -> "macromodule"

end

module AlwaysSpec = struct
  type t =
    | NORMAL
    | COMB
    | FF
    | LATCH

  let to_string = function
    | NORMAL -> "NORMAL"
    | COMB   -> "COMB"
    | FF     -> "FF"
    | LATCH  -> "LATCH"

  let to_rep = function
    | NORMAL -> "always"
    | COMB   -> "always_comb"
    | FF     -> "always_ff"
    | LATCH  -> "always_latch"

end

module BinsSpec = struct
  type t =
    | Normal
    | Illegal
    | Ignore

  let to_string = function
    | Normal  -> "Normal"
    | Illegal -> "Illegal"
    | Ignore  -> "Ignore"

  let to_simple_string = function
    | Normal  -> "normal"
    | Illegal -> "illegal"
    | Ignore  -> "ignore"

  let to_rep = function
    | Normal  -> "bins"
    | Illegal -> "illegal_bins"
    | Ignore  -> "ignore_bins"

end
