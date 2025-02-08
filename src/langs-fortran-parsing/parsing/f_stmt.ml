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

[%%prepare_logger]

open Label_common

type _t =
  | AccessStmt of F_access_spec.t
  | AllocatableStmt
  | AllocateStmt
  | ArithmeticIfStmt
  | AssignedGotoStmt
  | AssignmentStmt
  | AssignStmt of label
  | AssociateStmt of name option
  | BackspaceStmt
  | BlockDataStmt of name option
  | BlockStmt of name option
  | CallStmt of name
  | CaseStmt of name option
  | CloseStmt
  | CommonStmt
  | ComponentDefStmt
  | ComputedGotoStmt
  | ContainsStmt
  | ContinueStmt
  | CriticalStmt of name option
  | CycleStmt of name option
  | DataStmt
  | DeallocateStmt
  | DerivedTypeStmt of name
  | DimensionStmt
  | DoStmt of name option * label option * var option (* var for Diff/TS *)
  | ElseIfStmt of name option
  | ElseStmt of name option
  | ElsewhereStmt of name option
  | EndAssociateStmt of name option
  | EndEnumStmt
  | EndStmt (* dummy *)
  | EndBlockDataStmt of name option
  | EndBlockStmt of name option
  | EndCriticalStmt of name option
  | EndDoStmt of name option
  | EndfileStmt
  | EndForallStmt of name option
  | EndFunctionStmt of name option
  | EndIfStmt of name option
  | EndInterfaceStmt 
  | EndModuleStmt of name option
  | EndMpSubprogramStmt of name option
  | EndProgramStmt of name option
  | EndSelectStmt of name option
  | EndSubmoduleStmt of name option
  | EndSubroutineStmt of name option
  | EndTypeStmt of name option
  | EndWhereStmt of name option
  | EntryStmt of name
  | EnumDefStmt
  | EnumeratorDefStmt
  | EquivalenceStmt
  | ExitStmt of name option
  | ExternalStmt
  | ForallStmt
  | ForallConstructStmt of name option
  | FormatStmt
  | FlushStmt
  | FunctionStmt of name
  | GotoStmt
  | IfStmt
  | IfThenStmt of name option
  | ImplicitStmt
  | InquireStmt
  | IntentStmt
  | InterfaceStmt of name option
  | IntrinsicStmt
  | ModuleStmt of name
  | MpSubprogramStmt of name
  | NamelistStmt
  | NullifyStmt
  | OpenStmt
  | OptionalStmt
  | ParameterStmt
  | PauseStmt
  | PointerAssignmentStmt
  | PointerStmt
  | PrintStmt
  | PrivateStmt
  | ProcedureStmt
  | ProgramStmt of name
  | SequenceStmt
  | ReadStmt
  | ReturnStmt
  | RewindStmt
  | SaveStmt
  | SelectCaseStmt of name option
  | StmtFunctionStmt of name
  | StopStmt
  | SubmoduleStmt of name * name option * name
  | SubroutineStmt of name
  | TargetStmt
  | TypeDeclarationStmt of name list (* named for Diff/TS *)
  | UseStmt of name
  | WhereStmt
  | WhereConstructStmt of name option
  | WriteStmt

  | PpMacroId of name
  | PpMacroStmt of name

  | StructureStmt of name option (* Intel and IBM *)
  | EndStructureStmt             (* Intel and IBM *)
  | UnionStmt                    (* Intel and IBM *)
  | EndUnionStmt                 (* Intel and IBM *)
  | MapStmt                      (* Intel and IBM *)
  | EndMapStmt                   (* Intel and IBM *)
  | RecordStmt                   (* Intel and IBM *)
  | VirtualStmt                  (* Intel and IBM *)
  | AutomaticStmt                (* Intel and IBM *)
  | StaticStmt                   (* Intel and IBM *)

  | AsynchronousStmt          (* F2003 *)
  | BindStmt                  (* F2003 *)
  | ProtectedStmt             (* F2003 *)
  | ValueStmt                 (* F2003 *)
  | VolatileStmt              (* F2003 *)
  | AbstractInterfaceStmt     (* F2003 *)
  | ImportStmt                (* F2003 *)
  | BindingPrivateStmt        (* F2003 *)
  | FinalProcedureStmt        (* F2003 *)
  | TypeBoundGenericStmt      (* F2003 *)
  | ProcComponentDefStmt      (* F2003 *)
  | ProcedureDeclarationStmt  (* F2003 *)
  | SelectTypeStmt of name option            (* F2003 *)
  | TypeIsTypeGuardStmt of name option       (* F2003 *)
  | ClassIsTypeGuardStmt of name option      (* F2003 *)
  | ClassDefaultTypeGuardStmt of name option (* F2003 *)
  | EndSelectTypeStmt of name option         (* F2003 *)
  | WaitStmt                                 (* F2003 *)

  | TypeBoundProcedureStmt of name option (* F2008 *)
  | ErrorStopStmt                         (* F2008 *)
  | CodimensionStmt                       (* F2008 *)
  | ContiguousStmt                        (* F2008 *)
  | LockStmt                              (* F2008 *)
  | SyncAllStmt                           (* F2008 *)
  | SyncImagesStmt                        (* F2008 *)
  | SyncMemoryStmt

  | AcceptStmt     (* Intel *)
  | DecodeStmt     (* Intel *)
  | DefineFileStmt (* Intel *)
  | DeleteStmt     (* Intel *)
  | EncodeStmt     (* Intel *)
  | FindStmt       (* Intel *)
  | RewriteStmt    (* Intel *)
  | TypeStmt       (* Intel *)
  | UnlockStmt     (* Intel *)



let _to_string = function
  | AccessStmt a                -> "AccessStmt."^(F_access_spec.to_string a)
  | AllocatableStmt             -> "AllocatableStmt"
  | AllocateStmt                -> "AllocateStmt"
  | ArithmeticIfStmt            -> "ArithmeticIfStmt"
  | AssignedGotoStmt            -> "AssignedGotoStmt"
  | AssignmentStmt              -> "AssignmentStmt"
  | AssignStmt l                -> "AssignStmt:"^l
  | AssociateStmt n_opt         -> "AssociateStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | AutomaticStmt               -> "AutomaticStmt"
  | BackspaceStmt               -> "BackspaceStmt"
  | BlockDataStmt n_opt         -> "BlockDataStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | BlockStmt n_opt             -> "BlockStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | CallStmt n                  -> "CallStmt:"^n
  | CaseStmt n_opt              -> "CaseStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | CloseStmt                   -> "CloseStmt"
  | CommonStmt                  -> "CommonStmt"
  | ComponentDefStmt            -> "ComponentDefStmt"
  | ComputedGotoStmt            -> "ComputedGotoStmt"
  | ContainsStmt                -> "ContainsStmt"
  | ContinueStmt                -> "ContinueStmt"
  | CriticalStmt n_opt          -> "CriticalStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | CycleStmt n_opt             -> "CycleStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | DataStmt                    -> "DataStmt"
  | DeallocateStmt              -> "DeallocateStmt"
  | DerivedTypeStmt n           -> "DerivedTypeStmt:"^n
  | DimensionStmt               -> "DimensionStmt"
  | DoStmt(n_opt, l_opt, v_opt) -> "DoStmt"^(string_opt_to_string ~prefix:":" n_opt)^(string_opt_to_string ~prefix:":" l_opt)^(string_opt_to_string ~prefix:":" v_opt)
  | ElseIfStmt n_opt            -> "ElseIfStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | ElseStmt n_opt              -> "ElseStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | ElsewhereStmt n_opt         -> "ElsewhereStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndAssociateStmt n_opt      -> "EndAssociateStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndEnumStmt                 -> "EndEnumStmt"
  | EndStmt                     -> "EndStmt"
  | EndBlockDataStmt n_opt      -> "EndBlockDataStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndBlockStmt n_opt          -> "EndBlockStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndCriticalStmt n_opt       -> "EndCriticalStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndDoStmt n_opt             -> "EndDoStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndfileStmt                 -> "EndfileStmt"
  | EndForallStmt n_opt         -> "EndForallStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndFunctionStmt n_opt       -> "EndFunctionStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndIfStmt n_opt             -> "EndIfStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndInterfaceStmt            -> "EndInterfaceStmt"
  | EndModuleStmt n_opt         -> "EndModuleStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndMpSubprogramStmt n_opt   -> "EndMpSubprogramStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndProgramStmt n_opt        -> "EndProgramStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndSelectStmt n_opt         -> "EndSelectStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndSubmoduleStmt n_opt      -> "EndSubmoduleStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndSubroutineStmt n_opt     -> "EndSubroutineStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndTypeStmt n_opt           -> "EndTypeStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndWhereStmt n_opt          -> "EndWhereStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EntryStmt n                 -> "EntryStmt:"^n
  | EnumDefStmt                 -> "EnumDefStmt"
  | EnumeratorDefStmt           -> "EnumeratorDefStmt"
  | EquivalenceStmt             -> "EquivalenceStmt"
  | ExitStmt n_opt              -> "ExitStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | ExternalStmt                -> "ExternalStmt"
  | ForallStmt                  -> "ForallStmt"
  | ForallConstructStmt n_opt   -> "ForallConstructStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | FormatStmt                  -> "FormatStmt"
  | FlushStmt                   -> "FlushStmt"
  | FunctionStmt n              -> "FunctionStmt:"^n
  | GotoStmt                    -> "GotoStmt"
  | IfStmt                      -> "IfStmt"
  | IfThenStmt n_opt            -> "IfThenStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | ImplicitStmt                -> "ImplicitStmt"
  | InquireStmt                 -> "InquireStmt"
  | IntentStmt                  -> "IntentStmt"
  | InterfaceStmt n_opt         -> "InterfaceStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | IntrinsicStmt               -> "IntrinsicStmt"
  | ModuleStmt n                -> "ModuleStmt:"^n
  | MpSubprogramStmt n          -> "MpSubprogramStmt:"^n
  | NamelistStmt                -> "NamelistStmt"
  | NullifyStmt                 -> "NullifyStmt"
  | OpenStmt                    -> "OpenStmt"
  | OptionalStmt                -> "OptionalStmt"
  | ParameterStmt               -> "ParameterStmt"
  | PauseStmt                   -> "PauseStmt"
  | PointerAssignmentStmt       -> "PointerAssignmentStmt"
  | PointerStmt                 -> "PointerStmt"
  | PrintStmt                   -> "PrintStmt"
  | PrivateStmt                 -> "PrivateStmt"
  | ProcedureStmt               -> "ProcedureStmt"
  | ProgramStmt n               -> "ProgramStmt:"^n
  | SequenceStmt                -> "SequenceStmt"
  | StaticStmt                  -> "StaticStmt"
  | ReadStmt                    -> "ReadStmt"
  | ReturnStmt                  -> "ReturnStmt"
  | RewindStmt                  -> "RewindStmt"
  | SaveStmt                    -> "SaveStmt"
  | SelectCaseStmt n_opt        -> "SelectCaseStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | StmtFunctionStmt n          -> "StmtFunctionStmt:"^n
  | StopStmt                    -> "StopStmt"
  | SubmoduleStmt(a, p_opt, n)  -> "SubmoduleStmt:"^a^(string_opt_to_string ~prefix:":" p_opt)^":"^n
  | SubroutineStmt n            -> "SubroutineStmt:"^n
  | TargetStmt                  -> "TargetStmt"
  | TypeDeclarationStmt ns      -> "TypeDeclarationStmt"^(string_list_to_string ~prefix:":" ";" ns)
  | UseStmt n                   -> "UseStmt:"^n
  | WhereStmt                   -> "WhereStmt"
  | WhereConstructStmt n_opt    -> "WhereConstructStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | WriteStmt                   -> "WriteStmt"

  | PpMacroId n                 -> "PpMacroId:"^n
  | PpMacroStmt n               -> "PpMacroStmt:"^n

  | StructureStmt n_opt         -> "StructureStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndStructureStmt            -> "EndStructureStmt"
  | UnionStmt                   -> "UnionStmt"
  | EndUnionStmt                -> "EndUnionStmt"
  | MapStmt                     -> "MapStmt"
  | EndMapStmt                  -> "EndMapStmt"
  | RecordStmt                  -> "RecordStmt"
  | VirtualStmt                 -> "VirtualStmt"

  | AsynchronousStmt      -> "AsynchronousStmt"
  | BindStmt              -> "BindStmt"
  | ProtectedStmt         -> "ProtectedStmt"
  | ValueStmt             -> "ValueStmt"
  | VolatileStmt          -> "VolatileStmt"
  | AbstractInterfaceStmt -> "AbstractInterfaceStmt"
  | ImportStmt            -> "ImportStmt"
  | BindingPrivateStmt    -> "BindingPrivateStmt"

  | TypeBoundProcedureStmt n_opt -> "TypeBoundProcedureStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | ErrorStopStmt                -> "ErrorStopStmt"
  | CodimensionStmt              -> "CodimensionStmt"
  | ContiguousStmt               -> "ContiguousStmt"
  | LockStmt                     -> "LockStmt"
  | SyncAllStmt                  -> "SyncAllStmt"
  | SyncImagesStmt               -> "SyncImagesStmt"
  | SyncMemoryStmt               -> "SyncMemoryStmt"


  | FinalProcedureStmt   -> "FinalProcedureStmt"
  | TypeBoundGenericStmt -> "TypeBoundGenericStmt"
  | ProcComponentDefStmt -> "ProcComponentDefStmt"
  | ProcedureDeclarationStmt -> "ProcedureDeclarationStmt"
  | SelectTypeStmt n_opt            -> "SelectTypeStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | TypeIsTypeGuardStmt n_opt       -> "TypeIsTypeGuardStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | ClassIsTypeGuardStmt n_opt      -> "ClassIsTypeGuardStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | ClassDefaultTypeGuardStmt n_opt -> "ClassDefaultTypeGuardStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | EndSelectTypeStmt n_opt         -> "EndSelectTypeStmt"^(string_opt_to_string ~prefix:":" n_opt)
  | WaitStmt                        -> "WaitStmt"

  | AcceptStmt     -> "AcceptStmt"
  | DecodeStmt     -> "DecodeStmt"
  | DefineFileStmt -> "DefineFileStmt"
  | DeleteStmt     -> "DeleteStmt"
  | EncodeStmt     -> "EncodeStmt"
  | FindStmt       -> "FindStmt"
  | RewriteStmt    -> "RewriteStmt"
  | TypeStmt       -> "TypeStmt"
  | UnlockStmt     -> "UnlockStmt"


let _to_simple_string = function
  | AccessStmt a                -> F_access_spec.to_simple_string a
  | AllocatableStmt             -> "allocatable"
  | AllocateStmt                -> "allocate"
  | ArithmeticIfStmt            -> "if"
  | AssignedGotoStmt            -> "goto"
  | AssignmentStmt              -> "<assignment>"
  | AssignStmt l                -> "assign "^l
  | AssociateStmt n_opt         -> (string_opt_to_string ~suffix:":" n_opt)^"associate"
  | AutomaticStmt               -> "automatic"
  | BackspaceStmt               -> "backspace"
  | BlockDataStmt n_opt         -> "block data"^(string_opt_to_string ~prefix:" " n_opt)
  | BlockStmt n_opt             -> "block"^(string_opt_to_string ~prefix:" " n_opt)
  | CallStmt n                  -> "call "^n
  | CaseStmt n_opt              -> "case"^(string_opt_to_string ~prefix:" " n_opt)
  | CloseStmt                   -> "close"
  | CommonStmt                  -> "common"
  | ComponentDefStmt            -> "<component-def>"
  | ComputedGotoStmt            -> "goto"
  | ContainsStmt                -> "contains"
  | ContinueStmt                -> "continue"
  | CriticalStmt n_opt          -> (string_opt_to_string ~suffix:":" n_opt)^"critical"
  | CycleStmt n_opt             -> "cycle"^(string_opt_to_string ~prefix:" " n_opt)
  | DataStmt                    -> "data"
  | DeallocateStmt              -> "deallocate"
  | DerivedTypeStmt n           -> "type "^n
  | DimensionStmt               -> "dimention"
  | DoStmt(n_opt, l_opt, v_opt) -> "do"^(string_opt_to_string ~prefix:" " n_opt)^(string_opt_to_string ~prefix:" " l_opt)^(string_opt_to_string ~prefix:" " v_opt)
  | ElseIfStmt n_opt            -> "else if"^(string_opt_to_string ~prefix:" " n_opt)
  | ElseStmt n_opt              -> "else"^(string_opt_to_string ~prefix:" " n_opt)
  | ElsewhereStmt n_opt         -> "elsewhere"^(string_opt_to_string ~prefix:" " n_opt)
  | EndAssociateStmt n_opt      -> "end associate"^(string_opt_to_string ~prefix:" " n_opt)
  | EndEnumStmt                 -> "end enum"
  | EndStmt                     -> "end"
  | EndBlockDataStmt n_opt      -> "end block data"^(string_opt_to_string ~prefix:" " n_opt)
  | EndBlockStmt n_opt          -> "end block"^(string_opt_to_string ~prefix:" " n_opt)
  | EndCriticalStmt n_opt       -> "end critical"^(string_opt_to_string ~prefix:" " n_opt)
  | EndDoStmt n_opt             -> "end do"^(string_opt_to_string ~prefix:" " n_opt)
  | EndfileStmt                 -> "endfile"
  | EndForallStmt n_opt         -> "end forall"^(string_opt_to_string ~prefix:" " n_opt)
  | EndFunctionStmt n_opt       -> "end function"^(string_opt_to_string ~prefix:" " n_opt)
  | EndIfStmt n_opt             -> "end if"^(string_opt_to_string ~prefix:" " n_opt)
  | EndInterfaceStmt            -> "end interface"
  | EndModuleStmt n_opt         -> "end module"^(string_opt_to_string ~prefix:" " n_opt)
  | EndMpSubprogramStmt n_opt   -> "end procedure"^(string_opt_to_string ~prefix:" " n_opt)
  | EndProgramStmt n_opt        -> "end program"^(string_opt_to_string ~prefix:" " n_opt)
  | EndSelectStmt n_opt         -> "end select"^(string_opt_to_string ~prefix:" " n_opt)
  | EndSubmoduleStmt n_opt      -> "end submodule"^(string_opt_to_string ~prefix:" " n_opt)
  | EndSubroutineStmt n_opt     -> "end subroutine"^(string_opt_to_string ~prefix:" " n_opt)
  | EndTypeStmt n_opt           -> "end type"^(string_opt_to_string ~prefix:" " n_opt)
  | EndWhereStmt n_opt          -> "end where"^(string_opt_to_string ~prefix:" " n_opt)
  | EntryStmt n                 -> "entry "^n
  | EnumDefStmt                 -> "enum, bind(c)"
  | EnumeratorDefStmt           -> "enumerator"
  | EquivalenceStmt             -> "equivalence"
  | ExitStmt n_opt              -> "exit"^(string_opt_to_string ~prefix:" " n_opt)
  | ExternalStmt                -> "external"
  | ForallStmt                  -> "forall"
  | ForallConstructStmt n_opt   -> (string_opt_to_string ~suffix:":" n_opt)^"forall"
  | FormatStmt                  -> "format"
  | FlushStmt                   -> "flush"
  | FunctionStmt n              -> "function "^n
  | GotoStmt                    -> "goto"
  | IfStmt                      -> "if"
  | IfThenStmt n_opt            -> (string_opt_to_string ~suffix:":" n_opt)^"if then"
  | ImplicitStmt                -> "implicit"
  | InquireStmt                 -> "inquire"
  | IntentStmt                  -> "intent"
  | InterfaceStmt n_opt         -> "interface"^(string_opt_to_string ~prefix:" " n_opt)
  | IntrinsicStmt               -> "intrinsic"
  | ModuleStmt n                -> "module "^n
  | MpSubprogramStmt n          -> "module procedure "^n
  | NamelistStmt                -> "namelist"
  | NullifyStmt                 -> "nullify"
  | OpenStmt                    -> "open"
  | OptionalStmt                -> "optional"
  | ParameterStmt               -> "parameter"
  | PauseStmt                   -> "pause"
  | PointerAssignmentStmt       -> "<pointer-assignment>"
  | PointerStmt                 -> "pointer"
  | PrintStmt                   -> "print"
  | PrivateStmt                 -> "private"
  | ProcedureStmt               -> "procedure"
  | ProgramStmt n               -> "program "^n
  | SequenceStmt                -> "sequence"
  | StaticStmt                  -> "static"
  | ReadStmt                    -> "read"
  | ReturnStmt                  -> "return"
  | RewindStmt                  -> "rewind"
  | SaveStmt                    -> "save"
  | SelectCaseStmt n_opt        -> (string_opt_to_string ~suffix:":" n_opt)^"select case"
  | StmtFunctionStmt n          -> n
  | StopStmt                    -> "stop"
  | SubmoduleStmt(a, p_opt, n)  -> "submodule ("^a^(string_opt_to_string ~prefix:":" p_opt)^") "^n
  | SubroutineStmt n            -> "subroutine "^n
  | TargetStmt                  -> "target"
  | TypeDeclarationStmt _       -> "<type-declaration>"
  | UseStmt n                   -> "use "^n
  | WhereStmt                   -> "where"
  | WhereConstructStmt n_opt    -> (string_opt_to_string ~suffix:":" n_opt)^"where"
  | WriteStmt                   -> "write"

  | PpMacroId n                 -> n
  | PpMacroStmt n               -> n

  | StructureStmt n_opt         -> "structure"^(string_opt_to_string ~prefix:" /" ~suffix:"/" n_opt)
  | EndStructureStmt            -> "end structure"
  | UnionStmt                   -> "union"
  | EndUnionStmt                -> "end union"
  | MapStmt                     -> "map"
  | EndMapStmt                  -> "end map"
  | RecordStmt                  -> "record"
  | VirtualStmt                 -> "virtual"

  | AsynchronousStmt      -> "asynchronous"
  | BindStmt              -> "bind"
  | ProtectedStmt         -> "protected"
  | ValueStmt             -> "value"
  | VolatileStmt          -> "volatile"
  | AbstractInterfaceStmt -> "abstract interface"
  | ImportStmt            -> "import"
  | BindingPrivateStmt    -> "private"

  | TypeBoundProcedureStmt n_opt -> "procedure"^(string_opt_to_string ~prefix:"(" ~suffix:")" n_opt)
  | ErrorStopStmt                -> "error stop"
  | CodimensionStmt              -> "codimension"
  | ContiguousStmt               -> "contiguous"
  | LockStmt                     -> "lock"
  | SyncAllStmt                  -> "sync all"
  | SyncImagesStmt               -> "sync images"
  | SyncMemoryStmt               -> "sync memory"


  | FinalProcedureStmt   -> "final"
  | TypeBoundGenericStmt -> "generic"
  | ProcComponentDefStmt -> "procedure"
  | ProcedureDeclarationStmt -> "procedure"
  | SelectTypeStmt n_opt            -> (string_opt_to_string ~suffix:":" n_opt)^"select type"
  | TypeIsTypeGuardStmt n_opt       -> "type is"^(string_opt_to_string ~prefix:" " n_opt)
  | ClassIsTypeGuardStmt n_opt      -> "class is"^(string_opt_to_string ~prefix:" " n_opt)
  | ClassDefaultTypeGuardStmt n_opt -> "class default"^(string_opt_to_string ~prefix:" " n_opt)
  | EndSelectTypeStmt n_opt         -> "end select"^(string_opt_to_string ~prefix:" " n_opt)
  | WaitStmt                        -> "wait"

  | AcceptStmt     -> "accept"
  | DecodeStmt     -> "decode"
  | DefineFileStmt -> "define file"
  | DeleteStmt     -> "delete"
  | EncodeStmt     -> "encode"
  | FindStmt       -> "find"
  | RewriteStmt    -> "rewrite"
  | TypeStmt       -> "type"
  | UnlockStmt     -> "unlock"



let _to_tag = function
  | AccessStmt a                -> begin
      match a with
      | F_access_spec.Private -> "PrivateAccessStmt", []
      | F_access_spec.Public  -> "PublicAccessStmt", []
  end
  | AllocatableStmt             -> "AllocatableStmt", []
  | AllocateStmt                -> "AllocateStmt", []
  | ArithmeticIfStmt            -> "ArithmeticIfStmt", []
  | AssignedGotoStmt            -> "AssignedGotoStmt", []
  | AssignmentStmt              -> "AssignmentStmt", []
  | AssignStmt l                -> "AssignStmt", [label_attr_name,l]
  | AssociateStmt n_opt         -> "AssociateStmt", (string_opt_to_attr name_attr_name n_opt)
  | AutomaticStmt               -> "AutomaticStmt", []
  | BackspaceStmt               -> "BackspaceStmt", []
  | BlockDataStmt n_opt         -> "BlockDataStmt", (string_opt_to_attr name_attr_name n_opt)
  | BlockStmt n_opt             -> "BlockStmt", (string_opt_to_attr name_attr_name n_opt)
  | CallStmt n                  -> "CallStmt", [name_attr_name,n]
  | CaseStmt n_opt              -> "CaseStmt", (string_opt_to_attr name_attr_name n_opt)
  | CloseStmt                   -> "CloseStmt", []
  | CommonStmt                  -> "CommonStmt", []
  | ComponentDefStmt            -> "ComponentDefStmt", []
  | ComputedGotoStmt            -> "ComputedGotoStmt", []
  | ContainsStmt                -> "ContainsStmt", []
  | ContinueStmt                -> "ContinueStmt", []
  | CriticalStmt n_opt          -> "CriticalStmt", (string_opt_to_attr name_attr_name n_opt)
  | CycleStmt n_opt             -> "CycleStmt", (string_opt_to_attr name_attr_name n_opt)
  | DataStmt                    -> "DataStmt", []
  | DeallocateStmt              -> "DeallocateStmt", []
  | DerivedTypeStmt n           -> "DerivedTypeStmt", [name_attr_name,n]
  | DimensionStmt               -> "DimensionStmt", []
  | DoStmt(n_opt, l_opt, v_opt) -> "DoStmt", (string_opt_to_attr name_attr_name n_opt) @ (string_opt_to_attr label_attr_name l_opt) @ (string_opt_to_attr var_attr_name v_opt)
  | ElseIfStmt n_opt            -> "ElseIfStmt", (string_opt_to_attr name_attr_name n_opt)
  | ElseStmt n_opt              -> "ElseStmt", (string_opt_to_attr name_attr_name n_opt)
  | ElsewhereStmt n_opt         -> "ElsewhereStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndAssociateStmt n_opt      -> "EndAssociateStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndEnumStmt                 -> "EndEnumStmt", []
  | EndStmt                     -> "EndStmt", []
  | EndBlockDataStmt n_opt      -> "EndBlockDataStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndBlockStmt n_opt          -> "EndBlockStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndCriticalStmt n_opt       -> "EndCriticalStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndDoStmt n_opt             -> "EndDoStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndfileStmt                 -> "EndfileStmt", []
  | EndForallStmt n_opt         -> "EndForallStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndFunctionStmt n_opt       -> "EndFunctionStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndIfStmt n_opt             -> "EndIfStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndInterfaceStmt            -> "EndInterfaceStmt", []
  | EndModuleStmt n_opt         -> "EndModuleStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndMpSubprogramStmt n_opt   -> "EndMpSubprogramStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndProgramStmt n_opt        -> "EndProgramStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndSelectStmt n_opt         -> "EndSelectStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndSubmoduleStmt n_opt      -> "EndSubmoduleStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndSubroutineStmt n_opt     -> "EndSubroutineStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndTypeStmt n_opt           -> "EndTypeStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndWhereStmt n_opt          -> "EndWhereStmt", (string_opt_to_attr name_attr_name n_opt)
  | EntryStmt n                 -> "EntryStmt", [name_attr_name,n]
  | EnumDefStmt                 -> "EnumDefStmt", []
  | EnumeratorDefStmt           -> "EnumeratorDefStmt", []
  | EquivalenceStmt             -> "EquivalenceStmt", []
  | ExitStmt n_opt              -> "ExitStmt", (string_opt_to_attr name_attr_name n_opt)
  | ExternalStmt                -> "ExternalStmt", []
  | ForallStmt                  -> "ForallStmt", []
  | ForallConstructStmt n_opt   -> "ForallConstructStmt", (string_opt_to_attr name_attr_name n_opt)
  | FormatStmt                  -> "FormatStmt", []
  | FlushStmt                   -> "FlushStmt", []
  | FunctionStmt n              -> "FunctionStmt", [name_attr_name,n]
  | GotoStmt                    -> "GotoStmt", []
  | IfStmt                      -> "IfStmt", []
  | IfThenStmt n_opt            -> "IfThenStmt", (string_opt_to_attr name_attr_name n_opt)
  | ImplicitStmt                -> "ImplicitStmt", []
  | InquireStmt                 -> "InquireStmt", []
  | IntentStmt                  -> "IntentStmt", []
  | InterfaceStmt n_opt         -> "InterfaceStmt", (string_opt_to_attr name_attr_name n_opt)
  | IntrinsicStmt               -> "IntrinsicStmt", []
  | ModuleStmt n                -> "ModuleStmt", [name_attr_name,n]
  | MpSubprogramStmt n          -> "MpSubprogramStmt", [name_attr_name,n]
  | NamelistStmt                -> "NamelistStmt", []
  | NullifyStmt                 -> "NullifyStmt", []
  | OpenStmt                    -> "OpenStmt", []
  | OptionalStmt                -> "OptionalStmt", []
  | ParameterStmt               -> "ParameterStmt", []
  | PauseStmt                   -> "PauseStmt", []
  | PointerAssignmentStmt       -> "PointerAssignmentStmt", []
  | PointerStmt                 -> "PointerStmt", []
  | PrintStmt                   -> "PrintStmt", []
  | PrivateStmt                 -> "PrivateStmt", []
  | ProcedureStmt               -> "ProcedureStmt", []
  | ProgramStmt n               -> "ProgramStmt", [name_attr_name,n]
  | SequenceStmt                -> "SequenceStmt", []
  | StaticStmt                  -> "StaticStmt", []
  | ReadStmt                    -> "ReadStmt", []
  | ReturnStmt                  -> "ReturnStmt", []
  | RewindStmt                  -> "RewindStmt", []
  | SaveStmt                    -> "SaveStmt", []
  | SelectCaseStmt n_opt        -> "SelectCaseStmt", (string_opt_to_attr name_attr_name n_opt)
  | StmtFunctionStmt n          -> "StmtFunctionStmt", [name_attr_name,n]
  | StopStmt                    -> "StopStmt", []
  | SubmoduleStmt(a, p_opt, n)  -> "SubmoduleStmt", (name_attr_name,n)::("ancestor",a)::(string_opt_to_attr "parent" p_opt)
  | SubroutineStmt n            -> "SubroutineStmt", [name_attr_name,n]
  | TargetStmt                  -> "TargetStmt", []
  | TypeDeclarationStmt _       -> "TypeDeclarationStmt", []
  | UseStmt n                   -> "UseStmt", [name_attr_name,n]
  | WhereStmt                   -> "WhereStmt", []
  | WhereConstructStmt n_opt    -> "WhereConstructStmt", (string_opt_to_attr name_attr_name n_opt)
  | WriteStmt                   -> "WriteStmt", []

  | PpMacroId n                 -> "PpMacroId", [name_attr_name,n]
  | PpMacroStmt n               -> "PpMacroStmt", [name_attr_name,n]

  | StructureStmt n_opt         -> "StructureStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndStructureStmt            -> "EndStructureStmt", []
  | UnionStmt                   -> "UnionStmt", []
  | EndUnionStmt                -> "EndUnionStmt", []
  | MapStmt                     -> "MapStmt", []
  | EndMapStmt                  -> "EndMapStmt", []
  | RecordStmt                  -> "RecordStmt", []
  | VirtualStmt                 -> "VirtualStmt", []

  | AsynchronousStmt      -> "AsynchronousStmt", []
  | BindStmt              -> "BindStmt", []
  | ProtectedStmt         -> "ProtectedStmt", []
  | ValueStmt             -> "ValueStmt", []
  | VolatileStmt          -> "VolatileStmt", []
  | AbstractInterfaceStmt -> "AbstractInterfaceStmt", []
  | ImportStmt            -> "ImportStmt", []
  | BindingPrivateStmt    -> "BindingPrivateStmt", []

  | TypeBoundProcedureStmt n_opt -> "TypeBoundProcedureStmt", (string_opt_to_attr name_attr_name n_opt)
  | ErrorStopStmt                -> "ErrorStopStmt", []
  | CodimensionStmt              -> "CodimensionStmt", []
  | ContiguousStmt               -> "ContiguousStmt", []
  | LockStmt                     -> "LockStmt", []
  | SyncAllStmt                  -> "SyncAllStmt", []
  | SyncImagesStmt               -> "SyncImagesStmt", []
  | SyncMemoryStmt               -> "SyncMemoryStmt", []


  | FinalProcedureStmt -> "FinalProcedureStmt", []
  | TypeBoundGenericStmt -> "TypeBoundGenericStmt", []
  | ProcComponentDefStmt -> "ProcComponentDefStmt", []
  | ProcedureDeclarationStmt -> "ProcedureDeclarationStmt", []
  | SelectTypeStmt n_opt            -> "SelectTypeStmt", (string_opt_to_attr name_attr_name n_opt)
  | TypeIsTypeGuardStmt n_opt       -> "TypeIsTypeGuardStmt", (string_opt_to_attr name_attr_name n_opt)
  | ClassIsTypeGuardStmt n_opt      -> "ClassIsTypeGuardStmt", (string_opt_to_attr name_attr_name n_opt)
  | ClassDefaultTypeGuardStmt n_opt -> "ClassDefaultTypeGuardStmt", (string_opt_to_attr name_attr_name n_opt)
  | EndSelectTypeStmt n_opt         -> "EndSelectTypeStmt", (string_opt_to_attr name_attr_name n_opt)
  | WaitStmt                        -> "WaitStmt", []

  | AcceptStmt     -> "AcceptStmt", []
  | DecodeStmt     -> "DecodeStmt", []
  | DefineFileStmt -> "DefineFileStmt", []
  | DeleteStmt     -> "DeleteStmt", []
  | EncodeStmt     -> "EncodeStmt", []
  | FindStmt       -> "FindStmt", []
  | RewriteStmt    -> "RewriteStmt", []
  | TypeStmt       -> "TypeStmt", []
  | UnlockStmt     -> "UnlockStmt", []


let _get_name = function
  | CallStmt n
  | DerivedTypeStmt n      
  | EntryStmt n   
  | FunctionStmt n
  | ModuleStmt n 
  | MpSubprogramStmt n 
  | ProgramStmt n
  | StmtFunctionStmt n
  | SubmoduleStmt(_, _, n)
  | SubroutineStmt n 
  | UseStmt n        

  | PpMacroId n
  | PpMacroStmt n 

      -> n

  | AssociateStmt n_opt
  | BlockDataStmt n_opt
  | BlockStmt n_opt
  | DoStmt(n_opt, _, _)
  | CaseStmt n_opt
  | CycleStmt n_opt
  | CriticalStmt n_opt
  | ElseIfStmt n_opt
  | ElseStmt n_opt
  | InterfaceStmt n_opt
  | EndAssociateStmt n_opt
  | EndBlockDataStmt n_opt   
  | EndBlockStmt n_opt   
  | EndDoStmt n_opt
  | EndForallStmt n_opt
  | EndFunctionStmt n_opt
  | EndIfStmt n_opt
  | EndModuleStmt n_opt
  | EndMpSubprogramStmt n_opt
  | EndProgramStmt n_opt
  | EndSelectStmt n_opt
  | EndSubmoduleStmt n_opt
  | EndSubroutineStmt n_opt
  | EndTypeStmt n_opt 
  | EndWhereStmt n_opt       
  | ForallConstructStmt n_opt
  | ExitStmt n_opt
  | IfThenStmt n_opt
  | SelectCaseStmt n_opt
  | StructureStmt n_opt
  | WhereConstructStmt n_opt 
    -> begin
      match n_opt with
      | Some x -> x
      | _ -> raise Not_found
    end

  | _ -> raise Not_found

let _get_name_opt = function
  | AssociateStmt n_opt
  | BlockDataStmt n_opt
  | BlockStmt n_opt
  | DoStmt(n_opt, _, _)
  | CaseStmt n_opt
  | CycleStmt n_opt
  | CriticalStmt n_opt
  | ElseIfStmt n_opt
  | ElseStmt n_opt
  | InterfaceStmt n_opt
  | EndAssociateStmt n_opt
  | EndBlockDataStmt n_opt
  | EndBlockStmt n_opt
  | EndDoStmt n_opt
  | EndForallStmt n_opt
  | EndFunctionStmt n_opt
  | EndIfStmt n_opt
  | EndModuleStmt n_opt
  | EndMpSubprogramStmt n_opt
  | EndProgramStmt n_opt
  | EndSelectStmt n_opt
  | EndSubmoduleStmt n_opt
  | EndSubroutineStmt n_opt
  | EndTypeStmt n_opt 
  | EndWhereStmt n_opt  
  | ExitStmt n_opt
  | ForallConstructStmt n_opt
  | IfThenStmt n_opt
  | SelectCaseStmt n_opt     
  | WhereConstructStmt n_opt 
  | StructureStmt n_opt
    -> n_opt

  | CallStmt n
  | DerivedTypeStmt n      
  | EntryStmt n            
  | FunctionStmt n
  | ModuleStmt n 
  | MpSubprogramStmt n 
  | ProgramStmt n
  | StmtFunctionStmt n
  | SubmoduleStmt(_, _, n)
  | SubroutineStmt n 
  | UseStmt n        

  | PpMacroId n
  | PpMacroStmt n 

    -> Some n

  | _ -> None

let _get_names = function
  | TypeDeclarationStmt ns -> ns
  | _ -> []

let _is_named_orig = function
  | TypeDeclarationStmt _ -> false
  | lab ->
      (try
        ignore (_get_name lab);
        true
      with
        Not_found -> false
      ) ||
      (_get_names lab <> [])

let _get_label = function
  | AssignStmt lab -> lab
  | DoStmt(_, lab_opt, _) -> begin
      match lab_opt with
      | Some lab -> lab
      | _ -> raise Not_found
  end
  | _ -> raise Not_found

let _get_var = function
  | DoStmt(_, _, v_opt) ->
      begin
        match v_opt with
        | Some x -> x
        | _ -> raise Not_found
      end
  | _ -> raise Not_found

let _get_var_opt = function
  | DoStmt(_, _,  v_opt) -> v_opt
  | _ -> None

let _is_other_specification_stmt = function
  | AccessStmt _             
  | AllocatableStmt          
  | AsynchronousStmt      (* F2003 *)
  | BindStmt              (* F2003 *)
  | CodimensionStmt            
  | CommonStmt               
  | DataStmt                 
  | DimensionStmt            
  | EquivalenceStmt          
  | ExternalStmt             
  | IntentStmt               
  | IntrinsicStmt            
  | NamelistStmt             
  | OptionalStmt             
  | PointerStmt              
  | ProtectedStmt         (* F2003 *)
  | SaveStmt                 
  | TargetStmt
  | VolatileStmt          (* F2003 *)
  | ValueStmt             (* F2003 *)
  | VirtualStmt
  | AutomaticStmt (* Intel *)
  | StaticStmt    (* Intel *)
  | ContiguousStmt (* ?F2008 *)
    -> true
  | _ -> false

let _is_implicit_part_stmt = function
  | ImplicitStmt             
  | ParameterStmt            
  | FormatStmt               
  | EntryStmt _              -> true
  | _ -> false

let _is_declaration_construct_stmt = function
  | EntryStmt _              
  | FormatStmt               
  | ParameterStmt            
  | ProcedureDeclarationStmt      
  | TypeDeclarationStmt _     
  | StmtFunctionStmt _       -> true

  | DerivedTypeStmt _        
(*  | TypeParamDefStmt _*)
  | PrivateStmt              
  | SequenceStmt             
  | ComponentDefStmt  
  | BindingPrivateStmt
  | TypeBoundProcedureStmt _
  | TypeBoundGenericStmt
  | FinalProcedureStmt
  | EndTypeStmt _            -> true

  | InterfaceStmt _           
  | FunctionStmt _           
  | SubmoduleStmt _
  | SubroutineStmt _
  | ProcedureStmt      
  | EndInterfaceStmt         -> true

  | EnumDefStmt
  | EnumeratorDefStmt
  | EndEnumStmt       -> true

  | s -> _is_other_specification_stmt s

[%%capture_path
let _is_specification_part_stmt s = 
  let b =
    match s with
    | UseStmt _ 
    | ImportStmt
      -> true
    | _ ->
        _is_implicit_part_stmt s ||
        _is_declaration_construct_stmt s
  in
  [%debug_log "%s -> %B" (_to_string s) b];
  b
]

let _is_type_decl_stmt = function
  | TypeDeclarationStmt _ -> true
  | _ -> false

let _is_if_stmt = function
  | IfStmt -> true
  | _ -> false

let _is_arithmetic_if_stmt = function
  | ArithmeticIfStmt -> true
  | _ -> false

let _is_if_then_stmt = function
  | IfThenStmt _ -> true
  | _ -> false

let _is_else_if_stmt = function
  | ElseIfStmt _ -> true
  | _ -> false

let _is_else_stmt = function
  | ElseStmt _ -> true
  | _ -> false


let _is_action_stmt = function
  | AcceptStmt
  | AllocateStmt             
  | AssignmentStmt           
  | BackspaceStmt            
  | CallStmt _               
  | CloseStmt                
  | ComputedGotoStmt         
  | ContinueStmt             
  | CycleStmt _
  | DeallocateStmt           
  | DecodeStmt
  | DefineFileStmt
  | DeleteStmt
  | EncodeStmt
  | EndfileStmt              
  | EndFunctionStmt _
  | EndProgramStmt _
  | EndSubmoduleStmt _
  | EndSubroutineStmt _
  | ErrorStopStmt
  | ExitStmt _
  | FindStmt
  | FlushStmt
  | ForallStmt
  | GotoStmt                 
  | IfStmt                   
  | InquireStmt              
  | LockStmt
  | NullifyStmt              
  | OpenStmt                 
  | PointerAssignmentStmt    
  | PrintStmt                
  | ReadStmt                 
  | ReturnStmt               
  | RewindStmt               
  | RewriteStmt
  | StopStmt      
  | SyncAllStmt
  | SyncImagesStmt
  | SyncMemoryStmt
  | TypeStmt
  | UnlockStmt
  | WaitStmt
  | WhereStmt                
  | WriteStmt                
  | ArithmeticIfStmt         
  | AssignStmt _
  | AssignedGotoStmt
  | PauseStmt
    -> true

  | _ -> false


let _is_executable_construct_stmt = function
  | AssociateStmt _
  | EndAssociateStmt _       -> true
  | BlockStmt _
  | EndBlockStmt _           -> true
  | SelectCaseStmt _
  | CaseStmt _           
  | EndSelectStmt _          -> true
  | CriticalStmt _
  | EndCriticalStmt _        -> true
  | DoStmt _
  | EndDoStmt _          
  | ContinueStmt             -> true
  | ForallStmt 
  | ForallConstructStmt _
  | WhereStmt                
  | AssignmentStmt           
  | PointerAssignmentStmt    
  | EndForallStmt _          -> true
  | IfThenStmt _
  | ElseIfStmt _
  | ElseStmt _
  | EndIfStmt _              -> true
  | SelectTypeStmt _
  | TypeIsTypeGuardStmt _
  | ClassIsTypeGuardStmt _
  | ClassDefaultTypeGuardStmt _ -> true
  | ElsewhereStmt _
  | WhereConstructStmt _
  | EndWhereStmt _           -> true
  | s -> _is_action_stmt s

let _is_execution_part_construct_stmt = function
  | FormatStmt               
  | EntryStmt _              
  | DataStmt                 -> true
  | s -> _is_executable_construct_stmt s

[%%capture_path
let _is_execution_part_stmt s = 
  let b = _is_execution_part_construct_stmt s in
  [%debug_log "%s -> %B" (_to_string s) b];
  b
]

let _is_end_if_stmt = function
  | EndIfStmt _ -> true
  | _ -> false

let _is_do_stmt = function
  | DoStmt _ -> true
  | _ -> false

let _is_end_do_stmt = function
  | EndDoStmt _ -> true
  | _ -> false

let _is_call_stmt = function
  | CallStmt _ -> true
  | _ -> false

let _is_function_stmt = function
  | FunctionStmt _ -> true
  | _ -> false

let _is_subroutine_stmt = function
  | SubroutineStmt _ -> true
  | _ -> false

let _is_assignment_stmt = function
  | AssignmentStmt -> true
  | _ -> false

type t =
  | Labeled of label * _t
  | Nonlabeled of _t
        
let to_string = function
  | Labeled(lab, stmt) -> "Labeled:"^lab^"."^(_to_string stmt)
  | Nonlabeled stmt -> _to_string stmt

let to_simple_string = function
  | Labeled(lab, stmt) -> lab^" "^(_to_string stmt)
  | Nonlabeled stmt -> _to_simple_string stmt

let to_tag = function
  | Labeled(lab, stmt) -> 
      let t, a = _to_tag stmt in
      t, [slabel_attr_name,lab] @ a
  | Nonlabeled stmt -> _to_tag stmt

let get_name = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> _get_name stmt

let get_name_opt = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> _get_name_opt stmt

let get_names = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> _get_names stmt

let is_named_orig = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> _is_named_orig stmt

let get_label = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> _get_label stmt

let get_stmt_label = function
  | Labeled(lab, _) -> lab
  | Nonlabeled _ -> raise Not_found

let get_var = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> _get_var stmt

let get_var_opt = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> _get_var_opt stmt

let get_stmt = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> stmt


let mklabeled lab x = Labeled(lab, x)
let mk x = Nonlabeled x

let relab lab _lab' =
  match lab with
  | Labeled(l, _) -> Labeled(l, _lab')
  | Nonlabeled _ -> Nonlabeled _lab'

let is_xxx xxx = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> xxx stmt

let is_specification_part_stmt = is_xxx _is_specification_part_stmt
let is_execution_part_stmt     = is_xxx _is_execution_part_stmt
let is_action_stmt             = is_xxx _is_action_stmt
let is_type_decl_stmt          = is_xxx _is_type_decl_stmt
let is_if_stmt                 = is_xxx _is_if_stmt
let is_arithmetic_if_stmt      = is_xxx _is_arithmetic_if_stmt
let is_if_then_stmt            = is_xxx _is_if_then_stmt
let is_else_if_stmt            = is_xxx _is_else_if_stmt
let is_else_stmt               = is_xxx _is_else_stmt
let is_end_if_stmt             = is_xxx _is_end_if_stmt
let is_do_stmt                 = is_xxx _is_do_stmt
let is_end_do_stmt             = is_xxx _is_end_do_stmt
let is_call_stmt               = is_xxx _is_call_stmt
let is_function_stmt           = is_xxx _is_function_stmt
let is_subroutine_stmt         = is_xxx _is_subroutine_stmt
let is_assignment_stmt         = is_xxx _is_assignment_stmt

let get_raw_stmt = function
  | Labeled(_, stmt)
  | Nonlabeled stmt -> stmt

let of_keyword kw =
  match String.lowercase_ascii kw with
  | "external"   -> ExternalStmt
  | "protected"  -> ProtectedStmt
  | "value"      -> ValueStmt
  | "volatile"   -> VolatileStmt
  | "contiguous" -> ContiguousStmt
  | "automatic"  -> AutomaticStmt
  | "static"     -> StaticStmt

  | _ -> failwith "F_stmt.of_keyword"

let _anonymize = function
  | CallStmt _               -> CallStmt ""
  | DerivedTypeStmt _        -> DerivedTypeStmt ""
  | EntryStmt _              -> EntryStmt ""
  | FunctionStmt _           -> FunctionStmt ""
  | ModuleStmt _             -> ModuleStmt ""
  | MpSubprogramStmt _       -> MpSubprogramStmt ""
  | ProgramStmt _            -> ProgramStmt ""
  | StmtFunctionStmt _       -> StmtFunctionStmt ""
  | SubroutineStmt _         -> SubroutineStmt ""
  | UseStmt _                -> UseStmt ""

  | BlockDataStmt _       -> BlockDataStmt None
  | CaseStmt _            -> CaseStmt None
  | CycleStmt _           -> CycleStmt None
  | ElseIfStmt _          -> ElseIfStmt None
  | ElseStmt _            -> ElseStmt None
  | ElsewhereStmt _       -> ElsewhereStmt None
  | EndBlockDataStmt _    -> EndBlockDataStmt None
  | EndDoStmt _           -> EndDoStmt None
  | EndForallStmt _       -> EndForallStmt None
  | EndFunctionStmt _     -> EndFunctionStmt None
  | EndIfStmt _           -> EndIfStmt None
  | EndModuleStmt _       -> EndModuleStmt None
  | EndMpSubprogramStmt _ -> EndMpSubprogramStmt None
  | EndProgramStmt _      -> EndProgramStmt None
  | EndSelectStmt _       -> EndSelectStmt None
  | EndSubroutineStmt _   -> EndSubroutineStmt None
  | EndTypeStmt _         -> EndTypeStmt None
  | EndWhereStmt _        -> EndWhereStmt None
  | ExitStmt _            -> ExitStmt None
  | ForallConstructStmt _ -> ForallConstructStmt None
  | IfThenStmt _          -> IfThenStmt None
  | SelectCaseStmt _      -> SelectCaseStmt None
  | WhereConstructStmt _  -> WhereConstructStmt None

  | AssociateStmt _             -> AssociateStmt None
  | BlockStmt _                 -> BlockStmt None
  | CriticalStmt _              -> CriticalStmt None
  | EndAssociateStmt _          -> EndAssociateStmt None
  | EndBlockStmt _              -> EndBlockStmt None
  | EndCriticalStmt _           -> EndCriticalStmt None
  | SelectTypeStmt _            -> SelectTypeStmt None
  | TypeIsTypeGuardStmt _       -> TypeIsTypeGuardStmt None
  | ClassIsTypeGuardStmt _      -> ClassIsTypeGuardStmt None
  | ClassDefaultTypeGuardStmt _ -> ClassDefaultTypeGuardStmt None
  | EndSelectTypeStmt _         -> EndSelectTypeStmt None
  | TypeBoundProcedureStmt _    -> TypeBoundProcedureStmt None

  | AssignStmt _                -> AssignStmt ""
  | DoStmt(_, _, _) -> DoStmt(None, None, None)

  | PpMacroStmt _               -> PpMacroStmt ""

  | StructureStmt _         -> StructureStmt None

  | SubmoduleStmt(_, _, _)  -> SubmoduleStmt("", None, "")
  | EndSubmoduleStmt _      -> EndSubmoduleStmt None

  | l -> l

let anonymize = function
  | Labeled(_, stmt) -> Nonlabeled stmt
  | l -> l
