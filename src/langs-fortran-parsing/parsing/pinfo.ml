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

(* info.ml *)

[%%prepare_logger]

module Binding = Diffast_misc.Binding

open Common
open Labels

module Loc = Langs_common.Astloc
module L = Label
module BID = Binding.ID

let sprintf = Printf.sprintf


module Rank = struct
  type t =
    | Rnone
    | Runknown
    | Rzero
    | Rnon_zero
    | Rnon_zero_n of int


  let to_string = function
    | Rnone         -> "<none>"
    | Runknown      -> "<unknown>"
    | Rzero         -> "0"
    | Rnon_zero     -> "1+"
    | Rnon_zero_n i -> sprintf "%d" i

  let none = Rnone
  let unknown = Runknown
  let zero = Rzero
  let non_zero = Rnon_zero
  let mk i =
    if i = 0 then
      Rzero
    else
      Rnon_zero_n i

  let is_zero = function
    | Rzero -> true
    | _ -> false

  let is_non_zero = function
    | Rnon_zero
    | Rnon_zero_n _ -> true
    | _ -> false

end (* of module Rank *)



module TypeSpec = struct
  type t =
    | Unknown
    | Integer
    | Real
    | DoublePrecision
    | DoubleComplex (* nonstandard *)
    | Complex
    | Character
    | Logical
    | Type of name
    | Byte (* nonstandard *)
    | Derived of name
    | Structure of name (* for Compaq Fortran *)
    | Class of name
    | PpMacroTypeSpec of name
    | PpBranchTypeSpec of t list

  let to_string = function
    | Unknown           -> "Unknown"
    | Integer           -> "Integer"
    | Real              -> "Real"
    | DoublePrecision   -> "DoublePrecision"
    | DoubleComplex     -> "DoubleComplex"
    | Complex           -> "Complex"
    | Character         -> "Character"
    | Logical           -> "Logical"
    | Type n            -> "Type:"^n
    | Byte              -> "Byte"
    | Derived n         -> "Derived:"^n
    | Structure n       -> "Structure:"^n
    | Class n           -> "Class:"^n
    | PpMacroTypeSpec n -> "PpMacroTypeSpec:"^n
    | PpBranchTypeSpec _ -> "PpBranchTypeSpec"

  let get_name = function
    | Type n
    | Derived n
    | PpMacroTypeSpec n
    | Structure n
    | Class n
        -> n
    | _ -> raise Not_found

  let of_label = function
    | L.TypeSpec t -> begin
        match t with
        | TypeSpec.Integer           -> Integer
        | TypeSpec.Real              -> Real
        | TypeSpec.DoublePrecision   -> DoublePrecision
        | TypeSpec.DoubleComplex     -> DoubleComplex
        | TypeSpec.Complex           -> Complex
        | TypeSpec.Character         -> Character
        | TypeSpec.Logical           -> Logical
        | TypeSpec.Type n            -> Type n
        | TypeSpec.Byte              -> Byte
        | TypeSpec.Derived n         -> Derived n
        | TypeSpec.Class n           -> Class n
        | TypeSpec.PpMacroTypeSpec n -> PpMacroTypeSpec n
    end
    | lab ->
        failwith (sprintf "Pinfo.TypeSpec.of_label: not a TypeSpec: %s" (L.to_string lab))

  let is_resolved = function
    | Unknown -> false
    | _ -> true

end (* of module TypeSpec *)


module ProcInterface = struct
  type t =
    | Unknown
    | InterfaceName of name
    | DeclarationTypeSpec of TypeSpec.t

  let to_string = function
    | Unknown               -> "Unknown"
    | InterfaceName n       -> "InterfaceName:"^n
    | DeclarationTypeSpec t -> "DeclarationTypeSpec:"^(TypeSpec.to_string t)

  let get_name = function
    | InterfaceName n -> n
    | DeclarationTypeSpec t -> TypeSpec.get_name t
    | _ -> raise Not_found

  let of_label = function
    | L.Name n     -> InterfaceName n
    | L.TypeSpec _ as t -> DeclarationTypeSpec (TypeSpec.of_label t)

    | lab ->
        failwith
          (sprintf "Pinfo.ProcInterface.of_label: not a Name or TypeSpec: %s" (L.to_string lab))

  let is_interface_name = function
    | InterfaceName _ -> true
    | _ -> false

end (* of module ProcInterface *)

[%%capture_path
module Name = struct

  module IntentSpec = struct
    type t =
      | NoIntent
      | In
      | Out
      | Inout

    let to_string = function
      | NoIntent -> ""
      | In       -> "[in]"
      | Out      -> "[out]"
      | Inout    -> "[inout]"

    let of_ispec_label = function
      | IntentSpec.In    -> In
      | IntentSpec.Out   -> Out
      | IntentSpec.Inout -> Inout

  end (* module Pinfo.Name.IntentSpec *)


  module AccessSpec = struct
    type t =
      | NoAccessSpec
      | Private
      | Public

    let to_string = function
      | NoAccessSpec -> ""
      | Private      -> "[private]"
      | Public       -> "[public]"

    let is_public = function
      | Public -> true
      | Private -> false
      | _ -> failwith "Pinfo.Name.AccessSpec.is_public"

    let is_private = function
      | Private -> true
      | Public -> false
      | _ -> failwith "Pinfo.Name.AccessSpec.is_private"

  end (* of module Pinfo.Name.AccessSpec *)


  module Dimension = struct
    type t =
      | NoDimension
      | ExplicitShape of int
      | AssumedShape of int
      | DeferredShape of int
      | AssumedSize of int
      | ArraySpec of int (* unidentified array-spec *)
      | AssumedRank

    let to_string = function
      | NoDimension     -> ""
      | ExplicitShape r -> sprintf "[explicit-shape-array:rank=%d]" r
      | AssumedShape r  -> sprintf "[assumed-shape-array:rank=%d]" r
      | DeferredShape r -> sprintf "[deferred-shape-array:rank=%d]" r
      | AssumedSize r   -> sprintf "[assumed-size-array:rank=%d]" r
      | ArraySpec r     -> sprintf "[array-spec:rank=%d]" r
      | AssumedRank     -> sprintf "[assumed-rank-array]"

    let get_rank = function
      | NoDimension     -> 0
      | ExplicitShape r
      | AssumedShape r
      | DeferredShape r
      | AssumedSize r
      | ArraySpec r
        -> r
      | AssumedRank -> failwith "Pinfo.Name.Dimension.get_rank: assumed-rank"

    let of_label = function
      | L.ExplicitShapeArray r -> ExplicitShape r
      | L.AssumedShapeArray r  -> AssumedShape r
      | L.DeferredShapeArray r -> DeferredShape r
      | L.AssumedSizeArray r   -> AssumedSize r
      | L.ArraySpec r          -> ArraySpec r
      | L.AssumedRankArray     -> AssumedRank
      | L.ExplicitShapeComponentArray r -> ExplicitShape r
      | L.DeferredShapeComponentArray r -> DeferredShape r
      | lab ->
          warning_msg "invalid array-spec: %s" (L.to_string lab);
          NoDimension

    let explicit_shape r = ExplicitShape r

  end (* of module Pinfo.Name.Dimension *)


  module Codimension = struct
    type t =
      | NoCodimension
      | ExplicitCoshape
      | DeferredCoshape

    let to_string = function
      | NoCodimension   -> ""
      | ExplicitCoshape -> sprintf "[explicit_coshape_coarray]"
      | DeferredCoshape -> sprintf "[deferred_coshape_coarray]"

    let of_label = function
      | L.ExplicitCoshapeCoarray -> ExplicitCoshape
      | L.DeferredCoshapeCoarray -> DeferredCoshape
      | lab ->
          warning_msg "invalid coarray-spec: %s" (L.to_string lab);
          NoCodimension

  end (* of module Pinfo.Name.Codimension *)




  module Attribute = struct

    class accessibility = object(* (self : 'self)*)
      val mutable access_spec = AccessSpec.NoAccessSpec

      method access_spec             = access_spec
      method set_access_spec s       = access_spec <- s
      method set_access_spec_public  = access_spec <- AccessSpec.Public
      method set_access_spec_private = access_spec <- AccessSpec.Private
      method access_spec_not_set     = access_spec = AccessSpec.NoAccessSpec
      method is_public  = AccessSpec.is_public access_spec
      method is_private = AccessSpec.is_private access_spec

      method to_string =
        let buf = Buffer.create 0 in
        Buffer.add_string buf (AccessSpec.to_string access_spec);
        Buffer.contents buf

      method copy = {<>}

    end (* of class Name.Attribute.accessibility *)

    class c = object (self : 'self)

      inherit accessibility

      val mutable intent_spec       = IntentSpec.NoIntent
      val mutable dimension         = Dimension.NoDimension
      val mutable codimension       = Codimension.NoCodimension

      val mutable parameter_flag    = false
      val mutable save_flag         = false
      val mutable optional_flag     = false
      val mutable pointer_flag      = false
      val mutable target_flag       = false
      val mutable allocatable_flag  = false
      val mutable external_flag     = false
      val mutable intrinsic_flag    = false
      val mutable asynchronous_flag = false
      val mutable bind_flag         = false
      val mutable protected_flag    = false
      val mutable value_flag        = false
      val mutable volatile_flag     = false
      val mutable contiguous_flag   = false
      val mutable automatic_flag    = false
      val mutable static_flag       = false

      val mutable device_flag   = false
      val mutable managed_flag  = false
      val mutable constant_flag = false
      val mutable shared_flag   = false
      val mutable pinned_flag   = false
      val mutable texture_flag  = false


      method merge (attr : 'self) =
        begin
          match access_spec with
          | AccessSpec.NoAccessSpec -> self#set_access_spec attr#access_spec
          | _ -> ()
        end;
        begin
          match intent_spec with
          | IntentSpec.NoIntent -> self#set_intent_spec attr#intent_spec
          | _ -> ()
        end;
        begin
          match dimension with
          | Dimension.NoDimension -> self#set_dimension attr#dimension
          | _ -> ()
        end;
        begin
          match codimension with
          | Codimension.NoCodimension -> self#set_codimension attr#codimension
          | _ -> ()
        end;
        if not parameter_flag then
          self#_set_parameter attr#is_parameter;
        if not save_flag then
          self#_set_save attr#is_save;
        if not optional_flag then
          self#_set_optional attr#is_optional;
        if not pointer_flag then
          self#_set_pointer attr#is_pointer;
        if not target_flag then
          self#_set_target attr#is_target;
        if not allocatable_flag then
          self#_set_allocatable attr#is_allocatable;
        if not external_flag then
          self#_set_external attr#is_external;
        if not intrinsic_flag then
          self#_set_intrinsic attr#is_intrinsic;
        if not asynchronous_flag then
          self#_set_asynchronous attr#is_asynchronous;
        if not bind_flag then
          self#_set_bind attr#is_bind;
        if not protected_flag then
          self#_set_protected attr#is_protected;
        if not value_flag then
          self#_set_value attr#is_value;
        if not volatile_flag then
          self#_set_volatile attr#is_volatile;
        if not contiguous_flag then
          self#_set_contiguous attr#is_contiguous;
        if not automatic_flag then
          self#_set_automatic attr#is_automatic;
        if not static_flag then
          self#_set_static attr#is_static;

        if not device_flag then
          self#_set_device attr#is_device;
        if not managed_flag then
          self#_set_managed attr#is_managed;
        if not constant_flag then
          self#_set_constant attr#is_constant;
        if not shared_flag then
          self#_set_shared attr#is_shared;
        if not pinned_flag then
          self#_set_pinned attr#is_pinned;
        if not texture_flag then
          self#_set_texture attr#is_texture;

      method intent_spec = intent_spec
      method set_intent_spec i = intent_spec <- i

      method dimension = dimension
      method get_rank = Dimension.get_rank dimension
      method set_dimension d = dimension <- d

      method codimension = codimension
      method set_codimension d = codimension <- d

      method is_parameter = parameter_flag
      method _set_parameter b = parameter_flag <- b
      method set_parameter = parameter_flag <- true
      method clear_parameter = parameter_flag <- false

      method is_save = save_flag
      method _set_save b = save_flag <- b
      method set_save = save_flag <- true
      method clear_save = save_flag <- false

      method is_optional = optional_flag
      method _set_optional b = optional_flag <- b
      method set_optional = optional_flag <- true
      method clear_optional = optional_flag <- false

      method is_pointer = pointer_flag
      method _set_pointer b = pointer_flag <- b
      method set_pointer = pointer_flag <- true
      method clear_pointer = pointer_flag <- false

      method is_target = target_flag
      method _set_target b = target_flag <- b
      method set_target = target_flag <- true
      method clear_target = target_flag <- false

      method is_allocatable = allocatable_flag
      method _set_allocatable b = allocatable_flag <- b
      method set_allocatable = allocatable_flag <- true
      method clear_allocatable = allocatable_flag <- false

      method is_external = external_flag
      method _set_external b = external_flag <- b
      method set_external = external_flag <- true
      method clear_external = external_flag <- false

      method is_intrinsic = intrinsic_flag
      method _set_intrinsic b = intrinsic_flag <- b
      method set_intrinsic = intrinsic_flag <- true
      method clear_intrinsic = intrinsic_flag <- false

      method is_asynchronous = asynchronous_flag
      method _set_asynchronous b = asynchronous_flag <- b
      method set_asynchronous = asynchronous_flag <- true
      method clear_asynchronous = asynchronous_flag <- false

      method is_bind = bind_flag
      method _set_bind b = bind_flag <- b
      method set_bind = bind_flag <- true
      method clear_bind = bind_flag <- false

      method is_protected = protected_flag
      method _set_protected b = protected_flag <- b
      method set_protected = protected_flag <- true
      method clear_protected = protected_flag <- false

      method is_value = value_flag
      method _set_value b = value_flag <- b
      method set_value = value_flag <- true
      method clear_value = value_flag <- false

      method is_volatile = volatile_flag
      method _set_volatile b = volatile_flag <- b
      method set_volatile = volatile_flag <- true
      method clear_volatile = volatile_flag <- false

      method is_contiguous = contiguous_flag
      method _set_contiguous b = contiguous_flag <- b
      method set_contiguous = contiguous_flag <- true
      method clear_contiguous = contiguous_flag <- false

      method is_automatic = automatic_flag
      method _set_automatic b = automatic_flag <- b
      method set_automatic = automatic_flag <- true
      method clear_automatic = automatic_flag <- false

      method is_static = static_flag
      method _set_static b = static_flag <- b
      method set_static = static_flag <- true
      method clear_static = static_flag <- false

      method is_device = device_flag
      method _set_device b = device_flag <- b
      method set_device = device_flag <- true
      method clear_device = device_flag <- false

      method is_managed = managed_flag
      method _set_managed b = managed_flag <- b
      method set_managed = managed_flag <- true
      method clear_managed = managed_flag <- false

      method is_constant = constant_flag
      method _set_constant b = constant_flag <- b
      method set_constant = constant_flag <- true
      method clear_constant = constant_flag <- false

      method is_shared = shared_flag
      method _set_shared b = shared_flag <- b
      method set_shared = shared_flag <- true
      method clear_shared = shared_flag <- false

      method is_pinned = pinned_flag
      method _set_pinned b = pinned_flag <- b
      method set_pinned = pinned_flag <- true
      method clear_pinned = pinned_flag <- false

      method is_texture = texture_flag
      method _set_texture b = texture_flag <- b
      method set_texture = texture_flag <- true
      method clear_texture = texture_flag <- false

      method! to_string =
        let buf = Buffer.create 0 in
        Buffer.add_string buf (AccessSpec.to_string access_spec);
        Buffer.add_string buf (IntentSpec.to_string intent_spec);
        Buffer.add_string buf (Dimension.to_string dimension);
        Buffer.add_string buf (Codimension.to_string codimension);
        if parameter_flag then
          Buffer.add_string buf "[param]";
        if save_flag then
          Buffer.add_string buf "[save]";
        if optional_flag then
          Buffer.add_string buf "[opt]";
        if pointer_flag then
          Buffer.add_string buf "[ptr]";
        if target_flag then
          Buffer.add_string buf "[trgt]";
        if allocatable_flag then
          Buffer.add_string buf "[alloc]";
        if external_flag then
          Buffer.add_string buf "[extern]";
        if intrinsic_flag then
          Buffer.add_string buf "[intrinsic]";

        if asynchronous_flag then
          Buffer.add_string buf "[async]";
        if bind_flag then
          Buffer.add_string buf "[bind]";
        if protected_flag then
          Buffer.add_string buf "[protected]";
        if value_flag then
          Buffer.add_string buf "[val]";
        if volatile_flag then
          Buffer.add_string buf "[volatile]";
        if contiguous_flag then
          Buffer.add_string buf "[contiguous]";
        if automatic_flag then
          Buffer.add_string buf "[automatic]";
        if static_flag then
          Buffer.add_string buf "[static]";

        if device_flag then
          Buffer.add_string buf "[device]";
        if managed_flag then
          Buffer.add_string buf "[managed]";
        if constant_flag then
          Buffer.add_string buf "[constant]";
        if shared_flag then
          Buffer.add_string buf "[shared]";
        if pinned_flag then
          Buffer.add_string buf "[pinned]";
        if texture_flag then
          Buffer.add_string buf "[texture]";

        Buffer.contents buf

      method! copy = {<>}

    end (* of class Name.Attribute.c *)


  end (* of module Name.Attribute *)

  module Spec = struct

    type loc_of_decl =
      | Lunknown
      | Limplicit of Loc.t option
      | Lexplicit of Loc.t

    let loc_of_decl_to_string = function
      | Lunknown -> "[unknown]"
      | Limplicit loc_opt -> begin
          match loc_opt with
          | None -> "[implicit]"
          | Some loc -> sprintf "[implicit:%s]" (Loc.to_string loc)
      end
      | Lexplicit loc -> sprintf "[%s]" (Loc.to_string loc)

    let loc_of_decl_to_loc = function
      | Limplicit (Some loc) | Lexplicit loc -> loc
      | _ -> raise Not_found

    let loc_of_decl_unknown          = Lunknown
    let loc_of_decl_implicit_default = Limplicit None
    let loc_of_decl_implicit l       = Limplicit (Some l)
    let loc_of_decl_explicit l       = Lexplicit l


    class accessibility_attr_spec = object
      val mutable attr_opt = (None : Attribute.accessibility option)

      method attr = match attr_opt with Some a -> a | _ -> raise Not_found
      method attr_opt = attr_opt
      method set_attr a = attr_opt <- Some a

      method to_string =
        (opt_to_string (fun a -> a#to_string) ~prefix:":" attr_opt)
    end (* of class Pinfo.Name.Spec.accessibility_attr_spec *)

    class full_attr_spec = object
      val mutable attr_opt = (None : Attribute.c option)

      method attr = match attr_opt with Some a -> a | _ -> raise Not_found
      method attr_opt = attr_opt
      method set_attr a = attr_opt <- Some a

      method to_string =
        (opt_to_string (fun a -> a#to_string) ~prefix:":" attr_opt)
    end (* of class Pinfo.Name.Spec.full_attr_spec *)


    class spec_base ?(loc_of_decl=Lunknown) ?(id_of_decl=(-1)) ?(bid_opt=None) () = object
      val mutable bid_opt = (bid_opt : BID.t option)
      val mutable loc_of_decl = loc_of_decl
      val mutable id_of_decl = id_of_decl

      method bid = match bid_opt with Some bid -> bid | _ -> raise Not_found
      method bid_opt = bid_opt
      method set_bid b = bid_opt <- Some b

      method loc_of_decl = loc_of_decl
      method set_loc_of_decl lod = loc_of_decl <- lod

      method set_loc_of_decl_unknown =
        loc_of_decl <- loc_of_decl_unknown

      method set_loc_of_decl_implicit_default =
        loc_of_decl <- loc_of_decl_implicit_default

      method set_loc_of_decl_implicit loc =
        loc_of_decl <- loc_of_decl_implicit loc

      method set_loc_of_decl_explicit loc =
        loc_of_decl <- loc_of_decl_explicit loc

      method id_of_decl = id_of_decl
      method set_id_of_decl i = id_of_decl <- i

      method to_string =
        "@"^(loc_of_decl_to_string loc_of_decl)^
        (match bid_opt with Some bid -> BID.to_string bid | None -> "")

    end (* of class Pinfo.Name.Spec.spec_base *)


    class object_spec ?(loc_of_decl=Lunknown) ?(id_of_decl=(-1)) ?(bid_opt=None) () = object
      inherit spec_base ~loc_of_decl ~id_of_decl ~bid_opt () as super
      inherit! accessibility_attr_spec as super_attr

      method! to_string =
        super_attr#to_string^
        super#to_string
    end

    let make_public_object_spec() =
      let ospec = new object_spec() in
      let a = new Attribute.accessibility in
      a#set_access_spec_public;
      ospec#set_attr a;
      ospec

    class data_object_spec
        ?(loc_of_decl=Lunknown)
        ?(id_of_decl=(-1))
        ?(bid_opt=None)
        ?(type_spec=TypeSpec.Unknown)
        ()
        =
      object
        inherit spec_base ~loc_of_decl ~id_of_decl ~bid_opt () as super
        inherit! full_attr_spec as super_attr

        val mutable type_spec = type_spec

        method set_type_spec ty = type_spec <- ty
        method type_spec = type_spec

        method! to_string =
          (TypeSpec.to_string type_spec)^
          super_attr#to_string^
          super#to_string

      end (* of class Pinfo.Name.Spec.data_object_spec *)

    class procedure_spec
        ?(loc_of_decl=Lunknown)
        ?(id_of_decl=(-1))
        ?(bid_opt=None)
        proc_interface
        =
    object
      inherit spec_base ~loc_of_decl ~id_of_decl ~bid_opt () as super
      inherit! full_attr_spec as super_attr

      method proc_interface = proc_interface

      method! to_string =
        (ProcInterface.to_string proc_interface)^
        super_attr#to_string^
        super#to_string

    end (* of class Pinfo.Name.Spec.procedure_spec *)

    class intrinsic_procedure_spec rank = object
      method rank = rank (* the rank of the result *)
      method to_string =
        sprintf "%s" (Rank.to_string rank)
    end (* of class Pinfo.Name.Spec.procedure_spec *)


    type t =
      | Unknown
      | DataObject of data_object_spec
      | DerivedType of frame_v * object_spec
      | InterfaceBlock
      | IntrinsicFunction of intrinsic_procedure_spec
      | IntrinsicSubroutine
      | FunctionSubprogram of object_spec
      | SubroutineSubprogram of object_spec
      | SeparateModuleSubprogram of object_spec
      | Generic of object_spec
      | Procedure of procedure_spec
      | NamelistGroup of object_spec
      | MainProgram
      | Module of (unit -> name Xset.t) * frame_v
      | ModuleEntity (* unknown module entity *)
      | BlockData
      | CommonBlock (* has save attr *)
      | AssociateName
      | External of name (* module name *) * name
      | InterfaceName of name
      | LindaOperation
      | Object of object_spec

    and frame_v = { find : name -> t; add  : name -> t -> unit }

    let unknown = Unknown
    let module_entity = ModuleEntity
    let intrinsic_subroutine = IntrinsicSubroutine

    let mkframev ~add ~find = { find=find; add=add }

    let to_string = function
      | Unknown                    -> "Unknown"
      | DataObject dspec           -> "DataObject:"^dspec#to_string
      | DerivedType(_, ospec)      -> "DerivedType"^ospec#to_string
      | InterfaceBlock             -> "InterfaceBlock"
      | IntrinsicFunction pspec    -> "IntrinsicFunction:"^pspec#to_string
      | IntrinsicSubroutine        -> "IntrinsicSubroutine"
      | FunctionSubprogram ospec   -> "FunctionSubprogram"^ospec#to_string
      | SubroutineSubprogram ospec -> "SubroutineSubprogram"^ospec#to_string
      | SeparateModuleSubprogram ospec -> "SeparateModuleSubprogram"^ospec#to_string
      | Generic ospec              -> "Generic"^ospec#to_string
      | Procedure pspec            -> "Procedure:"^pspec#to_string
      | NamelistGroup ospec        -> "NamelistGroup"^ospec#to_string
      | MainProgram                -> "MainProgram"
      | Module _                   -> "Module"
      | ModuleEntity               -> "ModuleEntity"
      | BlockData                  -> "BlockData"
      | CommonBlock                -> "CommonBlock"
      | AssociateName              -> "AssociateName"
      | External(m, n)             -> "External:"^m^":"^n
      | InterfaceName n            -> "InterfaceName:"^n
      | LindaOperation             -> "LindaOperation"
      | Object ospec               -> "Object"^ospec#to_string

    let filter_out_ambiguous =
      List.filter
        (function
          | Unknown | ModuleEntity -> false
          | _ -> true
        )

    let is_resolved = function
      | DataObject o -> TypeSpec.is_resolved o#type_spec
      | Unknown -> false
      | _ -> true

    let is_namelist_group = function
      | NamelistGroup _ -> true
      | _ -> false

    let is_procedure = function
      | IntrinsicFunction _
      | IntrinsicSubroutine
      | FunctionSubprogram _
      | SubroutineSubprogram _
      | SeparateModuleSubprogram _
      | Generic _
      | Procedure _
        -> true
      | _ -> false

    let is_function = function
      | IntrinsicFunction _
      | FunctionSubprogram _
      | Generic _              -> true
      | _ -> false

    let is_intrinsic_procedure = function
      | IntrinsicFunction _
      | IntrinsicSubroutine -> true
      | _ -> false

    let is_generic = function
      | Generic _ -> true
      | _ -> false

    let is_external = function
      | External _ -> true
      | _ -> false

    let decompose_external = function
      | External(m, n) -> (m, n)
      | _ -> invalid_arg "Pinfo.Name.Spec.decompose_external"

    let is_linda_operation = function
      | LindaOperation -> true
      | _ -> false

    let rec contain_generic = function
      | [] -> false
      | spec::rest ->
          if is_generic spec then
            true
          else
            contain_generic rest

    let is_module = function
      | Module _ -> true
      | _ -> false

    let is_derived_type = function
      | DerivedType _ -> true
      | _ -> false

    let is_data_object_spec = function
      | DataObject _ -> true
      | _ -> false

    let has_object_spec = function
      | DerivedType(_, _)
      | FunctionSubprogram _
      | SubroutineSubprogram _
      | SeparateModuleSubprogram _
      | Generic _
      | NamelistGroup _
      | Object _ -> true
      | _ -> false

    let has_data_object_spec = function
      | DataObject _ -> true
      | _ -> false

    let get_data_object_spec = function
      | DataObject dspec -> dspec
      | _ -> raise Not_found

    let has_data_object_attr spec =
      try
        match (get_data_object_spec spec)#attr_opt with
        | None -> false
        | _ -> true
      with
        Not_found -> false

    (*let get_data_object_attr spec =
      (get_data_object_spec spec)#attr*)

    let has_procedure_spec = function
      | Procedure _ -> true
      | _ -> false

    let get_procedure_spec = function
      | Procedure pspec -> pspec
      | _ -> raise Not_found

    let has_procedure_attr spec =
      let b =
        try
          match (get_procedure_spec spec)#attr_opt with
          | None -> false
          | _ -> true
        with
          Not_found -> false
      in
      (* [%debug_log "%s --> %B" (N.Spec.to_string spec) b]; *)
      b

    let get_object_spec = function
      | DerivedType(_, ospec)
      | FunctionSubprogram ospec
      | SubroutineSubprogram ospec
      | SeparateModuleSubprogram ospec
      | Generic ospec
      | NamelistGroup ospec
      | Object ospec -> ospec
      | _ -> raise Not_found

    let has_object_attr spec =
      let b =
        try
          match (get_object_spec spec)#attr_opt with
          | None -> false
          | _ -> true
        with
          Not_found -> false
      in
      (* [%debug_log "%s --> %B" (N.Spec.to_string spec) b]; *)
      b

    let get_data_object_attr spec =
      (get_data_object_spec spec)#attr

    let get_procedure_attr spec =
      (get_procedure_spec spec)#attr

    let get_object_attr spec =
      (get_object_spec spec)#attr

    let get_accessibility_attr = function
      | DataObject dspec -> (dspec#attr :> Attribute.accessibility)
      | DerivedType(_, ospec)
      | FunctionSubprogram ospec
      | SubroutineSubprogram ospec
      | SeparateModuleSubprogram ospec
      | Generic ospec
      | NamelistGroup ospec
      | Object ospec -> ospec#attr
      | Procedure pspec -> (pspec#attr :> Attribute.accessibility)
      | _ -> raise Not_found

    let has_accessibility_attr spec =
      try
        let _ = get_accessibility_attr spec in
        true
      with
        Not_found -> false

    let get_finder = function
      | DerivedType(fv, _)
      | Module(_, fv)
        -> fv.find
      | _ -> raise Not_found

    let get_adder = function
      | DerivedType(fv, _)
      | Module(_, fv)
        -> fv.add
      | _ -> raise Not_found

    let get_domain = function
      | Module(mkdom, _) -> mkdom()
      | _ -> failwith "Name.Spec.get_domain"

    let get_loc_of_decl = function
      | DataObject dspec -> dspec#loc_of_decl
      | DerivedType(_, ospec)
      | FunctionSubprogram ospec
      | SubroutineSubprogram ospec
      | SeparateModuleSubprogram ospec
      | Generic ospec
      | NamelistGroup ospec
      | Object ospec -> ospec#loc_of_decl
      | _ -> raise Not_found

    let has_decl spec =
      try
        let lod = get_loc_of_decl spec in
        lod <> Lunknown
      with
        _ -> false

    let set_loc_of_decl lod = function
      | DataObject dspec -> dspec#set_loc_of_decl lod
      | DerivedType(_, ospec)
      | FunctionSubprogram ospec
      | SubroutineSubprogram ospec
      | SeparateModuleSubprogram ospec
      | Generic ospec
      | NamelistGroup ospec
      | Object ospec -> ospec#set_loc_of_decl lod
      | _ -> ()

    let set_id_of_decl lod = function
      | DataObject dspec -> dspec#set_id_of_decl lod
      | DerivedType(_, ospec)
      | FunctionSubprogram ospec
      | SubroutineSubprogram ospec
      | SeparateModuleSubprogram ospec
      | Generic ospec
      | NamelistGroup ospec
      | Object ospec -> ospec#set_id_of_decl lod
      | _ -> ()

    let mkobj ?(loc_of_decl=Lunknown) ?(id_of_decl=(-1)) ?(bid_opt=None) () =
      let spec = new object_spec ~loc_of_decl ~id_of_decl ~bid_opt () in
      let a = new Attribute.accessibility in
      spec#set_attr a;
      spec

    let mkproc ?(loc_of_decl=Lunknown) ?(id_of_decl=(-1)) ?(bid_opt=None) pi =
      let spec = new procedure_spec ~loc_of_decl ~id_of_decl ~bid_opt pi in
      let a = new Attribute.c in
      spec#set_attr a;
      spec

    let mkfunction ospec      = FunctionSubprogram ospec
    let mksubroutine ospec    = SubroutineSubprogram ospec
    let mkseparate_module_subprogram ospec = SeparateModuleSubprogram ospec
    let mkgeneric ospec       = Generic ospec
    let mknamelistgroup ospec = NamelistGroup ospec
    let mkderivedtype f ospec = DerivedType(f, ospec)
    let mkprocedure pspec     = Procedure pspec
    let mkmodule mkdom f      = Module(mkdom, f)
    let mkintrinsicfunc pspec = IntrinsicFunction pspec
    let mkobject ospec        = Object ospec

    let mkdobj
        ?(loc_of_decl=Lunknown)
        ?(id_of_decl=(-1))
        ?(bid_opt=None)
        ?(type_spec=TypeSpec.Unknown)
        attr_opt =
      let spec = new data_object_spec ~loc_of_decl ~id_of_decl ~bid_opt ~type_spec () in
      begin
        match attr_opt with
        | Some a -> spec#set_attr a
        | None -> ()
      end;
      DataObject spec

    let mkext mname uname =
      External(String.lowercase_ascii mname, String.lowercase_ascii uname)

    let mkiname n = InterfaceName n

    let make_public_subroutine() =
      SubroutineSubprogram (make_public_object_spec())

    let make_public_function() =
      FunctionSubprogram (make_public_object_spec())

    let get_access_spec nspec =
      let fail() = failwith "Pinfo.Name.Spec.get_access_spec" in
      match nspec with
      | DataObject dospec -> begin
          try
            dospec#attr#access_spec
          with
            Not_found -> fail()
      end
      | DerivedType(_, ospec)
      | FunctionSubprogram ospec
      | SubroutineSubprogram ospec
      | Generic ospec
      | NamelistGroup ospec
      | Object ospec -> begin
          try
            ospec#attr#access_spec
          with
            Not_found -> fail()
      end
      | Procedure pspec -> begin
          try
            pspec#attr#access_spec
          with
            Not_found -> fail()
      end
      | _ -> fail()

    let is_public nspec =
      AccessSpec.is_public (get_access_spec nspec)


  end (* of module Pinfo.Name.Spec *)





  exception Spec_found of Spec.t
  exception Specs_found of Spec.t list


  module ScopingUnit = struct

    type t =
      | Program
      | DerivedTypeDef of name
      | MainProgram of name option * bool ref (* headed or not *)
      | FunctionSubprogram of name
      | SubroutineSubprogram of name
      | SeparateModuleSubprogram of name
      | Module of name
      | BlockData of name option
      | BlockConstruct of name option (* F2003 *)
      | StructureDecl of name option (* Compaq Fortran *)

    let mkmodule n = Module n
    let mkderivedtypedef n = DerivedTypeDef n

    let to_string = function
      | Program                -> "Program"
      | DerivedTypeDef n       -> "DerivedTypeDefinition:"^n
      | MainProgram(n_opt, hd) ->
          sprintf "MainProgram(%s%B)" (string_opt_to_string ~prefix:":" ~suffix:"," n_opt) !hd

      | FunctionSubprogram n       -> "FunctionSubprogram:"^n
      | SubroutineSubprogram n     -> "SubroutineSubprogram:"^n
      | SeparateModuleSubprogram n -> "SeparateModuleSubprogram:"^n
      | Module n               -> "Module:"^n
      | BlockData n_opt        -> "BlockData"^(string_opt_to_string ~prefix:":" n_opt)
      | BlockConstruct n_opt   -> "BlockConstruct"^(string_opt_to_string ~prefix:":" n_opt)
      | StructureDecl n_opt    -> "StructureDecl"^(string_opt_to_string ~prefix:":" n_opt)

    let copy = function
      | MainProgram(n_opt, hd) -> MainProgram(n_opt, ref !hd)
      | s -> s
  end

  module ImplicitSpec = struct

    class c (type_spec : TypeSpec.t) = object

      val mutable letter_spec_list = ([] : (Char.t * Char.t) list)

      val mutable bid_opt = (None : BID.t option)

      val mutable loc_of_decl = Spec.loc_of_decl_implicit_default

      val mutable id_of_decl = -1

      method set_bid bid = bid_opt <- Some bid
      method bid_opt = bid_opt

      method loc_of_decl = loc_of_decl
      method set_loc_of_decl lod = loc_of_decl <- lod

      method id_of_decl = id_of_decl
      method set_id_of_decl iod = id_of_decl <- iod

      method type_spec = type_spec

      method letter_spec_list = letter_spec_list
      method set_letter_spec_list l = letter_spec_list <- l

      method check c =
        [%debug_log "c=%d" c];
        let rec chk = function
          | [] -> false
          | (f, t)::rest ->
              let fc = Char.code f in
              let tc = Char.code t in
              [%debug_log "from=%d to=%d" fc tc];
              let b = fc <= c && c <= tc in
              if b then
                true
              else
                chk rest
        in
        chk letter_spec_list

      method to_string =
        sprintf "%s:%s"
          (TypeSpec.to_string type_spec)
          (Xlist.to_string
             (fun (c0, c1) ->
               if c0 = c1 then
                 sprintf "%c" c0
               else
               sprintf "%c-%c" c0 c1
             ) ";" letter_spec_list)

    end (* of class ImplicitSpec.c *)

    let letter_spec_of_label = function
      | L.LetterSpec(f, t_opt) -> begin
          let fh = Char.lowercase_ascii f.[0] in
          let th =
            match t_opt with
            | Some t -> Char.lowercase_ascii t.[0]
            | None -> fh
          in
          [%debug_log "%c-%c" fh th];
          Some (fh, th)
      end
      | l ->
          warning_msg "not a letter-spec: %s" (L.to_simple_string l);
          None



  end (* of module ImplicitSpec *)



  class frame (scope : ScopingUnit.t) = object (self)

    val scope = scope

    val tbl = (Hashtbl.create 0 : (name, Spec.t) Hashtbl.t)
    val regexp_tbl = (Hashtbl.create 0 : (name, Spec.t) Hashtbl.t)

    val mutable implicit_spec_list = (None : ImplicitSpec.c list option)

    (* it is assumed to be an integer if n starts with [i-n] and a real otherwise *)
    val default_implicit_spec_list =
      let int_spec = new ImplicitSpec.c TypeSpec.Integer in
      let real_spec = new ImplicitSpec.c TypeSpec.Real in
      int_spec#set_letter_spec_list [('i','n')];
      real_spec#set_letter_spec_list [('a','h');('o','z')];
      [int_spec;real_spec]

    val mutable default_accessibility =  AccessSpec.NoAccessSpec

    val mutable used_module_list = []

    (* *)

    method iter f = Hashtbl.iter f tbl

    method add_used_module (m : name) =
      let m_ = String.lowercase_ascii m in
      if not (List.mem m_ used_module_list) then
        used_module_list <- m_ :: used_module_list

    method iter_used_modules f = List.iter f used_module_list

    method has_open_module_use = used_module_list <> []

    method default_accessibility = default_accessibility

    method set_default_accessibility_public =
      default_accessibility <- AccessSpec.Public

    method set_default_accessibility_private =
      default_accessibility <- AccessSpec.Private


    method scope = scope


    method post_find n =
      [%debug_log "name=\"%s\"" n];
      let c = Char.code (Char.lowercase_ascii n.[0]) in
      let rec find = function
        | [] -> raise Not_found
        | ispec::rest ->
            [%debug_log "checking: %s" ispec#to_string];
            if ispec#check c then
              ispec
            else
              find rest
      in
      let il =
        match implicit_spec_list with
        | None -> default_implicit_spec_list
        | Some [] -> []
        | Some l -> l @ default_implicit_spec_list
      in
      let ispec = find il in
      let type_spec = ispec#type_spec in
      let loc_of_decl = ispec#loc_of_decl in
      let id_of_decl = ispec#id_of_decl in
      let bid_opt = ispec#bid_opt in
      let dobj = Spec.mkdobj ~loc_of_decl ~id_of_decl ~bid_opt ~type_spec None in
      [%debug_log "found: %s" (Spec.to_string dobj)];
      dobj

    method set_implicit_spec_list ispec_nds =
      [%debug_log "[%s]" (String.concat ";" (List.map (fun x -> x#to_string) ispec_nds))];
      implicit_spec_list <- Some ispec_nds

    method add_implicit_spec_list ispec_nds =
      [%debug_log "[%s]" (String.concat ";" (List.map (fun x -> x#to_string) ispec_nds))];
      match implicit_spec_list with
      | None -> implicit_spec_list <- Some ispec_nds
      | Some l -> implicit_spec_list <- Some (ispec_nds @ l)

(*
    method post_find_all n =
      try
        [self#post_find n]
      with
        Not_found -> (* [] *)
          let l = ref [] in
          self#iter_used_modules (fun m -> l := (Spec.External(m, String.lowercase_ascii n)) :: !l);
          !l
*)
    method get_ext_names n =
      let l = ref [] in
      self#iter_used_modules (fun m -> l := (Spec.mkext m n) :: !l);
      !l

    method post_mem n =
      try
        ignore (self#post_find n);
        true
      with
        Not_found -> false

    method find_all_data_object n =
      List.filter (fun s -> Spec.is_data_object_spec s) (self#find_all n)

    method find_all_object n =
      List.filter (fun s -> Spec.has_object_spec s) (self#find_all n)

    method add n spec =
      [%debug_log "n=%s" n];
      let n_ = String.lowercase_ascii n in
      [%debug_log "n_=%s" n_];
      let is_regexp = String.contains n_ '|' in
      [%debug_log "is_regexp=%B" is_regexp];

      let tbl_add =
        if is_regexp then
          Hashtbl.add regexp_tbl
        else
          Hashtbl.add tbl
      in

      let specs = self#_find_all n_ in
      let attrs =
        Xlist.filter_map
          (fun s ->
            try
              Some (Spec.get_data_object_attr s)
            with
              Not_found -> None
          ) specs
      in
      let aattrs =
        Xlist.filter_map
          (fun s ->
            try
              Some (Spec.get_object_attr s)
            with
              Not_found -> None
          ) specs
      in

      match spec with
      | Spec.DataObject dospec -> begin
          if aattrs = [] && attrs = [] then begin
            tbl_add n_ spec
          end
          else begin
            let attr =
              try
                dospec#attr
              with
                Not_found ->
                  let a = new Attribute.c in
                  dospec#set_attr a;
                  a
            in
            if List.exists (fun a -> try a#is_private with _ -> false) aattrs then
              attr#set_access_spec_private;

            List.iter
              (fun a ->

                if a#access_spec <> AccessSpec.NoAccessSpec then
                  attr#set_access_spec a#access_spec;

                if a#intent_spec <> IntentSpec.NoIntent then
                  attr#set_intent_spec a#intent_spec;

                if a#dimension <> Dimension.NoDimension then
                  attr#set_dimension a#dimension;

                if a#is_parameter then
                  attr#set_parameter;

                if a#is_save then
                  attr#set_save;

                if a#is_optional then
                  attr#set_optional;

                if a#is_pointer then
                  attr#set_pointer;

                if a#is_target then
                  attr#set_target;

                if a#is_allocatable then
                  attr#set_allocatable;

                if a#is_external then
                  attr#set_external;

                if a#is_intrinsic then
                  attr#set_intrinsic
              ) (List.rev attrs);

            tbl_add n_ spec
          end
      end

      | Spec.DerivedType(_, ospec)
      | Spec.FunctionSubprogram ospec
      | Spec.SubroutineSubprogram ospec
      | Spec.SeparateModuleSubprogram ospec
      | Spec.Generic ospec
      | Spec.NamelistGroup ospec -> begin
          try
            let attr = ospec#attr in
            if
              (List.exists (fun a -> try a#is_private with _ -> false) aattrs) ||
              (List.exists (fun a -> try a#is_private with _ -> false) attrs)
            then
              attr#set_access_spec_private;
            tbl_add n_ spec
          with
            Not_found -> assert false
      end

      | _ -> tbl_add n_ spec



    method fold : 'a. (name -> Spec.t -> 'a -> 'a) -> 'a -> 'a =
      fun f ini -> Hashtbl.fold f tbl ini

    method _find n =
      (*[%debug_log "\"%s\"" n];*)
      try
        Hashtbl.find tbl n
      with
        Not_found ->
          try
            Hashtbl.find regexp_tbl n
          with
            Not_found ->
              try
                Hashtbl.iter
                  (fun pat spec ->
                    let re = Str.regexp ("^"^pat^"$") in
                    if Str.string_match re n 0 then
                      raise (Spec_found spec)
                  ) regexp_tbl;
                raise Not_found
              with
                Spec_found spec -> spec

    method find n = self#_find (String.lowercase_ascii n)

    method _find_all n =
      (*[%debug_log "\"%s\"" n];*)
      let l = Hashtbl.find_all tbl n in
      if l = [] then
        let l = Hashtbl.find_all regexp_tbl n in
        if l = [] then
          let l0 = ref [] in
          Hashtbl.iter
            (fun pat spec ->
              [%debug_log "pat=%s" pat];
              let re = Str.regexp ("^"^pat^"$") in
              if Str.string_match re n 0 then
                l0 := spec :: !l0
            ) regexp_tbl;
          !l0
        else
          l
      else
        l

    method find_all n = self#_find_all (String.lowercase_ascii n)

    method _mem n =
      if Hashtbl.mem tbl n then
        true
      else if Hashtbl.mem regexp_tbl n then
        true
      else
        try
          Hashtbl.iter
            (fun pat _ ->
              let re = Str.regexp ("^"^pat^"$") in
              if Str.string_match re n 0 then
                raise Exit
            ) regexp_tbl;
          false
        with
          Exit -> true

    method mem n = self#_mem (String.lowercase_ascii n)

    method _copy =
      {<scope = ScopingUnit.copy scope;
        tbl = tbl;
        regexp_tbl = regexp_tbl;
        >}

    method copy =
      {<scope = ScopingUnit.copy scope;
        tbl = Hashtbl.copy tbl;
        regexp_tbl = Hashtbl.copy regexp_tbl;
        (*implicit_spec_list = implicit_spec_list;
        default_accessibility = default_accessibility;
        used_module_list = used_module_list;*)
        >}

    method to_string =
      let buf = Buffer.create 0 in
      let buf_add = Buffer.add_string buf in
      let nl() = buf_add "\n" in
      buf_add "scope:\n";
      buf_add (ScopingUnit.to_string scope);
      nl();
      buf_add "default_accessibility:\n";
      buf_add (AccessSpec.to_string default_accessibility);
      nl();
      buf_add "used_module_list:\n";
      buf_add (Xlist.to_string (fun x -> x) ";" used_module_list);
      nl();
      buf_add "bound names:\n";
      Hashtbl.iter
        (fun n spc ->
          buf_add (sprintf "%s -> %s\n" n (Spec.to_string spc))
        ) tbl;
      Hashtbl.iter
        (fun n spc ->
          buf_add (sprintf "%s -> %s\n" n (Spec.to_string spc))
        ) regexp_tbl;

      Buffer.contents buf


  end (* of class Pinfo.Name.frame *)

(*
  let copy_frame frm =
  let f = new frame frm#scope in
  f#_set_tbl frm#_tbl;
  f
 *)



  exception Frame_found of frame


  let intrinsic_function_list =
    [
     (* intrinsic functions *)
     new Spec.intrinsic_procedure_spec (Rank.mk 0),
     [
       "abs";
       "achar";
       "acos";
       "acosh";
       "adjustl";
       "adjustr";
       "aimag";
       "aint";
       "allocated";
       "alog";
       "alog10";
       "amax0";
       "amax1";
       "amin0";
       "amin1";
       "amod";
       "anint";
       "asin";
       "associated";
       "atan";
       "atan2";
       "atanh";
       "bessel_j0";
       "bessel_j1";
       "bessel_jn";
       "bessel_y0";
       "bessel_y1";
       "bessel_yn";
       "bge";
       "bgt";
       "ble";
       "blt";
       "bit_size";
       "cabs";
       "ccos";
       "ceiling";
       "cexp";
       "char";
       "clog";
       "cmplx";
       "command_argument_count";
       "conjg";
       "cos";
       "cosh";
       "csin";
       "csqrt";
       "dabs";
       "dacos";
       "dasin";
       "datan";
       "datan2";
       "dble";
       "dcos";
       "dcosh";
       "ddim";
       "dexp";
       "digits";
       "dim";
       "dint";
       "dlog";
       "dlog10";
       "dmax1";
       "dmin1";
       "dmod";
       "dnint";
       "dprod";
       "dsin";
       "dsinh";
       "dshiftl";
       "dshiftr";
       "dsqrt";
       "dtan";
       "dtanh";
       "dot_product";
       "dprod";
       "epsilon";
       "erf";
       "erfc";
       "erfc_scaled";
       "exp";
       "exponent";
       "extends_type_of";
       "float";
       "floor";
       "fraction";
       "gamma";
       "huge";
       "hypot";
       "iabs";
       "iachar";
       "iand";
       "ibclr";
       "ibits";
       "ibset";
       "ichar";
       "idim";
       "idint";
       "idnint";
       "ieor";
       "ifix";
       "image_index";
       "index";
       "int";
       "ior";
       "ishft";
       "ishftc";
       "isign";
       "is_contiguous";
       "is_iostat_end";
       "is_iostat_eor";
       "kind";
       "leadz";
       "len";
       "len_trim";
       "lge";
       "lgt";
       "lle";
       "llt";
       "log";
       "log_gamma";
       "log10";
       "logical";
       "maskl";
       "maskr";
       "max";
       "max0";
       "max1";
       "maxexponent";
       "merge_bits";
       "min";
       "min0";
       "min1";
       "minexponent";
       "mod";
       "modulo";
       "nearest";
       "new_line";
       "nint";
       "not";
       "num_images";
       "precision";
       "present";
       "radix";
       "range";
       "real";
       "repeat";
       "rrspacing";
       "same_type_as";
       "scale";
       "scan";
       "selected_char_kind";
       "selected_int_kind";
       "selected_real_kind";
       "set_exponent";
       "shifta";
       "shiftl";
       "shiftr";
       "sign";
       "sin";
       "sinh";
       "size";
       "sngl";
       "spacing";
       "sqrt";
       "storage_size";
       "tan";
       "tanh";
       "tiny";
       "trailz";
       "trim";
       "verify";
     ];
     new Spec.intrinsic_procedure_spec (Rank.mk 2),
     [ "transpose";
     ];
     new Spec.intrinsic_procedure_spec (Rank.unknown),
     [
      "all";
      "any";
      "btest";
      "count";
      "cshift";
      "eoshift";
      "findloc";
      "fstat";
      "iall";
      "iany";
      "iparity";
      "lbound";
      "lcobound";
      "matmul";
      "maxloc";
      "maxval";
      "merge";
      "minloc";
      "minval";
      "norm2";
      "pack";
      "parity";
      "popcnt";
      "poppar";
      "product";
      "reshape";
      "shape";
      "spread";
      "sum";
      "this_image";
      "transfer";
      "ubound";
      "ucobound";
      "unpack";
    ];
   ]

  let intrinsic_subroutine_list =
    [
     (* intrinsic subroutine *)
     "atomic_define";
     "atomic_ref";
     "cpu_time";
     "date_and_time";
     "execute_command_line";
     "get_command";
     "get_command_argument";
     "get_environment_variable";
     "move_alloc";
     "mvbits";
     "random_number";
     "random_seed";
     "system_clock";
   ]


  let omp_subroutine_list =
    [ "omp_destroy_lock";
      "omp_destroy_nest_lock";
      "omp_get_schedule";
      "omp_init_lock";
      "omp_init_nest_lock";
      "omp_set_dynamic";
      "omp_set_lock";
      "omp_set_max_active_levels";
      "omp_set_nest_lock";
      "omp_set_nested";
      "omp_set_num_threads";
      "omp_set_schedule";
      "omp_unset_lock";
      "omp_unset_nest_lock";
    ]

  let omp_function_list =
    [ "omp_get_active_level";
      "omp_get_ancestor_therad_num";
      "omp_get_cancellation";
      "omp_get_default_device";
      "omp_get_dynamic";
      "omp_get_level";
      "omp_get_max_active_levels";
      "omp_get_max_threads";
      "omp_get_nested";
      "omp_get_num_devices";
      "omp_get_num_procs";
      "omp_get_num_teams";
      "omp_get_num_threads";
      "omp_get_proc_bind";
      "omp_get_schedule";
      "omp_get_team_num";
      "omp_get_team_size";
      "omp_get_thread_limit";
      "omp_get_thread_num";
      "omp_get_wtick";
      "omp_get_wtime";
      "omp_in_final";
      "omp_in_parallel";
      "omp_is_initial_device";
      "omp_test_lock";
      "omp_test_nest_lock";
      "omp_get_num_threads";
    ]

  let linda_operation_list =
    [ "in";
      "rd";
      "out";
      "eval";
      "inp";
      "rdp";
    ]

  let linda_function_list =
    [ "flexit";
      "flhalt";
      "flintoff";
      "flinton";
      "floffexit";
      "flonexit";
      "flprocs";
   ]

  let gnu_function_list =
    [ "%val";   (* gfortran, Compaq Fortran *)
      "%ref";   (* gfortran, Compaq Fortran *)
      "%loc";   (* gfortran, Compaq Fortran *)
      "%descr"; (* Compaq Fortran *)

      "abort"; (* *)
      "access"; (* *)
      "alarm"; (* *)
      "besj0"; (* *)
      "besj1"; (* *)
      "besjn"; (* *)
      "besy0"; (* *)
      "besy1"; (* *)
      "besyn"; (* *)
      "complex"; (* *)
      "ctime"; (* *)
      "dbesj0"; (* *)
      "dbesj1"; (* *)
      "dbesjn"; (* *)
      "dbesy0"; (* *)
      "dbesy1"; (* *)
      "dbesyn"; (* *)
      "derf"; (* *)
      "derfc"; (* *)
      "etime"; (* *)
      "fdate"; (* *)
      "fnum"; (* *)
      "ftell"; (* *)
      "getcwd"; (* *)
      "getgid"; (* *)
      "getpid"; (* *)
      "getuid"; (* *)
      "hostnm"; (* *)
      "ierrno"; (* *)
      "imag"; (* *)
      "imagpart"; (* *)
      "int8"; (* *)
      "irand"; (* *)
      "isatty"; (* *)
      "lnblnk"; (* *)
      "lstat"; (* *)
      "mclock"; (* *)
      "mclock8"; (* *)
      "rank"; (* *)
      "realpart"; (* *)
      "second"; (* *)
      "time8"; (* *)
      "ttynam"; (* *)
   ]

  let gnu_subroutine_list =
    [ "chdir"; (* *)
      "chmod"; (* *)
      "dtime"; (* *)
      "fget"; (* *)
      "fgetc"; (* *)
      "fput"; (* *)
      "fputc"; (* *)
      "fseek"; (* *)
      "gerror"; (* *)
      "getarg"; (* *)
      "getenv"; (* *)
      "getlog"; (* *)
      "gmtime"; (* *)
      "itime"; (* *)
      "kill"; (* *)
      "ltime"; (* *)
      "perror"; (* *)
      "rename"; (* *)
      "sleep"; (* *)
      "srand"; (* *)
      "symlnk"; (* *)
      "system"; (* *)
      "umask"; (* *)
      "unlink"; (* *)
   ]

  let compaq_function_list =
    [ "acosd";
      "aimax0";
      "aimin0";
      "ajmax0";
      "ajmin0";
      "and";
      "asind";
      "asm";
      "atan2d";
      "atand";
      "bitest";
      "bjtest";
      "cdabs";
      "cdcos";
      "cdexp";
      "cdlog";
      "cdsin";
      "cdsqrt";
      "cosd";
      "cotan";
      "cotand";
      "dacosd";
      "dasind";
      "dasm";
      "datan2";
      "datan2d";
      "datand";
      "date";
      "dcmplx";
      "dconjg";
      "dcosd";
      "dcotan";
      "dcotand";
      "dfloat";
      "dfloti";
      "dflotj";
      "dimag";
      "dreal";
      "dsind";
      "dtand";
      "eof";
      "errsns";
      "exit";
      "fasm";
      "floati";
      "floatj";
      "fp_class";
      "free";
      "hfix";
      "iargptr";
      "ibchng";
      "idate";
      "iiabs";
      "iiand";
      "iibclr";
      "iibset";
      "iidim";
      "iidint";
      "iidnnt";
      "iieor";
      "iifix";
      "iint";
      "iior";
      "iishft";
      "iishftc";
      "iisign";
      "imax0";
      "imax1";
      "imin0";
      "imin1";
      "imod";
      "imvbits";
      "inint";
      "inot";
      "int1";
      "int2";
      "int4";
      "isha";
      "ishc";
      "ishl";
      "isnan";
      "izext";
      "jfix";
      "jiand";
      "jibclr";
      "jibits";
      "jibset";
      "jidim";
      "jidint";
      "jidnnt";
      "jieor";
      "jishft";
      "jishftc";
      "jisign";
      "jmax0";
      "jmax1";
      "jmin0";
      "jmin1";
      "jmod";
      "jmvbits";
      "jnint";
      "jnot";
      "jzext";
      "leadz";
      "loc";
      "lshift";
      "malloc";
      "mult_high";
      "nworkers";
      "or";
      "popcnt";
      "poppar";
      "ran";
      "randu";
      "rshift";
      "secnds";
      "sind";
      "sizeof";
      "tand";
      "time";
      "tailz";
      "xor";
      "zabs";
      "zcos";
      "zexp";
      "zext";
      "zlog";
      "zsin";
      "zsqrt";

(* for OpenVMS, Tru64, Linux *)
      "cqabs";
      "cqcos";
      "cqexp";
      "cqlog";
      "cqsin";
      "cqsqrt";
      "dbleq";
      "iiqint";
      "iiqnnt";
      "iqint";
      "iqnint";
      "jiqint";
      "jiqnnt";
      "kiqint";
      "kiqnnt";
      "qabs";
      "qacos";
      "qacosd";
      "qasin";
      "qasind";
      "qatan";
      "qatan2";
      "qatan2d";
      "qatand";
      "qcmplx";
      "qconjg";
      "qcos";
      "qcosd";
      "qcosh";
      "qcotan";
      "qcotand";
      "qdim";
      "qexp";
      "qext";
      "qextd";
      "qfloat";
      "qimag";
      "qint";
      "qlog";
      "qlog10";
      "qmax1";
      "qmin1";
      "qmod";
      "qnint";
      "qreal";
      "qsign";
      "qsin";
      "qsind";
      "qsinh";
      "qsqrt";
      "qtan";
      "qtand";
      "qtanh";
      "snglq";

(* for VMS *)
      "iargcount";

(* for HPF *)
      "number_of_processors";
      "processors_shape";
      "ilen";
    ]

  let mpi_function_list =
    [ "mpi_abort";
      "mpi_accumulate";
      "mpi_address";
      "mpi_add_error_class";
      "mpi_add_error_code";
      "mpi_add_error_string";
      "mpi_allgather";
      "mpi_allgatherv";
      "mpi_alloc_mem";
      "mpi_allreduce";
      "mpi_alltoall";
      "mpi_alltoallv";
      "mpi_alltoallw";
      "mpi_attr_delete";
      "mpi_attr_get";
      "mpi_attr_put";
      "mpi_barrier";
      "mpi_bcast";
      "mpi_bsend";
      "mpi_bsend_init";
      "mpi_buffer_attach";
      "mpi_buffer_detach";
      "mpi_cancel";
      "mpi_cartdim_get";
      "mpi_cart_coords";
      "mpi_cart_create";
      "mpi_cart_get";
      "mpi_cart_map";
      "mpi_cart_rank";
      "mpi_cart_shift";
      "mpi_cart_sub";
      "mpi_close_port";
      "mpi_comm_accept";
      "mpi_comm_c2f";
      "mpi_comm_call_errhandler";
      "mpi_comm_clone";
      "mpi_comm_compare";
      "mpi_comm_connect";
      "mpi_comm_create";
      "mpi_comm_create_errhandler";
      "mpi_comm_create_keyval";
      "mpi_comm_delete_attr";
      "mpi_comm_disconnect";
      "mpi_comm_dup";
      "mpi_comm_dup_fn";
      "mpi_comm_f2c";
      "mpi_comm_free";
      "mpi_comm_free_keyval";
      "mpi_comm_get_attr";
      "mpi_comm_get_errhandler";
      "mpi_comm_get_name";
      "mpi_comm_get_parent";
      "mpi_comm_group";
      "mpi_comm_join";
      "mpi_comm_null_copy_fn";
      "mpi_comm_null_delete_fn";
      "mpi_comm_rank";
      "mpi_comm_remote_group";
      "mpi_comm_remote_size";
      "mpi_comm_set_attr";
      "mpi_comm_set_errhandler";
      "mpi_comm_set_name";
      "mpi_comm_size";
      "mpi_comm_spawn";
      "mpi_comm_spawn_multiple";
      "mpi_comm_split";
      "mpi_comm_test_inter";
      "mpi_dims_create";
      "mpi_dist_graph_create";
      "mpi_dist_graph_create_adjacent";
      "mpi_dist_graph_neighbors";
      "mpi_dist_graph_neighbors_count";
      "mpi_dist_graph_neighbor_count";
      "mpi_dist_neighbors";
      "mpi_dist_neighbors_count";
      "mpi_dup_fn";
      "mpi_dist_graph_create";
      "mpi_errhandler_c2f";
      "mpi_errhandler_create";
      "mpi_errhandler_f2c";
      "mpi_errhandler_free";
      "mpi_errhandler_get";
      "mpi_errhandler_set";
      "mpi_error_class";
      "mpi_error_string";
      "mpi_exscan";
      "mpi_file_c2f";
      "mpi_file_call_errhandler";
      "mpi_file_close";
      "mpi_file_create_errhandler";
      "mpi_file_delete";
      "mpi_file_f2c";
      "mpi_file_get_amode";
      "mpi_file_get_atomicity";
      "mpi_file_get_byte_offset";
      "mpi_file_get_errhandler";
      "mpi_file_get_group";
      "mpi_file_get_info";
      "mpi_file_get_position";
      "mpi_file_get_position_shared";
      "mpi_file_get_size";
      "mpi_file_get_type_extent";
      "mpi_file_get_view";
      "mpi_file_iread";
      "mpi_file_iread_at";
      "mpi_file_iread_shared";
      "mpi_file_iwrite";
      "mpi_file_iwrite_at";
      "mpi_file_iwrite_shared";
      "mpi_file_open";
      "mpi_file_preallocate";
      "mpi_file_read";
      "mpi_file_read_all";
      "mpi_file_read_all_begin";
      "mpi_file_read_all_end";
      "mpi_file_read_at";
      "mpi_file_read_at_all";
      "mpi_file_read_at_all_begin";
      "mpi_file_read_at_all_end";
      "mpi_file_read_ordered";
      "mpi_file_read_ordered_begin";
      "mpi_file_read_ordered_end";
      "mpi_file_read_shared";
      "mpi_file_seek";
      "mpi_file_seek_shared";
      "mpi_file_set_atomicity";
      "mpi_file_set_errhandler";
      "mpi_file_set_info";
      "mpi_file_set_size";
      "mpi_file_set_view";
      "mpi_file_sync";
      "mpi_file_write";
      "mpi_file_write_all";
      "mpi_file_write_all_begin";
      "mpi_file_write_all_end";
      "mpi_file_write_at";
      "mpi_file_write_at_all";
      "mpi_file_write_at_all_begin";
      "mpi_file_write_at_all_end";
      "mpi_file_write_ordered";
      "mpi_file_write_ordered_begin";
      "mpi_file_write_ordered_end";
      "mpi_file_write_shared";
      "mpi_finalize";
      "mpi_finalized";
      "mpi_free_mem";
      "mpi_gather";
      "mpi_gatherv";
      "mpi_get";
      "mpi_get_address";
      "mpi_get_count";
      "mpi_get_elements";
      "mpi_get_processor_name";
      "mpi_get_version";
      "mpi_graphdims_get";
      "mpi_graph_create";
      "mpi_graph_get";
      "mpi_graph_map";
      "mpi_graph_neighbors";
      "mpi_graph_neighbors_count";
      "mpi_grequest_complete";
      "mpi_grequest_start";
      "mpi_group_c2f";
      "mpi_group_compare";
      "mpi_group_difference";
      "mpi_group_excl";
      "mpi_group_f2c";
      "mpi_group_free";
      "mpi_group_incl";
      "mpi_group_intersection";
      "mpi_group_range_excl";
      "mpi_group_range_incl";
      "mpi_group_rank";
      "mpi_group_size";
      "mpi_group_translate_ranks";
      "mpi_group_union";
      "mpi_ibsend";
      "mpi_info_c2f";
      "mpi_info_create";
      "mpi_info_delete";
      "mpi_info_dup";
      "mpi_info_f2c";
      "mpi_info_free";
      "mpi_info_get";
      "mpi_info_get_nkeys";
      "mpi_info_get_nthkey";
      "mpi_info_get_valuelen";
      "mpi_info_set";
      "mpi_init";
      "mpi_initialized";
      "mpi_init_thread";
      "mpi_intercomm_create";
      "mpi_intercomm_merge";
      "mpi_iprobe";
      "mpi_irecv";
      "mpi_irsend";
      "mpi_isend";
      "mpi_issend";
      "mpi_is_thread_main";
      "mpi_keyval_create";
      "mpi_keyval_free";
      "mpi_lookup_name";
      "mpi_null_copy_fn";
      "mpi_null_delete_fn";
      "mpi_open_port";
      "mpi_op_c2f";
      "mpi_op_commutative";
      "mpi_op_create";
      "mpi_op_f2c";
      "mpi_op_free";
      "mpi_pack";
      "mpi_pack_external";
      "mpi_pack_external_size";
      "mpi_pack_size";
      "mpi_pcontrol";
      "mpi_probe";
      "mpi_publish_name";
      "mpi_put";
      "mpi_query_thread";
      "mpi_recv";
      "mpi_recv_init";
      "mpi_reduce";
      "mpi_reduce_local";
      "mpi_reduce_scatter";
      "mpi_reduce_scatter_block";
      "mpi_register_datarep";
      "mpi_request_c2f";
      "mpi_request_f2c";
      "mpi_request_free";
      "mpi_request_get_status";
      "mpi_rsend";
      "mpi_rsend_init";
      "mpi_scan";
      "mpi_scatter";
      "mpi_scatterv";
      "mpi_send";
      "mpi_sendrecv";
      "mpi_send_init";
      "mpi_sizeof";
      "mpi_ssend";
      "mpi_ssend_init";
      "mpi_start";
      "mpi_startall";
      "mpi_status_c2f";
      "mpi_status_f2c";
      "mpi_status_set_cancelled";
      "mpi_status_set_elements";
      "mpi_test";
      "mpi_testall";
      "mpi_testany";
      "mpi_testsome";
      "mpi_test_cancelled";
      "mpi_topo_test";
      "mpi_type_c2f";
      "mpi_type_commit";
      "mpi_type_contiguous";
      "mpi_type_create_darray";
      "mpi_type_create_f90_complex";
      "mpi_type_create_f90_integer";
      "mpi_type_create_f90_real";
      "mpi_type_create_hindexed";
      "mpi_type_create_hvector";
      "mpi_type_create_indexed_block";
      "mpi_type_create_keyval";
      "mpi_type_create_resized";
      "mpi_type_create_struct";
      "mpi_type_create_subarray";
      "mpi_type_delete_attr";
      "mpi_type_dup";
      "mpi_type_dup_fn";
      "mpi_type_extent";
      "mpi_type_f2c";
      "mpi_type_free";
      "mpi_type_free_keyval";
      "mpi_type_get_attr";
      "mpi_type_get_contents";
      "mpi_type_get_envelope";
      "mpi_type_get_extent";
      "mpi_type_get_name";
      "mpi_type_get_true_extent";
      "mpi_type_hindexed";
      "mpi_type_hvector";
      "mpi_type_indexed";
      "mpi_type_lb";
      "mpi_type_match_size";
      "mpi_type_null_copy_fn";
      "mpi_type_null_delete_fn";
      "mpi_type_set_attr";
      "mpi_type_set_name";
      "mpi_type_size";
      "mpi_type_struct";
      "mpi_type_ub";
      "mpi_type_vector";
      "mpi_unpack";
      "mpi_unpack_external";
      "mpi_unpublish_name";
      "mpi_wait";
      "mpi_waitall";
      "mpi_waitany";
      "mpi_waitsome";
      "mpi_win_c2f";
      "mpi_win_call_errhandler";
      "mpi_win_complete";
      "mpi_win_create";
      "mpi_win_create_errhandler";
      "mpi_win_create_keyval";
      "mpi_win_delete_attr";
      "mpi_win_dup_fn";
      "mpi_win_f2c";
      "mpi_win_fence";
      "mpi_win_free";
      "mpi_win_free_keyval";
      "mpi_win_get_attr";
      "mpi_win_get_errhandler";
      "mpi_win_get_group";
      "mpi_win_get_name";
      "mpi_win_lock";
      "mpi_win_null_copy_fn";
      "mpi_win_null_delete_fn";
      "mpi_win_post";
      "mpi_win_set_attr";
      "mpi_win_set_errhandler";
      "mpi_win_set_name";
      "mpi_win_start";
      "mpi_win_test";
      "mpi_win_unlock";
      "mpi_win_wait";
      "mpi_wtick";
      "mpi_wtime";
      "pmpi_wtick";
      "pmpi_wtime";
    ]

  let const_x ?(dim=Dimension.NoDimension) type_spec =
    let a = new Attribute.c in
    a#set_parameter;
    a#set_dimension dim;
    let dobj = Spec.mkdobj ~type_spec (Some a) in
    dobj

  let const_int()  = const_x TypeSpec.Integer
  let const_char() = const_x TypeSpec.Character

  let const_derived_type tname = const_x (TypeSpec.Derived tname)

  let const_derived_type_array1 tname =
    const_x ~dim:(Dimension.explicit_shape 1) (TypeSpec.Derived tname)

  let const_int_array1() =
    const_x ~dim:(Dimension.explicit_shape 1) TypeSpec.Integer

  let derived_type0 n =
    let obj = Spec.mkobj() in
    let frm = new frame (ScopingUnit.mkderivedtypedef n) in
    Spec.mkderivedtype (Spec.mkframev ~add:frm#add ~find:frm#find) obj

  let intrinsic_function0() =
    let spec = new Spec.intrinsic_procedure_spec (Rank.mk 0) in
    Spec.mkintrinsicfunc spec


  let intrinsic_module_list =
    [
     "iso_fortran_env",
     [ "atomic_int_kind"              , const_int();
       "atomic_logical_kind"          , const_int();
       "character_kinds"              , const_int_array1();
       "character_storage_size"       , const_int();
       "error_unit"                   , const_int();
       "file_storage_size"            , const_int();
       "input_unit"                   , const_int();
       "int8"                         , const_int();
       "int16"                        , const_int();
       "int32"                        , const_int();
       "int64"                        , const_int();
       "integer_kinds"                , const_int_array1();
       "iostat_end"                   , const_int();
       "iostat_eor"                   , const_int();
       "iostat_inquire_internal_unit" , const_int();
       "numeric_storage_size"         , const_int();
       "logical_kinds"                , const_int_array1();
       "output_unit"                  , const_int();
       "real32"                       , const_int();
       "real64"                       , const_int();
       "real128"                      , const_int();
       "real_kinds"                   , const_int_array1();
       "stat_locked"                  , const_int();
       "stat_locked_other_image"      , const_int();
       "stat_stopped_image"           , const_int();
       "stat_failed_image"            , const_int();
       "stat_unlocked"                , const_int();
       "lock_type"                    , derived_type0 "lock_type";
       "compiler_options"             , intrinsic_function0();
       "compiler_version"             , intrinsic_function0();
     ];
     "iso_c_binding",
     [ "c_associated"          , intrinsic_function0();
       "c_f_pointer"           , Spec.intrinsic_subroutine;
       "c_f_procpointer"       , Spec.intrinsic_subroutine;
       "c_funloc"              , intrinsic_function0();
       "c_loc"                 , intrinsic_function0();
       "c_sizeof"              , intrinsic_function0();
       "c_int"                 , const_int();
       "c_short"               , const_int();
       "c_long"                , const_int();
       "c_long_long"           , const_int();
       "c_signed_char"         , const_int();
       "c_size_t"              , const_int();
       "c_int8_t"              , const_int();
       "c_int16_t"             , const_int();
       "c_int32_t"             , const_int();
       "c_int64_t"             , const_int();
       "c_int128_t"            , const_int(); (* GNU *)
       "c_int_least8_t"        , const_int();
       "c_int_least16_t"       , const_int();
       "c_int_least32_t"       , const_int();
       "c_int_least64_t"       , const_int();
       "c_int_least128_t"      , const_int(); (* GNU *)
       "c_int_fast8_t"         , const_int();
       "c_int_fast16_t"        , const_int();
       "c_int_fast32_t"        , const_int();
       "c_int_fast64_t"        , const_int();
       "c_int_fast128_t"       , const_int(); (* GNU *)
       "c_intmax_t"            , const_int();
       "c_intptr_t"            , const_int();
       "c_ptrdiff_t"           , const_int(); (* TS29113 *)
       "c_float"               , const_int();
       "c_double"              , const_int();
       "c_long_double"         , const_int();
       "c_float128"            , const_int(); (* GNU *)
       "c_float_complex"       , const_int();
       "c_double_complex"      , const_int();
       "c_long_double_complex" , const_int();
       "c_float128_complex"    , const_int(); (* GNU *)
       "c_bool"                , const_int();
       "c_char"                , const_int();
       "c_null_char"           , const_char();
       "c_alert"               , const_char();
       "c_backspace"           , const_char();
       "c_form_feed"           , const_char();
       "c_new_line"            , const_char();
       "c_carriage_return"     , const_char();
       "c_horizontal_tab"      , const_char();
       "c_vertical_tab"        , const_char();
       "c_ptr"                 , derived_type0 "c_ptr";
       "c_funptr"              , derived_type0 "c_funptr";
       "c_null_ptr"            , const_derived_type "c_ptr";
       "c_null_funptr"         , const_derived_type "c_funptr";
     ];
     "ieee_exceptions",
     [ "ieee_flag_type"        , derived_type0 "ieee_flag_type";
       "ieee_invalid"          , const_derived_type "ieee_flag_type";
       "ieee_overflow"         , const_derived_type "ieee_flag_type";
       "ieee_divide_by_zero"   , const_derived_type "ieee_flag_type";
       "ieee_underflow"        , const_derived_type "ieee_flag_type";
       "ieee_inexact"          , const_derived_type "ieee_flag_type";
       "ieee_usual"            , const_derived_type_array1 "ieee_flag_type";
       "ieee_all"              , const_derived_type_array1 "ieee_flag_type";
       "ieee_status_type"      , derived_type0 "ieee_status_type";
       "ieee_get_flag"         , Spec.intrinsic_subroutine;
       "ieee_get_halting_mode" , Spec.intrinsic_subroutine;
       "ieee_get_status"       , Spec.intrinsic_subroutine;
       "ieee_set_flag"         , Spec.intrinsic_subroutine;
       "ieee_set_halting_mode" , Spec.intrinsic_subroutine;
       "ieee_set_status"       , Spec.intrinsic_subroutine;
       "ieee_support_flag"     , intrinsic_function0();
       "ieee_support_halting"  , intrinsic_function0();
     ];
     "ieee_arithmetic",
     [ "ieee_class_type"                , derived_type0 "ieee_class_type";
       "ieee_signaling_nan"             , const_derived_type "ieee_class_type";
       "ieee_quiet_nan"                 , const_derived_type "ieee_class_type";
       "ieee_negative_inf"              , const_derived_type "ieee_class_type";
       "ieee_negative_normal"           , const_derived_type "ieee_class_type";
       "ieee_negative_denormal"         , const_derived_type "ieee_class_type";
       "ieee_negative_zero"             , const_derived_type "ieee_class_type";
       "ieee_positive_zero"             , const_derived_type "ieee_class_type";
       "ieee_positive_denormal"         , const_derived_type "ieee_class_type";
       "ieee_positive_normal"           , const_derived_type "ieee_class_type";
       "ieee_positive_inf"              , const_derived_type "ieee_class_type";
       "ieee_other_value"               , const_derived_type "ieee_class_type";
       "ieee_round_type"                , derived_type0 "ieee_round_type";
       "ieee_nearest"                   , const_derived_type "ieee_round_type";
       "ieee_to_zero"                   , const_derived_type "ieee_round_type";
       "ieee_up"                        , const_derived_type "ieee_round_type";
       "ieee_down"                      , const_derived_type "ieee_round_type";
       "ieee_other"                     , const_derived_type "ieee_round_type";
       "ieee_class"                     , intrinsic_function0();
       "ieee_copy_sign"                 , intrinsic_function0();
       "ieee_get_rounding_mode"         , Spec.intrinsic_subroutine;
       "ieee_get_underflow_mode"        , Spec.intrinsic_subroutine;
       "ieee_is_finite"                 , intrinsic_function0();
       "ieee_is_nan"                    , intrinsic_function0();
       "ieee_is_negative"               , intrinsic_function0();
       "ieee_is_normal"                 , intrinsic_function0();
       "ieee_logb"                      , intrinsic_function0();
       "ieee_next_after"                , intrinsic_function0();
       "ieee_rem"                       , intrinsic_function0();
       "ieee_rint"                      , intrinsic_function0();
       "ieee_scalb"                     , intrinsic_function0();
       "ieee_selected_real_kind"        , intrinsic_function0();
       "ieee_set_rounding_mode"         , Spec.intrinsic_subroutine;
       "ieee_set_underflow_mode"        , Spec.intrinsic_subroutine;
       "ieee_support_datatype"          , intrinsic_function0();
       "ieee_support_denormal"          , intrinsic_function0();
       "ieee_support_divide"            , intrinsic_function0();
       "ieee_support_inf"               , intrinsic_function0();
       "ieee_support_io"                , intrinsic_function0();
       "ieee_support_nan"               , intrinsic_function0();
       "ieee_support_rounding"          , intrinsic_function0();
       "ieee_support_sqrt"              , intrinsic_function0();
       "ieee_support_standard"          , intrinsic_function0();
       "ieee_support_underflow_control" , intrinsic_function0();
       "ieee_unordered"                 , intrinsic_function0();
       "ieee_value"                     , intrinsic_function0();
     ];
     "ieee_features",
     [ "ieee_features_type"  , derived_type0 "ieee_features_type";
       "ieee_data_type"      , const_derived_type "ieee_features_type";
       "ieee_denormal"       , const_derived_type "ieee_features_type";
       "ieee_divide"         , const_derived_type "ieee_features_type";
       "ieee_halting"        , const_derived_type "ieee_features_type";
       "ieee_inexact_flag"   , const_derived_type "ieee_features_type";
       "ieee_inf"            , const_derived_type "ieee_features_type";
       "ieee_invalid_flag"   , const_derived_type "ieee_features_type";
       "ieee_nan"            , const_derived_type "ieee_features_type";
       "ieee_rounding"       , const_derived_type "ieee_features_type";
       "ieee_sqrt"           , const_derived_type "ieee_features_type";
       "ieee_underflow_flag" , const_derived_type "ieee_features_type";
     ];
     "omp_lib_kinds",
     [ "omp_lock_kind"      , const_int();
       "omp_nest_lock_kind" , const_int();
       "omp_proc_bind_kind" , const_int();
       "omp_sched_kind"     , const_int();
     ];
     "omp_lib",
     [ "omp_version"          , const_int();
       "omp_sched_static"     , const_int();
       "omp_sched_dynamic"    , const_int();
       "omp_sched_guided"     , const_int();
       "omp_sched_auto"       , const_int();
       "omp_proc_bind_false"  , const_int();
       "omp_proc_bind_true"   , const_int();
       "omp_proc_bind_master" , const_int();
       "omp_proc_bind_close"  , const_int();
       "omp_proc_bind_spread" , const_int();
     ] @
     (List.map (fun x -> x, Spec.intrinsic_subroutine) omp_subroutine_list) @
     (List.map (fun x -> x, intrinsic_function0()) omp_function_list);
     "openacc",
     [ "openacc_version"       , const_int();
       "acc_get_num_devices"   , intrinsic_function0();
       "acc_set_device_type"   , Spec.intrinsic_subroutine;
       "acc_get_device_type"   , intrinsic_function0();
       "acc_set_device_num"    , Spec.intrinsic_subroutine;
       "acc_get_device_num"    , intrinsic_function0();
       "acc_async_test"        , intrinsic_function0();
       "acc_async_test_all"    , intrinsic_function0();
       "acc_wait"              , Spec.intrinsic_subroutine;
       "acc_wait_all"          , Spec.intrinsic_subroutine;
       "acc_wait_async"        , Spec.intrinsic_subroutine;
       "acc_wait_all_async"    , Spec.intrinsic_subroutine;
       "acc_init"              , Spec.intrinsic_subroutine;
       "acc_shutdown"          , Spec.intrinsic_subroutine;
       "acc_on_device"         , intrinsic_function0();
       "acc_copyin"            , Spec.intrinsic_subroutine;
       "acc_present_or_copyin" , Spec.intrinsic_subroutine;
       "acc_pcopyin"           , Spec.intrinsic_subroutine;
       "acc_create"            , Spec.intrinsic_subroutine;
       "acc_present_or_create" , Spec.intrinsic_subroutine;
       "acc_pcreate"           , Spec.intrinsic_subroutine;
       "acc_copyout"           , Spec.intrinsic_subroutine;
       "acc_delete"            , Spec.intrinsic_subroutine;
       "acc_update_device"     , Spec.intrinsic_subroutine;
       "acc_update_self"       , Spec.intrinsic_subroutine;
       "acc_is_present"        , intrinsic_function0();
     ];
   ]


  let make_module (*mod_name*)_ frm =
    let mkdom() =
      let s = Xset.create 0 in
      frm#iter
        (fun nm spc ->
          let is_public =
            try
              Spec.is_public spc
            with
              _ -> AccessSpec.is_public frm#default_accessibility
          in
          [%debug_log "is_public: %s --> %B" nm is_public];
          if is_public then
            Xset.add s nm
        );
      [%debug_log "dom: {%s}" (Xlist.to_string (fun x -> x) "," (Xset.to_list s))];
      s
    in
    Spec.mkmodule mkdom (Spec.mkframev ~find:frm#find ~add:frm#add)



  let make_toplevel_frame() =
    let frm = new frame ScopingUnit.Program in

    List.iter
      (fun (pspec, list) ->
        let spec = Spec.IntrinsicFunction pspec in
        List.iter (fun fn -> frm#add fn spec) list
      ) intrinsic_function_list;

    List.iter
      (fun fn -> frm#add fn Spec.IntrinsicSubroutine)
      intrinsic_subroutine_list;

    List.iter
      (fun fn -> frm#add fn Spec.LindaOperation)
      linda_operation_list;

    List.iter
      (fun lst ->
        List.iter
          (fun fn -> frm#add fn (Spec.make_public_subroutine())) lst
      )
      [ omp_subroutine_list;
        gnu_subroutine_list;
      ];

    List.iter
      (fun lst ->
        List.iter
          (fun fn -> frm#add fn (Spec.make_public_function())) lst
      )
      [ omp_function_list;
        linda_function_list;
        gnu_function_list;
        compaq_function_list;
        mpi_function_list;
      ];

    List.iter
      (fun (mod_name, entity_list) ->
        let f = new frame (ScopingUnit.mkmodule mod_name) in
        f#set_default_accessibility_public;
        List.iter (fun (n, spc) -> f#add n spc) entity_list;
        frm#add mod_name (make_module mod_name f)
      ) intrinsic_module_list;

    frm

end (* of module Pinfo.Name *)
]

type t =
  | NoInfo
  | NameSpec of Name.Spec.t
  | PossibleNameSpecs of Name.Spec.t list


let to_string = function
  | NoInfo         -> ""
  | NameSpec nspec -> Name.Spec.to_string nspec
  | PossibleNameSpecs nspecs -> Xlist.to_string Name.Spec.to_string ";" nspecs


let mknamespec nspec = NameSpec nspec

let mkpossiblenamespecs nspecs = PossibleNameSpecs nspecs

let mkext mname name =
  mknamespec (Name.Spec.mkext mname name)

let make specs =
  match specs with
  | []     -> NoInfo
  | [spec] -> NameSpec spec
  | _      -> PossibleNameSpecs specs

let get_namespecs = function
  | NoInfo -> []
  | NameSpec spec -> [spec]
  | PossibleNameSpecs specs -> specs

let merge i0 i1 =
  let specs0 = get_namespecs i0 in
  let specs1 = get_namespecs i1 in
  make (specs0 @ specs1)

let iter_external f = function
  | NoInfo         -> ()
  | NameSpec nspec -> begin
      try
        f (Name.Spec.decompose_external nspec)
      with
        _ -> ()
  end
  | PossibleNameSpecs nspecs -> begin
      List.iter
        (fun nspec ->
          try
            f (Name.Spec.decompose_external nspec)
          with
            _ -> ()
        ) nspecs
  end

let iter_name_spec f = function
  | NoInfo -> ()
  | NameSpec nspec -> f nspec
  | PossibleNameSpecs nspecs -> List.iter f nspecs

let iter_data_object f = function
  | NoInfo -> ()
  | NameSpec nspec -> begin
      try
        f (Name.Spec.get_data_object_spec nspec)
      with
        Not_found -> ()
  end
  | PossibleNameSpecs (*nspecs*)_ -> ()


let is_public info =
  let fail() = failwith "Pinfo.is_public" in
  match info with
  | NoInfo -> fail()
  | NameSpec nspec -> Name.Spec.is_public nspec
  | PossibleNameSpecs nspecs -> (*fail()*)
      List.exists Name.Spec.is_public nspecs


(* end of Pinfo *)
