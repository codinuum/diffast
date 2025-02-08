(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2020 Chiba Institude of Technology

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

(*open Label_common*)

type t =
  | Async
  | Auto
  | Bind
  | Collapse
  | Copy
  | Copyin
  | Copyout
  | Create
  | DefaultNone
  | DefaultPresent
  | Delete
  | Device
  | Deviceptr
  | Device_resident
  | Device_type
  | Device_typeAny
  | Dtype
  | DtypeAny
  | Firstprivate
  | Gang
  | Host
  | If
  | Independent
  | Link
  | Nohost
  | Num_gangs
  | Num_workers
  | Pcopy
  | Pcopyin
  | Pcopyout
  | Pcreate
  | Present
  | Present_or_copy
  | Present_or_copyin
  | Present_or_copyout
  | Present_or_create
  | Private
  | Reduction
  | Self
  | Seq
  | Tile
  | Use_device
  | Vector
  | Vector_length
  | Wait
  | Worker

let to_string = function
  | Async              -> "Async"
  | Auto               -> "Auto"
  | Bind               -> "Bind"
  | Collapse           -> "Collapse"
  | Copy               -> "Copy"
  | Copyin             -> "Copyin"
  | Copyout            -> "Copyout"
  | Create             -> "Create"
  | DefaultNone        -> "DefaultNone"
  | DefaultPresent     -> "DefaultPresent"
  | Delete             -> "Delete"
  | Device             -> "Device"
  | Deviceptr          -> "Deviceptr"
  | Device_resident    -> "Device_resident"
  | Device_type        -> "Device_type"
  | Device_typeAny     -> "Device_typeAny"
  | Dtype              -> "Dtype"
  | DtypeAny           -> "DtypeAny"
  | Firstprivate       -> "Firstprivate"
  | Gang               -> "Gang"
  | Host               -> "Host"
  | If                 -> "If"
  | Independent        -> "Independent"
  | Link               -> "Link"
  | Nohost             -> "Nohost"
  | Num_gangs          -> "Num_gangs"
  | Num_workers        -> "Num_workers"
  | Pcopy              -> "Pcopy"
  | Pcopyin            -> "Pcopyin"
  | Pcopyout           -> "Pcopyout"
  | Pcreate            -> "Pcreate"
  | Present            -> "Present"
  | Present_or_copy    -> "Present_or_copy"
  | Present_or_copyin  -> "Present_or_copyin"
  | Present_or_copyout -> "Present_or_copyout"
  | Present_or_create  -> "Present_or_create"
  | Private            -> "Private"
  | Reduction          -> "Reduction"
  | Self               -> "Self"
  | Seq                -> "Seq"
  | Tile               -> "Tile"
  | Use_device         -> "Use_device"
  | Vector             -> "Vector"
  | Vector_length      -> "Vector_length"
  | Wait               -> "Wait"
  | Worker             -> "Worker"

let to_simple_string = function
  | Async              -> "async"
  | Auto               -> "auto"
  | Bind               -> "bind"
  | Collapse           -> "collapse"
  | Copy               -> "copy"
  | Copyin             -> "copyin"
  | Copyout            -> "copyout"
  | Create             -> "create"
  | DefaultNone        -> "default(none)"
  | DefaultPresent     -> "default(present)"
  | Delete             -> "delete"
  | Device             -> "device"
  | Deviceptr          -> "deviceptr"
  | Device_resident    -> "device_resident"
  | Device_type        -> "device_type"
  | Device_typeAny     -> "device_type(*)"
  | Dtype              -> "dtype"
  | DtypeAny           -> "dtype(*)"
  | Firstprivate       -> "firstprivate"
  | Gang               -> "gang"
  | Host               -> "host"
  | If                 -> "if"
  | Independent        -> "independent"
  | Link               -> "link"
  | Nohost             -> "nohost"
  | Num_gangs          -> "num_gangs"
  | Num_workers        -> "num_workers"
  | Pcopy              -> "pcopy"
  | Pcopyin            -> "pcopyin"
  | Pcopyout           -> "pcopyout"
  | Pcreate            -> "pcreate"
  | Present            -> "present"
  | Present_or_copy    -> "present_or_copy"
  | Present_or_copyin  -> "present_or_copyin"
  | Present_or_copyout -> "present_or_copyout"
  | Present_or_create  -> "present_or_create"
  | Private            -> "private"
  | Reduction          -> "reduction"
  | Self               -> "self"
  | Seq                -> "seq"
  | Tile               -> "tile"
  | Use_device         -> "use_device"
  | Vector             -> "vector"
  | Vector_length      -> "vector_length"
  | Wait               -> "wait"
  | Worker             -> "worker"

let to_tag = function
  | Async              -> "AccAsync", []
  | Auto               -> "AccAuto", []
  | Bind               -> "AccBind", []
  | Collapse           -> "AccCollapse", []
  | Copy               -> "AccCopy", []
  | Copyin             -> "AccCopyin", []
  | Copyout            -> "AccCopyout", []
  | Create             -> "AccCreate", []
  | DefaultNone        -> "AccDefaultNone", []
  | DefaultPresent     -> "AccDefaultPresent", []
  | Delete             -> "AccDelete", []
  | Device             -> "AccDevice", []
  | Deviceptr          -> "AccDeviceptr", []
  | Device_resident    -> "AccDevice_resident", []
  | Device_type        -> "AccDevice_type", []
  | Device_typeAny     -> "AccDevice_typeAny", []
  | Dtype              -> "AccDtype", []
  | DtypeAny           -> "AccDtypeAny", []
  | Firstprivate       -> "AccFirstprivate", []
  | Gang               -> "AccGang", []
  | Host               -> "AccHost", []
  | If                 -> "AccIf", []
  | Independent        -> "AccIndependent", []
  | Link               -> "AccLink", []
  | Nohost             -> "AccNohost", []
  | Num_gangs          -> "AccNum_gangs", []
  | Num_workers        -> "AccNum_workers", []
  | Pcopy              -> "AccPcopy", []
  | Pcopyin            -> "AccPcopyin", []
  | Pcopyout           -> "AccPcopyout", []
  | Pcreate            -> "AccPcreate", []
  | Present            -> "AccPresent", []
  | Present_or_copy    -> "AccPresent_or_copy", []
  | Present_or_copyin  -> "AccPresent_or_copyin", []
  | Present_or_copyout -> "AccPresent_or_copyout", []
  | Present_or_create  -> "AccPresent_or_create", []
  | Private            -> "AccPrivate", []
  | Reduction          -> "AccReduction", []
  | Self               -> "AccSelf", []
  | Seq                -> "AccSeq", []
  | Tile               -> "AccTile", []
  | Use_device         -> "AccUse_device", []
  | Vector             -> "AccVector", []
  | Vector_length      -> "AccVector_length", []
  | Wait               -> "AccWait", []
  | Worker             -> "AccWorker", []

let anonymize = function
  | DefaultPresent -> DefaultNone
  | Dtype          -> Device_type
  | Device_typeAny -> Device_type
  | DtypeAny       -> Device_type
  | Pcopy          -> Present_or_copy
  | Pcopyin        -> Present_or_copyin
  | Pcopyout       -> Present_or_copyout
  | Pcreate        -> Present_or_create
  | l -> l
