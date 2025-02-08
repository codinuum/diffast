(*
   Copyright 2012-2023 Codinuum Software Lab <https://codinuum.com>

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
(* entity.ml *)

type vkind =
  | V_REL
  | V_SVNREV
  | V_GITREV
  | V_VARIANT
  | V_UNKNOWN

let vkind_to_string = function
  | V_REL     -> "REL"
  | V_SVNREV  -> "SVNREV"
  | V_GITREV  -> "GITREV"
  | V_VARIANT -> "VARIANT"
  | V_UNKNOWN -> "UNKNOWN"

let vkind_is_unknown = function
  | V_UNKNOWN -> true
  | _ -> false

type version = vkind * string

let unknown_version = (V_UNKNOWN, "???")

exception Illegal_version_format of string

let vkind_ver_of_string str =
  let kind, ver =
    match Str.split (Str.regexp_string ":") str with
    | [] | [_] ->
        raise (Illegal_version_format str)

    | "REL"::rest ->
        (V_REL, String.concat ":" rest)

    | "SVNREV"::rest ->
        (V_SVNREV, String.concat ":" rest)

    | "GITREV"::rest ->
        (V_GITREV, String.concat ":" rest)

    | "VARIANT"::rest ->
        (V_VARIANT, String.concat ":" rest)

    | _ ->
        raise (Illegal_version_format str)
  in
  kind, ver

let version_to_string (vkind, ver) =
  (vkind_to_string vkind)^":"^ver

type encoding =
  | FD     (* file digest (entire file) *)
  | PV     (* proj + ver *)
  | PVF    (* proj + ver + file (entire file) *)
  | FDLC   (* file digest + line + column *)
  | FDO    (* file digest + offset *)
  | FDLO   (* file digest + line + offset *)
  | FDLCO  (* file digest + line + column + offset *)
  | PVFLC  (* proj + ver + file + line + column *)
  | PVFO   (* proj + ver + file + offset *)
  | PVFLO  (* proj + ver + file + line + offset *)
  | PVFLCO (* proj + ver + file + line + column + offset *)

let encoding_to_string = function
  | FD     -> "FD"
  | PV     -> "PV"
  | PVF    -> "PVF"
  | FDLC   -> "FDLC"
  | FDO    -> "FDO"
  | FDLO   -> "FDLO"
  | FDLCO  -> "FDLCO"
  | PVFLC  -> "PVFLC"
  | PVFO   -> "PVFO"
  | PVFLO  -> "PVFLO"
  | PVFLCO -> "PVFLCO"

let sep = "-"
let sub_sep = "_"
let sub_sub_sep = "."

let mkvkey vkind ver =
  match vkind with
  | V_REL     -> (vkind_to_string V_REL)^sub_sep^ver
  | V_SVNREV  -> (vkind_to_string V_SVNREV)^sub_sep^ver
  | V_GITREV  -> (vkind_to_string V_GITREV)^sub_sep^ver
  | V_VARIANT -> (vkind_to_string V_VARIANT)^sub_sep^ver
  | V_UNKNOWN -> "???"

let is_FD_encoding = function
  | FD | FDLC | FDO | FDLO | FDLCO -> true
  | _ -> false

let is_PVF_encoding = function
  | PV | PVF | PVFLC | PVFO | PVFLO | PVFLCO -> true
  | _ -> false



