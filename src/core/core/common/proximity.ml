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
(* proximity *)


module UID = Diffast_misc.UID

type confidence = Chigh | Clow

class ['node_t] node_proximity = object
  val mutable confidence = Chigh

  val mutable primary_prox = 0
  val mutable secondary_prox = 0

  val mutable primary_pivot = (None : ('node_t * 'node_t) option)
  val mutable secondary_pivot = (None : ('node_t * 'node_t) option)

  method lower_confidence = confidence <- Clow

  method low_confidence = confidence = Clow
  method high_confidence = confidence = Chigh

  method primary_prox   = primary_prox
  method secondary_prox = secondary_prox
  method set_primary_prox p   = primary_prox <- p
  method set_secondary_prox p = secondary_prox <- p

  method primary_pivot =
    match primary_pivot with
    | None -> raise Not_found
    | Some piv -> piv

  method secondary_pivot =
    match secondary_pivot with
    | None -> raise Not_found
    | Some piv -> piv

  method set_primary_pivot p   = primary_pivot <- Some p
  method set_secondary_pivot p = secondary_pivot <- Some p

end (* of class node_proximity *)


let null_uid_tbl = (Hashtbl.create 0 : (UID.t, UID.t) Hashtbl.t)
