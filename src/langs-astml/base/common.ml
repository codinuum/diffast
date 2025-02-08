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

module Xprint = Diffast_misc.Xprint
module Entity = Diffast_core.Entity

let warning_msg = Xprint.warning ~head:"[Astml]"

let decode_digest =
  let pat = Str.regexp_string Entity.sub_sep in
  let decode s =
    match Str.split pat s with
    | [] | [_] -> s
    | [_;d] -> d
    | _ -> s
  in
  decode

