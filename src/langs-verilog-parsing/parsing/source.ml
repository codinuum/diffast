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

module Source_base = Langs_common.Source_base


type lang_spec = V1995 | V2001 | V2005 | SV2005 | SV2009

let lang_spec_to_string = function
  | V1995  -> "IEEE1364-1995"
  | V2001  -> "IEEE1364-2001"
  | V2005  -> "IEEE1364-2005"
  | SV2005 -> "IEEE1800-2005"
  | SV2009 -> "IEEE1800-2009"


class c file = object
  inherit Source_base.c file as super

  val mutable lang_spec = SV2009

  method lang_spec = lang_spec
  method set_lang_spec_v2005 =
    match lang_spec with
    | SV2009 | SV2005 -> lang_spec <- V2005
    | _ -> ()

  method set_lang_spec_sv2005 =
    match lang_spec with
    | SV2009 -> lang_spec <- SV2005
    | _ -> ()

  initializer
    super#update_encoding Source_base.E_Latin1

end (* of class Source.c *)
