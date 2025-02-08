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

module XML = Diffast_misc.XML
module Xstring = Diffast_misc.Xstring


let ident_attr_name = "ident"
let label_attr_name = "label"
let value_attr_name = "value"
let path_attr_name  = "path"
let spec_attr_name  = "spec"

let strlit_to_encoded_path s =
  XML.encode_string (Xstring.remove_quotes s)
