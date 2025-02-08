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
(* compression.ml *)

let gzip_default_compression_level = 9


class virtual c = object
  method virtual is_compressed : bool
  method virtual ext           : string
  method virtual to_string     : string
  method virtual level         : int
  method virtual set_level     : int -> unit
end

let none = object
  inherit c

  method is_compressed = false

  method ext = ""

  method to_string = "<none>"

  method level = 0
  method set_level _ = ()
end

let gzip = object
  inherit c

  method is_compressed = true

  val mutable comp_level = gzip_default_compression_level
  method level = comp_level
  method set_level lv = comp_level <- lv

  method ext = ".gz"

  method to_string = Printf.sprintf "<gzip:%d>" comp_level
end


let extensions = [ (gzip#ext, gzip) ]

let from_filename fname =
  let ext = Xfile.get_extension fname in
  let c =
    try
      List.assoc ext extensions
    with
      Not_found -> none
  in
  c
