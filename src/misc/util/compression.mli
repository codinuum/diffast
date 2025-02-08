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

val gzip_default_compression_level : int
class virtual c : object
  method virtual ext : string
  method virtual is_compressed : bool
  method virtual level : int
  method virtual set_level : int -> unit
  method virtual to_string : string
end
val none : c
val gzip : c
val extensions : (string * c) list
val from_filename : string -> c
