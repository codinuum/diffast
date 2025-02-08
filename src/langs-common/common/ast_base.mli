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
class c : object
  method comment_LOC : int
  method comment_regions : (int * int) list
  method file_name : string
  method ignored_LOC : int
  method ignored_regions : (int * int) list
  method lines_read : int
  method missed_LOC : int
  method missed_regions : (int * int) list
  method set_comment_LOC : int -> unit
  method set_comment_regions : (int * int) list -> unit
  method set_file_name : string -> unit
  method set_ignored_LOC : int -> unit
  method set_ignored_regions : (int * int) list -> unit
  method set_lines_read : int -> unit
  method set_missed_LOC : int -> unit
  method set_missed_regions : (int * int) list -> unit
end
