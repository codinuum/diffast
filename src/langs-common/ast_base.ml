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
(* *)

class c = object
  val mutable file_name       = ""
  val mutable lines_read      = 0
  val mutable ignored_regions = ([] : (int * int) list)
  val mutable ignored_LOC     = 0
  val mutable comment_regions = ([] : (int * int) list)
  val mutable comment_LOC     = 0
  val mutable missed_regions  = ([] : (int * int) list)
  val mutable missed_LOC      = 0

  method set_file_name fname = file_name <- fname
  method file_name = file_name

  method set_lines_read n = lines_read <- n
  method lines_read = lines_read

  method set_ignored_regions rs = ignored_regions <- rs
  method ignored_regions = ignored_regions

  method set_ignored_LOC n = ignored_LOC <- n
  method ignored_LOC = ignored_LOC

  method set_comment_regions rs = comment_regions <- rs
  method comment_regions = comment_regions

  method set_comment_LOC n = comment_LOC <- n
  method comment_LOC = comment_LOC

  method set_missed_regions rs = missed_regions <- rs
  method missed_regions = missed_regions

  method set_missed_LOC n = missed_LOC <- n
  method missed_LOC = missed_LOC

end (* of class Ast_base.c *)
