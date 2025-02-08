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

class c = object

  val mutable keep_filtered_temp_file_flag = false

  method keep_filtered_temp_file_flag = keep_filtered_temp_file_flag
  method set_keep_filtered_temp_file_flag = keep_filtered_temp_file_flag <- true
  method clear_keep_filtered_temp_file_flag = keep_filtered_temp_file_flag <- false


  val mutable max_retry_count = 10

  method max_retry_count = max_retry_count
  method set_max_retry_count x = max_retry_count <- x


  val mutable root_path = ""

  method root_path = root_path
  method set_root_path p = root_path <- p

end
