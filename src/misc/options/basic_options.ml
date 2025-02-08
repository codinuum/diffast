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
  inherit Base_options.c
  inherit Hash_options.c
  inherit Fs_options.c

  val mutable ignore_if0_flag = true
  method ignore_if0_flag = ignore_if0_flag
  method set_ignore_if0_flag = ignore_if0_flag <- true
  method clear_ignore_if0_flag = ignore_if0_flag <- false


end (* of class Basic_options.c *)
