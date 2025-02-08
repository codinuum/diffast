(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>

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

module Compression = Diffast_misc.Compression

class c = object

  val mutable dump_delta_out = ""

  method dump_delta_out = dump_delta_out
  method set_dump_delta_out p = dump_delta_out <- p

  val mutable minimize_delta_flag = false

  method minimize_delta_flag = minimize_delta_flag
  method set_minimize_delta_flag = minimize_delta_flag <- true
  method clear_minimize_delta_flag = minimize_delta_flag <- false

  val mutable dump_delta_flag = false

  method dump_delta_flag = dump_delta_flag
  method set_dump_delta_flag = dump_delta_flag <- true
  method clear_dump_delta_flag = dump_delta_flag <- false

  val mutable irreversible_flag = true

  method irreversible_flag = irreversible_flag
  method set_irreversible_flag = irreversible_flag <- true
  method clear_irreversible_flag = irreversible_flag <- false

  val mutable delta_compression = Compression.none

  method delta_compression = delta_compression

  val mutable compress_delta_flag = false

  method compress_delta_flag = compress_delta_flag
  method set_compress_delta_flag =
    compress_delta_flag <- true;
    delta_compression <- Compression.gzip

  method clear_compress_delta_flag =
    compress_delta_flag <- false;
    delta_compression <- Compression.none

  val mutable nobackup_flag = false
  method nobackup_flag = nobackup_flag
  method set_nobackup_flag = nobackup_flag <- true
  method clear_nobackup_flag = nobackup_flag <- false

end
