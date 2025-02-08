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
(* options.ml *)

module Xhash = Diffast_misc.Xhash
module Storage = Diffast_misc.Storage


class c = object (self)
  inherit Parser_options.c
  inherit Engine_options.c
  inherit Delta_options.c

  (* output *)
  val mutable dump_ccs_flag    = false
  val mutable dump_origin_flag = false

  (* mode *)
  val mutable split_hunk_flag = false

  (* configuration *)
  val mutable ignore_unmodified_flag = false


  (* origin *)
  val mutable nctms_file = ""
  val mutable revindex = 0


  val mutable get_cache_name_for_file2 =
    fun (_ : Storage.file) (_ : Storage.file) -> ""

  method set_get_cache_name_for_file2 f = get_cache_name_for_file2 <- f
  method get_cache_name_for_file2 = get_cache_name_for_file2

  method get_cache_path_for_file2 file1 file2 =
    let p =
      Cache.create_cache_path self (self#get_cache_name_for_file2 file1 file2)
    in
    if local_cache_name = "" then
      p
    else
      Filename.concat p local_cache_name

  method get_cache_path_for_dir_digest2 d1 d2 =
    let h1 = Xhash.to_hex d1 in
    let h2 = Xhash.to_hex d2 in
    let p =
      Cache.create_cache_path self (Cache.make_cache_name_for_dir2 h1 h2)
    in
    if local_cache_name = "" then
      p
    else
      Filename.concat p local_cache_name


(* flags getter/setter *)
  method ignore_unmodified_flag = ignore_unmodified_flag
  method set_ignore_unmodified_flag = ignore_unmodified_flag <- true
  method clear_ignore_unmodified_flag = ignore_unmodified_flag <- false

  (* output *)
  method dump_ccs_flag = dump_ccs_flag
  method set_dump_ccs_flag = dump_ccs_flag <- true
  method clear_dump_ccs_flag = dump_ccs_flag <- false

  method dump_origin_flag = dump_origin_flag
  method set_dump_origin_flag =
    self#set_no_collapse_flag;
    dump_origin_flag <- true

  method clear_dump_origin_flag = dump_origin_flag <- false


  (* mode *)
  method split_hunk_flag = split_hunk_flag
  method set_split_hunk_flag = split_hunk_flag <- true
  method clear_split_hunk_flag = split_hunk_flag <- false


(* configurations getter/setter *)


  (* origin *)
  method nctms_file = nctms_file
  method set_nctms_file x = nctms_file <- x

  method revindex = revindex
  method set_revindex x = revindex <- x


end (* of class Options.c *)
