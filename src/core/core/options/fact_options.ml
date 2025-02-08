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

module Xhash = Diffast_misc.Xhash
module Comp = Diffast_misc.Compression
module Hash_options = Diffast_misc.Hash_options


class c = object (self)
  inherit Hash_options.c

  val mutable fact_flag                        = false
  val mutable fact_restricted_flag             = false
  val mutable fact_add_versions_flag           = false
  val mutable fact_for_changes_flag            = false
  val mutable fact_for_changes_basic_flag      = false
  val mutable fact_for_mapping_flag            = false
  val mutable fact_for_mapping_restricted_flag = false
  val mutable fact_for_ast_flag                = false
  val mutable fact_for_delta_flag              = false
  val mutable fact_compress_flag               = true

  val mutable fact_proj              = ""
  val mutable fact_proj_roots        = ([||] : string array)
  val mutable fact_versions          = ([||] : (Entity.vkind * string) array)
  val mutable fact_enc               = Entity.FDLC
  val mutable fact_algo              = Xhash.MD5
  val mutable fact_compression       = Comp.gzip
  val mutable fact_size_threshold    = 1000
  val mutable fact_into_virtuoso     = ""
  val mutable fact_virtuoso_temp_dir = "/opt/virtuoso/tmp"
  val mutable fact_into_directory    = ""

  method fact_flag = fact_flag
  method set_fact_flag = fact_flag <- true
  method clear_fact_flag = fact_flag <- false

  method fact_restricted_flag = fact_restricted_flag
  method set_fact_restricted_flag = fact_restricted_flag <- true
  method clear_fact_restricted_flag = fact_restricted_flag <- false

  method fact_add_versions_flag = fact_add_versions_flag
  method set_fact_add_versions_flag = fact_add_versions_flag <- true
  method clear_fact_add_versions_flag = fact_add_versions_flag <- false

  method fact_for_changes_flag = fact_for_changes_flag
  method set_fact_for_changes_flag = fact_for_changes_flag <- true
  method clear_fact_for_changes_flag = fact_for_changes_flag <- false

  method fact_for_changes_basic_flag = fact_for_changes_basic_flag
  method set_fact_for_changes_basic_flag = fact_for_changes_basic_flag <- true
  method clear_fact_for_changes_basic_flag = fact_for_changes_basic_flag <- false

  method fact_for_mapping_flag = fact_for_mapping_flag
  method set_fact_for_mapping_flag = fact_for_mapping_flag <- true
  method clear_fact_for_mapping_flag = fact_for_mapping_flag <- false

  method fact_for_mapping_restricted_flag = fact_for_mapping_restricted_flag
  method set_fact_for_mapping_restricted_flag = fact_for_mapping_restricted_flag <- true
  method clear_fact_for_mapping_restricted_flag = fact_for_mapping_restricted_flag <- false

  method fact_for_ast_flag = fact_for_ast_flag
  method set_fact_for_ast_flag = fact_for_ast_flag <- true
  method clear_fact_for_ast_flag = fact_for_ast_flag <- false

  method fact_for_delta_flag = fact_for_delta_flag
  method set_fact_for_delta_flag = fact_for_delta_flag <- true
  method clear_fact_for_delta_flag = fact_for_delta_flag <- false

  method fact_compress_flag = fact_compress_flag
  method set_fact_compress_flag =
    fact_compress_flag <- true;
    fact_compression <- Comp.gzip

  method clear_fact_compress_flag =
    fact_compress_flag <- false;
    fact_compression <- Comp.none

  method fact_proj = fact_proj
  method set_fact_proj x = fact_proj <- x

  method fact_proj_roots = fact_proj_roots
  method set_fact_proj_roots x = fact_proj_roots <- x

  method fact_versions = fact_versions
  method set_fact_versions x = fact_versions <- x

  method fact_enc = fact_enc
  method set_fact_enc x = fact_enc <- x

  method fact_algo = fact_algo
  method set_fact_algo x =
    fact_algo <- x;
    self#set_hash_algo x

  method fact_size_threshold = fact_size_threshold
  method set_fact_size_threshold n = fact_size_threshold <- n

  method fact_compression = fact_compression

  method fact_into_virtuoso = fact_into_virtuoso
  method set_fact_into_virtuoso uri = fact_into_virtuoso <- uri

  method fact_virtuoso_temp_dir = fact_virtuoso_temp_dir

  method fact_into_directory = fact_into_directory
  method set_fact_into_directory dir = fact_into_directory <- dir

end
