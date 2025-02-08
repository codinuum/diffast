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


val open_temp_file : string -> (string * out_channel)
type kind = K_DUMMY | K_FS | K_GIT of string | K_UNKNOWN
val kind_fs : kind
val kind_git : string -> kind
val kind_dummy : kind
val kind_unknown : kind
val kind_to_string : kind -> string
val kind_is_fs : kind -> bool
val kind_is_git : kind -> bool

class type entry_t = object
  method path        : string
  method dirname     : string
  method name        : string
  method is_dir      : bool
  method size        : int
  method entries     : entry_t list
  method file_digest : Xhash.t
  method dir_digest  : Xhash.t option
  method get_content : unit -> string
end

val scan_dir : ?recursive:bool -> entry_t -> (entry_t -> unit) -> unit
val scan_dir_for_dirs : (string -> bool) -> entry_t -> (entry_t -> unit) -> unit
(*
class converter : (string -> string) -> object
  method conv : Netbuffer.t -> bool -> Netbuffer.t -> unit
end

class filtered_in_channel : Netchannels.in_obj_channel -> Netchannels.in_obj_channel -> object
  inherit Netchannels.in_obj_channel_delegation
  method close_in : unit -> unit
end
*)
class virtual tree : object
  method virtual hash_algo       : Xhash.algo
  method virtual kind            : kind
  method virtual id              : string
  method virtual get_entry       : ?ignore_case:bool -> string -> entry_t
  method virtual get_channel     : ?ignore_case:bool -> string -> Xchannel.input_channel
  method virtual get_local_file  : ?ignore_case:bool -> string -> string
  method virtual free_local_file : string -> unit

  method keep_local_path : string -> unit
  method is_kept_local_path : string -> bool
  method set_filter : string list -> (string -> string) -> unit
  method get_filter_by_ext : string -> (string -> string)
  method get_filter_by_name : string -> (string -> string)
  (*method get_filt_channel : string -> filtered_in_channel*)
  method name : string
  method exists : ?ignore_case:bool -> string -> bool
  method is_dir : ?ignore_case:bool -> string -> bool
  method is_file : ?ignore_case:bool -> string -> bool
  method search_path : ?ignore_case:bool -> string -> string -> (entry_t * string) list
end

type obj_t = Tree of tree | Entry of entry_t

class file : ?digest_opt:(Xhash.t option) -> ?ignore_case:bool -> obj_t -> string -> object
  method set_extra_ext : string -> unit
  method set_digest : Xhash.t -> unit
  method tree : tree
  method fullpath : string
  method path : string
  method basename : string
  method dirname : string
  method is_dir : bool
  method exists : bool
  method size : int
  method kind : kind
  method digest : Xhash.t
  method get_extension : string
  method get_entry : entry_t
  method get_channel : Xchannel.input_channel
  method get_local_file : string
  method free_local_file : unit
  method set_filter : string list -> (string -> string) -> unit
end

val dummy_entry : entry_t
val dummy_tree : tree
val stdin : file
