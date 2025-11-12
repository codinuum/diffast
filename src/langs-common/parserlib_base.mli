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
module Storage = Diffast_misc.Storage

val cmd_name : string

exception Parse_error of string * string
type 'rawtoken token = 'rawtoken * Lexing.position * Lexing.position
type 'rawtoken qtoken = 'rawtoken * Astloc.t

val is_bom : string -> bool
val get_bom_name : string -> string
val is_extended_pos : Lexing.position -> bool
val extend_pos : ?cache:Fname.ext_cache_t -> string -> Lexing.position -> Lexing.position
val extend_poss : ?cache:Fname.ext_cache_t -> string -> Lexing.position -> Lexing.position ->
  Lexing.position * Lexing.position
val get_stripped_pos : Lexing.position -> Lexing.position
val make_token : ?cache:Fname.ext_cache_t -> ?ext:string -> 'rawtoken -> Lexing.position ->
  Lexing.position -> 'rawtoken token
val token_to_rawtoken : 'rt token -> 'rt
val token_to_lexposs : 'rt token -> Lexing.position * Lexing.position
val decompose_token : 'rt token -> 'rt * Lexing.position * Lexing.position
val _token_to_string : ('rt -> 'a) -> 'rt token -> 'a
val merge_locs : ?cache:Fname.ext_cache_t option -> Astloc.t -> Astloc.t -> Astloc.t
val loc_of_lexposs : ?cache:Fname.ext_cache_t option -> Lexing.position -> Lexing.position ->
  Astloc.t
val make_qtoken : ?cache:Fname.ext_cache_t -> ?ext:string -> 'rt -> Lexing.position ->
  Lexing.position -> 'rt qtoken
val qtoken_to_loc : 'rt qtoken -> Astloc.t
val qtoken_to_rawtoken : 'rt qtoken -> 'rt
val qtoken_to_token : 'rt qtoken -> 'rt token
val _qtoken_to_string : ('rt -> string) -> 'rt qtoken -> string
val fail_to_parse : ?head:string -> string -> 'a
val parse_error_loc : ?head:string -> < keep_going_flag : bool; .. > -> (Astloc.t -> 'b) ->
  Astloc.t -> ('a, unit, string, 'b) format4 -> 'a
val parse_error : ?head:string -> < keep_going_flag : bool; .. > -> (Astloc.t -> 'a) ->
  Lexing.position -> Lexing.position -> ('c, unit, string, 'a) format4 -> 'c
val parse_warning_loc : ?out:out_channel -> ?head:string -> Astloc.t ->
  ('a, out_channel, unit, unit) format4 -> 'a
val parse_warning : ?out:out_channel -> ?head:string -> Lexing.position -> Lexing.position ->
  ('b, out_channel, unit, unit) format4 -> 'b
val mkparser :
    ('a, 'b) MenhirLib.Convert.traditional ->
      ('a * Lexing.position * Lexing.position, 'b) MenhirLib.Convert.revised

class virtual ['rawtoken] scanner : object
  method virtual get_token : unit -> 'rawtoken token
end

class virtual ['a, 'rawtoken, 'ast] c : ('a #Env_base.c as 'b) -> object
  constraint 'a = #Source_base.c
  val env : 'b
  method virtual _parse : 'ast
  method _set_keep_going_flag : bool -> unit
  method _set_verbose_flag : bool -> unit
  method add_search_path : string -> unit
  method clear_keep_going_flag : unit
  method clear_verbose_flag : unit
  method extra_source_files : Storage.file list
  method lines_read : int
  method virtual make_source : Storage.file -> 'a
  method virtual make_source_stdin : 'a
  method parse_file : Storage.file -> 'ast
  method parse_stdin : 'ast
  method parser_init : unit
  method set_keep_going_flag : unit
  method set_search_path_list : string list -> unit
  method set_verbose_flag : unit
end

class virtual ['rawtoken, 'ast] sb_c : (Source_base.c #Env_base.c as 'a) -> object
  val env : 'a
  method virtual _parse : 'ast
  method _set_keep_going_flag : bool -> unit
  method _set_verbose_flag : bool -> unit
  method add_search_path : string -> unit
  method clear_keep_going_flag : unit
  method clear_verbose_flag : unit
  method extra_source_files : Storage.file list
  method lines_read : int
  method make_source : Storage.file -> Source_base.c
  method make_source_stdin : Source_base.c
  method parse_file : Storage.file -> 'ast
  method parse_stdin : 'ast
  method parser_init : unit
  method set_keep_going_flag : unit
  method set_search_path_list : string list -> unit
  method set_verbose_flag : unit
end
