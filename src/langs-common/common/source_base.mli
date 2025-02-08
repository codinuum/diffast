(*
   Copyright 2012-2024 Codinuum Software Lab <https://codinuum.com>

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

module Loc = Astloc
module Xchannel = Diffast_misc.Xchannel
module Storage = Diffast_misc.Storage

type encoding =
  | E_Latin1
  | E_UTF8
  | E_UTF16BE
  | E_UTF16LE

val default_encoding : encoding
val encoding_to_string : encoding -> string

class c : Storage.file -> object
  method close : unit
  method eof_loc : Loc.t option
  method eof_reached : bool
  method exists : bool
  method file : Storage.file
  method filename : string
  method get_channel : Xchannel.input_channel
  method get_ulexbuf : Sedlexing.lexbuf
  method get_ulexbuf_from_channel : Xchannel.input_channel -> Sedlexing.lexbuf
  method get_ulexbuf_from_stdin : Sedlexing.lexbuf
  method init : unit
  method path : string
  method pos_mgr : Position.manager
  method refill : Xchannel.input_channel -> Uchar.t Array.t -> int -> int -> int
  method set_eof_loc : Loc.t -> unit
  method set_eof_reached : unit
  method set_filename : string -> unit
  method tree : Storage.tree
  method update_encoding : ?update_buf:bool -> encoding -> unit
end
