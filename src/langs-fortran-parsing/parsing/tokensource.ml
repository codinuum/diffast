(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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

(* Author: Masatomo Hashimoto <m.hashimoto@stair.center> *)

module Xqueue = Diffast_misc.Xqueue
module Astloc = Langs_common.Astloc

module Loc = Astloc

exception Empty

type rawtoken = Tokens_.token

type qtoken = Token.qtoken_t


class virtual c = object

  method virtual prepend_queue   : ?copy:bool -> qtoken Xqueue.c -> unit
  method virtual prepend         : qtoken -> unit

  method virtual peek_nth_rawtok : int -> rawtoken
  method virtual peek_nth        : int -> qtoken

  method virtual peek_next_rawtok : ?skip_eol:bool -> unit -> rawtoken (* skip directives *)
  method virtual get              : ?prefetch:bool -> unit -> qtoken

  method virtual discard         : ?skip_pp_branch:bool -> unit -> qtoken

  method virtual get_last_rawtok : rawtoken
  method virtual set_last_rawtok : rawtoken -> unit

  method virtual get_last_loc    : Loc.t
  method virtual set_last_loc    : Loc.t -> unit

  method virtual get_prev_rawtok : rawtoken
  method virtual set_prev_rawtok : rawtoken -> unit

  method virtual get_prev_loc    : Loc.t
  method virtual set_prev_loc    : Loc.t -> unit
(*
  method enter_branch = ()
  method exit_branch  = ()
*)
end (* of class Tokensource.c *)






