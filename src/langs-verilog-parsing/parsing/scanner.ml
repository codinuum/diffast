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

[%%prepare_logger]

module Parserlib_base = Langs_common.Parserlib_base
module Astloc = Langs_common.Astloc

module Loc = Astloc
module Aux = Parser_aux
module PB = Parserlib_base
module TB = Tokenbuffer


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  module TBF = Tokenbuffer.F (Stat)
  module U = Ulexer.F (Stat)
  module A = Aux.F (Stat)

  type bufs = {
      b_tokensrc : TBF.tokensource;
    }

  let mkbufs tokensrc = {
    b_tokensrc = tokensrc;
  }

  exception Empty

  class c
      (env : Aux.env)
      (partial_parser_selector : Context.t -> TBF.partial_parser)
      =
    object (self)
      inherit [Tokens_.token] PB.scanner

      val mutable current_bufs = None
      val mutable current_src = None

      method private current_bufs =
        match current_bufs with
        | Some bufs -> bufs
        | None -> raise Empty

      method private current_src =
        match current_src with
        | Some src -> src
        | None -> raise Empty

      method get_token() =
        let current_bufs = self#current_bufs in
        let tokensrc = current_bufs.b_tokensrc in

        if env#context_enter_flag then begin
          env#clear_context_enter_flag;
          env#set_last_active_ofss tokensrc#tokenbuf#get_last_offsets
        end;

        if env#context_activate_flag then begin
          env#clear_context_activate_flag;
          env#set_last_active_ofss tokensrc#tokenbuf#get_prev_offsets
        end;

        let current_src = self#current_src in

        [%debug_log "current_src: %s" current_src#filename];

        if current_src#eof_reached then begin
          match current_src#eof_loc with
          | Some loc ->
	      A.parse_failure_loc loc "syntax error"
          | None -> assert false
        end
        else begin
          [%debug_log "calling pp"];
          let _qtoken = TBF.pp tokensrc in
          let _tok, _loc = _qtoken in
          let qtoken = TBF.hack_token tokensrc _qtoken in
          let tok, loc = qtoken in
          let token = PB.qtoken_to_token qtoken in
          [%debug_log "token ------------> %s" (Token.qtoken_to_string qtoken)];
          begin
	    match tok with
	    | Tokens_.EOF -> begin
                current_src#set_eof_reached;
                current_src#set_eof_loc loc
            end
	    | _ -> ()
          end;
          token
        end


      method enter_source src =
        [%debug_log "source=\"%s\"" src#filename];
        current_src <- Some src;

        let ulexbuf =
          if src#filename = "<stdin>" then begin
            src#get_ulexbuf_from_stdin
          end
          else begin
            src#get_ulexbuf
          end
        in
        let tokenbuf = new TBF.c partial_parser_selector in
        let tokensrc = new TBF.tokensource tokenbuf ulexbuf in
        let bufs = mkbufs tokensrc in
        env#set_enter_source_callback tokensrc#enter_source;
        current_bufs <- Some bufs;
        ulexbuf
(*
      method exit_source =
        env#ignored_regions#add_regions (poped.b_tokenbuf#ignored_regions);
        env#pop_loc
*)

      initializer
        env#set_enter_source_callback self#enter_source


    end (* of class Scanner.F.c *)


end (* of functor Scanner.F *)
]
