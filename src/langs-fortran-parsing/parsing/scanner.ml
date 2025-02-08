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

[%%prepare_logger]

module Astloc = Langs_common.Astloc
module Parserlib_base = Langs_common.Parserlib_base

module Loc = Astloc
module Aux = Parser_aux
module PB  = Parserlib_base
module TB  = Tokenbuffer
module SF  = Common.SourceForm
module Tk  = Tokens_


[%%capture_path
module F (Stat : Aux.STATE_T) = struct

  module TBF = Tokenbuffer.F (Stat)
  module T   = Trunk.F (Stat)
  module PP  = Tokenpp.F (Stat)
  module U   = Ulexer.F (Stat)
  module A   = Aux.F (Stat)

  type bufs = {
      b_ppbuf    : PP.buffer;
      b_trunkbuf : T.buffer;
      b_tokensrc : T.tokensource;
    }

  let mkbufs ppbuf trunkbuf tokensrc = {
      b_ppbuf    = ppbuf;
      b_trunkbuf = trunkbuf;
      b_tokensrc = tokensrc;
    }

  exception Empty

  class c
      (env : Aux.env)
      (partial_parser_selector : Context.t -> TB.partial_parser list)
      =
    object (self)
      inherit [Tk.token] PB.scanner

      val mutable current_bufs = None

      val mutable current_src = None

      val mutable last_token = PB.make_token (Tk.EOF None) Loc.dummy_lexpos Loc.dummy_lexpos

      val mutable set_ignored_regions = fun () -> ()



      method last_loc =
        Token.to_loc ~cache:(Some env#fname_ext_cache) last_token

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
        let ppbuf = current_bufs.b_ppbuf in
        let trunkbuf = current_bufs.b_trunkbuf in
        let tokensrc = current_bufs.b_tokensrc in

        if env#context_enter_flag then begin
          env#clear_context_enter_flag;
          env#set_last_active_ofss trunkbuf#get_last_offsets
        end;

        if env#context_activate_flag then begin
          env#clear_context_activate_flag;
          env#set_last_active_ofss trunkbuf#get_prev_offsets
        end;

        let current_src = self#current_src in

        if current_src#eof_reached then begin
          match current_src#eof_loc with
          | Some loc ->
              Common.fail_to_parse ~head:(Loc.to_string ~prefix:"[" ~suffix:"]" loc) "syntax error"

          | None -> assert false
        end
        else begin
          [%debug_log "calling pp"];
          let _qtoken = ppbuf#pp() in
          let qtoken = TBF.hack_token (tokensrc :> Tokensource.c) _qtoken in
          let tok, loc = qtoken in
          let token = PB.qtoken_to_token qtoken in
          [%debug_log "token --------------------> %s" (Token.to_string ~show_ext:true token)];
          (*Printf.printf "%s\n%!" (Token.to_string token);*)
          last_token <- token;
          begin
	    match tok with
	    | Tk.EOF _ -> begin
                current_src#set_eof_reached;
                current_src#set_eof_loc loc
            end
            | Tk.PP_DEFINE__IDENT__BODY _ | Tk.PP_UNDEF__IDENT _ | Tk.PP_ISSUE__MESG _
            | Tk.PP_INCLUDE__FILE _ | Tk.PP_UNKNOWN__REST _ -> ()

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
            self#guess_source_form src;
            src#get_ulexbuf
          end
        in
        let trunkbuf = new T.buffer partial_parser_selector in
        let tokensrc = new T.tokensource trunkbuf ulexbuf in
        let ppbuf =
          new PP.buffer 0 partial_parser_selector (tokensrc :> Tokensource.c)
        in
        let bufs = mkbufs ppbuf trunkbuf tokensrc in
        current_bufs <- Some bufs;
        env#set_enter_source_callback tokensrc#enter_source;
        set_ignored_regions <-
          (fun () ->
            env#ignored_regions#add_regions ppbuf#ignored_regions
          );
        ulexbuf


      method set_ignored_regions =
        set_ignored_regions()

(*
      method exit_source =
        [%debug_log "called"];
        let poped = Stack.pop stack in
        env#ignored_regions#add_regions (poped.b_ppbuf#ignored_regions);
        let bufs_opt =
          try
            Some (Stack.top stack)
          with
            Stack.Empty -> None
        in
        current_bufs <- bufs_opt
*)

      method guess_source_form src =
        let file = src#file in
        let form = U.guess_source_form file in
        env#verbose_msg "setting source form of \"%s\" to %s" file#path (SF.to_string form);
        src#set_source_form form



      initializer
        env#set_enter_source_callback self#enter_source




    end (* of class Scanner.F.c *)


end (* of functor Scanner.F *)
]
