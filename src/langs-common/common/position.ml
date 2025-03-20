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
(*
 * position handling
 *
 * position.ml
 *
 *)

[%%prepare_logger]


let lexing_pos_start = Sedlexing.lexing_position_start

let[@inline always] lexing_pos_end ulexbuf =
  let pos_ = Sedlexing.lexing_position_curr ulexbuf in
  let pos =
    try
      Astloc.decr_n_lexpos 1 pos_
    with
      Invalid_argument _ -> pos_
  in
  pos

let get_lc pos = pos.Lexing.pos_lnum, pos.Lexing.pos_cnum - pos.Lexing.pos_bol


[%%capture_path
class manager (fn : string) = object (self)

  val mutable filename = fn

  val mutable start_offset = 0
  val mutable characters_read = 0

  val mutable lines_read = 0
  val mutable newline = 0


  method to_string =
    let l = [
      "lines_read", string_of_int lines_read;
      "characters_read", string_of_int characters_read;
      "newline", string_of_int newline;
    ] in
    String.concat ","
      ((Printf.sprintf "filename:\"%s\"" filename)::
       (List.map (fun (k, v) -> Printf.sprintf "%s=%s" k v) l))

  method filename = filename
  method set_filename f = filename <- f


  method feed n =
    [%debug_log "n=%d" n];
    characters_read <- characters_read + n

  method feedline n =
    [%debug_log "n=%d" n];
    lines_read <- lines_read + 1;
    start_offset <- characters_read;
    characters_read <- characters_read + n;
    newline <- characters_read - 1;


  method get_position ofs =
    [%debug_log "ofs=%d" ofs];
    match ofs with
    | 0 -> begin
        [%debug_log "%d -> (1, 0)" ofs];
        1, 0
    end

    | _ when ofs > newline -> begin
        [%debug_log "lines_read=%d" lines_read];
        [%debug_log "newline=%d" newline];
        let l = lines_read + 1 in
        let c = ofs - newline - 1 in
        [%debug_log "%d -> (%d, %d)" ofs l c];
        l, c
    end

    | _ -> raise Not_found


  method get_current_position =
    self#get_position start_offset

  method reset =
    lines_read <- 0;
    start_offset <- 0;
    characters_read <- 0;
    newline <- 0;

  method lines_read = lines_read

  method show_status =
    Printf.printf "\nLines read: %d\nCharacters read: %d\n"
      lines_read characters_read

  method _offsets_to_loc start_offset end_offset start_line start_char end_line end_char =
    let loc =
      Astloc.make ~fname:filename
        start_offset end_offset start_line start_char end_line end_char
    in
    loc

  method offsets_to_loc start_offset end_offset =
    let start_line, start_char = self#get_position start_offset in
    let end_line, end_char     = self#get_position end_offset in
    let loc =
      self#_offsets_to_loc start_offset end_offset start_line start_char end_line end_char
    in
    loc

  method lexposs_to_loc ?(get_position=true) st_pos ed_pos =
    let _ = get_position in
    (*if get_position then
      self#offsets_to_loc st_pos.Lexing.pos_cnum ed_pos.Lexing.pos_cnum
    else*)
      let so = st_pos.Lexing.pos_cnum in
      let eo = ed_pos.Lexing.pos_cnum in
      self#_offsets_to_loc so eo
        st_pos.Lexing.pos_lnum (so - st_pos.Lexing.pos_bol)
        ed_pos.Lexing.pos_lnum (eo - ed_pos.Lexing.pos_bol)


  initializer
    self#reset


end (* of class Position.manager *)
]
