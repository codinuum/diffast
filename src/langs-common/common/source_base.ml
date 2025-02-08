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
(* source_base.ml *)

[%%prepare_logger]

module Xchannel = Diffast_misc.Xchannel
module Storage = Diffast_misc.Storage

module Loc = Astloc


let array_set = Array.unsafe_set
let bytes_get = Bytes.unsafe_get
let bytes_fill = Bytes.unsafe_fill
let bytes_blit = Bytes.unsafe_blit
let bytes_to_string = Bytes.unsafe_to_string


type encoding =
  | E_Latin1
  | E_UTF8
  | E_UTF16BE
  | E_UTF16LE

let default_encoding = E_UTF8

let encoding_to_string = function
  | E_Latin1 -> "Latin1"
  | E_UTF8 -> "UTF8"
  | E_UTF16BE -> "UTF16BE"
  | E_UTF16LE -> "UTF16LE"

let internal_ubuf_size = 512


let linefeed = Uchar.of_int 0xa


let char_to_str c = String.escaped (Printf.sprintf "%c" c)

let uchar_to_str uc =
  if Uchar.is_char uc then
    char_to_str (Uchar.to_char uc)
  else
    Printf.sprintf "U+%X;" (Uchar.to_int uc)


let _ = bytes_to_string
let _ = uchar_to_str


module Latin1 = struct
  let check_length _ = 1
  let get_uchar buf i = Uchar.utf_decode 1 (Uchar.of_char (bytes_get buf i))
  let is_valid_utf _ = true
  let utf_byte_length _ = 1
  let max_bytes_per_uchar = 1
end

[%%capture_path
module Utf8 = struct
  let check_length c = (* derive length from head char *)
    let b = Char.code c in
    let len =
      if b land 0b10000000 = 0 then
        1
      else if b land 0b11100000 = 0b11000000 then
        2
      else if b land 0b11110000 = 0b11100000 then
        3
      else if b land 0b11111000 = 0b11110000 then
        4
      else
        invalid_arg "Utf8.check_length"
    in
    [%debug_log "c='%s' b=%#x %#o (%d) len=%d" (char_to_str c) b b b len];
    len

  let get_uchar = Bytes.get_utf_8_uchar
  let is_valid_utf = Bytes.is_valid_utf_8
  let utf_byte_length = Uchar.utf_8_byte_length
  let max_bytes_per_uchar = 4

end
]


[%%capture_path
module Utf16 = struct

  let check_length c = (* derive length from head char *)
    let b = Char.code c in
    let len =
      if b land 0b11111100 = 0b11011000 then
        4
      else
        2
    in
    [%debug_log "c='%s' b=%#x %#o (%d) len=%d" (char_to_str c) b b b len];
    len

  module BE = struct
    let get_uchar = Bytes.get_utf_16be_uchar
    let is_valid_utf = Bytes.is_valid_utf_16be
  end

  module LE = struct
    let get_uchar = Bytes.get_utf_16le_uchar
    let is_valid_utf = Bytes.is_valid_utf_16le
  end

  let utf_byte_length = Uchar.utf_16_byte_length
  let max_bytes_per_uchar = 4

end
]


[%%capture_path
class c (file : Storage.file) =
  let tree = file#tree in
  let path = file#path in
  object (self)

    val pos_mgr = new Position.manager path

    val mutable eof_reached = false
    val mutable eof_loc : Loc.t option = None

    val mutable channel = None

    val mutable encoding = default_encoding

    val mutable utf_check_length = Utf8.check_length
    val mutable get_uchar = Utf8.get_uchar
    val mutable is_valid_utf = Utf8.is_valid_utf
    val mutable utf_byte_length = Utf8.utf_byte_length
    val mutable max_bytes_per_uchar = Utf8.max_bytes_per_uchar

    val mutable ulexbuf_list = []

    val mutable eof_flag = false

    val mutable internal_buf_size = internal_ubuf_size * 4
    val mutable internal_buf = Bytes.create (internal_ubuf_size * 4)
    val internal_ubuf = Array.make internal_ubuf_size Uchar.min

    val mutable last_uchar = Uchar.min

    val mutable bytes_decoded = 0
    val mutable last_bytes = 0


    method update_encoding ?(update_buf=true) enc =
      encoding <- enc;
      begin
        match enc with
        | E_Latin1 -> begin
            utf_check_length <- Latin1.check_length;
            get_uchar <- Latin1.get_uchar;
            is_valid_utf <- Latin1.is_valid_utf;
            utf_byte_length <- Latin1.utf_byte_length;
            max_bytes_per_uchar <- Latin1.max_bytes_per_uchar;
        end
        | E_UTF8 -> begin
            utf_check_length <- Utf8.check_length;
            get_uchar <- Utf8.get_uchar;
            is_valid_utf <- Utf8.is_valid_utf;
            utf_byte_length <- Utf8.utf_byte_length;
            max_bytes_per_uchar <- Utf8.max_bytes_per_uchar;
        end
        | E_UTF16BE -> begin
            utf_check_length <- Utf16.check_length;
            get_uchar <- Utf16.BE.get_uchar;
            is_valid_utf <- Utf16.BE.is_valid_utf;
            utf_byte_length <- Utf16.utf_byte_length;
            max_bytes_per_uchar <- Utf16.max_bytes_per_uchar;
        end
        | E_UTF16LE -> begin
            utf_check_length <- Utf16.check_length;
            get_uchar <- Utf16.LE.get_uchar;
            is_valid_utf <- Utf16.LE.is_valid_utf;
            utf_byte_length <- Utf16.utf_byte_length;
            max_bytes_per_uchar <- Utf16.max_bytes_per_uchar;
        end
      end;
      if update_buf then begin
        internal_buf_size <- internal_ubuf_size * max_bytes_per_uchar;
        internal_buf <- Bytes.create internal_buf_size
      end


    method tree = tree

    method path = path

    method init =
      pos_mgr#reset

    method eof_reached = eof_reached
    method set_eof_reached = eof_reached <- true

    method eof_loc = eof_loc
    method set_eof_loc loc = eof_loc <- Some loc

    method file = file

    method filename = pos_mgr#filename
    method set_filename fn = pos_mgr#set_filename fn
    method pos_mgr = pos_mgr

    method exists = file#exists

    method get_channel =
      let ch =
        try
          tree#get_channel self#filename
        with
          Sys_error s -> failwith ("Source_base.c#get_channel: "^s)
      in
      ch

    method get_ulexbuf_from_channel ch =
      let ulexbuf =
        Sedlexing.create ~bytes_per_char:utf_byte_length (self#refill ch)
      in
      Sedlexing.set_filename ulexbuf self#filename;
      ulexbuf_list <- ulexbuf :: ulexbuf_list;
      ulexbuf

    method get_ulexbuf =
      let ch = self#get_channel in
      channel <- Some ch;
      self#get_ulexbuf_from_channel ch

    method close =
      match channel with
      | Some ch -> begin
          ch#close();
          [%debug_log "%s closed" path]
      end
      | None -> ()

    method get_ulexbuf_from_stdin =
      match encoding with
      | E_Latin1 -> Sedlexing.Latin1.from_channel stdin
      | E_UTF8 -> Sedlexing.Utf8.from_channel stdin
      | E_UTF16BE -> Sedlexing.Utf16.from_channel stdin (Some Sedlexing.Utf16.Big_endian)
      | E_UTF16LE -> Sedlexing.Utf16.from_channel stdin (Some Sedlexing.Utf16.Little_endian)


    method private read_uchar () =
      let dec =
        let dec = get_uchar internal_buf bytes_decoded in
        if Uchar.utf_decode_is_valid dec then begin
          begin %trace_block
            let c = bytes_get internal_buf bytes_decoded in
            let b = Char.code c in
            [%trace_log "bytes_decoded=%d '%s' %#x %#o (%d)"
               bytes_decoded (char_to_str c) b b b]
          end;
          dec
        end
        else begin
          let c = bytes_get internal_buf bytes_decoded in
          let _ = c in
          begin %trace_block
            let b = Char.code c in
            [%trace_log "decode failed: bytes_decoded=%d '%s' %#x %#o (%d)"
               bytes_decoded (char_to_str c) b b b]
          end;
          [%warn_log "[%s] invalid character '%s'"
             (encoding_to_string encoding) (char_to_str c)];
          [%warn_log "falling back to latin1 encoding"];
          self#update_encoding ~update_buf:false E_Latin1;
          get_uchar internal_buf bytes_decoded
        end
      in
      let uc = Uchar.utf_decode_uchar dec in
      [%trace_log "uc=%s" (uchar_to_str uc)];
      uc

    method refill ch ubuf pos n =
      [%debug_log "|ubuf|=%d pos=%d n=%d" (Array.length ubuf) pos n];
      try
        [%debug_log "bytes_decoded=%d last_bytes=%d" bytes_decoded last_bytes];

        let req_size, ofs =
          if bytes_decoded < last_bytes then begin
            let bbuf = Bytes.create internal_buf_size in
            let rem = last_bytes - bytes_decoded in
            bytes_blit internal_buf bytes_decoded bbuf 0 rem;
            internal_buf <- bbuf;
            internal_buf_size - rem, rem
          end
          else
            internal_buf_size, 0
        in
        [%debug_log "ofs=%d req_size=%d" ofs req_size];

        let bytes_read = ch#input internal_buf ofs req_size in
        last_bytes <- ofs + bytes_read;
        [%debug_log "internal_buf_size=%d bytes_read=%d last_bytes=%d"
           internal_buf_size bytes_read last_bytes];

        if last_bytes = 0 then begin
          if eof_flag then
            0
          else begin
            [%debug_log "last_uchar='%s'" (uchar_to_str last_uchar)];
            if Uchar.equal last_uchar linefeed then
              0
            else begin
              eof_flag <- true;
              array_set ubuf pos linefeed;
              1
            end
          end
        end
        else begin
          if last_bytes < internal_buf_size then begin
            let d = min 3 (internal_buf_size - last_bytes) in
            bytes_fill internal_buf last_bytes d '\000'
          end;
          [%debug_log "internal_buf=%s" (bytes_to_string internal_buf)];

          bytes_decoded <- 0;
          let nc = ref 0 in
          let line_len = ref 0 in

          while !nc < n && bytes_decoded < last_bytes do
            [%trace_log "bytes_decoded=%d nc=%d" bytes_decoded !nc];

            (*let d = last_bytes - bytes_decoded in
            if d < 3 then begin
              [%debug_log "bytes_decoded=%d d=%d" bytes_decoded d];
              try
                let blen = utf_check_length (bytes_get internal_buf bytes_decoded) in
                [%debug_log "blen=%d" blen];
                if blen > 1 then begin
                  if blen > d then begin
                    let blen_ = blen - d in
                    [%debug_log "reading %d more bytes" blen_];
                    let actual_blen = ch#input internal_buf (bytes_decoded + 1) blen_ in
                    let _ = actual_blen in
                    [%debug_log "actual_blen=%d" actual_blen]
                  end
                end
              with Invalid_argument _ -> ()
            end;*)

            let uc = (self#read_uchar[@inlined])() in

            if Uchar.equal uc linefeed then begin
              pos_mgr#feedline (!line_len + 1);
              line_len := -1
            end;

            array_set ubuf (pos + !nc) uc;
            last_uchar <- uc;

            let uc_len = utf_byte_length uc in
            [%trace_log "uc_len=%d" uc_len];

            bytes_decoded <- bytes_decoded + uc_len;
            incr nc;
            incr line_len
          done;

          if !line_len > 0 then
            pos_mgr#feed !line_len;

          begin %debug_block
            let cbuf = Buffer.create 0 in
            for i = pos to pos + !nc - 1 do
              let c = ubuf.(i) in
              if Uchar.is_char c then
                Buffer.add_char cbuf (Uchar.to_char c)
              else
                Buffer.add_char cbuf '?'
            done;
            [%debug_log "ubuf[%d:%d]=%s"
               pos (pos + !nc) (Buffer.contents cbuf)];
          end;

          [%debug_log "nc=%d" !nc];

          !nc

        end

      with
      | End_of_file -> 0
      (*| exc -> begin
          [%warn_log "\"%s\": %s: \"%s\""
             file#fullpath (Printexc.to_string exc) (bytes_to_string internal_buf)];
          failwith ("Source_base.c#refill: " ^ (Printexc.to_string exc))
      end*)


end (* of class Sourcefile_base.c *)
]
