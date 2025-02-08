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
(* xchannel.ml *)

module C = Compression

exception Error of string
exception File_exists of string
exception File_not_found of string

let sprintf = Printf.sprintf


(* output channel *)

module Destination = struct
  type t =
    | File of string
    | Buffer of Buffer.t
    | Channel of out_channel

  let of_file f     = File f
  let of_buffer b   = Buffer b
  let of_channel ch = Channel ch

  let to_string = function
    | File s    -> sprintf "<file:%s>" s
    | Buffer _  -> "<buffer>"
    | Channel _ -> "<out_channel>"
end

module D = Destination

class output_buffer (buf : Buffer.t) = object
  method output (bs : bytes) pos len = Buffer.add_bytes buf (Bytes.sub bs pos len)
  method flush () = ()
  method close () = Buffer.reset buf
end


class output_channel (ch : out_channel) = object
  method output (buf : bytes) pos len = Stdlib.output ch buf pos len
  method flush () = Stdlib.flush ch
  method close () = Stdlib.close_out ch
end

class gzip_output
    ?(level=C.gzip_default_compression_level)
    (w : Bytesrw.Bytes.Writer.t)
    =
  object
    val mutable writer = Obj.magic ()

    method output (buf : bytes) pos len =
      let bs = Bytes.create len in
      Bytes.blit buf pos bs 0 len;
      Bytesrw.Bytes.Writer.write_bytes writer bs

    method flush () = ()
    method close () = Bytesrw.Bytes.Writer.write_eod writer

    initializer
      let filt = Bytesrw_zlib.Gzip.compress_writes ~level () in
      writer <- filt ~eod:true w
  end

class gzip_output_channel
    ?(level=C.gzip_default_compression_level)
    (ch : out_channel)
    =
  object
    inherit gzip_output ~level (Bytesrw.Bytes.Writer.of_out_channel ch)
  end

class gzip_output_buffer
    ?(level=C.gzip_default_compression_level)
    (buf : Buffer.t)
    =
  object
    inherit gzip_output ~level (Bytesrw.Bytes.Writer.of_buffer buf)
  end


class out_channel ?(overwrite=true) ?(comp=C.none) dest
    =
  object (self)

    val mutable extchs = []

    val mutable och = Obj.magic ()

    method private close_extra =
      List.iter (fun c -> c#close()) extchs

    initializer
      let ooch =
        try
          if comp = C.none then begin
            match dest with
            | D.File file -> begin
                if Sys.file_exists file && not overwrite then
                  raise (File_exists file)
                else
                  new output_channel (open_out file)
            end
            | D.Buffer buf -> new output_buffer buf
            | D.Channel ch -> new output_channel ch
          end
          else if comp = C.gzip then begin
            let lv = comp#level in
            match dest with
            | D.File file -> begin
                if Sys.file_exists file && not overwrite then
                  raise (File_exists file)
                else
                  new gzip_output_channel ~level:lv (open_out file)
            end
            | D.Buffer buf -> begin
                let c = new gzip_output_buffer ~level:lv buf in
                extchs <- c :: extchs;
                c
            end
            | D.Channel ch -> begin
                let c = new gzip_output_channel ~level:lv ch in
                extchs <- c :: extchs;
                c
            end
          end
          else
            raise (Error "unknown compression")
        with
        | File_exists s -> raise (File_exists s)
        | e -> raise (Error (Printexc.to_string e))
      in
      och <- ooch

    method out_obj_channel = och

    method flush =
      och#flush()

    method output (buf : bytes) pos len =
      try
        och#output buf pos len
      with
      | e -> raise (Error (Printexc.to_string e))

    method output_ (buf : string) pos len =
      try
        och#output (Bytes.of_string buf) pos len
      with
      | e -> raise (Error (Printexc.to_string e))

    method close =
      try
        och#close();
        self#close_extra
      with
      | e -> raise (Error (Printexc.to_string e))

  end (* of class Xchannel.out_channel *)


let output_bytes (ch : out_channel) b =
  ignore (ch#output b 0 (Bytes.length b))

let output_string (ch : out_channel) s =
  let b = Bytes.of_string s in
  output_bytes ch b


let fprintf ch fmt = Printf.ksprintf (output_string ch) fmt

let dump : ?comp:C.c -> ?add_ext:bool -> string -> ('och -> unit) -> unit =
  fun ?(comp=C.none) ?(add_ext=true) fname dumper ->
    let fname =
      if add_ext then
        fname^comp#ext
      else
        fname
    in
    try
      let dest = Destination.of_file fname in
      let ch = new out_channel ~comp dest in
      begin
        try
          dumper ch
        with
        | Error s -> let _ = s in [%warn_log "%s" s]
      end;
      try
        ch#close
      with
      | Error s -> let _ = s in [%warn_log "%s" s]
    with
    | Error s -> let _ = s in [%warn_log "%s" s]


(* input channel *)

module Source = struct
  type t =
    | File of string
    | Channel of in_channel

  let of_file f     = File f
  let of_channel ch = Channel ch

  let to_string = function
    | File s    -> sprintf "<file:%s>" s
    | Channel _ -> "<in_channel>"
end

module S = Source


class virtual input_channel = object
  method virtual input : bytes -> int -> int -> int
  method input_line () : string = failwith "Xchannel.input_channel#input_line: not implemented"
  method virtual input_char : unit -> char
  method virtual close : unit -> unit
end

class input_channel_ch ch = object
  inherit input_channel
  method input buf pos len = Stdlib.input ch buf pos len
  method! input_line () = Stdlib.input_line ch
  method input_char () = Stdlib.input_char ch
  method close () = Stdlib.close_in ch
end

class input_channel_str str = object
  inherit input_channel

  val length = String.length str
  val mutable cur = 0

  method input buf pos len =
    if len < 1 || pos < 0 || pos >= Bytes.length buf then
      invalid_arg "Xchannel.input_channel_str#input";
    let nread = min (length - cur) len in
    try
      Bytes.blit_string str cur buf pos nread;
      cur <- cur + nread;
      nread
    with
      _ -> raise End_of_file

  method input_char () =
    try
      let c = str.[cur] in
      cur <- cur + 1;
      c
    with
      _ -> raise End_of_file

  method close () = cur <- 0
end

class gzip_input (r : Bytesrw.Bytes.Reader.t) = object

  inherit input_channel

  val mutable reader = Obj.magic ()

  method input buf pos len =
    let slice = Bytesrw.Bytes.Reader.read (Bytesrw.Bytes.Reader.sub len reader) in
    if slice = Bytesrw.Bytes.Slice.eod then
      raise End_of_file;
    let bs = Bytesrw.Bytes.Slice.bytes slice in
    let i = Bytesrw.Bytes.Slice.first slice in
    let nb = Bytesrw.Bytes.Slice.length slice in
    Bytes.blit bs i buf pos nb;
    nb

  method input_char () =
    let slice = Bytesrw.Bytes.Reader.read (Bytesrw.Bytes.Reader.sub 1 reader) in
    if slice = Bytesrw.Bytes.Slice.eod then
      raise End_of_file;
    let bs = Bytesrw.Bytes.Slice.bytes slice in
    let i = Bytesrw.Bytes.Slice.first slice in
    let c = Bytes.get bs i in
    c
    
  method close () = ()

  initializer
    let filt = Bytesrw_zlib.Gzip.decompress_reads() in
    reader <- filt r
end

class gzip_input_channel ch = object
  inherit gzip_input (Bytesrw.Bytes.Reader.of_in_channel ch)
end

let base64_buf_length = 32

class base64_input_channel (src_ich: input_channel) = object (self)
  inherit input_channel

  val encoder = Base64_rfc2045.encoder `Manual

  val mutable rem_buf = Bytes.create base64_buf_length
  val mutable rem_len = 0

  val buf1 = Bytes.create 1

  method input buf pos len =
    if rem_len > 0 then begin
      if rem_len <= len then begin
        Bytes.blit rem_buf 0 buf pos rem_len;
        let nb = rem_len in
        rem_len <- 0;
        nb
      end
      else begin (* rem_len > len *)
        Bytes.blit rem_buf 0 buf pos len;
        let new_buf = Bytes.create base64_buf_length in
        Bytes.blit rem_buf len new_buf 0 (rem_len - len);
        rem_buf <- new_buf;
        len
      end
    end
    else begin
      Base64_rfc2045.dst encoder buf pos len;
      let partial_flag = ref false in
      let count = ref 0 in
      try
        while true do
          let e =
            if !partial_flag then
              `Await
            else
              try
                let x = `Char (src_ich#input_char()) in
                incr count;
                x
              with _ -> `End
          in
          match Base64_rfc2045.encode encoder e with
          | `Ok when !partial_flag -> begin
              rem_len <- base64_buf_length - (Base64_rfc2045.dst_rem encoder);
              raise Exit
          end
          | `Ok -> ()
          | `Partial -> begin
              Base64_rfc2045.dst encoder rem_buf 0 base64_buf_length;
              partial_flag := true
          end
        done;
        0
      with
        Exit -> !count
    end

  method input_char () =
    let nb = self#input buf1 0 1 in
    if nb = 0 then
      raise End_of_file
    else
      Bytes.get buf1 0

  method close () = ()

end

let string_buf_length = 1024

let string_of_input_channel (ch : input_channel) =
  let obuf = Buffer.create 0 in
  let buf = Bytes.create string_buf_length in
  begin
    try
      while true do
        let nb = ch#input buf 0 string_buf_length in
        Buffer.add_subbytes obuf buf 0 nb
      done
    with End_of_file -> ()
  end;
  Buffer.contents obuf


class in_channel ?(comp=C.none) source
    =
  object (self)

    val mutable extchs = []

    val mutable ich = Obj.magic ()

    method close_extra () =
      List.iter (fun c -> c#close()) extchs

    initializer
      let ioch =
        try
          if comp = C.none then begin
            match source with
            | S.File file -> begin
                if not (Sys.file_exists file) then
                  raise (File_not_found file)
                else
                  new input_channel_ch (open_in file)
            end
            | S.Channel ch -> new input_channel_ch ch
          end
          else if comp = C.gzip then begin
            match source with
            | S.File file -> begin
                if Sys.file_exists file then
                  new gzip_input_channel (open_in file)
                else
                  raise (File_not_found file)
            end
            | S.Channel ch ->
                let c = new gzip_input_channel ch in
                extchs <- c :: extchs;
                c
          end
          else
            raise (Error "unknown compression")
        with
        | File_exists s    -> raise (File_exists s)
        | File_not_found s -> raise (File_not_found s)
        | e -> raise (Error (Printexc.to_string e))
      in
      ich <- ioch

    method input_channel = ich

    method input buf pos len =
      try
        ich#input buf pos len
      with
      | e -> raise (Error (Printexc.to_string e))

    method input_char () = ich#input_char()

    method close =
      try
        ich#close();
        self#close_extra()
      with
      | e -> raise (Error (Printexc.to_string e))

  end (* of class Xchannel.in_channel *)
