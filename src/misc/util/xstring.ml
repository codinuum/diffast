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
(* xstring.ml *)


let startswith s s0 =
  let len = String.length s in
  let len0 = String.length s0 in

  if len < len0 then
    false
  else
    try
      for i = 0 to len0 - 1 do
        if s.[i] != s0.[i] then
          raise Exit
      done;
      true
    with
    | Exit -> false

let endswith s s0 =
  let len = String.length s in
  let len0 = String.length s0 in
  if len < len0 then
    false
  else
    try
      for i = len - len0 to len - 1 do
        if s.[i] != s0.[i - (len - len0)] then
          raise Exit
      done;
      true
    with
    | Exit -> false


let white_spaces = ["\t"; " "; "\n"]


let rec rstrip ?(strs=white_spaces) s =
  let s0_opt =
    let rec doit = function
      | [] -> None
      | s0::rest ->
          if endswith s s0 then
            Some s0
          else
            doit rest
    in
    doit strs
  in
  match s0_opt with
  | None -> s
  | Some s0 ->
      let len = (String.length s) - (String.length s0) in
      rstrip ~strs:[s0] (String.sub s 0 len)



let rec lstrip ?(strs=white_spaces) s =
  let s0_opt =
    let rec doit = function
      | [] -> None
      | s0::rest ->
          if startswith s s0 then
            Some s0
          else
            doit rest
    in
    doit strs
  in
  match s0_opt with
  | None -> s
  | Some s0 ->
      let len0 = String.length s0 in
      let len = (String.length s) - len0 in
      lstrip ~strs:[s0] (String.sub s len0 len)


let strip ?(strs=white_spaces) s =
  rstrip ~strs (lstrip ~strs s)


let to_int_array s =
  let len = String.length s in
  let a = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- Char.code(s.[i])
  done;
  a

let to_char_array s =
  let len = String.length s in
  let a = Array.make len ' ' in
  for i = 0 to len - 1 do
    a.(i) <- s.[i]
  done;
  a

let encode s =
  let buf = Buffer.create 0 in
  String.iter
    (fun c ->
      Buffer.add_string buf (Printf.sprintf "%02x" (Char.code c));
    ) s;
  Buffer.contents buf

let decode encoded =
  let buf = Buffer.create 0 in
  let len = String.length encoded in
  if len mod 2 <> 0 then
    raise (Invalid_argument "Xstring.decode");
  for i = 0 to len / 2 - 1 do
    let b = String.sub encoded (2 * i) 2 in
    Scanf.sscanf b "%x" (fun code -> Buffer.add_char buf (Char.chr code));
  done;
  Buffer.contents buf



external length     : bytes -> int                 = "%bytes_length"
external create     : int -> bytes                 = "caml_create_bytes"
external unsafe_get : bytes -> int -> char         = "%bytes_unsafe_get"
external unsafe_set : bytes -> int -> char -> unit = "%bytes_unsafe_set"
external char_code  : char -> int                  = "%identity"
external char_chr   : int -> char                  = "%identity"

let bts = Bytes.to_string
let bos = Bytes.of_string

let _escaped (s : bytes) =
  let n = ref 0 in
  for i = 0 to length s - 1 do
    n := !n +
      (match unsafe_get s i with
       | '\"' | '\\' | '\n' | '\t' | '\r' | '\b' -> 2
       | ' ' .. '~' -> 1
       | c -> if (char_code c) > 127 then 1 else 4)
  done;
  if !n = length s then Bytes.copy s else begin
    let s' = create !n in
    n := 0;
    for i = 0 to length s - 1 do
      begin match unsafe_get s i with
      | ('\"' | '\\') as c ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n c
      | '\n' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'n'
      | '\t' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 't'
      | '\r' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'r'
      | '\b' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'b'
      | (' ' .. '~') as c -> unsafe_set s' !n c
      | c ->
          let a = char_code c in
          if a > 127 then
            unsafe_set s' !n c
          else begin
            unsafe_set s' !n '\\';
            incr n;
            unsafe_set s' !n (char_chr (48 + a / 100));
            incr n;
            unsafe_set s' !n (char_chr (48 + (a / 10) mod 10));
            incr n;
            unsafe_set s' !n (char_chr (48 + a mod 10));
          end
      end;
      incr n
    done;
    s'
  end

let _ntriples_escaped (s : bytes) =
  let n = ref 0 in
  for i = 0 to length s - 1 do
    n := !n +
        (match unsafe_get s i with
        | '"' | '\\' | '\n' | '\t' | '\r' -> 2
        | '\b' -> 3
        | ' ' .. '~' -> 1
        | c -> if (char_code c) > 127 then 1 else 5)
  done;
  if !n = length s then Bytes.copy s else begin
    let s' = create !n in
    n := 0;
    for i = 0 to length s - 1 do
      begin match unsafe_get s i with
      | ('"' | '\\') as c ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n c
      | '\n' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'n'
      | '\t' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 't'
      | '\r' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'r'
      | '\b' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n '\\';
          incr n; unsafe_set s' !n 'b'
      | (' ' .. '~') as c -> unsafe_set s' !n c
      | c ->
          let a = char_code c in
          if a > 127 then
            unsafe_set s' !n '?'
          else begin
            unsafe_set s' !n '\\';
            incr n;
            unsafe_set s' !n '\\';
            incr n;
            unsafe_set s' !n (char_chr (48 + a / 100));
            incr n;
            unsafe_set s' !n (char_chr (48 + (a / 10) mod 10));
            incr n;
            unsafe_set s' !n (char_chr (48 + a mod 10))
          end
      end;
      incr n
    done;
    s'
  end

let needs_escape (s : bytes) =
  let rec _needs_escape i =
    if i >= length s then
      false
    else
      match unsafe_get s i with
      | '\"' | '\\' | '\n' | '\t' | '\r' | '\b' -> true
      | ' ' .. '~' -> _needs_escape (i+1)
      | _ -> true
  in
  _needs_escape 0

let escaped s =
  let b = bos s in
  if needs_escape b then
    bts (_escaped b)
  else
    s

let ntriples_escaped s =
  let b = bos s in
  if needs_escape b then
    bts (_ntriples_escaped b)
  else
    s

let remove_quotes s =
  let len = String.length s in
  if len > 1 then
    String.sub s 1 (len-2)
  else
    s
