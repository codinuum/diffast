(*
   Copyright 2012-2023 Codinuum Software Lab <https://codinuum.com>

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
(* xhash.ml *)

module C = Cryptokit

type t = Digest.t

type algo =
  | MD5
  | SHA1
  | SHA2 of int
  | SHA3 of int
  | SHA256
  | SHA384
  | SHA512
  | RIPEMD160

let algo_to_string = function
  | MD5       -> "MD5"
  | SHA1      -> "SHA1"
  | SHA2 i    -> "SHA2:"^(string_of_int i)
  | SHA3 i    -> "SHA3:"^(string_of_int i)
  | SHA256    -> "SHA256"
  | SHA384    -> "SHA384"
  | SHA512    -> "SHA512"
  | RIPEMD160 -> "RIPEMD160"

let _algo_to_hash algo =
  match algo with
  | MD5       -> C.Hash.md5()[@alert "-all"]
  | SHA1      -> C.Hash.sha1()[@alert "-all"]
  | SHA2 i    -> C.Hash.sha2 i
  | SHA3 i    -> C.Hash.sha3 i
  | SHA256    -> C.Hash.sha256()
  | SHA384    -> C.Hash.sha384()
  | SHA512    -> C.Hash.sha512()
  | RIPEMD160 -> C.Hash.ripemd160()

let digest_of_string algo str =
  (C.hash_string (_algo_to_hash algo) str : t)

let digest_of_file algo fname =
  (Xfile.load fname (C.hash_channel (_algo_to_hash algo)) : t)

(* imported from lib-ocamlnet3 by Patrick Doane and Gerd Stolpmann *)
let bytes_of_in_channel (ich : in_channel) : Bytes.t =
  (* There are similarities to copy_channel below. *)
  (* The following algorithm uses only up to 2 * N memory, not 3 * N
   * as with the Buffer module.
   *)
  let slen = 1024 in
  let l = ref [] in
  let k = ref 0 in
  try
    while true do
      let s = Bytes.create slen in
      let n = Stdlib.input ich s 0 slen in
      if n = 0 then
        failwith "bytes_of_in_channel: No data (non-blocking I/O?)";
      k := !k + n;
      if n < slen then
        l := (Bytes.sub s 0 n) :: !l
      else
        l := s :: !l;
    done;
    assert false
  with
    End_of_file ->
      let s = Bytes.create !k in
      while !l <> [] do
        match !l with
          u :: l' ->
            let n = Bytes.length u in
            k := !k - n;
            Bytes.blit u 0 s !k n;
            l := l'
        | [] -> assert false
      done;
      assert (!k = 0);
      s

let string_of_in_channel ich = Bytes.unsafe_to_string (bytes_of_in_channel ich)

let git_digest_of_ch ch =
  let hash = C.Hash.sha1()[@alert "-all"] in
  let len = Stdlib.in_channel_length ch in
  let header = Printf.sprintf "blob %d\000" len in
  begin
    hash#add_string header;
    hash#add_string (string_of_in_channel ch)
  end;
  close_in ch;
  hash#result

let git_digest_of_file fname =
  Xfile.load fname git_digest_of_ch

let to_hex (d : t) =
  C.transform_string (C.Hexa.encode()) d

let digest_hex_of_string algo str =
  to_hex (digest_of_string algo str)

let digest_hex_of_file algo fname =
  to_hex (digest_of_file algo fname)

let of_hex s =
  C.transform_string (C.Hexa.decode()) s
