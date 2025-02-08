(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>

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
(* *)

let string_len_threshold = 32


let char_to_string c = String.make 1 c

let sep0 = "\x10"
let sep1 = "\x11"
let sep2 = "\x12"
let sep3 = "\x13"


let char_pool = (* 126 safe characters *)
  let ranges = [(0x30,0x39); (0x41,0x5a); (0x61,0x7a); (0xc0,0xff)] in
  let len = List.fold_left (fun a (st, ed) -> a + ed - st + 1) 0 ranges in
  let arr = Array.make len '0' in
  let n = ref 0 in
  List.iter
    (fun (st, ed) ->
      for i = st to ed do
	arr.(!n) <- Char.chr(i);
	incr n
      done
    ) ranges;
  arr

let char_pool_len = Array.length char_pool

let catstr strl = String.concat sep0 strl

let mkstr idx = char_to_string char_pool.(idx)

let encode_ids ?(ignore_identifiers_flag=false) id_list =
  if ignore_identifiers_flag then
    []
  else
    id_list

let combo ?(ignore_identifiers_flag=false) idx id_list =
  catstr ((mkstr idx)::(encode_ids ~ignore_identifiers_flag id_list))

let encode_strs str_list =
  let no_digest = ref true in
  let string_list =
    List.map
      (fun str ->
	if (String.length str) > string_len_threshold then begin
	  no_digest := false;
	  Digest.to_hex (Digest.string str)
	end
	else
	  str
      ) str_list
  in
  string_list, !no_digest

let mkstr_strs idx str_list = (* next index must be idx+2 *)
  let string_list, no_digest = encode_strs str_list in
  catstr ((mkstr (if no_digest then idx+1 else idx))::string_list)


(*
let mkstr_str idx str =
  if (String.length str) > string_len_threshold then
    catstr [mkstr idx; Digest.to_hex(Digest.string str)]
  else
    catstr [mkstr (idx+1); str]
*)

let mkstr_str idx str = mkstr_strs idx [str]


let mkstr2 idx =
  let c0 = char_pool.(idx / char_pool_len) in
  let c1 = char_pool.(idx mod char_pool_len) in
  let res = Bytes.make 2 c1 in
  Bytes.set res 0 c0;
  Bytes.to_string res

let combo2 ?(ignore_identifiers_flag=false) idx id_list =
  catstr ((mkstr2 idx)::(encode_ids ~ignore_identifiers_flag id_list))

let mkstr2_strs idx str_list =
  let string_list, no_digest = encode_strs str_list in
  catstr ((mkstr2 (if no_digest then idx+1 else idx))::string_list)

let mkstr2_str idx str = mkstr2_strs idx [str]
