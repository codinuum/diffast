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
(* *)

type ext_cache_t = (string * string, string) Hashtbl.t

let ext_sep = '\000'
let ext_sep_pat = Str.regexp_string (String.make 1 ext_sep)

let dir_sep = "\028"
let dir_sep_pat = Str.regexp_string dir_sep

let loc_sep = "\004"
let loc_sep_pat = Str.regexp_string loc_sep


let is_extended fname = String.contains fname ext_sep

let extend ?cache ?(force=false) fname ext =
  let ok =
    if force then
      true
    else
      ext <> "" && fname <> "" && not (is_extended fname)
  in
  if ok then begin
    let gen () = Printf.sprintf "%s%c%s" fname ext_sep ext in
    match cache with
    | Some c -> begin
        let key = (fname, ext) in
        try
          Hashtbl.find (c : ext_cache_t) key
        with
          Not_found ->
            let x = gen() in
            Hashtbl.add c key x;
            x
    end
    | None -> gen()
  end
  else
    fname

let strip fname =
  try
    let i = String.index fname ext_sep in
    String.sub fname 0 i
  with
    Not_found -> fname

let get_extension fname =
  try
    let i = String.index fname ext_sep in
    String.sub fname (i+1) ((String.length fname) - i - 1)
  with
    _ -> ""

let escape fname =
  Str.global_replace ext_sep_pat "@"
    (Str.global_replace loc_sep_pat "@"
       (Str.global_replace dir_sep_pat Filename.dir_sep
          fname
       )
    )

let to_string ?(show_ext=false) ?(short=false) (fname : string) =
  let fn =
    if show_ext then
      escape fname
    else
      strip fname
  in
  if fn = "" then
    ""
  else
    "\""^
    (if short && not show_ext then
      Filename.basename fn
    else
      fn
    )^
    "\""
