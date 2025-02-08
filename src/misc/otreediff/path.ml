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

module Elem = struct

  type t = { mutable pos : int;
             mutable ofs : float;
           }

  let ofs_to_str o =
    let s = string_of_float o in
    let len = String.length s in
    if s.[len - 1] = '.' then
      String.sub s 0 (len - 1)
    else
      s

  let to_string elem =
    Printf.sprintf "%d%s" elem.pos
      (if elem.ofs = 0. then
        ""
      else
        "_"^(ofs_to_str elem.ofs)
      )

  let elem_pat =
    Str.regexp "^\\([0-9]+\\)\\(_\\(-?[0-9]+\\(\\.[0-9]*\\)?\\)\\)?$"

  let of_string s =
    if Str.string_match elem_pat s 0 then begin
      let p = int_of_string (Str.matched_group 1 s) in
      let o =
        try
          float_of_string (Str.matched_group 3 s)
        with
          Not_found -> 0.
      in
      {pos=p;ofs=o}
    end
    else
      failwith "Path.elem_of_str"

  let make ?(ofs=0.) pos = {pos=pos;ofs=ofs}

  let dummy = make (-1)

  let has_frac_ofs elem =
    (fst (modf elem.ofs)) > 0.

  let strip {pos=pos;ofs=_} =
    make pos

  let get_offset_pos elem =
    if (fst (modf elem.ofs)) = 0. then
      elem.pos + (int_of_float elem.ofs)
    else
      elem.pos

  let compare elem0 elem1 =
    compare (elem0.pos, elem0.ofs) (elem1.pos, elem1.ofs)

end (* module Path.Elem *)


type t = PATH of Elem.t list (* in reverse order *)

exception Invalid_path of string

let to_string = function
  | PATH elems -> (Xlist.to_string Elem.to_string "/" (List.rev elems))

let sep_pat = Str.regexp_string "/"

let of_string s =
  try
    PATH (List.rev (List.map Elem.of_string (Str.split sep_pat s)))
  with
    Failure _ -> raise (Invalid_path s)

let root = PATH []

let strip = function
  | PATH elems -> PATH (List.map Elem.strip elems)

let length = function
  | PATH elems -> List.length elems

let append = function
  | PATH elems -> fun elem -> PATH (elem :: elems)

let append_pos ?(ofs=0.) path pos =
  match path with
  | PATH es -> PATH ((Elem.make ~ofs pos) :: es)

[%%capture_path
let set_ofs path ofs =
  [%debug_log "path=\"%s\" ofs=%s" (to_string path) (Elem.ofs_to_str ofs)];
  match path with
  | PATH (elem::_) -> elem.Elem.ofs <- ofs
  | _ -> assert false
]

let concat path1 path2 =
  match path1, path2 with
  | PATH es1, PATH es2 -> PATH (es2 @ es1)

[%%capture_path
let remove_head head path = (* ignore ofs *)
  [%debug_log "\"%s\" from \"%s\"" (to_string head) (to_string path)];
  match head, path with
  | PATH hd, PATH pa ->
      let rec doit h l =
        match h, l with
        | eh::h1, el::l1 ->
            if eh.Elem.pos = el.Elem.pos then
              doit h1 l1
            else
              failwith "Path.remove_head"
        | [], _ -> l
        | _ -> failwith "Path.remove_head"
      in
      PATH (List.rev (doit (List.rev hd) (List.rev pa)))
]

[%%capture_path
let remove_head_n n path = (* ignore ofs *)
  [%debug_log "removing %d elems from \"%s\"" n (to_string path)];
  match path with
  | PATH pa ->
      let rec doit i l =
        match l with
        | _::l1 when i > 0 -> doit (i-1) l1
        | [] when i > 0 -> failwith "Path.remove_head"
        | _ -> l
      in
      PATH (List.rev (doit n (List.rev pa)))
]

let get_positions = function
  | PATH elems ->
      List.rev
        (List.map (fun elem -> elem.Elem.pos) elems)

let get_elems = function
  | PATH elems -> List.rev elems

let split path =
  match path with
  | PATH (elem::parent) -> PATH parent, elem
  | _ -> failwith "Path.split"

let get_parent path =
  match path with
  | PATH (_::parent) -> PATH parent
  | _ -> failwith "Path.get_parent"

let get_offset path =
  match path with
  | PATH (elem::_) -> elem.Elem.ofs
  | _ -> failwith "Path.get_offset"

let get_position path =
  match path with
  | PATH (elem::_) -> elem.Elem.pos
  | _ -> failwith "Path.get_position"

let head path n =
  let len = length path in
  if n < 0 then begin
    match path with
    | PATH elems ->
        let l = ref elems in
        try
          for (*i*)_ = 1 to -n do
            l := List.tl !l
          done;
          PATH !l
        with
          _ -> root
  end
  else begin
    if n = 0 then
      root
    else if n = len then
      path
    else if n > len then
      failwith "Path.head"
    else
      match path with
      | PATH elems ->
          let l = ref elems in
          for (*i*)_ = 1 to len - n do
            l := List.tl !l
          done;
          PATH !l
  end

let tail path =
  match path with
  | PATH (elem::_) -> elem
  | _ -> failwith "Path.tail"

let nth = function
  | PATH elems ->
      fun nth ->
        try
          List.nth (List.rev elems) nth
        with
          _ -> invalid_arg "Path.nth"

let eq path0 path1 =
  let len0 = length path0 in
  let len1 = length path1 in
  if len0 = len1 then begin
    try
      List.iter2
        (fun e0 e1 ->
          if e0.Elem.pos <> e1.Elem.pos then
            raise Exit
        ) (get_elems path0) (get_elems path1);
      true
    with
      Exit -> false
  end
  else
    false

let is_prefix ?(exact=true) path0 path =
  let len0 = length path0 in
  let len = length path in
  if len0 > len then
    false
  else if len0 = len then
    if exact then
        path0 = path
    else
      eq path0 path
  else
    let p = head path len0 in
    if exact then
      p = path0
    else
      eq p path0

let compare path0 path1 =
  match path0, path1 with
  | PATH el0, PATH el1 -> begin
      let rec scan = function
        | e0::t0, e1::t1 -> begin
            let c = Elem.compare e0 e1 in
            if c = 0 then
              scan (t0, t1)
            else
              c
        end
        | _::_, [] -> -1
        | [], _::_ -> 1
        | [], [] -> 0
      in
      scan (List.rev el0, List.rev el1)
  end
