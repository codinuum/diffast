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
(* loc.ml *)

open Printf

type t =
    { mutable filename : string;
      start_offset : int;
      end_offset   : int;
      start_line   : int;
      start_char   : int;
      end_line     : int;
      end_char     : int;
    }

let dummy =
  { filename     = "";
    start_offset = -1;
    end_offset   = -1;
    start_line   = -1;
    start_char   = -1;
    end_line     = -1;
    end_char     = -1;
  }

let ghost =
  { filename     = "";
    start_offset = -10;
    end_offset   = -10;
    start_line   = -10;
    start_char   = -10;
    end_line     = -10;
    end_char     = -10;
  }

let make ?(fname="") so eo sl sc el ec =
  { filename     = fname;
    start_offset = so;
    end_offset   = eo;
    start_line   = sl;
    start_char   = sc;
    end_line     = el;
    end_char     = ec;
  }

let _merge loc0 loc1 =
  let fn0, fn1 = loc0.filename, loc1.filename in
  if fn0 <> fn1  then
    [%warn_log "\"%s\" != \"%s\"" fn0 fn1];
  { filename     = fn0;
    start_offset = loc0.start_offset;
    end_offset   = loc1.end_offset;
    start_line   = loc0.start_line;
    start_char   = loc0.start_char;
    end_line     = loc1.end_line;
    end_char     = loc1.end_char;
  }

let lines loc =
  loc.end_line - loc.start_line + 1

let to_offsets loc =
  loc.start_offset, loc.end_offset

let is_contained loc loc0 =
  if loc.start_offset < 0 || loc0.start_offset < 0 then
    false (* unknown location *)
  else if loc.filename <> loc0.filename then
    false
  else
    let start_offset = loc.start_offset in
    let end_offset = loc.end_offset in
    (start_offset = 0 && end_offset = 0) ||
    loc0.start_offset <=  start_offset &&
    end_offset <= loc0.end_offset


let merge loc0 loc1 =
  if is_contained loc0 loc1 then
    loc1
  else if is_contained loc1 loc0 then
    loc0
  else if loc0.start_offset < loc1.start_offset then
    _merge loc0 loc1
  else
    _merge loc1 loc0

let extend_end loc n = (* does not modify line end *)
    { filename     = loc.filename;
      start_offset = loc.start_offset;
      end_offset   = loc.end_offset + n;
      start_line   = loc.start_line;
      start_char   = loc.start_char;
      end_line     = loc.end_line;
      end_char     = loc.end_char + n;
    }

let to_string ?(long=false) loc =
  let fns =
    if loc.filename = "" then
      ""
    else if long then
      "\""^loc.filename^"\" "
    else
      "\""^(Filename.basename loc.filename)^"\" "
  in

  if loc = ghost then
    "<GHOST>"

  else if loc = dummy then
    "<DUMMY>"

  else if loc.start_line = loc.end_line then
    if loc.start_char >= 0 && loc.end_char >= 0 then
      sprintf "%s%dL,%dC-%dC(%d-%d)" fns loc.start_line loc.start_char loc.end_char
        loc.start_offset loc.end_offset
    else
      sprintf "%s%dL(%d-%d)" fns loc.start_line loc.start_offset loc.end_offset
  else
    if loc.start_char >= 0 && loc.end_char >= 0 then
      sprintf "%s%dL,%dC-%dL,%dC(%d-%d)" fns
        loc.start_line loc.start_char loc.end_line loc.end_char
        loc.start_offset loc.end_offset
    else
      sprintf "%s%dL-%dL(%d-%d)" fns
        loc.start_line loc.end_line loc.start_offset loc.end_offset

let to_attr_value loc =
  if loc.start_char >= 0 && loc.end_char >= 0 then
    sprintf "%d:%d(%d)-%d:%d(%d)"
      loc.start_line loc.start_char loc.start_offset
      loc.end_line loc.end_char loc.end_offset
  else
    sprintf "%d(%d)-%d(%d)"
      loc.start_line loc.start_offset
      loc.end_line loc.end_offset


let compare loc0 loc1 =
  if loc0.filename <> loc1.filename then
    failwith "Loc.compare"

  else if is_contained loc0 loc1 || is_contained loc1 loc0 then
    0
  else if loc0.end_offset <= loc1.start_offset then
    -1
  else if loc1.end_offset <= loc0.start_offset then
    1
  else
    assert false

let meet loc0 loc1 =
  let fn0, fn1 = loc0.filename, loc1.filename in
  if fn0 <> fn1  then
    [%warn_log "file mismatch: %s and %s" (to_string ~long:true loc0) (to_string ~long:true loc1)];
  if is_contained loc0 loc1 then
    loc0
  else if is_contained loc1 loc0 then
    loc1
  else if loc0.end_offset < loc1.start_offset then
    failwith "Loc.meet"
  else if loc1.end_offset < loc0.start_offset then
    failwith "Loc.meet"
  else
    let tbl = [ loc0.start_offset, (loc0.start_line, loc0.start_char);
                loc0.end_offset, (loc0.end_line, loc0.end_char);
                loc1.start_offset, (loc1.start_line, loc1.start_char);
                loc1.end_offset, (loc1.end_line, loc1.end_char);
              ]
    in
    let so = max loc0.start_offset loc1.start_offset in
    let eo = min loc0.end_offset loc1.end_offset in
    let sl, sc = List.assoc so tbl in
    let el, ec = List.assoc eo tbl in
    { filename     = fn0;
      start_offset = so;
      end_offset   = eo;
      start_line   = sl;
      start_char   = sc;
      end_line     = el;
      end_char     = ec;
    }
