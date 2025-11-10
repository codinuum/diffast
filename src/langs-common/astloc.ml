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

module Xprint = Diffast_misc.Xprint


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
  { filename = "";
    start_offset = 0;
    end_offset   = 0;
    start_line   = 0;
    start_char   = 0;
    end_line     = 0;
    end_char     = 0;
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

let copy
    { filename = fname;
      start_offset = so;
      end_offset   = eo;
      start_line   = sl;
      start_char   = sc;
      end_line     = el;
      end_char     = ec;
    }
    =
  make ~fname so eo sl sc el ec

let interchange
    { filename = fname;
      start_offset = so;
      end_offset   = eo;
      start_line   = sl;
      start_char   = sc;
      end_line     = el;
      end_char     = ec;
    }
    =
  make ~fname eo so el ec sl sc

let is_valid ?(weak=false)
    { start_offset = so;
      end_offset   = eo;
      start_line   = sl;
      start_char   = sc;
      end_line     = el;
      end_char     = ec;
      _
    }
    =
  let b = so <= eo in
  if weak then
    b
  else
    b &&
    (sl <= el || (sl = el && sc <= ec))

let is_dummy loc =
  loc == dummy || (loc.start_offset < 0 && loc.end_offset < 0)


let dir_sep_pat = Str.regexp_string Filename.dir_sep

let sep = Fname.dir_sep
let sep_pat = Fname.dir_sep_pat

let encode_path = Str.global_replace dir_sep_pat sep
let decode_path = Str.global_replace sep_pat Filename.dir_sep


let rep_fmt () = format_of_string "%d:%d:%d-%d:%d:%d:%s"

let to_rep loc =
  Printf.sprintf (rep_fmt())
    loc.start_line loc.start_char loc.start_offset
    loc.end_line loc.end_char loc.end_offset
    (encode_path loc.filename)

let from_rep str =
  Scanf.sscanf (decode_path str) (rep_fmt())
    (fun sl sc so el ec eo fname ->
      make ~fname so eo sl sc el ec
    )

let is_extended loc = Fname.is_extended loc.filename

let get_stripped loc =
  if Fname.is_extended loc.filename then begin
    let cpy = copy loc in
    cpy.filename <- (Fname.strip loc.filename);
    cpy
  end
  else
    loc

let get_extended ?cache loc ext =
  if Fname.is_extended loc.filename then
    loc
  else begin
    let cpy = copy loc in
    cpy.filename <- (Fname.extend ?cache loc.filename ext);
    cpy
  end

let extend ?cache loc ext =
  if not (Fname.is_extended loc.filename) then begin
    loc.filename <- (Fname.extend ?cache loc.filename ext)
  end

let to_string ?(show_ext=false) ?(short=false) ?(prefix="") ?(suffix="") loc =
  let fstr = Fname.to_string ~show_ext ~short loc.filename in
  let fstr = if fstr = "" then "" else fstr^" " in
  if loc.start_line = loc.end_line then
    Printf.sprintf "%s%s%dL,%dC-%dC(%d-%d)%s"
      prefix
      fstr
      loc.start_line loc.start_char loc.end_char
      loc.start_offset loc.end_offset
      suffix
  else
    Printf.sprintf "%s%s%dL,%dC-%dL,%dC(%d-%d)%s"
      prefix
      fstr
      loc.start_line loc.start_char loc.end_line loc.end_char
      loc.start_offset loc.end_offset
      suffix

let start_to_string ?(show_ext=false) ?(short=false) ?(prefix="") ?(suffix="") loc =
  let fstr = Fname.to_string ~show_ext ~short loc.filename in
  Printf.sprintf "%s%s %dL,%dC(%d)%s"
    prefix fstr loc.start_line loc.start_char loc.start_offset suffix

let end_to_string ?(show_ext=false) ?(short=false) ?(prefix="") ?(suffix="") loc =
  let fstr = Fname.to_string ~show_ext ~short loc.filename in
  Printf.sprintf "%s%s %dL,%dC(%d)%s"
    prefix fstr loc.end_line loc.end_char loc.end_offset suffix

let normalize_fname fn =
  if Fname.is_extended fn then
    Fname.strip fn
  else
    fn

let select_longer s0 s1 =
  let n0 = String.length s0 in
  let n1 = String.length s1 in
  if n0 < n1 then
    s1
  else
    s0

let merge loc0 loc1 =
  if is_dummy loc0 then
    loc1
  else if is_dummy loc1 then
    loc0
  else begin
    let fn0 = loc0.filename in
    let fn1 = loc1.filename in
    let fname =
      if fn0 = fn1 then
        fn0
      else
        let sfn0 = normalize_fname fn0 in
        let sfn1 = normalize_fname fn1 in
        if sfn0 <> sfn1 then begin
          if sfn0 <> "" && sfn1 <> "" then begin
            [%warn_log "\"%s\" != \"%s\"" (Fname.escape fn0) (Fname.escape fn1)];
            failwith "Astloc.merge"
          end
        end;
        select_longer fn0 fn1
    in
    let loc =
      { filename     = fname;
        start_offset = loc0.start_offset;
        end_offset   = loc1.end_offset;
        start_line   = loc0.start_line;
        start_char   = loc0.start_char;
        end_line     = loc1.end_line;
        end_char     = loc1.end_char;
      }
    in
    if not (is_valid loc) then begin
      Xprint.warning "malformed loc: %s" (to_string loc);
      if not (is_valid ~weak:true loc) then begin
        [%warn_log "interchanged"];
        interchange loc
        (*failwith "Astloc.merge"*)
      end
      else
        loc
    end
    else
      loc
  end

let collapse_forward ?(len=1)
    { filename = fn0;
      start_offset = so0;
      start_line   = sl0;
      start_char   = sc0;
      _
    }
=
    { filename = fn0;
      start_offset = so0;
      end_offset   = so0+len-1;
      start_line   = sl0;
      start_char   = sc0;
      end_line     = sl0;
      end_char     = sc0+len-1;
    }

let collapse_backward ?(len=1)
    { filename = fn0;
      end_offset   = eo0;
      end_line     = el0;
      end_char     = ec0;
      _
    }
=
    { filename = fn0;
      start_offset = eo0-len+1;
      end_offset   = eo0;
      start_line   = el0;
      start_char   = ec0-len+1;
      end_line     = el0;
      end_char     = ec0;
    }

let widen
    { filename = fn0;
      start_offset = so0;
      end_offset   = eo0;
      start_line   = sl0;
      start_char   = sc0;
      end_line     = el0;
      end_char     = ec0;
    } d
=
    { filename = fn0;
      start_offset = so0;
      end_offset   = eo0 + d;
      start_line   = sl0;
      start_char   = sc0;
      end_line     = el0;
      end_char     = ec0 + d;
    }

let is_contained loc loc0 =
  let fn = loc.filename in
  let fn0 = loc0.filename in
  let sfn = normalize_fname fn in
  let sfn0 = normalize_fname fn0 in
  if sfn <> sfn0 then begin
    if fn <> "" && fn0 <> "" then begin
      [%warn_log "\"%s\" != \"%s\"" (Fname.escape fn) (Fname.escape fn0)];
    end;
    false
  end
  else begin
    let start_offset = loc.start_offset in
    let end_offset = loc.end_offset in
    (start_offset = 0 && end_offset = 0) ||
    loc0.start_offset <=  start_offset &&
    end_offset <= loc0.end_offset
  end


let to_offsets loc =
  loc.start_offset, loc.end_offset

let dump_locs locs =
  if (List.length locs) > 0 then begin
    let sorted =
      List.fast_sort
        (fun loc0 loc1 ->
          Stdlib.compare loc0.start_offset loc1.end_offset
        ) locs
    in
    List.iter
      (fun loc ->
        Printf.printf "%s\n" (to_string loc)
      ) sorted
  end

let lines_of_locs locs =
  List.fold_left
    (fun n loc ->
      n + loc.end_line - loc.start_line + 1
    ) 0 locs


let mklexpos ?(fname="") ?(lnum=1) ?(bol=0) i =
    { Lexing.pos_fname = fname;
      Lexing.pos_lnum  = lnum;
      Lexing.pos_bol   = bol;
      Lexing.pos_cnum  = i
    }

let of_lexpos pos =
  let fn = pos.Lexing.pos_fname in
  let c = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
  make
    ~fname:fn
    pos.Lexing.pos_cnum
    pos.Lexing.pos_cnum
    pos.Lexing.pos_lnum
    c
    pos.Lexing.pos_lnum
    c

let of_lexposs st_pos ed_pos =
  let st_fn = st_pos.Lexing.pos_fname in
  let ed_fn = ed_pos.Lexing.pos_fname in
  let fname =
    if st_fn = ed_fn then
      st_fn
    else
      let s_st_fn = normalize_fname st_fn in
      let s_ed_fn = normalize_fname ed_fn in
      if s_st_fn <> s_ed_fn then begin
        if st_fn <> "" && ed_fn <> "" then begin
          [%warn_log "%s != %s" (Fname.escape st_fn) (Fname.escape ed_fn)];
          failwith "Astloc.of_lexposs"
        end
      end;
      select_longer st_fn ed_fn
  in
  make
    ~fname
    st_pos.Lexing.pos_cnum
    ed_pos.Lexing.pos_cnum
    st_pos.Lexing.pos_lnum
    (st_pos.Lexing.pos_cnum - st_pos.Lexing.pos_bol)
    ed_pos.Lexing.pos_lnum
    (ed_pos.Lexing.pos_cnum - ed_pos.Lexing.pos_bol)


let incr_n_lexpos n pos =
  let cnum = pos.Lexing.pos_cnum + n in
  mklexpos
    ~fname:pos.Lexing.pos_fname
    ~lnum:pos.Lexing.pos_lnum
    ~bol:pos.Lexing.pos_bol
    cnum

let decr_n_lexpos n pos =
  let cnum = pos.Lexing.pos_cnum - n in
  if cnum < pos.Lexing.pos_bol then begin
    [%debug_log "invalid argument: pos_cnum=%d pos_bol=%d n=%d"
       pos.Lexing.pos_cnum pos.Lexing.pos_bol n];
    invalid_arg "Astloc.decr_n_lexpos"
  end;
  mklexpos
    ~fname:pos.Lexing.pos_fname
    ~lnum:pos.Lexing.pos_lnum
    ~bol:pos.Lexing.pos_bol
    cnum

let incr_lexpos = incr_n_lexpos 1
let decr_lexpos = decr_n_lexpos 1


let gt_lexpos pos1 pos2 =
  pos1.Lexing.pos_cnum > pos2.Lexing.pos_cnum

let lt_lexpos pos1 pos2 =
  pos1.Lexing.pos_cnum < pos2.Lexing.pos_cnum

let ge_lexpos pos1 pos2 =
  pos1.Lexing.pos_cnum >= pos2.Lexing.pos_cnum

let le_lexpos pos1 pos2 =
  pos1.Lexing.pos_cnum <= pos2.Lexing.pos_cnum

let dummy_lexpos = mklexpos (-1)

let to_start_lexpos loc =
  let fn = loc.filename in
  mklexpos
    ~fname:fn ~lnum:loc.start_line ~bol:(loc.start_offset-loc.start_char)
    loc.start_offset

let to_end_lexpos loc =
  let fn = loc.filename in
  mklexpos
    ~fname:fn ~lnum:loc.end_line ~bol:(loc.end_offset-loc.end_char)
    loc.end_offset

let to_lexposs loc =
  let fn = loc.filename in
  mklexpos
    ~fname:fn ~lnum:loc.start_line ~bol:(loc.start_offset-loc.start_char)
    loc.start_offset,
  mklexpos
    ~fname:fn ~lnum:loc.end_line ~bol:(loc.end_offset-loc.end_char)
    loc.end_offset

let lexpos_to_string { Lexing.pos_fname = fn;
                       Lexing.pos_lnum = l;
                       Lexing.pos_bol = b;
                       Lexing.pos_cnum = c
                     }
    =
  Printf.sprintf "%s%dL,%dC"
    (if fn = "" then "" else "\""^(Fname.escape fn)^"\" ") l (c - b)
