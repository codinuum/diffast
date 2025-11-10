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
(* macro.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xstring = Diffast_misc.Xstring


module Loc = Astloc

type stat =
  | Unresolved
  | Resolved of Obj.t

let stat_to_string = function
  | Unresolved -> "UNRESOLVED"
  | Resolved _ -> "RESOLVED"

let stat_resolved = function
  | Resolved _ -> true
  | _ -> false

let tok_of_stat = function
  | Resolved o -> Obj.obj o
  | _ -> raise Not_found


type line = {         ln_raw         : string;
              mutable ln_stat        : stat;
              mutable ln_conditional : bool;
                      ln_loc         : Loc.t;
            }

let mk_line ?(loc=Loc.dummy) ?(raw="<predefined>") ?(conditional=false) mktok id =
  { ln_raw=raw;
    ln_stat=Resolved (Obj.repr (mktok id));
    ln_conditional=conditional;
    ln_loc=loc;
  }

let line_to_string { ln_raw         = raw;
                     ln_stat        = stat;
                     ln_conditional = b;
                     ln_loc         = loc;
                   } =
  Printf.sprintf "{%s%s:%s%s}"
    (stat_to_string stat)
    (if b then ":conditional" else "")
    raw
    (if loc = Loc.dummy then "" else "@"^(Loc.to_string loc))

let tok_of_line ln = tok_of_stat ln.ln_stat

let _resolve_line ln x = ln.ln_stat <- Resolved x

let resolve_line ln x = _resolve_line ln (Obj.repr x)

let line_resolved ln = stat_resolved ln.ln_stat




type body =
  | Object of line
  | Function of string list * line

let mk_obj_body ?(loc=Loc.dummy) ?(stat=Unresolved) ?(conditional=false) s =
  Object { ln_raw=Xstring.strip s;
           ln_stat=stat;
           ln_conditional=conditional;
           ln_loc=loc;
         }

let mk_fun_body ?(loc=Loc.dummy) ?(stat=Unresolved) ?(conditional=false) sl s =
  Function(sl, { ln_raw=Xstring.strip s;
                 ln_stat=stat;
                 ln_conditional=conditional;
                 ln_loc=loc;
               }
          )

let line_of_body = function
  | Object ln
  | Function(_, ln) -> ln

let body_to_string = function
  | Object ln        -> Printf.sprintf "OBJ%s" (line_to_string ln)
  | Function(sl, ln) -> Printf.sprintf "FUN(%s)%s" (String.concat "," sl) (line_to_string ln)

let body_to_rep = function
  | Object ln        -> Printf.sprintf "{%s}" ln.ln_raw
  | Function(sl, ln) -> Printf.sprintf "(%s){%s}" (String.concat "," sl) ln.ln_raw

let body_length = function
  | Object ln        -> String.length ln.ln_raw
  | Function(_, ln) -> String.length ln.ln_raw

let _resolve_body x = function
  | Object ln
  | Function(_, ln) -> _resolve_line ln x

let resolve_body x = _resolve_body (Obj.repr x)

let body_is_conditional = function
  | Object ln
  | Function(_, ln) -> ln.ln_conditional

let body_set_conditional = function
  | Object ln
  | Function(_, ln) -> ln.ln_conditional <- true

let body_clear_conditional = function
  | Object ln
  | Function(_, ln) -> ln.ln_conditional <- false



[%%capture_path
class table (tname : string) = object (self)

  val tbl : (string, body) Hashtbl.t = Hashtbl.create 0

  val mutable readonly_flag = false

  val hidden : (string, int) Hashtbl.t = Hashtbl.create 0

  method name = tname

  method hide id =
    let n =
      try
        Hashtbl.find hidden id
      with
        Not_found -> 0
    in
    let n' = n + 1 in
    [%debug_log "[%s] %s: %d -> %d" tname id n n'];
    Hashtbl.replace hidden id n'

  method expose id =
    let n =
      try
        Hashtbl.find hidden id
      with
        Not_found -> 0
    in
    let n' = n - 1 in
    [%debug_log "[%s] %s: %d -> %d" tname id n n'];
    if n' = 0 then
      Hashtbl.remove hidden id
    else
      Hashtbl.replace hidden id n'

  method readonly = readonly_flag
  method set_readonly = readonly_flag <- true

  method find id =
    (*[%debug_log "[%s] %s" tname id];*)
    try
      let n = Hashtbl.find hidden id in
      let l = Hashtbl.find_all tbl id in
      (*[%debug_log "[%s] found %d binds (discard %d)" tname (List.length l) n];*)
      List.nth l n
    with
    | Not_found -> Hashtbl.find tbl id
    | Failure _ -> raise Not_found

  method find_all id =
    (*[%debug_log "[%s] %s" tname id];*)
    try
      let n = Hashtbl.find hidden id in
      let l = Hashtbl.find_all tbl id in
      (*[%debug_log "[%s] found %d binds (discard %d)" tname (List.length l) n];*)
      let r = ref l in
      try
        for _ = 1 to n do
          r := List.tl !r
        done;
        !r
      with
        Failure _ -> []
    with
      Not_found -> Hashtbl.find_all tbl id

  method define ?(conditional=false) id body =
    if not readonly_flag then begin
      if conditional then
        body_set_conditional body;
      [%debug_log "[%s] \"%s\" --> %s%s"
        tname id (body_to_string body) (if conditional then " (conditional)" else "")];
      Hashtbl.add tbl id body
    end

  method undefine id =
    if not readonly_flag then begin
      [%debug_log "[%s] \"%s\"" tname id];
      Hashtbl.remove tbl id
    end

  method clear =
    Hashtbl.clear tbl

  method is_defined s = Hashtbl.mem tbl s

  method is_uniquely_defined s =
    try
      match self#find_all s with
      | [_] -> true
      | _ -> false
    with
      Not_found -> false

  method is_unconditionally_defined id =
    try
      match self#find_all id with
      | [] ->
          [%debug_log "not found: %s" id];
          false
      | bodies ->
          [%debug_log "found: %s ->\n%s" id (Xlist.to_string body_to_string "\n" bodies)];
          List.exists (fun body -> not (body_is_conditional body)) bodies
    with
      Not_found -> false

  method is_undefined s = not (Hashtbl.mem tbl s)

end (* of calss Macro.table *)
]
