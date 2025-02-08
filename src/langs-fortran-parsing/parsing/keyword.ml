(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2020 Chiba Institude of Technology

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

(* Author: Masatomo Hashimoto <m.hashimoto@stair.center> *)



open Tokens_

let find_position_spec_keyword =
  let keyword_list =
    [
      "unit",     (fun s -> UNIT s);
      "iomsg",    (fun s -> IOMSG s); (* F2003 *)
      "iostat",   (fun s -> IOSTAT s);
      "err",      (fun s -> ERR s);
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> IDENTIFIER s
  in
  find

let find_flush_spec_keyword = find_position_spec_keyword

let find_wait_spec_keyword =
  let keyword_list =
    [
      "end", (fun s -> END s);
      "eor", (fun s -> EOR s);
      "id",  (fun s -> ID s);
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_position_spec_keyword s
  in
  find


let find_close_connect_spec_keyword =
  let keyword_list =
    [
      "dispose", (fun s -> INTEL_CLOSE_CONNECT_SPEC s);
      "disp",    (fun s -> INTEL_CLOSE_CONNECT_SPEC s);
      "type",    (fun s -> INTEL_CLOSE_CONNECT_SPEC s);
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_position_spec_keyword s
  in
  find

let find_close_spec_keyword =
  let keyword_list =
    [
      "status",  (fun s -> STATUS s);
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_close_connect_spec_keyword s
  in
  find


let find_connect_inquire_ioctl_spec_keyword =
  let keyword_list =
    [
      "asynchronous", (fun s -> ASYNCHRONOUS s);
      "blank",        (fun s -> CONNECT_INQUIRE_IOCTL_SPEC s);
      "decimal",      (fun s -> CONNECT_INQUIRE_IOCTL_SPEC s);
      "delim",        (fun s -> CONNECT_INQUIRE_IOCTL_SPEC s);
      "pad",          (fun s -> CONNECT_INQUIRE_IOCTL_SPEC s);
      "round",        (fun s -> CONNECT_INQUIRE_IOCTL_SPEC s);
      "sign",         (fun s -> CONNECT_INQUIRE_IOCTL_SPEC s);
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_position_spec_keyword s
  in
  find


let find_connect_inquire_spec_keyword =
  let keyword_list =
    [
      "file",            (fun s -> FILE s);

      "access",          (fun s -> CONNECT_INQUIRE_SPEC s);
      "action",          (fun s -> CONNECT_INQUIRE_SPEC s);
      "async",           (fun s -> CONNECT_INQUIRE_SPEC s); (* IBM *)
      "encoding",        (fun s -> CONNECT_INQUIRE_SPEC s);
      "form",            (fun s -> CONNECT_INQUIRE_SPEC s);
      "position",        (fun s -> CONNECT_INQUIRE_SPEC s);
      "recl",            (fun s -> CONNECT_INQUIRE_SPEC s);

(* Compaq Fortran *)
      "buffered",          (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "carriagecontrol",   (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "convert",           (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "defaultfile",       (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "iofocus",           (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "mode",              (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "organization",      (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "organisation",      (fun s -> CONNECT_INQUIRE_SPEC s); (* ??? *)
      "recordsize",        (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "recordtype",        (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
      "share",             (fun s -> CONNECT_INQUIRE_SPEC s); (* Intel *)
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_connect_inquire_ioctl_spec_keyword s
  in
  find

let find_connect_spec_keyword =
  let keyword_list =
    [
      "name",    (fun s -> NAME_ s);        (* Intel *)
      "newunit", (fun s -> CONNECT_SPEC s);
      "status",  (fun s -> STATUS s);

      "associatevariable", (fun s -> CONNECT_SPEC s); (* Intel *)
      "blocksize",         (fun s -> CONNECT_SPEC s); (* Intel *)
      "buffercount",       (fun s -> CONNECT_SPEC s); (* Intel *)
      "maxrec",            (fun s -> CONNECT_SPEC s); (* Intel *)
      "readonly",          (fun s -> CONNECT_SPEC s); (* Intel *)
      "shared",            (fun s -> CONNECT_SPEC s); (* Intel *)
      "title",             (fun s -> CONNECT_SPEC s); (* Intel *)
      "useropen",          (fun s -> CONNECT_SPEC s); (* Intel *)
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_connect_inquire_spec_keyword s
  in
  find


let find_io_control_spec_keyword =
  let keyword_list =
    [
      "fmt",     (fun s -> FMT s);
      "nml",     (fun s -> NML s);

      "advance", (fun s -> (*ADVANCE*)IOCTL_SPEC s);
      "end",     (fun s -> END s);
      "eor",     (fun s -> EOR s);
      "id",      (fun s -> INQUIRE_IOCTL_SPEC s);
      "num",     (fun s -> IOCTL_SPEC s); (* IBM *)
      "pos",     (fun s -> INQUIRE_IOCTL_SPEC s);
      "rec",     (fun s -> (*REC*)IOCTL_SPEC s);
      "size",    (fun s -> INQUIRE_IOCTL_SPEC s);
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_connect_inquire_ioctl_spec_keyword s
  in
  find


let find_inquire_spec_keyword =
  let keyword_list =
    [
      "direct",      (fun s -> INQUIRE_SPEC s);
      "exist",       (fun s -> INQUIRE_SPEC s);
      "formatted",   (fun s -> INQUIRE_SPEC s);
      "id",          (fun s -> INQUIRE_IOCTL_SPEC s);
      "iolength",    (fun s -> IOLENGTH s);
      "name",        (fun s -> NAME_ s);
      "named",       (fun s -> INQUIRE_SPEC s);
      "nextrec",     (fun s -> INQUIRE_SPEC s);
      "number",      (fun s -> INQUIRE_SPEC s);
      "opened",      (fun s -> INQUIRE_SPEC s);
      "pending",     (fun s -> INQUIRE_SPEC s);
      "pos",         (fun s -> INQUIRE_IOCTL_SPEC s);
      "readwrite",   (fun s -> INQUIRE_SPEC s);
      "sequential",  (fun s -> INQUIRE_SPEC s);
      "size",        (fun s -> INQUIRE_IOCTL_SPEC s);
      "stream",      (fun s -> INQUIRE_SPEC s);
      "unformatted", (fun s -> INQUIRE_SPEC s);

      "binary",      (fun s -> INQUIRE_SPEC s); (* Intel *)
      "strid",       (fun s -> INQUIRE_SPEC s); (* Apollo *)

    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> find_connect_inquire_spec_keyword s
  in
  find

let find_language_binding_spec_keyword =
  let keyword_list =
    [
      "name",        (fun s -> NAME_ s);
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keyword_list
  in
  let find s =
    try
      (Hashtbl.find keyword_table (String.lowercase_ascii s)) s
    with
      Not_found -> IDENTIFIER s
  in
  find


let find_separated_keyword =
  let concat l = String.concat "" l in
  let keyword_list =
    [
      ["block"; "data"],       (fun l -> BLOCK_DATA (concat l));
      ["double"; "precision"], (fun l -> DOUBLE_PRECISION (concat l));
      ["double"; "complex"],   (fun l -> DOUBLE_COMPLEX (concat l)); (* non-standard ext. *)
      ["else"; "if"],          (fun l -> ELSE_IF (concat l));
      ["else"; "where"],       (fun l -> ELSEWHERE (concat l)); (* non-standard ext. *)
      ["end"; "associate"],    (fun l -> END_ASSOCIATE (concat l)); (* F2003 *)
      ["end"; "block"],        (fun l -> END_BLOCK (concat l));
      ["end"; "blockdata"],    (fun l -> END_BLOCK_DATA (concat l));
      ["endblock"; "data"],    (fun l -> END_BLOCK_DATA (concat l));
      ["end"; "critical"],     (fun l -> END_CRITICAL (concat l));
      ["end"; "do"],           (fun l -> END_DO (concat l));
      ["end"; "enum"],         (fun l -> END_ENUM (concat l)); (* F2003 *)
      ["end"; "file"],         (fun l -> END_FILE (concat l));
      ["end"; "forall"],       (fun l -> END_FORALL (concat l));
(*      ["end"; "function"],     (fun l -> END_FUNCTION (concat l));*)
      ["end"; "function"],     (fun l -> END_SUBPROGRAM (concat l));
      ["end"; "if"],           (fun l -> END_IF (concat l));
      ["end"; "interface"],    (fun l -> END_INTERFACE (concat l));
      ["end"; "module"],       (fun l -> END_MODULE (concat l));
      ["end"; "procedure"],    (fun l -> END_PROCEDURE (concat l)); (* F2008 *)
      ["end"; "program"],      (fun l -> END_PROGRAM (concat l));
      ["end"; "select"],       (fun l -> END_SELECT (concat l));
      ["end"; "submodule"],    (fun l -> END_SUBMODULE (concat l)); (* F2008 *)
(*      ["end"; "subroutine"],   (fun l -> END_SUBROUTINE (concat l));*)
      ["end"; "subroutine"],   (fun l -> END_SUBPROGRAM (concat l));
      ["end"; "type"],         (fun l -> END_TYPE (concat l));
      ["end"; "where"],        (fun l -> END_WHERE (concat l));
      ["go"; "to"],            (fun l -> GO_TO (concat l));
      ["in"; "out"],           (fun l -> INTENT_SPEC (concat l));
      ["select"; "case"],      (fun l -> SELECT_CASE (concat l));
      ["select"; "type"],      (fun l -> SELECT_TYPE (concat l)); (* F2003 *)

      ["end"; "structure"],    (fun l -> END_STRUCTURE (concat l)); (* Compaq Fortran *)
      ["end"; "union"],        (fun l -> END_UNION (concat l));     (* Compaq Fortran *)
      ["end"; "map"],          (fun l -> END_MAP (concat l));       (* Compaq Fortran *)
(*      ["define"; "file"],      (fun l -> DEFINE_FILE (concat l));   (* Compaq Fortran *)*)
    ] in
  let keyword_table = Hashtbl.create (List.length keyword_list) in
  let _ =
    List.iter (fun (kwd_list, tok) -> Hashtbl.add keyword_table kwd_list tok)
      keyword_list
  in
  let lowercase l = List.map String.lowercase_ascii l in
  let find sl =
    (Hashtbl.find keyword_table (lowercase sl)) sl
  in
  find

