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
(* fragment.ml *)

module GI = Diffast_misc.GIndex


exception Found
exception Invalid_format of string

type gid = GI.t

type elem = Fsingle of gid | Frange of gid * gid

let elem_to_string = function
  | Fsingle n -> Printf.sprintf "%d" n
  | Frange(n1, n2) -> Printf.sprintf "%d-%d" n1 n2

class c = object (self)
  val mutable _list = [] (* elem list *)
  val mutable _rep = "" (* ex. 1;4-9;13;19-42 *)

  method hash =
    Digest.to_hex (Digest.string _rep)


  method size =
    let sz = ref 0 in
    List.iter
      (function
        | Fsingle _      -> incr sz
        | Frange(i1, i2) -> sz := !sz + i2 - i1 + 1
      ) _list;
    !sz

  method get_list =
    let res = ref [] in
    List.iter
      (function
        | Fsingle i      -> res := i::!res
        | Frange(i1, i2) ->
            for j = i1 to i2 do
              res := j::!res
            done
      ) _list;
    !res


  method to_string = _rep

  method set_rep rep =
    _rep <- rep;
    self#sync_list

  method set_list l =
    _list <- [];
    let l = List.fast_sort Stdlib.compare l in
    let st_opt = ref None in
    let prev_opt = ref None in
    List.iter
      (fun cur ->
        begin
          match !st_opt with
            None ->
              st_opt := Some cur
          | Some st -> begin
              match !prev_opt with
                None -> () (* impossible *)
              | Some prev ->
                  if cur = prev + 1 then
                    ()
                  else begin
                    if st = prev then
                      _list <- (Fsingle st)::_list
                    else
                      _list <- (Frange(st, prev))::_list;
                    st_opt := Some cur
                  end
          end
        end;
        prev_opt := Some cur
      ) (l @ [max_int]);
    _list <- List.rev _list;
    self#sync_rep

  method private sync_rep =
    _rep <- String.concat ";" (List.map elem_to_string _list)

  method private sync_list =
    let cur = ref None in
    let buf = Buffer.create 0 in
    String.iter
      (fun c ->
        if c = ';' then begin
          let ns = Buffer.contents buf in
          let n =
            try
              int_of_string ns
            with Failure _ -> raise (Invalid_format ns)
          in
          begin
            match !cur with
              Some i -> _list <- (Frange(i, n))::_list
            | _ -> _list <- (Fsingle n)::_list
          end;
          cur := None;
          Buffer.clear buf
        end
        else if c = '-' then
          let ns = Buffer.contents buf in
          let n =
            try
              int_of_string ns
            with Failure _ -> raise (Invalid_format ns)
          in
          cur := Some n;
          Buffer.clear buf
        else begin
          Buffer.add_char buf c
        end
      ) _rep;
    let rest = Buffer.contents buf in
    if rest <> "" then begin
      let n =
        try
          int_of_string rest
        with Failure _ -> raise (Invalid_format rest)
      in
      begin
        match !cur with
          Some i -> _list <- (Frange(i, n))::_list
        | _ -> _list <- (Fsingle n)::_list
      end
    end;
    _list <- List.rev _list

  method contains i =
    try
      List.iter
        (function
            Fsingle n ->
              if n = i then
                raise Found
          | Frange(n1, n2) ->
              if n1 <= i && i <= n2 then
                raise Found
        ) _list;
      false
    with Found -> true

end (* of class GIDfragment.c *)

let from_list l =
  let f = new c in
  f#set_list l;
  f

let load fpath =
  let l = ref [] in
  begin
    try
      let ich = open_in fpath in
      begin
        try
          while true do
            let line = input_line ich in
            let frag = new c in
            frag#set_rep line;
            l := frag::!l
          done
        with End_of_file -> ()
      end;
      close_in ich
    with exn ->
      [%warn_log "load: %s" (Printexc.to_string exn)];
      raise exn
  end;
  let res = List.rev !l in
  res
