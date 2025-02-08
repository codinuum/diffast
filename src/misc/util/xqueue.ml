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
(* Based on OCaml Stdlib *)

exception Empty = Queue.Empty

type 'a cell = { mutable content : 'a;
                 mutable next    : 'a cell;
               }

type 'a t = { mutable length : int;
              mutable tail   : 'a cell;
            }

class ['a] c = object (self : 'self)

  val repr = { length=0; tail=(Obj.magic None) }

  val mutable last_accessed_index = 0
  val mutable last_accessed_cell = Obj.magic None

  method repr = (repr : 'a t)

  method clear =
    repr.length <- 0;
    repr.tail   <- Obj.magic None;
    last_accessed_index <- 0;
    last_accessed_cell <- Obj.magic None

  method add x =
    if repr.length = 0 then
      let rec cell = { content=x; next=cell } in
      repr.length <- 1;
      repr.tail <- cell
    else
      let tl = repr.tail in
      let hd = tl.next in
      let cell = { content=x; next=hd } in
      repr.length <- repr.length + 1;
      tl.next <- cell;
      repr.tail <- cell

  method peek =
    if repr.length = 0 then begin
      raise Empty
    end
    else begin
      last_accessed_cell <- repr.tail.next;
      last_accessed_index <- 1;
      last_accessed_cell.content
    end

  method peek_last =
    if repr.length = 0 then begin
      raise Empty
    end
    else
      repr.tail.content

  method peek_nth n =
    if n = 1 then
      try
        self#peek
      with
        Empty -> failwith "Xqueue.c#peek_nth"
    else if n < 1 || n > self#length then
      failwith "Xqueue.c#peek_nth"
    else begin
      if last_accessed_index = n - 1 then begin
        last_accessed_cell <- last_accessed_cell.next;
      end
      else begin
        last_accessed_cell <- repr.tail.next;
        for _ = 2 to n do
          last_accessed_cell <- last_accessed_cell.next
        done
      end;
      last_accessed_index <- n;
      last_accessed_cell.content
    end

  method take =
    if repr.length = 0 then
      raise Empty;
    repr.length <- repr.length - 1;
    last_accessed_index <- last_accessed_index - 1;
    let tl = repr.tail in
    let hd = tl.next in
    if hd == tl then
      repr.tail <- Obj.magic None
    else
      tl.next <- hd.next;
    hd.content

  method copy =
    if repr.length = 0 then
      {< repr = { length = 0; tail = Obj.magic None }; last_accessed_index = 0 >}
    else
      let tl = repr.tail in
      let rec tl' = { content=tl.content; next=tl' } in
      let rec copy prev cell =
        if cell != tl then
          let res = { content=cell.content; next=tl' } in
          prev.next <- res;
          copy res cell.next
      in
      copy tl' tl.next;
      {< repr = { length = repr.length; tail = tl' }; last_accessed_index = 0 >}

  method is_empty = repr.length = 0

  method length = repr.length

  method private iter_cell (f : 'a cell -> unit) =
    if repr.length > 0 then
      let tl = repr.tail in
      let rec iter cell =
        f cell;
        if cell != tl then
          iter cell.next
      in
      iter tl.next

  method iter (f : 'a -> unit) =
    if repr.length > 0 then
      let tl = repr.tail in
      let rec iter cell =
        f cell.content;
        if cell != tl then
          iter cell.next
      in
      iter tl.next

  method fold : 'b. ('b -> 'a -> 'b) -> 'b -> 'b =
    fun f accu ->
    if repr.length = 0 then
      accu
    else
      let tl = repr.tail in
      let rec fold accu cell =
        let accu = f accu cell.content in
        if cell == tl then
          accu
        else
          fold accu cell.next
      in
      fold accu tl.next

  method transfer (q : 'self) =
    let len = repr.length in
    if len > 0 then begin
      let tl = repr.tail in
      self#clear;
      if q#length > 0 then begin
        let tl' = q#repr.tail in
        let hd = tl.next in
        let hd' = tl'.next in
        tl.next <- hd';
        tl'.next <- hd
      end;
      q#repr.length <- (q#length + len);
      q#repr.tail <- tl
    end

  method prepend_from (q : 'self) =
    let len' = q#length in
    if len' > 0 then begin
      let tl' = q#repr.tail in
      let hd' = tl'.next in
      q#clear;
      if self#is_empty then begin
        repr.length <- len';
        repr.tail <- tl'
      end
      else begin
        let hd = repr.tail.next in
        repr.length <- (repr.length + len');
        last_accessed_index <- last_accessed_index + len';
        repr.tail.next <- hd';
        tl'.next <- hd
      end
    end

  method prepend (x : 'a) =
    if self#is_empty then
      self#add x
    else
      let tl = repr.tail.next in
      let cell = { content=x; next=tl } in
      repr.length <- repr.length + 1;
      last_accessed_index <- last_accessed_index + 1;
      repr.tail.next <- cell

  method remove_last =
    let len = repr.length in
    if len = 1 then begin
      self#clear
    end
    else if len > 1 then begin
      let last2 = ref repr.tail in
      for _ = 1 to len - 1 do
        last2 := (!last2).next
      done;
      repr.length <- repr.length - 1;
      (!last2).next <- repr.tail.next;
      repr.tail <- !last2
    end

  method filter (f : 'a -> bool) =
    let q = Queue.create() in
    self#iter
      (fun x ->
        if f x then
          Queue.add x q
      );
    self#clear;
    Queue.iter self#add q

  method replace (subst : 'a -> 'a) =
    self#iter_cell
      (fun cell ->
        cell.content <- subst cell.content
      )


end (* class Xqueue.c *)
