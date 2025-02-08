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
(* Limited Length List *)


type 'a cell = { mutable content : 'a;
                 mutable prev : 'a cell;
                 mutable next : 'a cell;
               }

type 'a t = { mutable head : 'a cell;
              mutable length : int;
            }

class ['a] c capacity = object(* (self : 'self)*)

  val repr = { head=Obj.magic None;
               length=0;
             }

  method length = repr.length

  method clear =
    repr.length <- 0;
    repr.head   <- Obj.magic None


  method add x =
    if repr.length = 0 then begin
      let rec cell = { content=x; next=cell; prev=cell } in
      repr.length <- 1;
      repr.head <- cell
    end
    else if repr.length = capacity then begin
      repr.head <- repr.head.prev;
      repr.head.content <- x;
    end
    else begin
      let hd = repr.head in
      let tl = repr.head.prev in
      let cell = { content=x; prev=tl; next=hd } in
      repr.length <- repr.length + 1;
      hd.prev <- cell;
      tl.next <- cell;
      repr.head <- cell
    end

  method iter (f : 'a -> unit) =
    if repr.length > 0 then
      let tl = repr.head.prev in
      let rec iter cell =
        f cell.content;
        if cell != tl then
          iter cell.next
      in
      iter repr.head

  initializer
    if capacity <= 0 then
      raise (Invalid_argument (Printf.sprintf "LLL.c#init: invalid capacity %d" capacity))

end (* class LLL.c *)
