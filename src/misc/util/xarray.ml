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
(* xarray.ml *)


let to_string to_str sep a =
  Xlist.to_string to_str sep (Array.to_list a)

let filter f a =
  let l = Array.to_list a in
  Array.of_list (List.filter f l)

let exists f a =
  try
    Array.iter
      (fun x ->
        if f x then
          raise Exit
      ) a;
    false
  with
    Exit -> true

let for_all f a =
  try
    Array.iter
      (fun x ->
        if not (f x) then
          raise Exit
      ) a;
    true
  with
    Exit -> false

let iter2 f a1 a2 =
  let len1 = Array.length a1 in
  let len2 = Array.length a2 in
  if len1 <> len2 then
    raise (Invalid_argument "Xarray.iter2")
  else
    for i = 0 to len1 - 1 do
      f a1.(i) a2.(i)
    done

exception Index_out_of_bounds of int

class ['a] array_list block_size = object (self)

  val mutable block_list = []
  val mutable nblocks = 0
  val mutable last_index = -1

  method private get_block i = List.nth block_list i

  method clear =
    block_list <- [];
    nblocks <- 0;
    last_index <- -1

  method length = last_index + 1

  method is_empty = last_index < 0

  method get idx =
    if idx < 0 || idx > last_index then
      raise (Index_out_of_bounds idx)
    else
      let bi = idx / block_size in
      let i = idx mod block_size in
      let b = self#get_block bi in
      b.(i)

  method set idx x =
    if idx < 0 || idx > last_index then
      raise (Index_out_of_bounds idx)
    else
      let bi = idx / block_size in
      let i = idx mod block_size in
      let b = self#get_block bi in
      b.(i) <- x

  method add (x : 'a) =
    let idx = last_index + 1 in
    let bi = idx / block_size in
    let i = idx mod block_size in
    if bi < nblocks then begin
      let b = self#get_block bi in
      b.(i) <- x
    end
    else begin
      let b = Array.make block_size x in
      block_list <- block_list @ [b];
      nblocks <- nblocks + 1
    end;
    last_index <- idx

  method iter (f : 'a -> unit) =
    let last_bi = nblocks - 1 in
    let last_i = last_index mod block_size in
    List.iteri
      (fun bi b ->
        if bi = last_bi then
          for i = 0 to last_i do
            f b.(i)
          done
        else
          Array.iter f b
      ) block_list

  method iteri (f : int -> 'a -> unit) =
    let last_bi = nblocks - 1 in
    let last_i = last_index mod block_size in
    List.iteri
      (fun bi b ->
        let n =
          if bi = last_bi then
            last_i
          else
            block_size - 1
        in
        let a = bi * block_size in
        for i = 0 to n do
          f (a + i) b.(i)
        done
      ) block_list

  method to_string to_str =
    let buf = Buffer.create 0 in
    Buffer.add_string buf "[";
    self#iter
      (fun x ->
        Buffer.add_string buf (to_str x);
        Buffer.add_string buf ";"
      );
    Buffer.add_string buf "]";
    Buffer.contents buf

end (* Xarray.array_list *)

module A = Bigarray.Array1

let kind = Bigarray.int
let layout = Bigarray.c_layout

class int_array_list block_size = object (self)

  val block_tbl = Hashtbl.create 0
  val mutable nblocks = 1
  val mutable last_index = -1
  val mutable last_local_index = -1
  val mutable current_block = A.create kind layout block_size

  initializer
    Hashtbl.add block_tbl 0 current_block

  method private get_block i = Hashtbl.find block_tbl i

  method clear =
    Hashtbl.clear block_tbl;
    nblocks <- 1;
    last_index <- -1;
    last_local_index <- -1;
    current_block <- A.create kind layout block_size;
    Hashtbl.add block_tbl 0 current_block

  method length = last_index + 1

  method is_empty = last_index < 0

  method get idx =
    match idx with
    | _ when idx < 0 || idx > last_index -> raise (Index_out_of_bounds idx)
    | _ ->
      let bi = idx / block_size in
      let i = idx mod block_size in
      let b = self#get_block bi in
      A.get b i

  method set idx x =
    if idx < 0 || idx > last_index then
      raise (Index_out_of_bounds idx)
    else
      let bi = idx / block_size in
      let i = idx mod block_size in
      let b = self#get_block bi in
      A.set b i x

  method add x =
    let idx = last_index + 1 in
    let i = last_local_index + 1 in
    if i >= block_size then begin
      let b = A.create kind layout block_size in
      A.set b 0 x;
      current_block <- b;
      last_local_index <- 0;
      Hashtbl.add block_tbl nblocks b;
      nblocks <- nblocks + 1
    end
    else begin
      A.set current_block i x;
      last_local_index <- i
    end;
    last_index <- idx

  method iter f =
    for bi = 0 to nblocks - 2 do
      let b = self#get_block bi in
      for i = 0 to (block_size - 1) do
        f (A.get b i)
      done
    done;
    let last_b = self#get_block (nblocks - 1) in
    let last_i = last_index mod block_size in
    for i = 0 to last_i do
      f (A.get last_b i)
    done

  method iteri (f : int -> int -> unit) =
    for bi = 0 to nblocks - 2 do
      let b = self#get_block bi in
      let a = bi * block_size in
      for i = 0 to (block_size - 1) do
        f (a + i) (A.get b i)
      done
    done;
    let last_bi = nblocks - 1 in
    let last_b = self#get_block last_bi in
    let last_i = last_index mod block_size in
    let a = last_bi * block_size in
    for i = 0 to last_i do
      f (a + i) (A.get last_b i)
    done

  method to_string =
    let buf = Buffer.create 0 in
    Buffer.add_string buf "[";
    self#iter
      (fun x ->
        Buffer.add_string buf (string_of_int x);
        Buffer.add_string buf ";"
      );
    Buffer.add_string buf "]";
    Buffer.contents buf

end (* Xarray.int_array_list *)
