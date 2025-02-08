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
(* xlist.ml *)

let to_string to_str sep l =
  String.concat sep (List.map to_str l)

let _uniq eq lst =
  List.rev
    (List.fold_left
       (fun l x ->
         match l with
         | [] -> [x]
         | y :: _ ->
             if eq x y then
               l
             else
               x :: l
       ) [] lst)

let uniq lst = _uniq (=) lst

let uniqq lst = _uniq (==) lst

let _union mem l1 l2 =
  List.rev
    (List.fold_left
       (fun l x ->
         if mem x l then
           l
         else
           x :: l
       ) (List.rev l1) l2)

let union l1 l2 = _union List.mem l1 l2

let unionq l1 l2 = _union List.memq l1 l2

let _intersection mem l1 l2 =
  List.rev
    (List.fold_left
       (fun l x ->
         if mem x l1 then
           x :: l
         else l
       ) [] l2)

let intersection l1 l2 = _intersection List.mem l1 l2

let intersectionq l1 l2 = _intersection List.memq l1 l2


let overlap l1 l2 = (intersection l1 l2) <> []

let overlapq l1 l2 = (intersectionq l1 l2) <> []

let subtract l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

let subtractq l1 l2 = List.filter (fun x -> not (List.memq x l2)) l1

let split3 (l : ('a * 'b * 'c) list) =
  let al, bl, cl =
    List.fold_left
      (fun (al, bl, cl) (a, b, c) -> a::al, b::bl, c::cl)
      ([], [], []) l
  in
  List.rev al, List.rev bl, List.rev cl

let max l =
  match l with
  | [] -> invalid_arg "Xlist.max"
  | a::_ -> List.fold_left (fun m x -> if x > m then x else m) a l

let min l =
  match l with
  | [] -> invalid_arg "Xlist.min"
  | a::_ -> List.fold_left (fun m x -> if x < m then x else m) a l

let first = function
  | [] -> failwith "Xlist.first"
  | h::_ -> h

let rec last = function
  | [] -> failwith "Xlist.last"
  | [x] -> x
  | _::t -> last t

let firstn n l =
  let len = List.length l in
  if n < 1 || n > len then
    failwith "Xlist.firstn"
  else
    let cur = ref l in
    let l' = ref [] in
    for _ = 1 to n do
      match !cur with
      | h::t ->
          l' := h :: !l';
          cur := t
      | [] -> assert false
    done;
    List.rev !l'

let lastn n l =
  let len = List.length l in
  if n < 1 || n > len then
    failwith "Xlist.lastn"
  else
    let l' = ref l in
    for _ = 1 to len - n do
      l' := List.tl !l'
    done;
    !l'

let rec balance = function
  | [], _ -> [], []
  | _, [] -> [], []
  | h1::t1, h2::t2 ->
      let l1, l2 = balance (t1, t2) in
      h1::l1, h2::l2

let range n =
  let l = ref [] in
  for i = n - 1 downto 0 do
    l := i::!l
  done;
  !l

let filter_map (f : 'a -> 'b option) (lst : 'a list) =
  let rvd =
    List.fold_left
      (fun l x ->
        match f x with
        | Some y -> y :: l
        | None -> l
      ) [] lst
  in
  List.rev rvd

let rec partition_at_last = function
  | [] -> failwith "Xlist.partition_at_last"
  | [x] -> [], x
  | h::t -> let t', last = partition_at_last t in h::(t'), last
