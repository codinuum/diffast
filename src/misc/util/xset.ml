(*
   Copyright 2012-2024 Codinuum Software Lab <https://codinuum.com>

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

type 'a t = ('a, bool) Hashtbl.t

let create n = (Hashtbl.create n : 'a t)

let clear (set : 'a t) = Hashtbl.clear set

let length (set : 'a t) = Hashtbl.length set
let size = length

let is_empty (set : 'a t) = (length set) = 0

let iter (f : 'a -> unit) (set : 'a t) =
  Hashtbl.iter (fun x _ -> f x) set

let add (set : 'a t) x = Hashtbl.replace set x true

let add_set (set : 'a t) (s : 'a t) = iter (add set) s

let remove (set : 'a t) x = Hashtbl.remove set x

let remove_set (set : 'a t) (s : 'a t) = iter (remove set) s

let mem (set : 'a t) x = Hashtbl.mem set x

let copy (set : 'a t) = (Hashtbl.copy set : 'a t)

let to_list (set : 'a t) = Hashtbl.fold (fun x _ l -> x::l) set []

let from_list l =
  let s = create (List.length l) in
  List.iter (fun x -> add s x) l;
  s

exception Found

let for_all (f : 'a -> bool) (s : 'a t) =
  try
    iter (fun x -> if not (f x) then raise Found) s;
    true
  with
    Found -> false

let exists (f : 'a -> bool) (s : 'a t) =
  try
    iter (fun x -> if f x then raise Found) s;
    false
  with
    Found -> true

let subset_eq (s0 : 'a t) (s1 : 'a t) = for_all (mem s1) s0

let equals (s0 : 'a t) (s1 : 'a t) =
  (subset_eq s0 s1) && (subset_eq s1 s0)

let map f (s : 'a t) =
  let s' = create (length s) in
  iter
    (fun x ->
      add s' (f x)
    ) s;
  s'

let filter f (s : 'a t) =
  let s' = create 0 in
  iter
    (fun x ->
      if f x then
        add s' x
    ) s;
  s'

let filter_map f (s : 'a t) =
  let s' = create 0 in
  iter
    (fun x ->
      match f x with
      | Some y -> add s' y
      | None -> ()
    ) s;
  s'

let filter_inplace f (s : 'a t) =
  let to_be_removed = ref [] in
  iter
    (fun x ->
      if f x then
        ()
      else
        to_be_removed := x :: !to_be_removed
    ) s;
  List.iter (remove s) !to_be_removed
