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
(* common.ml *)

open Printf

exception Failure of string

exception Internal_error
let internal_error (fmt : ('a, out_channel, unit, 'b) format4) : 'a =
  kfprintf (fun ochan -> fprintf ochan "\n"; raise Internal_error) stderr fmt

exception Out_of_bounds
let out_of_bounds (fmt : ('a, out_channel, unit, 'b) format4) : 'a =
  kfprintf (fun ochan -> fprintf ochan "\n"; raise Out_of_bounds) stderr fmt



let maxn =
  List.fold_left
    (fun m x ->
      if x > m then
        x
      else
        m
    ) min_int

let minn =
  List.fold_left
    (fun m x ->
      if x < m then
        x
      else
        m
    ) max_int

let maxn_do l =
  let max, act =
  List.fold_left
    (fun ((m, _) as acc) ((x, _) as xf) ->
      if x > m then
        xf
      else
        acc
    ) (min_int, fun () -> ()) l
  in
  act();
  max

let minn_do l =
  let min, act =
  List.fold_left
    (fun ((m, _) as acc) ((x, _) as xf) ->
      if x < m then
        xf
      else
        acc
    ) (max_int, fun () -> ()) l
  in
  act();
  min

let maxn_do2 l =
  let x_max =
    List.fold_left
      (fun xm (x, _, _) ->
        if x > xm then
          x
        else
          xm
      ) min_int l
  in
  let maxes = List.filter (fun (x, _, _) -> x = x_max) l in
  let (*k_max*)_, act =
    List.fold_left
      (fun ((km, (*a*)_) as acc) ((*x*)_, k, f) ->
        if k > km then
          (k, f)
        else
          acc
      ) (min_int, fun () -> ()) maxes
  in
  act();
  x_max
