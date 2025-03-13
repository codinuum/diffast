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
(* weight *)

module type T = sig
  type t
  val zero : t
  val plus : t -> t -> t
  val le : t -> t -> bool
  val eq : t -> t -> bool
  val lt : t -> t -> bool
  val max : t
  val min : t
  val to_string : t -> string
end

module Int = struct
  type t = int
  let zero = 0
  let plus x y = x + y
  let le x y = x <= y
  let eq x y = x = y
  let lt x y = x < y
  let max = max_int
  let min = min_int
  let to_string x = string_of_int x
end

module Float = struct
  type t = float
  let zero = 0.0
  let plus x y = x +. y
  let le x y = x <= y
  let eq x y = x = y
  let lt x y = x < y
  let max = max_float
  let min = min_float
  let to_string x = string_of_float x
end

module FloatIntInt = struct
  type t = float * int * int
  let zero = (0.0, 0, 0)
  let plus (f1, i1, j1) (f2, i2, j2) = (f1 +. f2, i1 + i2, j1 + j2)
  let le (f1, i1, j1) (f2, i2, j2) =
    f1 < f2 || (f1 = f2 && (i1 < i2 || (i1 = i2 && j1 <= j2)))
  let eq x y = le x y && le y x
  let lt x y = le x y && not (eq x y)
  let max = (max_float, max_int, max_int)
  let min = (min_float, min_int, min_int)
  let to_string (f, i, j) = Printf.sprintf "(%f,%d,%d)" f i j
end

module FloatInt = struct
  type t = float * int
  let zero = (0.0, 0)
  let plus (f1, i1) (f2, i2) = (f1 +. f2, i1 + i2)
  let le (f1, i1) (f2, i2) = f1 < f2 || (f1 = f2 && i1 <= i2)
  let eq x y = le x y && le y x
  let lt x y = le x y && not (eq x y)
  let max = (max_float, max_int)
  let min = (min_float, min_int)
  let to_string (f, i) = Printf.sprintf "(%f,%d)" f i
end

module FloatFloat = struct
  type t = float * float
  let zero = (0.0, 0.0)
  let plus (f1, g1) (f2, g2) = (f1 +. f2, g1 +. g2)
  let le (f1, g1) (f2, g2) = f1 < f2 || (f1 = f2 && g1 <= g2)
  let eq x y = le x y && le y x
  let lt x y = le x y && not (eq x y)
  let max = (max_float, max_float)
  let min = (min_float, min_float)
  let to_string (f, g) = Printf.sprintf "(%f,%f)" f g
end

module IntInt = struct
  type t = int * int
  let zero = (0, 0)
  let plus (i1, j1) (i2, j2) = (i1 + i2, j1 + j2)
  let le (i1, j1) (i2, j2) = i1 < i2 || (i1 = i2 && j1 <= j2)
  let eq x y = le x y && le y x
  let lt x y = le x y && not (eq x y)
  let max = (max_int, max_int)
  let min = (min_int, min_int)
  let to_string (i, j) = Printf.sprintf "(%d,%d)" i j
end

module IntIntInt = struct
  type t = int * int * int
  let zero = (0, 0, 0)
  let plus (i1, j1, k1) (i2, j2, k2) = (i1 + i2, j1 + j2, k1 + k2)
  let le (i1, j1, k1) (i2, j2, k2) =
    i1 < i2 ||
    (i1 = i2 && j1 <= j2) ||
    (i1 = i2 && j1 = j2 && k1 <= k2)
  let eq x y = le x y && le y x
  let lt x y = le x y && not (eq x y)
  let max = (max_int, max_int, max_int)
  let min = (min_int, min_int, min_int)
  let to_string (i, j, k) = Printf.sprintf "(%d,%d,%d)" i j k
end

module IntFloat = struct
  type t = int * float
  let zero = (0, 0.0)
  let plus (i1, f1) (i2, f2) = (i1 + i2, f1 +. f2)
  let le (i1, f1) (i2, f2) = i1 < i2 || (i1 = i2 && f1 <= f2)
  let eq x y = le x y && le y x
  let lt x y = le x y && not (eq x y)
  let max = (max_int, max_float)
  let min = (min_int, min_float)
  let to_string (i, f) = Printf.sprintf "(%d,%f)" i f
end
