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
(* layeredloc.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist


class loc_stack = object
  val stack = (Stack.create() : Astloc.t Stack.t)

  method push loc =
    Stack.push loc stack

  method pop =
    ignore (Stack.pop stack)

  method get_layers =
    let lr = ref [] in
    Stack.iter (fun loc -> lr := (ref loc)::!lr) stack;
    List.rev !lr

  method get_level =
    Stack.length stack

  method to_string =
    let buf = Buffer.create 0 in
    Stack.iter
      (fun l ->
        Buffer.add_string buf (Printf.sprintf "[%s]" (Astloc.to_string ~short:true l))
      ) stack;
    Buffer.contents buf


  method init =
    Stack.clear stack
end

let sep = Fname.loc_sep
let sep_pat = Fname.loc_sep_pat

let encode_layers layers =
  Xlist.to_string (fun lr -> Astloc.to_rep !lr) sep layers

let decode_layers str =
  if str = "" then
    []
  else begin
    (*[%debug_log "decoding \"%s\"" str];*)
    List.map (fun s -> ref (Astloc.from_rep s)) (Str.split sep_pat str)
  end


class c ?(layers=[]) loc = object (self)
  val mutable locs = ((ref loc)::layers : Astloc.t ref list)

  method size = List.length locs

  method get_level = self#size - 1

  method get_layers n = (* last n locs *)
    let ls = ref locs in
    for _ = 1 to self#size - n do
      match !ls with
      | _::t -> ls := t
      | _ -> failwith "Layeredloc.c#get_layers"
    done;
    !ls

  method get_loc =
    match locs with
    | lr::_ -> Astloc.get_stripped !lr
    | _ -> assert false

  method get_loc_of_level lv =
    try
      !(List.nth locs (self#get_level - lv))
    with
      _ -> failwith "Layeredloc.c#get_loc"

  method get_orig_loc =
    Astloc.get_stripped (self#get_loc_of_level self#get_level)

  method collapse_backward =
    match locs with
    | lr::_ -> lr := Astloc.collapse_backward !lr
    | _ -> failwith "Layeredloc.c#collapse_backward"

  method to_loc ?(cache=None) () =
    match locs with
    | [] -> assert false
    | [loc] -> !loc
    | loc :: rest -> begin
        if Astloc.is_extended !loc then
          !loc
        else
          Astloc.get_extended ?cache !loc (encode_layers rest)
    end

  method to_string ?(short=true) () =
    let buf = Buffer.create 0 in
    List.iter
      (fun lr ->
        Buffer.add_string buf (Printf.sprintf "[%s]" (Astloc.to_string ~short !lr))
      ) locs;
    Buffer.contents buf

end (* class Layeredloc.c *)

let dummy = new c Astloc.dummy

let layers_eq ls0 ls1 =
  try
    List.for_all2 (fun lr0 lr1 -> !lr0 = !lr1) ls0 ls1
  with
    _ -> false

let get_common_layers (lloc0 : c) (lloc1 : c) =
    let lv = min lloc0#get_level lloc1#get_level in
    let ls0 = List.rev (lloc0#get_layers lv) in
    let ls1 = List.rev (lloc1#get_layers lv) in
    let rec doit common = function
      | x0::xs0, x1::xs1 ->
          if !x0 = !x1 then
            doit (x0::common) (xs0, xs1)
          else
            common
      | _ -> common
    in
    doit [] (ls0, ls1)

let get_common_level lloc0 lloc1 =
  List.length (get_common_layers lloc0 lloc1)

[%%capture_path
let merge (lloc0 : c) (lloc1 : c) =
  [%debug_log "%s and %s" (lloc0#to_string()) (lloc1#to_string())];
  if lloc0 == dummy then
    lloc1
  else if lloc1 == dummy then
    lloc0
  else
    let common = get_common_layers lloc0 lloc1 in
    let lv = List.length common in
    [%debug_log "lv=%d common=%s" lv
      (Xlist.to_string (fun x -> Astloc.to_string ~show_ext:true !x) "; " common)];
    let loc0 = lloc0#get_loc_of_level lv in
    let loc1 = lloc1#get_loc_of_level lv in
    [%debug_log "loc0=%s (lv=%d)" (Astloc.to_string ~show_ext:true loc0) lv];
    [%debug_log "loc1=%s (lv=%d)" (Astloc.to_string ~show_ext:true loc1) lv];
    new c ~layers:common (Astloc.merge loc0 loc1)
]

let dump_llocs llocs =
  if (List.length llocs) > 0 then begin
    let sorted =
      List.fast_sort
        (fun lloc0 lloc1 ->
          let lv = get_common_level lloc0 lloc1 in
          let loc0 = lloc0#get_loc_of_level lv in
          let loc1 = lloc1#get_loc_of_level lv in
          Stdlib.compare loc0.Astloc.start_offset loc1.Astloc.end_offset
        ) llocs
    in
    List.iter
      (fun lloc ->
        Printf.printf "%s\n" (lloc#to_string ?short:(Some true) ())
      ) sorted
  end

let lines_of_llocs llocs =
  List.fold_left
    (fun n lloc ->
      let loc = lloc#get_loc in
      n + loc.Astloc.end_line - loc.Astloc.start_line + 1
    ) 0 llocs

[%%capture_path
let of_loc loc =
  [%debug_log "loc=[%s]" (Astloc.to_string ~short:true ~show_ext:true loc)];
  let fn = loc.Astloc.filename in
  if Fname.is_extended fn then begin
    let ext = Fname.get_extension fn in
    [%debug_log "ext found: %s" (Fname.escape ext)];
    let layers = decode_layers ext in
    new c ~layers loc
  end
  else begin
    new c loc
  end
]

let of_lexpos pos = of_loc (Astloc.of_lexpos pos)
