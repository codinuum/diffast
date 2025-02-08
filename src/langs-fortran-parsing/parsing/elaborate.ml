(*
   Copyright 2013-2018 RIKEN
   Copyright 2018-2025 Chiba Institude of Technology

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

[%%prepare_logger]

module Layeredloc = Langs_common.Layeredloc

open Common

module L = Label

exception Not_changed


[%%capture_path
class node_map = object (* pp-section -> directive list *)
  val tbl = Hashtbl.create 0

  method add (x : Ast.node) (d : Ast.node) =
    [%debug_log "%s -> %s" x#to_string d#to_string];
    (*Printf.printf "%s -> %s\n%!" x#to_string d#to_string;*)
    try
      let l = Hashtbl.find tbl x in
      Hashtbl.replace tbl x (d::l)
    with
      Not_found ->
        Hashtbl.add tbl x [d]

  method find x =
    Hashtbl.find tbl x

end
]

let copy_stack stack =
  let l = ref [] in
  Stack.iter
    (fun (nd, cstr, memr, endchk) ->
      l := (nd, cstr, ref !memr, endchk)::!l
    ) stack;
  let copy = Stack.create() in
  List.iter (fun x -> Stack.push x copy) !l;
  copy

[%%capture_path
class c = object (self)
  val dangling_node_map = new node_map

  method get_endchk_and_construct_from_pp_branch nd =
    if L.is_pp_branch nd#label && (List.length nd#children) > 0 then begin
      [%debug_log "%s" (L.to_string nd#label)];
      let ll =
        List.map
          (fun n ->
            try
              let ds = dangling_node_map#find n in
              let l = ref [] in
              List.iter
                (fun d ->
                  [%debug_log "d=%s" d#to_string];
                  try
                    l := (L.get_endchk_and_construct d#label) :: !l
                  with
                    Not_found -> ()
                ) ds;
              !l
            with
              Not_found -> []
          ) nd#children
      in
      let selected = ref (List.hd ll) in
      let max = ref (List.length !selected) in
      List.iter
        (fun l ->
          [%debug_log "l=%s" (Xlist.to_string (fun (_, x) -> L.to_string x) "; " l)];
          let len = List.length l in
          if len > !max then begin
            max := len;
            selected := l
          end
        ) ll;
      if !max = 0 then
        raise Not_found;

      selected := List.rev !selected;
      [%debug_log "selected=%s" (Xlist.to_string (fun (_, x) -> L.to_string x) "; " !selected)];
      !selected
    end
    else
      raise Not_found

  method do_endchk _stack nd next_lab_opt =
    let lab = nd#label in
    let is_pp_branch = L.is_pp_branch lab in
    let is_pp_section = L.is_pp_section lab in

    if (is_pp_branch || is_pp_section) && (List.length nd#children) > 0 then begin

      let min = ref (Stack.length _stack) in
      let selected = ref _stack in
      let selected_id = ref 0 in
      let end_found = ref false in

      let sections =
        if is_pp_branch then
          nd#children
        else
          [nd]
      in

      List.iteri
        (fun sect_id sect ->
          [%debug_log "* SECTION%d" sect_id];
          let stack = copy_stack _stack in
          let (bn, cstr, memr, endchk) = Stack.top stack in
          let _ = bn in
          memr := nd :: !memr;
          let ns = sect#children in
          let getl i =
            try
              Some ((List.nth ns i)#label)
            with _ -> None
          in
          List.iteri
            (fun i n ->
              [%debug_log "  [%d] %s" i n#to_string];
              if i = 0 && L.is_pp_directive_branch n#label then
                () (* skip *)
              else if endchk n#label (getl (i+1)) then begin
                [%debug_log "end found: %s (%s)" (L.to_string n#label) (L.to_string bn#label)];
                end_found := true;
                let _ = Stack.pop stack in
                let children = List.rev !memr in
                let lloc = Layeredloc.merge cstr#lloc nd#lloc in
                cstr#set_children children;
                cstr#set_lloc lloc;
                let (_, _, memr', _) = Stack.top stack in
                memr' := cstr :: !memr'
              end
            ) ns;

          let len = Stack.length stack in
          if len < !min then begin
            selected_id := sect_id;
            min := len;
            selected := stack
          end

        ) sections;

      if !end_found then begin
        [%debug_log "selected: SECTION%d" !selected_id];
      end
      else begin
        let (_, _, memr, _) = Stack.top _stack in
        memr := nd :: !memr
      end;

      !selected

    end
    else begin
      let stack = _stack in

      let rec doit ini cond =
        let (bn, cstr, memr, endchk) = Stack.top stack in
        if ini then
          memr := nd :: !memr;
        if cond && (endchk (if ini then lab else cstr#label) next_lab_opt) then begin
          [%debug_log "end found: %s (%s)" (L.to_string lab) (L.to_string bn#label)];
          let _ = Stack.pop stack in
          let children = List.rev !memr in
          let lloc = Layeredloc.merge cstr#lloc nd#lloc in
          cstr#set_children children;
          cstr#set_lloc lloc;
          let (bn', _, memr', _) = Stack.top stack in
          memr' := cstr :: !memr';
          let b = (L.anonymize bn#label) <> (L.anonymize bn'#label) in
          [%debug_log "b=%B" b];
          doit false b
        end
      in
      doit true true;
      stack
    end

  method has_endchk verbose nd =
    if verbose then
      [%debug_log "%s" nd#to_string];
    if L.has_endchk nd#label then
      true
    else
      try
        let _ = self#get_endchk_and_construct_from_pp_branch nd in
        true
      with
        Not_found -> false

  method elaborate_node_list parent (nodes : Ast.node list) =
    let stackr = ref (Stack.create()) in
    let pushed_flag = ref false in
    Stack.push (Ast.empty_node, Ast.empty_node, ref [], (fun _ _ -> false)) !stackr;

    let nodea = Array.of_list nodes in

    let get_lab i =
      try
        Some (nodea.(i)#label)
      with _ -> None
    in

    Array.iteri
      (fun idx nd ->
        [%debug_log "[%d] %s" idx nd#to_string];
        try
          begin
            try
              let (endchk, cstr) = L.get_endchk_and_construct nd#label in
              let cstr = new Ast.node ~lloc:nd#lloc cstr in
              Stack.push (nd, cstr, ref [nd], endchk) !stackr;
              pushed_flag := true
            with
              Not_found ->
                List.iter
                  (fun (endchk, cstr) ->
                    let cstr = new Ast.node ~lloc:nd#lloc cstr in
                    Stack.push (nd, cstr, ref [nd], endchk) !stackr;
                    pushed_flag := true
                  ) (self#get_endchk_and_construct_from_pp_branch nd)
          end
        with
          Not_found -> begin
            try
              stackr := self#do_endchk !stackr nd (get_lab (idx+1))
            with
            | L.Not_a_construct_head l ->
                parse_warning_loc nd#loc "not a construct head: %s" (L.to_string l)

            | exn ->
                [%warn_log "%s" (Printexc.to_string exn)];
                raise exn
          end
      ) nodea;

    if !pushed_flag then begin
      let (orig, _, memr, _) = Stack.pop !stackr in
      if Stack.is_empty !stackr then
        List.rev !memr
      else begin
        [%debug_log "dangling node: %s" (L.to_string orig#label)];
        if L.is_pp_section parent#label then begin
          dangling_node_map#add parent orig;
          let all = ref !memr in
          Stack.iter
            (fun (o, _, mr, _) ->
              all := !all @ !mr;
              if o != Ast.empty_node then begin
                [%debug_log "dangling node: %s" (L.to_string o#label)];
                dangling_node_map#add parent o
              end
            ) !stackr;
          List.rev !all
        end
        else begin
          parse_warning_loc orig#loc "dangling directive: %s" (L.to_string orig#label);
          let all = ref !memr in
          Stack.iter (fun (_, _, mr, _) -> all := !all @ !mr) !stackr;
          List.rev !all
        end
      end

    end
    else
      raise Not_changed
  (*method elaborate_node_list*)

  method private elaborate_omps_followed_by_cond nodes =
    let prefix, last = Xlist.partition_at_last nodes in
    last#add_children_l prefix;
    last#set_lloc (Layeredloc.merge (List.hd prefix)#lloc last#lloc);
    last

  method elaborate_ast (ast : Ast.c) =
    ast#visit_post
      (fun nd ->
        try
          let c = nd#children in
          let len = List.length c in

          let flag =
            match nd#label with
            | L.DoBlock -> true
            | _ -> false
          in
          if flag then
            [%debug_log "%s (%d)" nd#to_string len];

          if len > 1 then begin
            let has_endchk = ref false in
            let omps_followed_by_cond = ref true in
            let len0 = len - 1 in

            List.iteri
              (fun i n ->
                let lab = n#label in

                if flag then
                  [%debug_log "  %s" n#to_string];

                if self#has_endchk flag n then
                  has_endchk := true;

                if !omps_followed_by_cond then
                  if i = len0 then begin
                    if not (L.is_pp_section_omp lab) then
                      omps_followed_by_cond := false
                  end
                  else begin
                    if not (L.is_omp_directive lab) then
                      omps_followed_by_cond := false
                  end
              ) c;

            if flag then
              [%debug_log "has_endchk=%B" !has_endchk];

            if !has_endchk then begin
              [%debug_log "%s (%d)" nd#to_string len];
              let c' =
                if !omps_followed_by_cond then begin
                  [%debug_log "found: OMPs followed by OMP conditional"];
                  let n = self#elaborate_omps_followed_by_cond c in
                  n#set_children (self#elaborate_node_list n n#children);
                  [n]
                end
                else
                  self#elaborate_node_list nd c
              in
              nd#set_children c'
            end

          end
        with
        | Not_changed
        | L.Not_a_construct_head _ -> ()
      )

end (* of class Elaborate.c *)
]
