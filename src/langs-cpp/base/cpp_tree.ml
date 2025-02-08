(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>
   Copyright 2020-2025 Chiba Institute of Technology

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

(*
 * AST for C/C++
 *
 * cpp/tree.ml
 *
 *)

[%%prepare_logger]

module Xhash = Diffast_misc.Xhash
module Xfile = Diffast_misc.Xfile
module Binding = Diffast_misc.Binding
module Loc = Diffast_misc.Loc
module Sourcecode = Diffast_core.Sourcecode
module Fact_base = Diffast_core.Fact_base
module Entity = Diffast_core.Entity
module Triple = Diffast_core.Triple
module Fname = Langs_common.Fname
module Astloc = Langs_common.Astloc
module Pinfo = Cpp_parsing.Pinfo
module Ast = Cpp_parsing.Ast

module L = Cpp_label
module B = Binding
module I = Pinfo
module FB  = Fact_base.F (L)
module UID = Diffast_misc.UID

let sprintf = Printf.sprintf

let conv_loc = L.conv_loc

let set_loc nd loc = nd#data#set_loc (conv_loc loc)

module Tree = Sourcecode.Tree (L)
open Tree

class c options root is_whole = object
  inherit Tree.c options root is_whole

  method! private create root is_whole = new c options root is_whole

  method! unparse_subtree_ch ?(no_boxing=false) ?(no_header=false) ?(fail_on_error=true) =
    make_unparser (Cpp_unparsing.unparse ~no_boxing ~no_header ~fail_on_error)

end

let of_xnode options =
  Tree.of_xnode ~tree_creator:(fun options nd -> new c options nd true) options



let make_include_node options ast_nd =
  let f = Fname.strip (ast_nd#lloc#get_loc_of_level 1).Astloc.filename in
  let nd = mkleaf options (L.PpInclude f) in
  set_loc nd (ast_nd#lloc#get_loc_of_level 0);
  nd

let getlab = FB.getlab

let apply_child is_xxx f children =
  Array.iter
    (fun nd ->
      let lab = getlab nd in
      if is_xxx lab then
        f nd
    ) children

let get_nth_children = Sourcecode._get_logical_nth_child


[%%capture_path
let set_control_flow label_tbl body =

  let find_target = Hashtbl.find label_tbl in
  let find_break_target = function
    | (_, x) :: _ -> x
    | [] -> raise Not_found
  in
  let rec find_continue_target = function
    | (Some x, _) :: _ -> x
    | (None, _) :: rest -> find_continue_target rest
    | [] -> raise Not_found
  in
  let rec set_succ loop_env nexts nd =
    let ndlab = getlab nd in
    let add_succ1 s =
      [%debug_log "%s[%s] -> %s[%s]"
        (L.to_string ndlab) (Loc.to_string nd#data#src_loc)
        (L.to_string (getlab s)) (Loc.to_string s#data#src_loc)];
      (*Printf.printf "! %s[%s] -> %s[%s]\n%!"
        (L.to_string ndlab) (Loc.to_string nd#data#src_loc)
        (L.to_string (getlab s)) (Loc.to_string s#data#src_loc);*)
      nd#data#add_successor s
    in
    let add_succ = List.iter add_succ1 in

    let children = nd#children in
    let nchildren = nd#nchildren in

    let handle_block children nchildren =
      [%debug_log "nchidlen=%d" nchildren];
      if nchildren = 0 then
        add_succ nexts
      else if nchildren > 0 then begin
        add_succ1 children.(0);
        let lasti = nchildren - 1 in
        for i = 0 to lasti - 1 do
          [%debug_log "i=%d" i];
          set_succ loop_env [children.(i+1)] children.(i)
        done;
        set_succ loop_env nexts children.(lasti)
      end
    in (* set_succ *)
    match ndlab with
    | L.IfStatement -> begin
        let c1 = (get_nth_children nd 3).(0) in
        add_succ1 c1;
        set_succ loop_env nexts c1;
        try
          let c2 = (get_nth_children nd 4).(0) in
          add_succ1 c2;
          set_succ loop_env nexts c2
        with
        | _ -> add_succ nexts
    end
    | L.SwitchStatement -> begin
        let c2 = (get_nth_children nd 2).(0) in
        add_succ1 c2;
        set_succ ((None, nexts)::loop_env) nexts c2
    end
    | L.ForStatement -> begin
        let c3 = (get_nth_children nd 3).(0) in
        add_succ1 c3;
        set_succ ((Some c3, c3::nexts)::loop_env) nexts c3
    end
    | L.WhileStatement -> begin
        let c1 = children.(1) in
        add_succ1 c1;
        set_succ ((Some c1, c1::nexts)::loop_env) nexts c1
    end
    | L.DoStatement -> begin
        let c0 = children.(0) in
        add_succ1 c0;
        set_succ ((Some c0, c0::nexts)::loop_env) nexts c0
    end
    | L.BreakStatement -> begin
        try
          let ns = find_break_target loop_env in
          add_succ ns
        with
          _ -> ()
    end
    | L.ContinueStatement -> begin
        try
          let n = find_continue_target loop_env in
          add_succ1 n
        with
          _ -> ()
    end
    | L.GotoStatement i -> begin
        try
          let n = find_target i in
          add_succ1 n
        with
          _ -> ()
    end
    | L.LabeledStatement -> begin
        let c0 = (get_nth_children nd 1).(0) in
        add_succ1 c0;
        set_succ loop_env nexts c0
    end
    | L.TryBlock -> begin
        let c0 = children.(0) in
        add_succ1 c0;
        set_succ loop_env nexts c0
    end
    | L.PpIfSectionTryBlock -> begin
        let c1 = children.(1) in
        add_succ1 c1;
        set_succ loop_env nexts c1
    end
    | L.CompoundStatement -> handle_block children nchildren
    | L.Handler -> begin
        let c1 = children.(1) in
        handle_block c1#children c1#nchildren
    end

    | _ when L.is_stmt ndlab -> add_succ nexts

    | _ -> ()
  in (* set_succ *)
  let children = body#children in
  let nchildren = body#nchildren in
  [%debug_log "* %s[%s]: nchildren=%d"
    (L.to_string (getlab body)) (Loc.to_string body#data#src_loc) nchildren];
  for i = 0 to nchildren - 2 do
    set_succ [] [children.(i+1)] children.(i)
  done;
  if nchildren > 0 then
    set_succ [] [] children.(nchildren - 1)
]

[%%capture_path
class visitor conv_uid tree = object
  inherit Sourcecode.visitor tree
  method! scanner_body_after_subscan nd =
    begin
      match nd#data#binding with
      | B.Use(bid, uid_loc_opt) -> begin
          [%debug_log "bid=%a" B.ID.ps bid];
          match uid_loc_opt with
          | None -> ()
          | Some (uid, loc) ->
              let binding_ = B.Use(bid, Some (conv_uid uid, loc)) in
              nd#data#set_binding binding_
      end
      | _ -> ()
    end
end
]

[%%capture_path
let of_ast options ast =
(*
  let mktid nd =
    Lang.mktid
      (if options#incomplete_info_flag then
        ""
      else
        Xhash.to_hex (new c options nd false)#digest)
      (if options#incomplete_info_flag then
        ""
      else
        nd#data#anonymized_label)
  in
*)
  let uid_tbl = Hashtbl.create 0 in
  let reg_node ast_nd nd =
    let uid = UID.of_int (Oo.id ast_nd) in
    (*if B.is_def ast_nd#binding then*)
      Hashtbl.add uid_tbl uid nd#uid
  in
  let conv_uid u =
    try
      let u' = Hashtbl.find uid_tbl u in
      [%debug_log "%a -> %a" UID.ps u UID.ps u'];
      u'
    with Not_found -> assert false
  in

  let utbl = Hashtbl.create 0 in

  let proj_root = try options#fact_proj_roots.(0) with _ -> "" in
  let version = try options#fact_versions.(0) with _ -> Entity.unknown_version in

  let rec conv ?(orig_loc_flag=false) ?(label=None) ?(label_tbl_opt=None) ast_nd =
    [%debug_log "orig_loc_flag=%B, ast_nd=%s" orig_loc_flag ast_nd#to_string];

    let lab =
      match label with
      | Some lab' -> lab'
      | None -> ast_nd#label
    in

    let reg_label =
      match label_tbl_opt with
      | Some tbl -> fun lab nd -> Hashtbl.add tbl lab nd
      | None -> fun _ _ -> ()
    in

    let is_incl nd =
      ast_nd#lloc#get_level = 0 && nd#lloc#get_level > 0
    in

    let proc_included_node nd =
      [%debug_log "nd=%s" nd#to_string];
      let fn = nd#data#src_loc.Loc.filename in
      [%debug_log "fn=%s" fn];
      try
        let fn_, path =
          if Filename.is_relative fn then
            (Filename.concat proj_root fn), fn
          else
            fn, (Xfile.relpath proj_root fn)
        in
        let digest = Xhash.digest_of_file options#fact_algo fn_ in
        let fid_str =
          Triple._encode_fid options ~digest ~path proj_root version
        in
        if nd#data#source_fid = "" then begin
          nd#data#set_source_fid fid_str
        end
      with
        _ ->
          [%warn_log "failed to compute digest of %s" nd#to_string];
    in

    (*let rec conv_children ?(label_tbl_opt=None) = function
      | nd1::(nd2::rest as l) -> begin
          match nd1#label, nd2#label with
          | _ -> begin
              if is_incl nd1 then begin
                [%debug_log "nd1=%s" nd1#to_string];
                match nd1#label with
                | _ -> (make_include_node options nd1) :: (conv_children ~label_tbl_opt l)
              end
              else begin
                [%debug_log "nd1=%s" nd1#to_string];
                match conv ~orig_loc_flag ~label_tbl_opt nd1 with
                | Some x -> x :: (conv_children ~label_tbl_opt l)
                | None -> conv_children ~label_tbl_opt l
              end
          end
      end
      | [nd] -> begin
          if is_incl nd then begin
            [%debug_log "nd=%s" nd#to_string];
            match nd#label with
            | _ -> [make_include_node options nd]
          end
          else begin
            [%debug_log "nd=%s" nd#to_string];
            Xoption.to_list (conv ~orig_loc_flag ~label_tbl_opt nd)
          end
      end
      | [] -> []
    in*)
    let conv_children ?(label_tbl_opt=None) l = (* to handle huge list *)
      List.filter_map
        (fun nd ->
          if is_incl nd then begin
            [%debug_log "nd=%s" nd#to_string];
            Some (make_include_node options nd)
          end
          else begin
            [%debug_log "nd=%s" nd#to_string];
            conv ~orig_loc_flag ~label_tbl_opt nd
          end
        ) l
    in

    let label_tbl_opt =
      match lab with
      | L.FunctionBody _ | L.FunctionTryBlock _ -> Some (Hashtbl.create 0)
      | _ -> None
    in
    let children = conv_children ~label_tbl_opt ast_nd#children in

    if ast_nd#lloc#get_level > 0 && children = [] && not orig_loc_flag then
      None
    else begin
      [%debug_log "ast_nd=%s" ast_nd#to_string];

      let info = ast_nd#info in
      let binding = ast_nd#binding in
      let binding =
        match binding with
        | B.NoBinding -> begin
            try
              match (I.get_spec info)#bid_opt with
              | Some b -> B.make_unknown_def b true
              | _ -> binding
            with
              _ -> binding
        end
        | _ -> binding
      in

      let annot =
        let specs = ref [] in
        begin
          try
            let spec = I.get_spec info in
            if not spec#is_local then begin
              let n = spec#get_qualified_name() in
              specs := (L.Annotation.mkprovide [n]) :: !specs
            end;
            specs := (L.Annotation.mktype (Ast.encode_type_(spec#get_type()))) :: !specs
          with
            Not_found -> ()
        end;
        begin
          try
            let n = I.get_external info in
            specs := (L.Annotation.mkrequire [n]) :: !specs
          with
            Not_found -> ()
        end;
        let a = L.Annotation.from_specs !specs in
        [%debug_log "%s" (L.Annotation.to_string a)];
        a
      in

      let ordinal_tbl_opt =
        match ast_nd#pvec with
        | [] -> None
        | l -> Some (new ordinal_tbl l)
      in
      let nd = mknode options ~annot ~ordinal_tbl_opt lab children in
      reg_node ast_nd nd;

      let handle_binding binding =
        match binding with
        | B.NoBinding -> ()
        | B.Def(bid, use, _) -> begin
            [%debug_log "bid=%a" B.ID.ps bid];
            let b =
              match !use with
              | B.Unknown -> begin
                  try
                    B.make_used_def bid (Hashtbl.find utbl bid) true
                  with
                    Not_found -> binding
              end
              | B.Used _ -> binding
            in
            nd#data#set_binding b
        end
        | B.Use(bid, _) -> begin
            [%debug_log "bid=%a" B.ID.ps bid];
            nd#data#set_binding binding;
            try
              let c = Hashtbl.find utbl bid in
              Hashtbl.replace utbl bid (c+1)
            with
              Not_found ->
                Hashtbl.add utbl bid 1
        end
      in
      if options#use_binding_info_flag then
        handle_binding binding;

      let loc =
        if orig_loc_flag then
          ast_nd#orig_loc
        else
          ast_nd#loc
      in

      let nd =
        if
          lab == L.BracedInitList &&
          List.for_all (fun n -> L.is_literal (getlab n)) children &&
          options#ignore_huge_arrays_flag
        then begin
          let sz = List.length children in
          if sz >= options#huge_array_threshold then begin
            [%warn_log "huge array found at %s (size=%d)" (Astloc.to_string loc) sz];
            let u =
              String.concat ","
                (List.rev (List.rev_map (fun n -> L.to_simple_string (getlab n)) children))
            in
            mknode options ~annot (L.HugeArray(sz, u)) []
          end
          else
            nd
        end
        else
          nd
      in

      set_loc nd loc;
      nd#data#set_prefix ast_nd#get_prefix;
      nd#data#set_suffix ast_nd#get_suffix;

      if orig_loc_flag then
        proc_included_node nd;

      begin
        match lab with
        | L.LabeledStatement -> begin
            Array.iter
              (fun lnd ->
                match getlab lnd with
                | L.Label i -> reg_label i nd
                | _ -> ()
              ) (get_nth_children nd 0)
        end
        | _ -> ()
      end;

      begin
        match lab with
        | L.FunctionBody _ | L.FunctionTryBlock _ -> begin
            try
              let c1 = (get_nth_children nd 1).(0) in
              let label_tbl =
                match label_tbl_opt with
                | Some tbl -> tbl
                | _ -> assert false
              in
              set_control_flow label_tbl c1
            with
              Invalid_argument _ -> ()
        end
        | _ -> ()
      end;

      Some nd

    end
  in (* let rec conv *)

  let root_node =
    let rt = ast#root in
    match conv rt with
    | Some rn -> rn
    | None -> begin
        try
          make_include_node options rt
        with
          Failure _ -> assert false
    end
  in
  let tree = new c options root_node true in
  if options#use_binding_info_flag then begin
    let visitor = new visitor conv_uid tree in
    visitor#visit_all
  end;
  tree#collapse;
  tree#set_total_LOC ast#lines_read;
  tree#set_ignored_regions (ast#comment_regions @ ast#ignored_regions);
  tree#set_misparsed_regions ast#missed_regions;
  tree
]
