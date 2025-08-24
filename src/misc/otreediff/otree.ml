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
(* 
 * Ordered labeled trees for differentiation
 *
 * otree.ml
 *
 *)

(*************** Ordered Tree ***************)

[%%prepare_logger]

open Common
open Printf

module Comp = Compression

(* 
  does not contract the path less than contract_margin 
  when the cluster's top is the global root 
  (should contract_margin > 1)
*)
let contract_margin = 3 

let minimum_height = 3


type index = int

let cca_prefix = "cca"
let cca_ns = "http://codinuum.com/cca/"
let gid_attr_name = "gid"

module GI = GIndex

exception Parent_not_found of string

exception Found

exception Empty



(*** Tree Labels ***)

class virtual data =
  object (_ : 'data)
    method virtual equals       : 'data -> bool
    method virtual to_rep       : string
    method virtual to_string    : string
    method virtual to_elem_data : string * (string * string) list * string
  end

let tag_of_elem_data (tag, _, _) = tag
let name_of_elem_data (_, attrs, _) =
  List.fold_left
    (fun n (a, v) ->
      if n = "" then
        if Xstring.endswith a ":name" then
          v
        else
          ""
      else if Xstring.endswith a ":ident" then
        n^" "^v
      else
        n
    ) "" attrs

let _dot_label_of_node nd =
  sprintf "%d\\n%d:%s" nd#index nd#preorder_index
    (tag_of_elem_data nd#data#to_elem_data)


let dot_label_of_node nd =
  sprintf "%d(%a)\\n%d:%s%s" nd#index UID.ps nd#uid nd#preorder_index
    nd#to_qualified_string nd#data#digest_string

let dot_label_of_node_ini nd =
  let elem_data = nd#data#to_elem_data in
  sprintf "%a(%a)\\n%s%s" GI.ps nd#gindex UID.ps nd#uid
        (tag_of_elem_data elem_data)
        (let n = name_of_elem_data elem_data in
        if n = "" then "" else "\\n"^n)

let digest_to_string d_opt =
  match d_opt with
  | None -> ""
  | Some d -> Xhash.to_hex d

class virtual data2 = (* for collapsing/expanding *)
  object (self : 'data2)
    inherit data
    method virtual eq           : 'data2 -> bool (* data only equation *)
    method virtual digest       : Xhash.t option
    method virtual _digest      : Xhash.t option
    method virtual set_digest   : Xhash.t -> unit
    method virtual reset_digest : unit

    val mutable weight = 1
    method weight = weight
    method set_weight w = weight <- w

    val mutable gid = GI.unknown (* user specified global index *)
    method gid = gid
    method set_gid gi = gid <- gi

    method digest_string = digest_to_string self#digest
    method _digest_string = digest_to_string self#_digest
  end


(*** Tree Nodes ***)

[%%capture_path
class [ 'a ] node (d : 'a) =
  object (self : 'self)
    constraint 'a = #data

(* fields *)
    val mutable index = 0 (* post order index *)
    val mutable preorder_index = 0
    val mutable data = d
    val mutable parent = None
    val mutable children = ([||] : 'self array)
    val mutable position = 0

(* accessors *)
    method data = data
    method parent_edge = parent

    method parent = 
      match parent with 
      | Some x -> x 
      | _ -> raise (Parent_not_found (sprintf "index=%d" index))

    method children = children
    method children_indexes = 
      Array.to_list(Array.map (fun nd -> nd#index) children)

    method index = index
    method preorder_index = preorder_index
    method pos = position
    method nth_child n = 
      try
        children.(n)
      with 
        Invalid_argument _ ->
          out_of_bounds "Otree.node#nth_child: cannot get nth child: %d" n

    method nchildren = Array.length children

    method del_rightmost_child () =
      let len = self#nchildren in
      self#set_children (Array.sub self#children 0 (len - 1))

    method del_leftmost_child () =
      let len = self#nchildren in
      self#set_children (Array.sub self#children 1 (len - 1))

    method add_child_rightmost child =
      let len = self#nchildren in
      self#set_children (Array.append self#children [|child|]);
      child#set_parent self;
      child#set_pos len

    method add_child_leftmost child =
      let old_children = self#children in
      self#set_children (Array.append [|child|] old_children);
      child#set_parent self;
      child#set_pos 0;
      Array.iter (fun nd -> nd#set_pos (nd#pos + 1)) old_children

    method add_children_rightmost children =
      let len = self#nchildren in
      self#set_children (Array.append self#children children);
      Array.iteri 
        (fun i child ->
          child#set_pos (i+len);
          child#set_parent self
        ) children

    method add_children_leftmost children =
      let old_children = self#children in
      self#set_children (Array.append children old_children);
      Array.iteri 
        (fun i child ->
          child#set_pos i;
          child#set_parent self
        ) children;
      let len = Array.length children in
      Array.iteri (fun i ochild -> ochild#set_pos (i+len)) old_children

    method add_child pos child =
      (*printf "!!! add_child: %s (pos=%d) %s\n" self#to_string pos child#to_string;*)
      let children = self#children in
      let len = self#nchildren in
      if pos = 0 then self#add_child_leftmost child
      else if pos = len then self#add_child_rightmost child
      else if 0 < pos && pos < len then
        let left = Array.sub children 0 pos in
        let right = Array.sub children pos (len - pos) in
        self#set_children (Array.concat [left; [|child|]; right]);
        child#set_parent self;
        child#set_pos pos;
        Array.iter (fun nd -> nd#set_pos (nd#pos + 1)) right
      else
        out_of_bounds
          "Otree.node#add_child: illegal position: %d (node=%s, nchildren=%d)"
          pos (self#to_string) len

(* setters *)
    method set_data d = data <- d
    method set_index i = index <- i
    method set_preorder_index i = preorder_index <- i
    method set_parent_edge e = parent <- e
    method set_parent nd = parent <- Some nd
    method set_children nds = children <- nds
    method set_pos n = position <- n

(* misc *)
    method has_parent = match parent with Some _ -> true | None -> false

    method is_leaf = self#children = [||]

    method replace_nth_child n (children : 'self array) = 
      
      [%debug_log "node=%d pos=%d children=[%s]" self#index n
        (Xarray.to_string (fun nd -> nd#data#to_string) ";" children)];

      let a = self#children in
      (self#nth_child n)#set_pos (-1);
      let alen = Array.length a in
      let ca = children in
      try
        let left = if n = 0 then [||] else Array.sub a 0 n in
        let right =
          if n = alen - 1 then [||] else Array.sub a (n + 1) (alen - n - 1)
        in
        Array.iteri (fun i c -> c#set_parent self; c#set_pos (i + n)) ca;
        Array.iteri (fun i c -> c#set_pos (i + n + (Array.length ca))) right;
        self#set_children (Array.append (Array.append left ca) right)
      with 
        Invalid_argument _ ->
          raise (Invalid_argument "Otree.node#replace_nth_child")

    method replace_children pos_and_children_list =

      [%debug_log "index=%d {%s}" self#index
          (Xlist.to_string
             (fun (pos, children) ->
               sprintf "(%d,[%s])"
                 pos
                 (Xarray.to_string (fun n -> string_of_int n#index) ";" children)
             ) ";" pos_and_children_list)];

      let c = ref [] in
      let _ =
        for i = (self#nchildren) - 1 downto 0 do
          try
            let children = List.assoc i pos_and_children_list in
            (self#nth_child i)#set_pos(-1);
            Array.iter (fun c' -> c'#set_parent self) children;
            c := children::!c
          with
            Not_found -> c := [|self#nth_child i|]::!c
        done
      in
      let new_children = Array.concat !c in
      Array.iteri
        (fun i child -> child#set_pos i) new_children;
      self#set_children new_children


    method prune_nth_child n =

      [%debug_log "index=%d, n=%d, " self#index n];

      let pruned = self#nth_child n in

      [%debug_log "pruning child index=%d\n" pruned#index];

      let len = self#nchildren in

      for i = n + 1 to len - 1 do
        let child = self#nth_child i in child#set_pos (child#pos - 1)
      done;

      let a = self#children in
      try
        let new_children_L = Array.sub a 0 n in
        let new_children_R = Array.sub a (n + 1) (len - n - 1) in
        let new_children = Array.append new_children_L new_children_R in

        [%debug_log "new children [\n%s\n]" 
          (Xarray.to_string (fun nd -> nd#to_string) "\n" new_children)];

        self#set_children new_children;
        pruned#set_pos (-1)

      with 
        Invalid_argument _ ->
          raise (Invalid_argument "Otree.node#prune_nth_child")

    (* end of method prune_nth_child *)


    method to_rep =
      let chldrn_to_string = 
        Xarray.to_string (fun c -> string_of_int c#index) ";"
      in
      let chldrn_str = 
        let s = chldrn_to_string self#children in
        if s = "" then
          ""
        else
          sprintf " chldrn=[%s]" s
      in
      try
        sprintf "<%d:%s ps=%d prnt=%d%s>"
          self#index self#data#to_rep self#pos
          self#parent#index chldrn_str
      with 
        Parent_not_found _ ->
          sprintf "<%d:%s%s>"
            self#index self#data#to_rep chldrn_str


      
    method to_string =
      let chldrn_to_string = 
        Xarray.to_string (fun c -> string_of_int c#index) ";"
      in
      let chldrn_str = 
        let s = chldrn_to_string self#children in
        if s = "" then
          ""
        else
          sprintf " children=[%s]" s
      in
      try
        sprintf "<%d:%s pos=%d parent=%d%s>"
          self#index self#data#to_string self#pos
          self#parent#index chldrn_str
      with
        Parent_not_found _ ->
          sprintf "<%d:%s%s>"
            self#index self#data#to_string chldrn_str

    method print = printf "%s\n" self#to_string

    method to_dot ?(mklab=_dot_label_of_node) () =
      sprintf "%d [label=\"%s\"];\n" self#index (mklab self)

  end (* of class Otree.node *)

and [ 'node ] path =
  object (_ : 'self)
    constraint 'node = #data #node
    val mutable nodes = ([] : 'node list)
    method length = List.length nodes
    method is_empty = nodes = []
    method nodes = nodes
    method set_nodes nds = nodes <- nds
    method insert_nodes nds = nodes <- nds @ nodes
    method equals (path : 'self) =
      let nodes' = path#nodes in
      if List.length nodes <> List.length nodes' then false
      else begin
        List.fold_left2
          (fun b nd1 nd2 ->
            b && nd1#data#equals nd2#data
          ) true nodes nodes'
      end
    method to_string = 
      Xlist.to_string (fun nd -> nd#data#to_string) "/" nodes
  end
]

type 'node mutation =
  | Minsert of float (* offset *) * 'node list * bool (* later *)
  | Mdelete

let mutation_to_string = function
  | Minsert(o, cl, later) ->
      sprintf "ins(%s)%s:\n%s" (Path.Elem.ofs_to_str o) (if later then "*" else "")
        (String.concat "\n"
           (List.map (fun x -> "     "^x#initial_to_string) cl));
  | Mdelete -> "del"


[%%capture_path
class [ 'a ] node2 (uid_gen : UID.generator) (d : 'a) =
  let uid = uid_gen#gen in
  let hash = lnot uid in
  object (self : 'self)
    constraint 'a = #data2
    inherit [ 'a ] node d as super

    val mutation_tbl = (Hashtbl.create 0 : (int, 'self mutation list) Hashtbl.t)
    val mutable mutation_started = false

    val mutable apath = Path.root
    method set_apath p = apath <- p
    method apath = apath

    val mutable gindex = (GI.dummy : GI.t) (* global postorder index *)
    method set_gindex i = gindex <- i
    method gindex = gindex

    method uid = uid (* unique node id *)

    method hash = hash

    val mutable collapsible = false
    method collapsible = collapsible
    method set_collapsible = collapsible <- true
    method clear_collapsible = collapsible <- false

    method decide_collapsible_or_not =
      if self#children = [||] then
        self#clear_collapsible
      else
        self#set_collapsible

    method! set_parent nd = 
      [%debug_log "self=%a arg=%a" UID.ps self#uid UID.ps nd#uid];
      super#set_parent nd

    method! replace_children pos_and_children_list =
      self#_replace_children ~initial:false pos_and_children_list

    method _replace_children ?(initial=false) pos_and_children_list =

      [%debug_log "(self=%a) {%s}" UID.ps self#uid
        (Xlist.to_string
           (fun (pos, children) ->
             sprintf "(%d,[%s])"
               pos
               (Xarray.to_string (fun n -> UID.to_string n#uid) ";" children)
           ) ";" pos_and_children_list)];

      
      [%debug_log "(self=%a): old children=[%s]" UID.ps self#uid
        (Xarray.to_string (fun nd -> UID.to_string nd#uid) "," self#children)];
(*
      printf "!!! replace_children: (self=%a) {%s}\n" UID.p self#uid
        (Xlist.to_string
           (fun (pos, children) ->
             sprintf "(%d,[%s])"
               pos
               (Xarray.to_string (fun n -> UID.to_string n#uid) ";" children)
           ) ";" pos_and_children_list);

      printf "!!! old children=[%s]\n"
        (Xarray.to_string (fun nd -> UID.to_string nd#uid) "," self#children);
*)
(*      super#replace_children pos_and_children_list; *)

      let c = ref [] in
      let nchildren = if initial then self#initial_nchildren else self#nchildren in
      let nth_child =
        if initial then
          fun i -> self#initial_children.(i)
        else
          self#nth_child
      in
      let set_parent =
        if initial then
          fun c -> c#set_initial_parent self
        else
          fun c -> c#set_parent self
      in
      let _ =
        for i = nchildren - 1 downto 0 do
          try
            let children = List.assoc i pos_and_children_list in
            (nth_child i)#set_pos(-1);
            Array.iter set_parent children;
            c := children::!c
          with
            Not_found -> c := [|nth_child i|]::!c
        done
      in
      let new_children = Array.concat !c in
      let set_pos =
        if initial then
          fun i c -> c#set_initial_pos i
        else
          fun i c -> c#set_pos i
      in
      Array.iteri set_pos new_children;
      if initial then
        self#set_initial_children new_children
      else
        self#set_children new_children;

      [%debug_log "(self=%a): new children=[%s]" UID.ps self#uid
        (Xarray.to_string (fun nd -> UID.to_string nd#uid) "," new_children)];
(*
      printf "!!! new children=[%s]\n"
        (Xarray.to_string (fun nd -> UID.to_string nd#uid) "," new_children);
*)

    val mutable initial_children = ([||] : 'self array)
    method initial_children = initial_children
    method initial_children_uids = 
      Array.to_list(Array.map (fun nd -> nd#uid) initial_children)

    method set_initial_children c =
      (*printf "!!! set_initial_children: %a -> [%s]\n"
        UID.p self#uid (Xarray.to_string (fun c -> UID.to_string c#uid) ";" c);*)
      initial_children <- Array.copy c

    method initial_nchildren = Array.length initial_children

    val mutable initial_position = 0
    method initial_pos = initial_position
    method set_initial_pos pos = initial_position <- pos

    val mutable substances = ([] : 'self list)
    method add_substance nd = substances <- nd::substances
    method get_substances =
      List.concat_map
        (fun nd ->
          let s = nd#get_substances in
          match s with
          | [] -> [nd]
          | _ -> s
        ) substances



    method children_uids =
      Array.to_list(Array.map (fun nd -> nd#uid) children)

    method! nth_child n =
      try
        children.(n)
      with
        Invalid_argument _ ->
          out_of_bounds "Otree.node2#nth_child: cannot get nth child: %d (uid=%a)" n UID.p uid

    method! to_string =
      let chldrn_to_string =
        Xarray.to_string (fun c -> UID.to_string c#uid) ";"
      in
      let chldrn_str =
        let s = chldrn_to_string self#children in
        if s = "" then "" else sprintf " children=[%s]" s
      in
      let s =
        try
          sprintf "<%a(%a):%s pos=%d parent=%a%s>"
            UID.ps self#uid GI.ps self#gindex self#data#to_string
            self#pos UID.ps self#parent#uid
            chldrn_str
        with
          Parent_not_found _ ->
            sprintf "<%a(%a):%s%s>"
              UID.ps self#uid GI.ps self#gindex self#data#to_string chldrn_str
      in
      sprintf "%s%s" s
        (if self#is_collapsed then
          sprintf "$%s(%d)" self#data#digest_string self#data#weight
        else
          "")

    method initial_to_string =
      let chldrn_to_string =
        Xarray.to_string (fun c -> UID.to_string c#uid) ";"
      in
      let chldrn_str =
        let s = chldrn_to_string self#initial_children in
        if s = "" then "" else sprintf " children=[%s]" s
      in
      let s =
        try
          sprintf "<%a(%a):%s pos=%d parent=%a%s>"
            UID.ps self#uid GI.ps self#gindex self#data#to_string
            self#initial_pos UID.ps self#initial_parent#uid
            chldrn_str
        with
          Parent_not_found _ ->
            sprintf "<%a(%a):%s%s>"
              UID.ps self#uid GI.ps self#gindex self#data#to_string chldrn_str
      in
      sprintf "%s%s" s
        (if self#is_collapsed then
          sprintf "$%s(%d)" self#data#digest_string self#data#weight
        else
          "")

    val mutable collapse_locked = false

    method collapse_locked = collapse_locked
    method collapse_not_locked = not collapse_locked
    method lock_collapse = collapse_locked <- true
    method unlock_collapse = collapse_locked <- false

    val mutable is_collapsed = false

    val mutable in_path = false

    val mutable hidden_parent = None

    method hidden_parent = 
      match hidden_parent with 
      | Some nd -> nd 
      | None -> raise (Parent_not_found (sprintf "hidden:uid=%a" UID.ps self#uid))
    method hide_parent = hidden_parent <- parent; parent <- None
    method unhide_parent = parent <- hidden_parent; hidden_parent <- None
    method has_hidden_parent =
      match hidden_parent with Some _ -> true | None -> false


    val mutable initial_parent = (None : 'self option)

    method initial_parent = 
      match initial_parent with 
      | Some nd -> nd 
      | None -> raise (Parent_not_found (sprintf "initial:uid=%a" UID.ps self#uid))

    method set_initial_parent nd =
      (*printf "!!! set_initial_parent: %a -> %a\n" UID.p self#uid UID.p nd#uid;*)
      initial_parent <- Some nd

    method has_initial_parent = 
      match initial_parent with Some _ -> true | None -> false


    val mutable hidden_children = [||]

    method hidden_children = hidden_children
    method set_hidden_children c = hidden_children <- c

    method prune_all_children =
      [%debug_log "%a" UID.ps self#uid];
      Array.iter (fun c -> c#set_pos (-1)) self#children;
      self#set_children [||]

    method private _prune_children nchildren a set_pos set_children posl =
      let nth_child i = a.(i) in

      let posl = List.fast_sort compare posl in
      let posl = List.filter (fun p -> p >= 0) posl in

      [%debug_log "%s[%a](nchildren=%d) {%s}"
        self#to_string UID.ps self#uid self#nchildren
        (Xlist.to_string string_of_int "," posl)];

      let start = ref 0 in
      let res = ref [||] in
      try
        List.iter
          (fun pos ->
            let len = pos - !start in
            res := Array.append !res (Array.sub a !start len);
            start := pos + 1
          ) posl;
        if !start < nchildren then
          res := Array.append !res (Array.sub a !start (nchildren - !start));

        Array.iteri (fun i c -> set_pos c i) !res;

        [%debug_log "new children: [\n%s\n]"
          (Xarray.to_string (fun nd -> nd#to_string) "\n" !res)];

        List.iter (fun p -> set_pos (nth_child p) (-1)) posl;

        set_children !res

      with 
        Invalid_argument _ ->
          raise (Invalid_argument
                   (sprintf "Otree.node2#_prune_children: %s" self#to_string))
    (* end of method _prune_children *)

    method prune_children posl =
      self#_prune_children
        self#nchildren self#children (fun n -> n#set_pos) self#set_children
        posl

    method prune_initial_children posl =
      self#_prune_children
        self#initial_nchildren self#initial_children (fun n -> n#set_initial_pos)
        self#set_initial_children
        posl
(*
    method prune_children posl =
      let posl = List.fast_sort compare posl in
      let posl = List.filter (fun p -> p >= 0) posl in

      [%debug_log "%s[%a](nchildren=%d) {%s}" 
        self#to_string UID.ps self#uid self#nchildren
        (Xlist.to_string string_of_int "," posl)];

      let nchildren = self#nchildren in
      let a = self#children in
      let start = ref 0 in
      let res = ref [||] in
      try
        List.iter
          (fun pos ->
            let len = pos - !start in
            res := Array.append !res (Array.sub a !start len);
            start := pos + 1
          ) posl;
        if !start < nchildren then
          res := Array.append !res (Array.sub a !start (nchildren - !start));

        Array.iteri (fun i c -> c#set_pos i) !res;
        
        [%debug_log "new children: [\n%s\n]" 
          (Xarray.to_string (fun nd -> nd#to_string) "\n" !res)];

        List.iter (fun p -> (self#nth_child p)#set_pos (-1)) posl;

        self#set_children !res

      with 
        Invalid_argument s ->
          raise (Invalid_argument (sprintf "Otree.node2#prune_children: %s" self#to_string))
    (* end of method prune_children *)
*)
    method expand =
      if is_collapsed && not collapse_locked then begin
        [%debug_log "%a: expanding..." UID.ps self#uid];
        self#data#reset_digest;
        self#set_children hidden_children;
        self#set_hidden_children [||];
        is_collapsed <- false
      end


    method collapse w d =
      if not is_collapsed && collapsible (* && self#children <> [||] *) then begin
        [%debug_log "%a: collapsing..." UID.ps self#uid];
        self#data#set_digest d;
        self#data#set_weight w;
        self#set_hidden_children self#children;
        self#set_children [||];
        is_collapsed <- true
      end


    method set_digest d =
      self#data#set_digest d;

    method is_collapsed = is_collapsed
    method _set_is_collapsed b = is_collapsed <- b

    method in_path = in_path
    method set_in_path = in_path <- true
    method clear_in_path = in_path <- false

    method prune =

      [%debug_log "pruning [%a]" UID.ps self#uid];

      let rec prune nd =

        if nd#in_path then begin
          [%info_log "node(index=%d uid=%a) is in path" nd#index UID.ps nd#uid];
          List.iter prune nd#get_substances
        end
        else begin
          try
            let parent =
              try
                nd#parent
              with
                Parent_not_found _ -> nd#initial_parent
            in

            [%debug_log "from <%a: %s> prune %dU@%d" UID.ps parent#uid
              (Xlist.to_string UID.to_string ";" parent#children_uids)
              nd#uid nd#pos];

            parent#prune_nth_child nd#pos;
            nd#set_pos (-1);

            [%debug_log "<%a: %s>" UID.ps parent#uid
              (Xlist.to_string UID.to_string ";" parent#children_uids)]

          with
            Not_found -> ()
        end
      in
      prune self



    val path = (new path : 'self path)
    method path = path
    method set_path nds =
      path#set_nodes nds;
      List.iter
        (fun nd ->
          nd#set_in_path;
          nd#add_substance self
        ) nds

    method insert_path nds =
      [%info_log "(self=%a) %s" UID.ps uid
        (Xlist.to_string (fun nd -> UID.to_string nd#uid) "/" nds)];
      path#insert_nodes nds;
      List.iter
        (fun nd ->
          nd#set_in_path;
          nd#add_substance self
        ) nds

    method is_contracted = not path#is_empty

    method to_qualified_string = 
      let p = path#to_string in
      let s = if is_collapsed then "$" else "" in
      sprintf "%s%s%s" (if p = "" then "" else p^"/") (tag_of_elem_data self#data#to_elem_data) s


    method to_dot_str ?(mklab=dot_label_of_node) () =
      sprintf "%a [label=\"%s\"];\n" UID.rs self#uid (mklab self)

    method to_dot_str_ini ?(mklab=dot_label_of_node) () =
      sprintf "%a [label=\"%s\"];\n" UID.rs self#uid (mklab self)

(*
    method is_initial_ancestor_of (node : 'self) = (* inefficient *)
      let rec proc_one nd =
        try
          let pnd = nd#initial_parent in
          if pnd#uid = uid then
            true
          else
            proc_one pnd
        with
        | Parent_not_found _ -> false
      in
      proc_one node
*)

    method iter_initial_ancestor_nodes (f : 'self -> unit) = (* from the parent *)
      let rec proc_one nd =
        try
          let pnd = nd#initial_parent in
          f pnd;
          proc_one pnd
        with
          Parent_not_found _ -> ()
      in
      proc_one self


    method initial_ancestor_nodes = (* [ancestor0;...;parent] *)
      let res = ref [] in
      self#iter_initial_ancestor_nodes (fun nd -> res:= nd::!res);
      !res


    method is_valid = GI.is_valid self#gindex


(* virtual mutation (for consistent multiple child(ren) insertions and deletions) *)

    method private mutation_tbl_add pos m =
      try
        let l = Hashtbl.find mutation_tbl pos in
        Hashtbl.replace mutation_tbl pos (m::l)
      with
        Not_found -> Hashtbl.add mutation_tbl pos [m]

    method init_mutation() =
      mutation_started <- false


    method begin_mutation() =
      if not mutation_started then begin
        [%debug_log "start"];
        Hashtbl.clear mutation_tbl;
        mutation_started <- true
      end

    method v_insert_children ?(later=false)
        ?(offset=(-1.)) pos (children : 'self list)
        =
      [%debug_log "%s\npos=%d offset=%s [%s]" self#to_string
        pos (Path.Elem.ofs_to_str offset)
        (String.concat ";" (List.map (fun n -> UID.to_string n#uid) children))];

      (*Printf.printf "!!! v_insert_children: %s\npos=%d offset=%s [%s]\n"
        self#to_string
        pos (Path.Elem.ofs_to_str offset)
        (String.concat ";" (List.map (fun n -> UID.to_string n#uid) children));*)

      self#mutation_tbl_add pos (Minsert(offset, children, later))

    method v_insert_child ?(later=false) ?(offset=(-1.)) pos child =
      self#v_insert_children ~later ~offset pos [child]

    method v_update_children pos (children : 'self list) =
      [%debug_log "pos=%d" pos];
      self#mutation_tbl_add pos Mdelete;
      self#mutation_tbl_add pos (Minsert(0., children, false))

    method v_update_child pos child = self#v_update_children pos [child]
    val mutable v_delete_child_count = 0
    method v_delete_child pos =
      [%debug_log "pos=%d" pos];
      (*printf "!!! v_delete_child: %a: pos=%d\n" UID.p self#uid pos;*)
      self#mutation_tbl_add pos Mdelete

    method v_delete_children = List.iter self#v_delete_child

    method has_later_mutation =
      let b =
        try
          Hashtbl.iter
            (fun (*pos*)_ ms ->
              List.iter
                (function
                  | Minsert(_, _, true)(* as m*) ->
                      (*printf "pos=%d %s\n" pos (mutation_to_string m);*)
                      raise Exit
                  | _ -> ()
                ) ms
            ) mutation_tbl;
          false
        with
          Exit -> true
      in
      (*printf "has_later_mutation: %s -> %B\n" (UID.to_string uid) b;*)
      b

    method end_mutation ?(overwrite=true) () = (* flush mutations *)
      [%debug_log "overrite=%B %s" overwrite self#initial_to_string];
      (*printf "!!! end_mutation: overwrite=%B %s\n" overwrite self#initial_to_string;*)

      (*printf "!!! %s:\n" self#initial_to_string;
      Hashtbl.iter
        (fun pos ms ->
          printf "!!!   pos=%d:\n" pos;
          List.iter
            (fun m ->
              printf "!!!     %s\n" (mutation_to_string m);
            ) ms
        ) mutation_tbl;*)

      let buf = ref [] in
      let push x =
        (*printf "!!! [%s] push: %s\n" (UID.to_string uid) x#to_string;*)
        let b =
          overwrite ||
          let p_opt = try Some x#parent with _ -> None in
          let ip_opt = try Some x#initial_parent with _ -> None in
          match p_opt, ip_opt with
          | Some p, Some ip -> p == ip
          | None, None -> true
          | _ -> false
        in
        if b then begin
          (*printf "!!! pushed\n";*)
          buf := x :: !buf
        end
      in
      let push_multi = List.iter push in

      if self#initial_nchildren = 0 then begin
        [%debug_log "nchildren=0"];
        (*printf "!!! nchildren=0\n";*)
        try
          let ms = List.rev (Hashtbl.find mutation_tbl 0) in
          let _insl = List.filter (function Minsert _ -> true | _ -> false) ms in
          let insl =
            List.fast_sort
              (fun m0 m1 ->
                match m0, m1 with
                | (Minsert(o0, (*nds0*)_, _)), (Minsert(o1, (*nds1*)_, _)) -> begin
                    compare o0 o1
                    (*if o0 = o1 && o0 <> 0. then begin
                      try
                        let c = ref 0 in
                        let last0 = Xlist.last nds0 in
                        let head1 = List.hd nds1 in
                        if last0#initial_parent == head1#initial_parent then
                          if last0#initial_pos < head1#initial_pos then
                            c := -1;
                        if !c = 0 then begin
                          let last1 = Xlist.last nds1 in
                          let head0 = List.hd nds0 in
                          if last1#initial_parent == head0#initial_parent then
                            if last1#initial_pos < head0#initial_pos then
                              c := 1
                        end;
                        !c
                      with
                      | _ -> 0
                    end
                    else
                      compare o0 o1*)
                end
                | _ -> 0
              ) _insl
          in
          List.iter
            (function
              | Minsert(o, nds, _) ->
                  let _ = o in
                  [%debug_log "ofs=%s" (Path.Elem.ofs_to_str o)];
                  (*printf "!!! ofs=%s\n" (Path.Elem.ofs_to_str o);*)
                  push_multi nds
              | _ -> ()
            ) insl
          
        with
          Not_found -> () (* weird *)
      end
      else begin
        Array.iteri
          (fun pos child ->
            [%debug_log "pos=%d %s" pos child#initial_to_string];
            (*printf "!!! %s: pos=%d %s\n" (UID.to_string uid) pos child#initial_to_string;*)
            
            try
              let ms = Hashtbl.find mutation_tbl pos in

              let ins_tbl = Hashtbl.create 0 in (* ofs -> mutation list *)
              let ins_tbl_add ofs m =
                try
                  let l = Hashtbl.find ins_tbl ofs in
                  Hashtbl.replace ins_tbl ofs (m::l)
                with
                  Not_found -> Hashtbl.add ins_tbl ofs [m]
              in

              let del_count, ins_count, has_0ofs =
                List.fold_left
                  (fun (d, i, z) m ->
                    match m with
                    | Minsert(o, _, _) ->

                        [%debug_log " %s" (mutation_to_string m)];
                        (*printf "!!! %s\n" (mutation_to_string m);*)

                        ins_tbl_add o m;
                        (d, i + 1, z || o = 0.)

                    | Mdelete       ->
                        [%debug_log " del"];
                        (*printf "!!! del\n";*)
                        (d + 1, i, z)

                  ) (0, 0, false) ms
              in
              [%debug_log "del_count=%d ins_count=%d" del_count ins_count];
              (*printf "!!! del_count=%d ins_count=%d\n" del_count ins_count;*)

              let has_del = del_count > 0 in

              let moved =
                ins_count > 0 && del_count > ins_count && child#initial_parent != self
              in
              
              [%debug_log "has_del=%B has_0ofs=%B moved=%B" has_del has_0ofs moved];
              (*printf "!!! has_del=%B has_0ofs=%B moved=%B\n" has_del has_0ofs moved;*)
            
              let insl =
                Hashtbl.fold
                  (fun _ ms l ->
                    match ms with
                    | [] -> assert false
                    | [m] -> m::l
                    | _ -> ms @ l
                  ) ins_tbl []
              in
              [%debug_log "insl:\n%s" (String.concat "\n" (List.map mutation_to_string insl))];
              (*printf "!!! insl:\n%s\n" (String.concat "\n" (List.map mutation_to_string insl));*)
              
              let insl =
                List.fast_sort
                  (fun m0 m1 ->
                    match m0, m1 with
                    | (Minsert(o0, _, _)), (Minsert(o1, _, _)) -> compare o0 o1
                    | _ -> 0
                  )
                  (if has_del || has_0ofs then begin
                    if moved then begin
                      let _, others =
                        List.partition
                          (function
                            | Minsert(ofs, nds, _) -> begin
                                let b = ofs = 0. in
                                if b then begin

                                  [%debug_log "%s: %d -> [%s]"
                                    (UID.to_string child#initial_parent#uid)
                                    child#initial_pos
                                    (String.concat ";"
                                       (List.map (fun n -> UID.to_string n#uid) nds))];

                                  (*printf "!!! %s: %d -> [%s]\n"
                                    (UID.to_string child#initial_parent#uid)
                                    child#initial_pos
                                    (String.concat ";"
                                       (List.map (fun n -> UID.to_string n#uid) nds));*)

                                  child#initial_parent#_replace_children
                                    ~initial:true
                                    [child#initial_pos, Array.of_list nds];

                                  child#set_initial_parent child#parent;
                                  Array.iteri
                                    (fun pos c -> if c == child then child#set_initial_pos pos)
                                    child#initial_parent#initial_children

                                end;
                                b
                            end
                            | _ -> assert false
                          ) insl
                      in
                      others
                    end
                    else
                      insl
                  end
                  else begin
                    (Minsert(0., [child], false)) :: insl
                  end
                  )
              in

              List.iter
                (function
                  | Minsert(_, nds, _) -> push_multi nds
                  | Mdelete -> assert false
                ) insl

            with
              Not_found -> push child

          ) initial_children; (* Array.iteri (fun pos child ->... *)

      end;

      initial_children <- (Array.of_list (List.rev !buf));

      Array.iteri
        (fun pos c ->
          let p_opt = try Some c#parent with _ -> None in
          let ip_opt = try Some c#initial_parent with _ -> None in
          if
            match p_opt, ip_opt with
            | Some p, Some ip -> p == ip
            | None, None -> true
            | _ -> false
          then begin
            c#set_initial_parent self;
            c#set_initial_pos pos;
          end
          else begin
            c#set_parent self;
            c#set_pos pos
          end
        ) initial_children;

      begin %debug_block
        [%debug_log "%s\nnew children:" self#initial_to_string];
        Array.iter (fun c -> [%debug_log "  %s" c#initial_to_string]) initial_children;
      end;

      (*printf "!!! %s\n" self#initial_to_string;
      printf "!!! new children:\n";
      Array.iter (fun c -> printf "  %s\n" c#initial_to_string) initial_children;*)

      [%debug_log "exit"];
      (*printf "!!! exit\n";*)

  end (* of class Otree.node2 *)
]


(*** Orderd Trees ***)

[%%capture_path
class [ 'node ] otree (root : 'node) =
  object (self : 'self)
    constraint 'node = #data #node

    val mutable size = 0
    val mutable node_table = [||] (* postorder *)
    val mutable leftmost_table = [||] (* maintain leftmost node for subtrees *)

(* accessors *)
    method root = root
    method size = size
    method node_table = node_table

(* getters *)
    method get idx =
      try
        node_table.(idx)
      with
        Invalid_argument _ ->
          out_of_bounds "Otree.otree#get: index=%d size=%d" idx self#size

    method nth_gen idx n =
      let rec gen nd n =
        let l = Array.to_list nd#children in
        if n < 1 then invalid_arg "Otree.otree#nth_gen"
        else if n = 1 then [nd]
        else if n = 2 then l
        else if n > 2 then
          List.concat_map (fun nd' -> gen nd' (n - 1)) l
        else []
      in
      gen (self#get idx) n

    method leftmost idx =
      try
        leftmost_table.(idx)
      with
        Invalid_argument _ ->
          out_of_bounds "Otree.otree#leftmost(%d)" idx

    method leaves =
      let res = ref [] in
      for i = 0 to self#size - 1 do
        let nd = self#get i in
        if nd#is_leaf then res := (nd#index)::!res
      done;
      !res

    method nleaves = List.length self#leaves

    method ancestor_nodes nod = (* rightmost is the parent *)
      let nd = ref nod in
      let old = ref [] in
      let a = ref [] in
      let _ = 
        try
          while true do
            let pnd = (!nd)#parent in
            old := !a;
            a := pnd::!a;
            nd := pnd
          done
        with
        | Parent_not_found _ -> ()
        | Out_of_bounds -> a := !old
      in !a

    method ancestors idx = (* rightmost is the parent *)
      List.map (fun nd -> nd#index) (self#ancestor_nodes (self#get idx))

    method distance nd1 nd2 =
      let ands1 = self#ancestor_nodes nd1 in
      let ands2 = self#ancestor_nodes nd2 in
      let rec scan count ndi_opt = function
        | h1::t1, h2::t2 ->
            if h1 == h2 then
              scan (count + 1) (Some (h1, count)) (t1, t2)
            else
              scan (count + 1) ndi_opt (t1, t2)
        | [], _ | _, [] ->
            ndi_opt
      in
      match scan 0 None (ands1, ands2) with
      | Some (_, i) ->
          let d = (List.length ands1) - i + (List.length ands2) - i in
          d
      | _ -> raise (Failure "Otree.otree#distance")
      

    method height = 
      maxn (List.map (fun i -> List.length(self#ancestors i)) self#leaves)

    method get_roots_of_forest (src : index) (dest : index) =
      if src > dest then invalid_arg "Otree.otree#get_roots_of_forest";
      let roots = ref [] in
      self#scan src dest
        (fun nd ->
          try
            let i = nd#parent#index in
            if not (src <= i && i <= dest) then roots := (nd#index)::!roots
          with
            Parent_not_found _ -> roots := (nd#index)::!roots
        );
      !roots


    method get_leaves nd =
      let res = ref [] in
      self#scan_subtree nd 
        (fun nd -> if nd#is_leaf then res := nd::!res);
      !res

    method get_all_leaves =
      let res = ref [] in
      self#scan_all (fun nd -> if nd#is_leaf then res := nd::!res);
      !res

    method get_leavesi idx =
      let res = ref [] in
      self#scan_subtree (self#get idx)
        (fun nd -> if nd#is_leaf then res := (nd#index)::!res);
      !res

    method get_all_leavesi =
      let res = ref [] in
      self#scan_all 
        (fun nd -> if nd#is_leaf then res := (nd#index)::!res);
      !res

(*
    method keynodes =
      let leftmost_idxs, res = ref [], ref [] in
      for i = self#size downto 1 do
        let lm = (self#leftmost i) in
        if List.mem lm !leftmost_idxs then ()
        else res := i::!res; leftmost_idxs := lm::!leftmost_idxs
      done; !res
*)
    method keynodes =
      let leftmost_idxs = Hashtbl.create 0 in
      let res = ref [] in
      for i = self#size downto 1 do
        let lm = self#leftmost i in
        if not (Hashtbl.mem leftmost_idxs lm) then begin
          res := i::!res;
          Hashtbl.add leftmost_idxs lm true
        end
      done; 
      !res

    method size_of_subtree idx =
      let sz = ref 0 in
      let rt = self#get idx in
      self#scan_subtree rt (fun _ -> incr sz);
      !sz

    method left_siblings idx =
      let ci = 
        Array.map (fun nd -> nd#index) (self#get idx)#parent#children
      in
      try
        Array.to_list(Array.sub ci 0 (self#get idx)#pos)
      with 
        Invalid_argument _ ->
          raise (Invalid_argument "Otree.otree#left_siblings")

    method right_siblings idx =
      let ci = 
        Array.map (fun nd -> nd#index) (self#get idx)#parent#children
      in
      let pos = (self#get idx)#pos in
      try
        Array.to_list(Array.sub ci (pos + 1) ((Array.length ci) - pos - 1))
      with 
        Invalid_argument _ ->
          raise (Invalid_argument "Otree.otree#right_siblings")

(* scanners *)

 (* postorder *)
    method scan_subtree node f = 
      let rec do_scan nd = Array.iter do_scan nd#children; f nd in
      do_scan node

    method scan_all f = self#scan_subtree self#root f

    method fast_scan_all (f : 'node -> unit) =
      for i = 1 to self#size do
        f (self#get i)
      done

    method scan_subtreei node (f : index -> 'node -> unit) =
      let i = ref 1 in
      let rec do_scan node =
        Array.iter (fun nd -> do_scan nd) node#children;
        f !i node; incr i
      in do_scan node

    method fast_subtree_members idx =
      let result = ref [] in
      for i = self#leftmost idx to idx do
        result := i::!result
      done;
      !result

    method subtree_members idx =
      let result = ref [] in
      self#scan_subtree (self#get idx) 
        (fun nd -> result := (nd#index)::!result);

      [%debug_log "subtree_members %d: %s" 
          idx (Xlist.to_string string_of_int "," !result)];

      !result

    method scan_alli (f : index -> 'node -> unit) =
      self#scan_subtreei self#root f

    method scan (src : index) (dest : index) f =
      if src > dest then invalid_arg "Otree.otree#scan";
      try
        for i = src to dest do f node_table.(i) done
      with 
        Invalid_argument _ -> invalid_arg "Otree.otree#scan"

 (* preorder *)
    method preorder_scan_subtreei node (f : index -> 'node -> unit) =
      let i = ref 1 in
      let rec do_scan nd =
        let c = nd#children in
        f !i nd;
        Array.iter (fun nd -> incr i; do_scan nd) c
      in do_scan node

    method preorder_scan_subtree node (f : 'node -> unit) =
      let rec do_scan nd = 
        let c = nd#children in
        f nd; Array.iter (fun nd -> do_scan nd) c
      in
      do_scan node

    method preorder_scan_alli (f : index -> 'node -> unit) =
      self#preorder_scan_subtreei self#root f

    method preorder_scan_all (f : 'node -> unit) =
      self#preorder_scan_subtree self#root f


    (*** updaters ***)

    method update_leftmost_table = 
      let res = ref [0] in
      let lm nd =
        let lmn = ref nd in
        while !lmn#children <> [||] do
          lmn := !lmn#children.(0)
        done;
        !lmn#index
      in
      self#scan_all (fun nd -> res := (lm nd)::!res);
      leftmost_table <- (Array.of_list (List.rev !res))

    method reindex = self#scan_alli (fun i nd -> nd#set_index i)

    method preorder_reindex = 
      self#preorder_scan_alli (fun i nd -> nd#set_preorder_index i)

    method update_node_table =
      let res = ref [root] in
      self#scan_alli
        (fun i nd ->
          res := nd::!res;
          nd#set_index i;
          let children = nd#children in
          Array.iter (fun cnd -> cnd#set_parent nd) children;
          for i = 0 to nd#nchildren - 1 do
            (children.(i))#set_pos i
          done
        );
      node_table <- (Array.of_list (List.rev !res));

    method update_size = size <- (Array.length node_table) - 1

    method update_parent_links =
      self#scan_all
        (fun nd -> Array.iter (fun cnd -> cnd#set_parent nd) nd#children)

    method update_pos =
      self#scan_all
        (fun nd ->
          let children = nd#children in
          for i = 0 to nd#nchildren - 1 do
            (children.(i))#set_pos i
          done
        )


(* misc *)


    method is_leaf i = (self#get i)#is_leaf

    method flat_rate =
      let nleaves =
        List.fold_left
          (fun s nd -> s + (if nd#is_leaf then 1 else 0))
          0 (Array.to_list self#root#children)
      in
      (float nleaves) /. (float root#nchildren)

    method is_member node =
      try 
        self#scan_all (fun nd -> if nd == node then raise Found);
        false
      with 
        Found -> true

    method print = (* self#fast_scan_all (fun nd -> nd#print) *)
      self#scan_all (fun nd -> nd#print)

    method to_rep_fast = (* must be used after tree init *)
      let buf = Buffer.create 0 in
      self#fast_scan_all 
        (fun nd -> Buffer.add_string buf ((nd#to_rep)^"\n"));
      Buffer.contents buf

    method to_string_fast = (* must be used after tree init *)
      let buf = Buffer.create 0 in
      self#fast_scan_all 
        (fun nd -> Buffer.add_string buf ((nd#to_string)^"\n"));
      Buffer.contents buf

    method to_rep =
      try
        let buf = Buffer.create 0 in
        self#scan_all 
          (fun nd -> Buffer.add_string buf ((nd#to_rep)^"\n"));
        Buffer.contents buf
      with 
        Empty -> "<empty>"

    method to_string =
      let buf = Buffer.create 0 in
      try
        self#scan_all 
          (fun nd -> Buffer.add_string buf ((nd#to_string)^"\n"));
        Buffer.contents buf
      with 
        Empty -> "<empty>"


    method to_dot ?(mklab=_dot_label_of_node) marked =
      let buf = Buffer.create 0 in
      self#scan_all
        (fun nd ->
          Buffer.add_string buf (nd#to_dot ~mklab ());
          if nd#nchildren > 0 then
            let cl = Array.to_list (nd#children) in
            Buffer.add_string buf
              (sprintf "%d -> {%s};\n" nd#index
                 (String.concat " " (List.map (fun n -> sprintf "%d" n#index) cl))
              )
        );
      List.iter 
        (fun i -> 
          Buffer.add_string buf (sprintf "%d [ color=red ]\n" i)
        ) marked;
      buf

    method save_dot prefix marked fname =
      let mklab nd =
        prefix^(_dot_label_of_node nd)
      in
      let buf0 = 
        try
          self#to_dot ~mklab marked
        with
          Empty -> Buffer.create 0
      in
      let ch = open_out fname in
      let buf = Buffer.create 0 in
      Buffer.add_string buf "digraph otree {\n";
      Buffer.add_string buf (sprintf "label=\"%s\";\nordering=out;\n" fname);
      Buffer.add_buffer buf buf0;
      Buffer.add_string buf "}";
      Buffer.output_buffer ch buf;
      close_out ch

(* initializer *)
    method init = 
      try
        self#update_node_table;
        self#preorder_reindex;
        self#update_leftmost_table;
        self#update_size
      with 
        Empty ->
          node_table <- [||];
          leftmost_table <- [||];
          size <- 0

    initializer 
      self#init

  end (* of class Otree.otree *)
]

exception Root_containing_cluster

type 'node cluster_mutation =
  | CMinsert of bool * int * float * 'node * ('node * Path.Elem.t) list
  | CMprune of int * 'node list

type 'node acc_result = { node    : 'node;
                          nelems  : int;
                          elem    : Path.Elem.t;
                          partial : bool;
                        }

let cluster_mutation_to_string = function
  | CMinsert(partial, pos, ofs, subroot, fnode_felem_list) ->
      sprintf "INSERT: partial=%B pos=%d ofs=%f subroot=%a frontier=[%s]"
        partial pos ofs UID.ps subroot#uid
        (String.concat ";"
           (List.map
              (fun (n, e) ->
                sprintf "<%a,%s>" UID.ps n#uid (Path.Elem.to_string e)
              ) fnode_felem_list))

  | CMprune(pos, excluded_nds) ->
      sprintf "PRUNE: pos=%d excluded=[%s]"
        pos (String.concat ";"
               (List.map (fun n -> UID.to_string n#uid) excluded_nds))

(* allows collapsing/expanding and contracting nodes *)
[%%capture_path
class [ 'node ] otree2 ?(hash=Xhash.MD5) (root : 'node) (is_whole : bool) =
  object (self : 'self)
    constraint 'node = #data2 #node2

    inherit [ 'node ] otree root as super

    method hash = hash
    method is_whole = is_whole

    val mutable is_empty = false

    method! root = 
      if is_empty then 
        raise Empty
      else 
        super#root

    val mutable _initial_size = 0
    val mutable initial_size = 0

    val uid_table = Hashtbl.create 0

    val mutable gindex_table = [||]
    val mutable gindex_offset = -1

    val mutable initial_leftmost_table = [||]

    method _gindex_table = gindex_table
    method _initial_leftmost_table = initial_leftmost_table

    method _set_gindex_table tbl = gindex_table <- tbl
    method _set_initial_leftmost_table tbl = initial_leftmost_table <- tbl


    method _initial_size = _initial_size
    method initial_size = initial_size

    method search_node_by_uid uid = Hashtbl.find uid_table uid

    method search_node_by_gindex gi = 
      try
        gindex_table.(GI.offset gi gindex_offset)
      with 
        Invalid_argument _ ->
          [%warn_log "%a: not found" GI.ps gi];
          raise Not_found

    method unregister_uid uid = 
      Hashtbl.remove uid_table uid

    method register_uid uid nd =
      Hashtbl.add uid_table uid nd

    method mem_uid uid = 
      try 
        ignore (self#search_node_by_uid uid);
        true
      with 
        Not_found -> false

    method mem_gindex gi = 
      try 
        ignore (self#search_node_by_gindex gi);
        true
      with 
        Not_found -> false

    method size_of_subtree_uid uid =
      let sz = ref 0 in
      let rt = self#search_node_by_uid uid in
      self#scan_subtree rt (fun _ -> incr sz);
      !sz

    method digest =
      if not is_whole then
        self#root#hide_parent;
      let d = Xhash.digest_of_string hash self#to_rep in
      if not is_whole then
        self#root#unhide_parent;
      d
      
    method is_flat =
      not (self#root#is_collapsed) &&
      Array.for_all (fun nd -> nd#is_leaf) self#root#children

    method equals (tree : 'self) = (* assumes no collapse *)
      let rec scan nds1 nds2 =
        match nds1, nds2 with
        | [], [] -> true
        | nd1::rest1, nd2::rest2 ->

            [%debug_log "%a - %a" UID.ps nd1#uid UID.ps nd2#uid];

            (if nd1#data#eq nd2#data then
              let cl1 = Array.to_list nd1#children in
              let cl2 = Array.to_list nd2#children in
              let sub = scan cl1 cl2 in
              sub
            else begin
              [%warn_log "%s != %s" (nd1#to_string) (nd2#to_string)];
              false
            end)
              &&
            (scan rest1 rest2)
        | nd::_, [] ->
            let _ = nd in
            [%warn_log "number of children mismatch: (>) %s [%s,...]"
              (nd#parent#to_string) (nd#to_string)];
            false

        | [], nd::_ ->
            let _ = nd in
            [%warn_log "number of children mismatch: (<) %s [%s,...]"
              (nd#parent#to_string) (nd#to_string)];
            false
      in
      scan [self#root] [tree#root]


    method collapse_root =
      self#root#collapse self#initial_size self#digest

    method set_digest_of_root =
      self#root#set_digest self#digest


    method collapse_node nd =
      (* nd#hide_parent; *)
      let weight, digest =
        match nd#data#_digest with
        | Some d -> nd#data#weight, d
        | None ->
            if nd#children = [||] then
              1, Xhash.digest_of_string hash nd#data#to_rep
            else
              let subtree = new otree2 nd false in
              let w = ref 0 in
              subtree#scan_all (fun n -> w := !w + n#data#weight);
              !w, subtree#digest
      in
      nd#collapse weight digest
      (* nd#unhide_parent *)


    method collapse_nodes filt =
(*      self#preorder_scan_all *)
      self#scan_all
        (fun nd ->
          if filt nd then
            self#collapse_node nd
        );
      super#init


    method set_digests filt =
      self#scan_all
        (fun nd ->
          if filt nd && nd#initial_nchildren > 0 then begin
            let subtree = new otree2 nd false in
            (* nd#hide_parent; *)
            nd#set_digest subtree#digest;
            (* nd#unhide_parent *)
          end
        )


    method collapse_nodei idx =
      let nd = self#get idx in
      self#collapse_node nd

    method expand_nodei idx =
      let nd = self#get idx in
      nd#expand

    method expand_root =
      let nd = self#root in
      nd#expand

(*
    method collapse idxs = 
      List.iter (fun idx -> self#collapse_nodei idx) idxs
*)

    method expand idxs =
      List.iter (fun idx -> self#expand_nodei idx) idxs

    method expand_uids uids =
      List.iter (fun uid -> (self#search_node_by_uid uid)#expand) uids

    method expand_nodes (nds : 'node list) =
      List.iter (fun nd -> nd#expand) nds

    method prune_initial_nodes (nds : 'node list) =
      let tbl = Hashtbl.create 0 in

      let add p pos uid =
(*
        [%debug_log "parent=%a pos=%d(uid=%a)" UID.ps p#uid pos UID.ps uid];
*)
        let _ = uid in
        try
          if pos < 0 then begin
            [%warn_log "already pruned: uid=%a" UID.ps uid];
          end
          else
            let ps = Hashtbl.find tbl p in
            if List.mem pos ps then begin
              [%warn_log "duplicated node: pos=%d(uid=%a)" pos UID.ps uid];
            end
            else
              Hashtbl.replace tbl p (pos::ps)
        with
          Not_found -> Hashtbl.add tbl p [pos]
      in
      List.iter
        (fun nd ->
          if nd != self#root || not is_whole then
            add nd#initial_parent nd#initial_pos nd#uid;
          if nd = self#root then is_empty <- true
        ) nds;
      Hashtbl.iter (fun p posl -> p#prune_initial_children posl) tbl
    (* end of method prune_initial_nodes *)


    method prune_nodes (nds : 'node list) =
      let tbl = Hashtbl.create 0 in
      let add p pos uid =
(*
        [%debug_log "parent=%a pos=%d(uid=%a)" UID.ps p#uid pos UID.ps uid];
*)
        let _ = uid in
        try
          if pos < 0 then begin
            [%warn_log "already pruned: uid=%a" UID.ps uid];
          end
          else
            let ps = Hashtbl.find tbl p in
            if List.mem pos ps then begin
              [%warn_log "duplicated node: pos=%d(uid=%a)" pos UID.ps uid];
            end
            else
              Hashtbl.replace tbl p (pos::ps)

        with
          Not_found -> Hashtbl.add tbl p [pos]
      in
      List.iter
        (fun nd ->
          if nd == self#root && is_whole then
            ()
          else
            if nd#in_path then begin
              [%info_log "node(index=%d,uid=%a) is in path" nd#index UID.ps nd#uid];

              List.iter (fun nd -> add nd#parent nd#pos nd#uid) nd#get_substances
            end
            else
              add nd#parent nd#pos nd#uid;
          if nd = self#root then is_empty <- true
        ) nds;
      Hashtbl.iter (fun p posl -> p#prune_children posl) tbl
(*
      List.iter (fun nd -> self#unregister_uid nd#uid) nds
      super#init;
*)
    (* end of method prune_nodes *)


    method prune idxs =
      self#prune_nodes (List.map self#get idxs)

    method prune_uids uids =
      self#prune_nodes (List.map self#search_node_by_uid uids)


(******** begin: for virtual mutation ********)

    method mutate (tbl : (UID.t, 'node cluster_mutation list) Hashtbl.t) =
      let extra = Xset.create 0 in
      Hashtbl.iter
        (fun uid mutations ->
          try
            let nd = self#search_node_by_uid uid in
            [%debug_log "%a (%d)" UID.ps uid (List.length mutations)];

            Xset.add extra nd;
            Xset.add_set extra (self#v_mutate uid mutations)
            
          with
            Not_found -> ()
        ) tbl;
      extra
      (*self#setup_uid_table*)

    method private v_mutate
        (uid : UID.t)
        (mutations : 'node cluster_mutation list)
        =
      let nd =
        try
          self#search_node_by_uid uid
        with
          Not_found ->
            internal_error
              "Otree.otree2#v_mutate: node not found: %a"
              UID.p uid
      in
      nd#begin_mutation();

      let nodes = Xset.create 0 in

      Xset.add nodes nd;

      List.iter
        (function
          | CMinsert(partial, pos, ofs, subroot, fnode_felem_list) ->
              Xset.add_set nodes
                (self#v_insert_cluster ~partial nd
                   (pos, ofs, subroot, fnode_felem_list))

          | CMprune(pos, excluded_nds) ->
              Xset.add_set nodes (self#v_prune_cluster nd pos excluded_nds)

        ) mutations;

      nodes
      (*nd#end_mutation()*)

    method private v_insert_cluster ?(partial=false) nd
        ((pos, ofs, subroot, fnode_felem_list)
           : int * float * 'node * ('node * Path.Elem.t) list)
        =
      [%debug_log "%s\npartial=%B pos=%d ofs=%s subroot=%a fnode_felem_list:\n%s"
        nd#initial_to_string partial pos (Path.Elem.ofs_to_str ofs) UID.ps subroot#uid
        (String.concat "\n"
           (List.map (fun (n, e) ->
             sprintf "%a(%s)" UID.ps n#uid (Path.Elem.to_string e)) fnode_felem_list))];

      (*printf "!!! v_insert_cluster: %s\npartial=%B pos=%d ofs=%s subroot=%a fnode_felem_list:\n%s\n"
        nd#initial_to_string partial pos (Path.Elem.ofs_to_str ofs) UID.p subroot#uid
        (String.concat "\n"
           (List.mapi (fun i (n, e) ->
             sprintf "%a (%s) pos=%d" UID.ps n#uid (Path.Elem.to_string e) (pos+i)) fnode_felem_list));*)

      let children = nd#initial_children in

      let extra = Xset.create 0 in

      begin
        match fnode_felem_list with
        | [] -> begin
            if not partial then
              nd#v_insert_child ~offset:ofs pos subroot
        end
        | _ -> begin
            let p_fnode_felem_list =
              List.mapi (fun i (fn, fe) -> i + pos, fn, fe) fnode_felem_list
            in

            List.iter (* filtering [pos; pos + 1; ...; pos + n - 1] *)
              (fun (p, _, (*fe*)_) ->
                if (*fe.Path.Elem.pos >= 0 && *)not partial then
                  nd#v_delete_child p
              ) p_fnode_felem_list;

            List.iter
              (fun (p, (fnode : 'node), felem) ->

                if not (Xset.mem extra fnode) then begin
                  fnode#begin_mutation();
                  Xset.add extra fnode
                end;

                let pos0 = felem.Path.Elem.pos in
                let ofs0 = felem.Path.Elem.ofs in
                if (fst (modf ofs0)) = 0. && pos0 >= 0 then
                  fnode#v_insert_child ~later:partial ~offset:ofs0 pos0 children.(p);

              ) p_fnode_felem_list;

            if not partial then
              nd#v_insert_child ~offset:0. pos subroot
        end
      end;
      extra
    (* end of method v_insert_cluster *)

    (* excluded_uids must preserve the left-to-right relation *)
    method private v_prune_cluster nd pos excluded_nds =

      [%debug_log "%s\npos=%d excluded=[%s]"
        nd#initial_to_string pos
        (String.concat ";" (List.map (fun n -> UID.to_string n#uid) excluded_nds))];

      (*printf "!!! v_prune_cluster: %s\npos=%d excluded=[%s]\n"
        nd#initial_to_string pos
        (String.concat ";" (List.map (fun n -> UID.to_string n#uid) excluded_nds));*)

      nd#v_delete_child pos;

      let fnode_tbl = Hashtbl.create 0 in (* node -> pos list *)
      List.iter
        (fun n ->
          let p = n#initial_parent in
          try
            let poss = Hashtbl.find fnode_tbl p in
            Hashtbl.replace fnode_tbl p (n#initial_pos::poss)
          with
            Not_found -> Hashtbl.add fnode_tbl p [n#initial_pos]
        ) excluded_nds;

      let extra = Xset.create 0 in

      Hashtbl.iter
        (fun fnode poss ->
          fnode#begin_mutation();
          fnode#v_delete_children poss;
          Xset.add extra fnode
        ) fnode_tbl;

      if excluded_nds <> [] then
        nd#v_insert_children ~offset:0. pos excluded_nds;

      extra
    (* end of method v_prune_cluster *)

(******** end: for virtual mutation ********)

    method insert_cluster
        (uid : UID.t) (* parent *)
        (pos : int)
        ((subroot : 'node), (* cluster to be inserted *)
         (fnode_fpos_list : ('node * int) list))
        =
      let nd =
        try
          self#search_node_by_uid uid
        with
          Not_found ->
            internal_error "Otree.otree2#insert_cluster: node not found: %a" UID.p uid
      in
      let children = nd#children in
      begin
        match fnode_fpos_list with
        | [] -> nd#add_child pos subroot
        | [fnode, fpos] ->
            fnode#add_child fpos children.(pos);
            nd#children.(pos) <- subroot;
            subroot#set_parent nd
        | _ ->
            let i = ref pos in
            let to_be_pruned =
              List.map (fun _ -> let p = !i in incr i; p) fnode_fpos_list
            in
            nd#prune_children to_be_pruned; (* [pos; pos + 1; ...; pos + n - 1] *)
            List.iter2
              (fun p (fnode, fpos) ->
                fnode#add_child fpos children.(p);
                children.(p)#set_parent fnode
              ) to_be_pruned fnode_fpos_list;
            nd#add_child pos subroot
      end;
      self#setup_uid_table
    (* end of method insert_cluster *)


    (* excluded_nodes must preserve the left-to-right relation *)
    method prune_cluster (pruned_node : 'node) (excluded_nodes : 'node list) : unit =
      try
        self#prune_nodes excluded_nodes;

        let excluded_nodes_a = Array.of_list excluded_nodes in

        [%debug_log "excluded_nodes_a: [%s]"
          (Xlist.to_string
             (fun nd -> UID.to_string nd#uid) "," excluded_nodes)];

        try
          let p = pruned_node#parent in
          p#replace_children [pruned_node#pos, excluded_nodes_a];
          pruned_node#set_pos (-1);
          self#unregister_uid pruned_node#uid
        with
          Parent_not_found _ ->
            internal_error
              "Otree.otree2#prune_cluster: parent not found: uid=%a" UID.p pruned_node#uid
      with
        Not_found ->
          [%warn_log "not found: %a[%s]" UID.ps pruned_node#uid
            (Xlist.to_string (fun n -> UID.to_string n#uid) ";" excluded_nodes)]
    (* end of method prune_cluster *)

    (* excluded_uids must preserve the left-to-right relation *)
    method prune_cluster_by_uid uid excluded_uids =
      try
        let pruned_node = self#search_node_by_uid uid in

        let excluded_nodes =
          List.map
            (fun u ->
              self#search_node_by_uid u
            ) (List.filter self#mem_uid excluded_uids)
        in
        self#prune_nodes excluded_nodes;

        let excluded_nodes_a = Array.of_list excluded_nodes in

        [%debug_log "excluded_nodes_a: [%s]"
          (Xlist.to_string
             (fun nd -> UID.to_string nd#uid) "," excluded_nodes)];

        try
          let p = pruned_node#parent in
          p#replace_children [pruned_node#pos, excluded_nodes_a];
          pruned_node#set_pos (-1);
          self#unregister_uid uid
        with
          Parent_not_found _ ->
            internal_error
              "Otree.otree2#prune_cluster: parent not found: uid=%a" UID.p uid
      with 
        Not_found ->
          [%warn_log "not found: %a[%s]" UID.ps uid
            (Xlist.to_string UID.to_string ";" excluded_uids)]
    (* end of method prune_cluster_by_uid *)

    (* excluded_gis must preserve the left-to-right relation *)
    method prune_cluster_by_gindex gi excluded_gis =
      try
        let pruned_node = self#search_node_by_gindex gi in

        let excluded_nodes =
          List.map
            (fun g ->
              self#search_node_by_gindex g
            ) (List.filter self#mem_gindex excluded_gis)
        in
        self#prune_nodes excluded_nodes;

        let excluded_nodes_a = Array.of_list excluded_nodes in

        [%debug_log "excluded_nodes_a: [%s]" 
          (Xlist.to_string 
             (fun nd -> GI.to_string nd#gindex) "," excluded_nodes)];

        try
          let p = pruned_node#parent in
          p#replace_children [pruned_node#pos, excluded_nodes_a];
          pruned_node#set_pos (-1);
          self#unregister_uid pruned_node#uid
        with
          Parent_not_found _ ->
            internal_error
              "Otree.otree2#prune_cluster_gindex: parent not found: gi=%a" GI.p gi
      with
        Not_found ->
          [%warn_log "not found: %a[%s]" GI.ps gi
            (Xlist.to_string GI.to_string ";" excluded_gis)]
    (* end of method prune_cluster_by_gindex *)

    method delete_node_by_gindex gi =
      try
        let nd = self#search_node_by_gindex gi in
        self#prune_cluster_by_gindex
          gi (List.map (fun n -> n#gindex) (Array.to_list nd#children))
      with
        Not_found ->
          [%warn_log "not found: %a" GI.ps gi];
          raise Not_found

    method frontier_of_cluster cluster =
      let derive i =

        [%debug_log "%d:" i];

        let node = self#get i in
        let ci = node#children_indexes in

        [%debug_log "children=[%s]:" (Xlist.to_string string_of_int ";" ci)];

        let result = List.filter (fun i -> not (List.mem i cluster)) ci in

        [%debug_log "result=[%s]:" (Xlist.to_string string_of_int ";" result)];
(*
        Printf.printf "!!! derive %a: [%s]\n"
          UID.p node#uid
          (Xlist.to_string (fun i -> UID.to_string ((self#get i)#uid)) ";" result);
*)
        result
      in
      let result = 
        Xlist.uniq (List.fold_left (fun l i -> l @ (derive i)) [] cluster)
      in

      [%info_log "[%s]: [%s]" 
        (Xlist.to_string UID.to_string ";" 
           (List.map 
              (fun i -> try (self#get i)#uid with 
                Out_of_bounds -> 0)
              cluster))
        (Xlist.to_string UID.to_string ";"
           (List.map
              (fun i -> try (self#get i)#uid with
                Out_of_bounds -> 0)
              result))];

      List.filter
        (fun i ->
          try
            let _ = self#get i in true
          with
            Out_of_bounds -> false
        ) result


    method contraction_candidates cluster outside_idxs = 

      let topnd_list = ref [] in

      if outside_idxs = [] then begin
        let min, max = minn cluster, maxn cluster in
        match self#get_roots_of_forest min max with
        | [topi] ->
            let topnd = self#get topi in
            if topnd#has_parent then [], [topnd], false
            else
              if topnd#has_initial_parent then (* root of subtree *)
                [], [topnd], true
              else (* root of the whole tree *)
                [], (self#nth_gen topi (contract_margin + 1)), false
        | _ ->
            internal_error
              "Otree.otree2#contraction_candidates: multiple or no roots"
      end
      else
        try
          let cand_of idx =
            let ancestors = self#ancestors idx in

            [%debug_log "%d" idx];
            [%debug_log "ancestors: [%s]"
              (Xlist.to_string
                 (fun i -> sprintf "%d:%s"
                     i (self#get i)#data#to_string) ";" ancestors)];

            let cand0 = List.filter (fun i -> List.mem i cluster) ancestors in
            let cand =
              let nd = self#get (List.hd cand0) in
              if nd#has_parent then cand0
              else
                if nd#has_hidden_parent then (* root of a subtree *)
                  raise Root_containing_cluster
                else (* root of the whole tree *)
                  if (List.length cand0) < contract_margin then
                    []
                  else
                    let c = ref cand0 in
                    for _ = 1  to contract_margin do c := List.tl !c done;
                    !c
            in

            [%info_log "path cand(%a)=[%s]" UID.ps (self#get idx)#uid
              (Xlist.to_string UID.to_string ";"
                 (List.map (fun i -> (self#get i)#uid) cand))];

            idx, cand
          in

          let height = ref min_int in
          let path_cands = ref [] in
          List.iter
            (fun idx ->
              let i, c = cand_of idx in
              try
                let _ = path_cands := (i, c)::!path_cands in
                let len = List.length c in
                if len > !height then height := len
              with
                Failure "hd" -> ()
            ) outside_idxs;

          [%info_log "height=%d" !height];

          let _ =
          topnd_list :=
            let min, max = minn cluster, maxn cluster in
            match self#get_roots_of_forest min max with
            | [topi] ->
                let topnd = self#get topi in
                if topnd#has_parent then [topnd]
                else
                  if topnd#has_initial_parent then (* root of subtree *)
                    [topnd]
                  else (* root of the whole tree *)
                    (self#nth_gen topi (contract_margin + 1))
            | _ ->
                internal_error
                  "Otree.otree2#contraction_candidates: multiple or no roots"
          in
          topnd_list :=
            List.filter (fun nd -> List.mem nd#index cluster) !topnd_list;

          (if !height >= minimum_height then !path_cands else []),
          !topnd_list,
          false

        with
        | Root_containing_cluster -> [], !topnd_list, true
        | Not_found ->
            internal_error "Otree.otree2#contraction_candidates: Not_found"
        | Failure "tl" ->
            internal_error "Otree.otree2#contraction_candidates: Failure tl"


    method contract path_candidates (topnd_list : 'node list) =

      let path_candidates =
        List.fast_sort
          (fun (idx0, _) (idx1, _) ->
            Stdlib.compare idx1 idx0
          ) path_candidates
      in

      let fromnd_list = ref [] in

      let contract_one (idx, cand) =
        if (List.length cand) >= 1 then begin
          let fromnd = self#get idx in
          fromnd#insert_path (List.map (fun i -> self#get i) cand);
          fromnd_list := fromnd::!fromnd_list
        end
      in
      List.iter contract_one path_candidates;

(*      fromnd_list := List.rev !fromnd_list; *)

      [%info_log "top nodes: [%s]"
        (Xlist.to_string (fun nd -> UID.to_string nd#uid) "," topnd_list)];

      [%info_log "from nodes: [%s]"
        (Xlist.to_string (fun nd -> UID.to_string nd#uid) "," !fromnd_list)];

      List.iter
        (fun tnd ->
          let new_children = (* descendants of topnd *)
            let cond nd =
              let i = nd#index in
              let a = self#ancestors i in

              [%info_log "ancestors[%a(%d)]: %s" UID.ps nd#uid i
                (Xlist.to_string string_of_int "," a)];

              List.mem tnd#index a
            in
            Array.of_list(List.filter cond !fromnd_list)
          in

          [%info_log "new_children: [%s]\n"
            (Xarray.to_string
               (fun nd -> UID.to_string nd#uid) "," new_children)];

          tnd#parent#replace_children [tnd#pos, new_children]
        ) topnd_list
    (* end of method contract *)


    method initial_to_string =
      let buf = Buffer.create 0 in
      try
        self#scan_whole_initial
          (fun nd -> Buffer.add_string buf ((nd#initial_to_string)^"\n"));
        Buffer.contents buf
      with 
        Empty -> "<empty>"


    method dump_xml_ch ?(initial=false) ?(pre_tags="") ?(post_tags="") (ch : Xchannel.out_channel) 
        =
      let _output_string s = ignore (ch#output_ s 0 (String.length s)) in
      let _printf fmt = ksprintf _output_string fmt in

      let attrs_to_string attrs =
        String.concat "" (List.map (fun (a, v) -> sprintf " %s='%s'" a v) attrs)
      in
      let get_gid nd =
        if nd#data#gid > 0 then
          nd#data#gid
        else
          nd#gindex
      in
      let get_elem_data nd =
        let name, _attrs, content = nd#data#to_elem_data in
        let attrs =
          let gid = get_gid nd in
          (cca_prefix^":apath",Path.to_string nd#apath)::
          (cca_prefix^":"^gid_attr_name,GI.to_string gid)::
          _attrs 
        in
        name, attrs, content
      in

      let rec put nd =
        let children =
          if initial then
            nd#initial_children
          else
            nd#children
        in
        let name, attrs, content = get_elem_data nd in

        if children = [||] then
          _printf "<%s%s/>" name (attrs_to_string attrs)
        else begin
          _printf "<%s%s>" name (attrs_to_string attrs);
          _printf "%s" content;
          Array.iter put children;
          _printf "</%s>" name
        end
      in

      _output_string XML.header;

      _output_string pre_tags;

      let name, _attrs, content = get_elem_data self#root in
      let attrs = 
        List.filter
          (fun (_, v) ->
            v <> ""
          ) (("xmlns:"^cca_prefix,cca_ns)::_attrs)
      in
      let children =
        if initial then
          self#root#initial_children
        else
          self#root#children
      in
      if children = [||] then
        _printf "<%s%s/>" name (attrs_to_string attrs)
      else begin
        _printf "<%s%s>" name (attrs_to_string attrs);
        _printf "%s" content;
        Array.iter put children;
        _printf "</%s>" name
      end;
      
      _output_string post_tags


    method save_in_xml ?(initial=false) ?(comp=Comp.none) ?(add_ext=true) ?(pre_tags="") ?(post_tags="") fname = 
      Xchannel.dump ~comp ~add_ext fname (self#dump_xml_ch ~initial ~pre_tags ~post_tags)

    method save_in_xml_gz ?(initial=false) ?(add_ext=true) ?(pre_tags="") ?(post_tags="") fname = 
      Xchannel.dump ~comp:Comp.gzip ~add_ext fname (self#dump_xml_ch ~initial ~pre_tags ~post_tags)


    method! to_dot ?(mklab=dot_label_of_node) marked =
      let buf = Buffer.create 0 in
      self#scan_all
        (fun nd ->
          Buffer.add_string buf (nd#to_dot_str ~mklab ());
          if nd#nchildren > 0 then
            let cl = Array.to_list (nd#children) in
            Buffer.add_string buf
              (sprintf "%a -> {%s};\n" UID.rs nd#uid
                 (String.concat " " (List.map (fun n -> sprintf "%a" UID.rs n#uid) cl))
              )
        );
      List.iter
        (fun i ->
          let nd = self#get i in
          Buffer.add_string buf (sprintf "%a [ color=red ]\n" UID.rs nd#uid)
        ) marked;
      buf

    method to_dot_initial ?(mklab=dot_label_of_node_ini) marked =
      let buf = Buffer.create 0 in
      self#scan_whole_initial
        (fun nd ->
          Buffer.add_string buf (nd#to_dot_str_ini ?mklab:(Some mklab) ());
          if nd#initial_nchildren > 0 then begin
            let cl = Array.to_list (nd#initial_children) in
            Buffer.add_string buf
              (sprintf "%a -> {%s};\n" UID.rs nd#uid
                 (String.concat " " (List.map (fun n -> sprintf "%a" UID.rs n#uid) cl))
              )
          end;
        );
      List.iter 
        (fun i ->
          let nd = self#get i in
          Buffer.add_string buf (sprintf "%a [color=red]\n" UID.rs nd#uid)
        ) marked;
      buf

    method iter_initial_ancestor_nodes node f = (* from the parent *)
      let rec proc_one nd =
        try
          let pnd = nd#initial_parent in
          f pnd;
          proc_one pnd
        with
          Parent_not_found _ -> ()
      in
      proc_one node

    method iter_initial_ancestor_nodeposs node f = (* from the parent *)
      let rec proc_one nd =
        try
          let pnd = nd#initial_parent in
          let pos = nd#initial_pos in
          f pnd pos;
          proc_one pnd
        with
          Parent_not_found _ -> ()
      in
      proc_one node

    (* preorder scan for a cluster *)
    method scan_cluster (nd, nds) (f : 'node -> unit) = 
      let rec scan nd =

        [%debug_log "scanning: %a" UID.ps nd#uid];

        f nd;
        let ca = nd#children in

        [%debug_log "children=[%s]"
          (Xarray.to_string (fun nd -> UID.to_string nd#uid) ";" ca)];

        Array.iter (fun c -> if List.memq c nds then () else scan c) ca
      in
      scan nd

    (* preorder scan for a cluster *)
    method scan_cluster_u (uid, uids) (f : 'node -> unit) = 
      let rec scan nd =

        [%debug_log "scanning: %a" UID.ps nd#uid];

        f nd;
        let ca = nd#children in

        [%debug_log "children=[%s]"
          (Xarray.to_string (fun nd -> UID.to_string nd#uid) ";" ca)];

        Array.iter (fun c -> if List.mem c#uid uids then () else scan c) ca
      in
      scan (self#search_node_by_uid uid)


    (* preorder scan for a cluster *)
    method scan_initial_cluster (nd, nds) (f : 'node -> unit) =
      let rec scan nd =
        f nd;
        let cl = nd#initial_children in
        Array.iter
          (fun c ->
            if List.memq c nds then () else scan c
          ) cl
      in
      scan nd

    method fast_scan_initial_cluster (nd, nds) (f : 'node -> unit) =
      let excluded = ref [] in
      List.iter
        (fun n ->
          excluded := ((self#initial_leftmost n)#gindex, n#gindex) :: !excluded
        ) nds;
      let is_excluded n =
        let gi = n#gindex in
        try
          List.iter
            (fun (st, ed) ->
              if st <= gi && gi <= ed then
                raise Found
            ) !excluded;
          false
        with
          Found -> true
      in
      self#fast_scan_whole_initial_subtree nd
        (fun n ->
          if not (is_excluded n) then
            f n
        )

    method fast_size_of_initial_cluster (nd, nds) =
      let sz = ref 0 in
      self#fast_scan_initial_cluster (nd, nds) (fun _ -> incr sz);
      !sz

    method size_of_initial_cluster (nd, nds) =
      let sz = ref 0 in
      self#scan_initial_cluster (nd, nds) (fun _ -> incr sz);
      !sz

    method size_of_initial_cluster_u (uid, uids) =
      let sz = ref 0 in
      self#scan_initial_cluster_u (uid, uids) (fun _ -> incr sz);
      !sz

    method scan_initial_cluster_u (uid, uids) (f : 'node -> unit) = 
      let rec scan nd =
        f nd;
        let cl = nd#initial_children in
        Array.iter
          (fun c ->
            let u = c#uid in
            if List.mem u uids then () else scan c
          ) cl
      in
      scan (self#search_node_by_uid uid)

    method scan_initial_cluster_g (gindex, gindexes) (f : 'node -> unit) = 
      let rec scan nd =
        f nd;
        let cl = nd#initial_children in
        Array.iter
          (fun c ->
            let gi = c#gindex in
            if List.mem gi gindexes then () else scan c
          ) cl
      in
      scan (self#search_node_by_gindex gindex)

    method size_of_cluster (nd, nds) =
      let count = ref 0 in
      self#scan_cluster (nd, nds) (fun _ -> incr count);
      !count

    method size_of_cluster_u (uid, uids) =
      let count = ref 0 in
      self#scan_cluster_u (uid, uids) (fun _ -> incr count);
      !count

    method iter_initial_ancestors uid f = (* from the parent *)
      let nd = self#search_node_by_uid uid in
      self#iter_initial_ancestor_nodes nd (fun nd -> f nd#uid)

    method _initial_leftmost (nd : 'node) =
      let lmn = ref nd in
      while !lmn#initial_children <> [||] do
        lmn := !lmn#initial_children.(0)
      done;
      !lmn

    method setup_initial_leftmost_table =
      let a = Array.make self#initial_size self#root in
      self#fast_scan_whole_initial
        (fun nd ->
          let gi = nd#gindex in
          if GI.is_valid gi then
            let i = GI.offset gi gindex_offset in
            try
              a.(i) <- self#_initial_leftmost nd
            with
              Invalid_argument mes ->
                internal_error
                  "Otree.otree2#setup_initial_leftmost_table: %s: index=%d gindex=%a offset=%d initial size=%d"
                  mes i GI.p nd#gindex gindex_offset self#initial_size
        );
      initial_leftmost_table <- a

    method initial_leftmost (nd : 'node) =
      try
        initial_leftmost_table.(GI.offset nd#gindex gindex_offset)
      with 
        Invalid_argument _ -> nd
(*
          out_of_bounds
            "Otree.otree2#initial_leftmost(%a:offset=%d) (root=%s,initial_size=%d)"
            GI.p nd#gindex gindex_offset self#root#to_string self#initial_size
*)

    method initial_ancestor_nodes node = (* [ancestor0;...;parent] *)
      let res = ref [] in
      self#iter_initial_ancestor_nodes node (fun nd -> res:= nd::!res);
      !res

    method initial_ancestor_nodeposs (node : 'node) = (* [ancestor0,pos0;...;parent,pos] *)
      let res = ref [] in
      self#iter_initial_ancestor_nodeposs node (fun nd pos -> res:= (nd,pos)::!res);
      !res

    method initial_ancestors uid = (* [ancestor0;...;parent] *)
      let res = ref [] in
      self#iter_initial_ancestors uid (fun u -> res:= u::!res);
      !res

    method is_initial_ancestor (an : 'node) (n : 'node) =
      let ngi = n#gindex in
      (self#initial_leftmost an)#gindex <= ngi && ngi < an#gindex


    method fast_scan_whole_initial (f : 'node -> unit) =
      Array.iter f gindex_table

    method fast_rev_scan_whole_initial (f : 'node -> unit) =
      for i = Array.length gindex_table - 1 downto 0 do
        f gindex_table.(i)
      done

    method scan_whole_initial (f : 'node -> unit) =
      self#scan_whole_initial_subtree self#root f


(*
    val whole_initial_subtree_scan_hist_tbl = Hashtbl.create 0
    val whole_initial_subtree_size_hist_tbl = Hashtbl.create 0

    method scan_whole_initial_subtree nd (f : 'node -> unit) =
      let count = ref 0 in
      let rec do_scan nd = incr count; Array.iter do_scan nd#initial_children; f nd in
      do_scan nd;
      begin
        try
          let c = Hashtbl.find whole_initial_subtree_scan_hist_tbl !count in
          Hashtbl.replace whole_initial_subtree_scan_hist_tbl !count (c+1)
        with
          Not_found -> Hashtbl.add whole_initial_subtree_scan_hist_tbl !count 1
      end

    method fast_scan_whole_initial_subtree nd (f : 'node -> unit) =
      let lgi = (self#initial_leftmost nd)#gindex in
      for i = lgi to GI.to_int nd#gindex do
        f (self#search_node_by_gindex (GI.of_int i))
      done;
      let count = (GI.to_int nd#gindex) - lgi + 1 in
      begin
        try
          let c = Hashtbl.find whole_initial_subtree_scan_hist_tbl count in
          Hashtbl.replace whole_initial_subtree_scan_hist_tbl count (c+1)
        with
          Not_found -> Hashtbl.add whole_initial_subtree_scan_hist_tbl count 1
      end

    method whole_initial_subtree_size nd =
      let sz = ref 0 in
      self#scan_whole_initial_subtree nd (fun _ -> incr sz);
      begin
        try
          let c = Hashtbl.find whole_initial_subtree_size_hist_tbl !sz in
          Hashtbl.replace whole_initial_subtree_size_hist_tbl !sz (c+1)
        with
          Not_found -> Hashtbl.add whole_initial_subtree_size_hist_tbl !sz 1
      end;
      !sz

    method fast_whole_initial_subtree_size nd =
      let sz =
        (GI.to_int nd#gindex) - (GI.to_int (self#initial_leftmost nd)#gindex) + 1
      in
      begin
        try
          let c = Hashtbl.find whole_initial_subtree_size_hist_tbl sz in
          Hashtbl.replace whole_initial_subtree_size_hist_tbl sz (c+1)
        with
          Not_found -> Hashtbl.add whole_initial_subtree_size_hist_tbl sz 1
      end;
      sz

    method show_whole_initial_subtree_size_hist =
      Printf.printf "initial subtree size freq:\n";
      let l =
        Hashtbl.fold
          (fun sz freq l -> (sz, freq)::l) whole_initial_subtree_size_hist_tbl []
      in
      let l' = List.fast_sort (fun (sz1, _) (sz2, _) -> Pervasives.compare sz1 sz2) l in
      List.iter
        (fun (sz, freq) ->
          Printf.printf "%d: %d\n" sz freq
        ) l'

    method show_whole_initial_subtree_scan_hist =
      Printf.printf "initial subtree scan freq:\n";
      let l =
        Hashtbl.fold
          (fun sz freq l -> (sz, freq)::l) whole_initial_subtree_scan_hist_tbl []
      in
      let l' = List.fast_sort (fun (sz1, _) (sz2, _) -> Pervasives.compare sz1 sz2) l in
      List.iter
        (fun (sz, freq) ->
          Printf.printf "%d: %d\n" sz freq
        ) l'
*)

    method scan_whole_initial_subtree nd (f : 'node -> unit) =
      let rec do_scan nd = Array.iter do_scan nd#initial_children; f nd in
      do_scan nd

    method rev_scan_whole_initial_subtree nd (f : 'node -> unit) =
      let rec do_scan nd =
        f nd;
        for i = nd#initial_nchildren - 1 downto 0 do
          do_scan nd#initial_children.(i)
        done
      in
      do_scan nd

    method fast_scan_whole_initial_subtree nd (f : 'node -> unit) = (* slow when subtree is small *)
      let gi = nd#gindex in
      if GI.is_valid gi then
        let lgi = (self#initial_leftmost nd)#gindex in
        if GI.is_valid lgi then
          for i = lgi to GI.to_int nd#gindex do
            f (self#search_node_by_gindex (GI.of_int i))
          done
      else
        f nd

    method fast_rev_scan_whole_initial_subtree nd (f : 'node -> unit) = (* ditto *)
      let gi = nd#gindex in
      if GI.is_valid gi then
        let lgi = (self#initial_leftmost nd)#gindex in
        if GI.is_valid lgi then
          for i = GI.to_int nd#gindex downto lgi do
            f (self#search_node_by_gindex (GI.of_int i))
          done
      else
        f nd


    method whole_initial_subtree_size nd =
      let sz = ref 0 in
      self#scan_whole_initial_subtree nd (fun _ -> incr sz);
      !sz

    method fast_whole_initial_subtree_size nd = (* slow when subtree is small *)
      (GI.to_int nd#gindex) - (GI.to_int (self#initial_leftmost nd)#gindex) + 1


    method setup_initial_size =
      initial_size <- 0;
      self#scan_whole_initial
        (fun _ -> initial_size <- initial_size + 1)


    method preorder_scan_whole_initial_subtree nd (f : 'node -> unit) =
      let rec do_scan nd =
        let c = nd#initial_children in
        f nd;
        Array.iter do_scan c
      in
      do_scan nd

    method preorder_scan_whole_initial (f : 'node -> unit) =
      self#preorder_scan_whole_initial_subtree self#root f

    method setup_initial_parent =
      self#preorder_scan_whole_initial_subtree self#root
        (fun nd ->
          Array.iter
            (fun cnd -> cnd#set_initial_parent nd) nd#initial_children)

    method scan_whole_subtree nd f = (* also scans collapsed nodes *)
      let rec do_scan nd =
        if nd#is_collapsed then Array.iter do_scan nd#hidden_children
        else Array.iter do_scan nd#children;
        f nd
      in
      do_scan nd

    method setup_uid_table =
      Hashtbl.clear uid_table;
      self#scan_whole_subtree self#root
        (fun nd -> self#register_uid nd#uid nd)

    method setup_gindex_table =
      let a = Array.make self#initial_size self#root in
      let c = ref 0 in
      gindex_offset <- -1;
      self#scan_whole_initial
        (fun nd ->
          incr c;
          let gi = GI.of_int !c in
          [%debug_log "%a -> %a" UID.ps nd#uid GI.ps gi];
          nd#set_gindex gi;
          a.(GI.offset gi gindex_offset) <- nd;
        );
      gindex_table <- a



    method _register_gindexes =
      let a = Array.make self#size self#root in
      let c = ref 0 in
      self#scan_all
        (fun nd ->
          a.(!c) <- nd;
          incr c
        );
      gindex_table <- a;
      self#setup_initial_children;
      self#setup_initial_parent;
      self#setup_initial_size;
      let lmn = self#_initial_leftmost self#root in
(*
      Printf.printf "_register_gindexes: size:%d lmn:%a\n" self#size GI.p lmn#gindex;
      Printf.printf "%s\n" self#to_string;
*)
      gindex_offset <- -(GI.to_int lmn#gindex);
      self#setup_initial_leftmost_table


    method setup_initial_children =
      self#scan_whole_subtree self#root
        (fun nd ->
          if nd#is_collapsed then begin
            nd#set_initial_children (Array.copy nd#hidden_children)
          end
          else begin
            nd#set_initial_children (Array.copy nd#children)
          end;
          let ic = nd#initial_children in
          for i = 0 to (Array.length ic) - 1 do
            (ic.(i))#set_initial_pos i
          done;

          [%debug_log "(%a)%s [%s]"
            UID.ps nd#uid nd#data#to_string
            (Xarray.to_string UID.to_string ","
               (Array.map (fun nd -> nd#uid) ic))]

        )

    method recover_all = (* recovers all pruned nodes *)
      is_empty <- false;
      self#fast_scan_whole_initial
        (fun nd ->
          nd#clear_in_path;
          if nd#is_collapsed then begin
            nd#set_hidden_children (Array.copy nd#initial_children);
            [%debug_log "nd=%a" UID.ps nd#uid];
            nd#set_children [||]; (* redundant? *)
          end
          else begin
            nd#set_children (Array.copy nd#initial_children);
            nd#set_hidden_children [||]; (* redundant? *)
          end;

          [%debug_log "%a {%s}"
            UID.ps nd#uid
            (Xarray.to_string (fun n -> UID.to_string n#uid) ";" nd#children)];
          try
            nd#set_parent nd#initial_parent
          with
            Parent_not_found _ -> ()
        )
    (* end of method recover_all *)

    (* recover pruned nodes not in path (filtered) *)
    method recover_filtered (filt : 'node -> bool) = 
      is_empty <- false;
      self#fast_scan_whole_initial
        (fun nd ->
          if not nd#in_path then
            let initial =
              List.concat_map
                (fun n ->
                  if n#in_path then begin
                    let subs =
                      List.fast_sort
                        (fun nd1 nd2 -> compare nd1#gindex nd2#gindex)
                        n#get_substances
                    in
                    subs
                  end
                  else [n]
                ) (Array.to_list nd#initial_children)
            in
            let mkchildren orig_a =
              let orig = Array.to_list orig_a in
              let filt' nd = if List.mem nd orig then true else filt nd in
              let filtered = List.filter filt' initial in
              Array.of_list filtered
            in

            if nd#is_collapsed then begin
              let new_children = mkchildren nd#hidden_children in
              nd#set_hidden_children new_children;
              [%debug_log "nd=%a" UID.ps nd#uid];
              nd#set_children [||]; (* redundant? *)
            end
            else begin
              let new_children = mkchildren nd#children in
              nd#set_children new_children;
              [%debug_log "nd=%a" UID.ps nd#uid];
              nd#set_hidden_children [||]; (* redundant? *)
            end;

            [%debug_log "%a {%s}"
              UID.ps nd#uid
              (Xarray.to_string (fun n -> UID.to_string n#uid) ";" nd#children)];

            try
              if filt nd#initial_parent then
                nd#set_parent nd#initial_parent
            with
              Parent_not_found _ -> ()
        )
    (* end of method recover_filtered *)

    method expand_all =
      let expanded = Hashtbl.create 0 in
      self#fast_scan_whole_initial
        (fun nd ->
          if nd#is_collapsed then begin
            nd#expand;
            Hashtbl.add expanded nd 0
          end
        );
      super#init;
(*      self#setup_uid_table; *)
      let is_expanded nd = Hashtbl.mem expanded nd in
      is_expanded


    (* recovers all pruned nodes and expands all collapsed *)
    method recover_and_expand = 
      is_empty <- false;

      [%debug_log "root=%a" UID.ps self#root#uid];

      let expanded = Hashtbl.create 0 in
      self#fast_scan_whole_initial
        (fun nd ->
          nd#clear_in_path;
          if nd#is_collapsed then begin
            Hashtbl.add expanded nd 0;
            nd#_set_is_collapsed false;
            nd#data#reset_digest
          end;
          nd#set_children (Array.copy nd#initial_children);
          nd#set_hidden_children [||];

          [%debug_log "%a childlen=[%s]"
            UID.ps nd#uid
            (Xarray.to_string (fun n -> UID.to_string n#uid) ";" nd#children)];
          try
            nd#set_parent nd#initial_parent
          with
            Parent_not_found _ -> ()
        );
      super#init;
(*      self#setup_uid_table; *)
      let is_expanded nd = Hashtbl.mem expanded nd in
      is_expanded
    (* end of method recover_and_expand *)


    method iter_whole_initial_leaves f =
      self#fast_scan_whole_initial
        (fun nd -> if nd#initial_children = [||] then f nd)

    method get_whole_initial_leaves =
      let res = ref [] in
      self#fast_scan_whole_initial
        (fun nd -> if nd#initial_children = [||] then res := nd::!res);
      !res

    method! to_rep =
      let buf = Buffer.create 0 in
(*      self#scan_whole_initial *)
      self#scan_all
        (fun nd -> Buffer.add_string buf ((nd#to_rep)^"\n"));
      let res = Buffer.contents buf in
      res

    method initial_subtree_mem (root : 'node) (nd : 'node) =
      let ndgi = nd#gindex in
      ndgi <= root#gindex && (self#initial_leftmost root)#gindex <= ndgi

    method private _acc ?(ignore_ofs=false) ?(from=self#root) get_child path =
      [%debug_log "path=%s" (Path.to_string path)];
      (*Printf.printf "!!! path=%s\n" (Path.to_string path);*)
      try
        let elems = Path.get_elems path in
        let node, nelems, _ =

          List.fold_left
            (fun (nd, i, b) elm ->
              try
                if b then begin
                  [%debug_log "  %a(%a)" GI.ps nd#gindex UID.ps nd#uid];
                  (*Printf.printf "!!!  %s ->\n" nd#to_string;*)

                  if elm.Path.Elem.ofs <> 0. && not ignore_ofs then
                    invalid_arg "";

                  let next = get_child nd elm.Path.Elem.pos in

                  [%debug_log " -> %a(%a)" GI.ps next#gindex UID.ps next#uid];

                  (next, i + 1, b)
                end
                else
                  (nd, i, b)
              with
                Invalid_argument _ -> (nd, i, false)

            ) (from, 0, true) elems
        in
        [%debug_log "path=%s node=%s" (Path.to_string path) node#to_string];
        [%debug_log "    %a(%a)" GI.ps node#gindex UID.ps node#uid];

        (*Printf.printf "!!! path=%s node=%s\n" (Path.to_string path) node#to_string;*)

        node, nelems
      with 
        Invalid_argument _ -> raise (Invalid_argument "Otree.otree2#_acc")

    method initial_acc ?(from=self#root) path =
      let get_child nd nth = nd#initial_children.(nth) in
      let n, _ = self#_acc ~ignore_ofs:true ~from get_child path in
      n

    method acc ?(from=self#root) path =
      let get_child nd nth = nd#children.(nth) in
      let n, _ = self#_acc ~ignore_ofs:true ~from get_child path in
      n

    method private _acc_parent ?(ignore_ofs=false) ?(from=self#root) get_child path =
      let parent = Path.get_parent path in
      let nd, nelems = self#_acc ~ignore_ofs ~from get_child parent in
      if nelems >= Path.length parent then
        { node=nd;
          nelems=nelems;
          elem=Path.tail path;
          partial=false;
        }
      else
        { node=nd;
          nelems=nelems;
          elem=Path.nth parent nelems;
          partial=true;
        }

    method initial_acc_parent ?(ignore_ofs=false) ?(from=self#root) path =
      let get_child nd nth = nd#initial_children.(nth) in
      self#_acc_parent ~ignore_ofs ~from get_child path

    method acc_parent ?(ignore_ofs=false) ?(from=self#root) path =
      let get_child nd nth = nd#children.(nth) in
      self#_acc_parent ~ignore_ofs ~from get_child path


    method setup_apath =
      let rec scan nd =
        let c = nd#initial_children in
        Array.iter
          (fun n ->
            let ppath = nd#apath in
            let apath = Path.append_pos ppath n#initial_pos in
            n#set_apath apath
          ) c;
        Array.iter scan c
      in
      let rt = self#root in
      rt#set_apath Path.root;
      scan self#root


    initializer
      self#setup_uid_table;
      if is_whole then begin
        self#setup_initial_children;
        self#setup_initial_parent;
        self#setup_initial_size;
        _initial_size <- initial_size;
        self#setup_gindex_table;
        self#setup_initial_leftmost_table;
        self#setup_apath
      end


  end (* of class Otree.otree2 *)
]


(*** Build Functions ***)

let create_node data children =
  let node = new node data in
  Array.iteri 
    (fun i nd -> nd#set_parent node; nd#set_pos i) children;
  node#set_children children;
  node

let create_leaf data = create_node data [||]

let create_node2 uid_gen data children =
  let node = new node2 uid_gen data in
  Array.iteri
    (fun i nd -> nd#set_parent node; nd#set_pos i) children;
  node#set_children children;
  node#decide_collapsible_or_not;
  node

let create_leaf2 uid_gen data = create_node2 uid_gen data [||]
