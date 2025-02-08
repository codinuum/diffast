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
(* delta_base.ml *)

[%%prepare_logger]

module Xlist = Diffast_misc.Xlist
module Xset = Diffast_misc.Xset
module Xstring = Diffast_misc.Xstring
module Xprint = Diffast_misc.Xprint
module Xfile = Diffast_misc.Xfile
module Xchannel = Diffast_misc.Xchannel
module XML = Diffast_misc.XML
module Path = Diffast_misc.Path
module Elem = Path.Elem
module MID  = Moveid

let sprintf = Printf.sprintf

exception Not_element

let delta_file_name = "delta"

(* namespace should be determined automatically to avoid name conflict *)
let delta_ns = "http://codinuum.com/diffts/delta/"
let delta_prefix = "xdd"

let mktag n = sprintf "%s%s" delta_ns n

let bundle_tag = mktag "bundle"

let loc_attr = mktag "location"

let root_tag = mktag "delta"

let old_tag  = mktag "old"
let new_tag  = mktag "new"
let text_tag = mktag "text"

let del_tag  = mktag "delete"
let ins_tag  = mktag "insert"
let mov_tag  = mktag "move"
let chg_tag  = mktag "change"
let achg_tag = mktag "change_attr"
let adel_tag = mktag "delete_attr"
let ains_tag = mktag "insert_attr"

let add_file_tag    = mktag "add_file"
let remove_file_tag = mktag "remove_file"
let rename_file_tag = mktag "rename_file"
let move_file_tag   = mktag "move_file"
let change_file_tag = mktag "change_file"

let digest1_attr   = mktag "digest"
let digest2_attr   = mktag "digest_"
(*let mid_attr       = mktag "mid"*)
let path_attr      = mktag "path"
let path_from_attr = mktag "path_from"
let path_to_attr   = mktag "path_to"
let path1_attr     = mktag "path"
let path1from_attr = mktag "path_from"
let path1to_attr   = mktag "path_to"
let path2_attr     = mktag "path_"
let path2from_attr = mktag "path_from_"
let path2to_attr   = mktag "path_to_"
let mid_attr       = mktag "mid"
let bdry_attr      = mktag "boundary"
let bdry_from_attr = mktag "boundary_from"
let bdry_to_attr   = mktag "boundary_to"
let bdry1_attr     = mktag "boundary"
let bdry1from_attr = mktag "boundary_from"
let bdry1to_attr   = mktag "boundary_to"
let bdry2_attr     = mktag "boundary_"
let bdry2from_attr = mktag "boundary_from_"
let bdry2to_attr   = mktag "boundary_to_"
let attr_attr      = mktag "attr"
let ov_attr        = mktag "old_value"
let nv_attr        = mktag "new_value"
let v_attr         = mktag "value"
let rvs_attr       = mktag "reversible"
let normd_attr     = mktag "normalized"
let lang_attr      = mktag "lang"
let stid_attr      = mktag "stid"
let adj_attr       = mktag "adj"
let adj1_attr      = mktag "adj"
let adj2_attr      = mktag "adj_"
let depth_attr     = mktag "depth"
let depth1_attr    = mktag "depth"
let depth2_attr    = mktag "depth_"
let parent_attr    = mktag "parent"
let parent1_attr   = mktag "parent"
let parent2_attr   = mktag "parent_"
let shift_attr     = mktag "shift"
let shift1_attr    = mktag "shift"
let shift2_attr    = mktag "shift_"

let potential_dup_attr = mktag "potential_dup"

(* for partial application of move *)
type move_control = Mfull | MdeleteOnly | MinsertOnly

let move_control_to_string = function
  | Mfull -> "F"
  | MdeleteOnly -> "D"
  | MinsertOnly -> "I"

let move_control_of_string = function
  | "F" -> Mfull
  | "D" -> MdeleteOnly
  | "I" -> MinsertOnly
  | _ -> Mfull

let move_control_attr = mktag "mctl"

let is_file_edit_tag n =
  n = add_file_tag ||
  n = remove_file_tag ||
  n = rename_file_tag ||
  n = move_file_tag ||
  n = change_file_tag


type subtree_id = int

let stid_to_str (stid : subtree_id) = string_of_int stid
let stid_of_str s = (int_of_string s : subtree_id)

type subtree_key =
  | K_stid of subtree_id
  | K_mid of MID.t
  | K_stable
  | K_del of subtree_id

let key_of_stid stid     = K_stid stid
let key_of_mid mid       = K_mid mid
let key_stable           = K_stable
let key_of_del_stid stid = K_del stid

let is_move_key = function
  | K_mid _ -> true
  | _ -> false

let key_opt_of_stid_opt = function
  | Some stid -> Some (key_of_stid stid)
  | None -> None

let key_opt_of_mid_opt = function
  | Some mid -> Some (key_of_mid mid)
  | None -> None

let key_to_string = function
  | K_stid stid -> sprintf "stid:%s" (stid_to_str stid)
  | K_mid mid   -> sprintf "mid:%a" MID.ps mid
  | K_stable    -> "stable"
  | K_del stid -> sprintf "del:%s" (stid_to_str stid)

let key_to_raw = function
  | K_stid stid -> stid_to_str stid
  | K_mid mid   -> sprintf "m%s" (MID.to_raw mid)
  | K_stable    -> "s"
  | K_del stid -> sprintf "d%s" (stid_to_str stid)

let key_opt_to_string = function
  | Some key -> key_to_string key
  | None -> ""

let keys_to_string kl = String.concat ";" (List.map key_to_string kl)

let key_of_string s =
  if s = "s" then
    K_stable
  else if s.[0] = 'm' then
    K_mid (MID.of_string (String.sub s 1 ((String.length s) - 1)))
  else if s.[0] = 'd' then
    K_del (int_of_string (String.sub s 1 ((String.length s) - 1)))
  else
    K_stid (int_of_string s)

let path_opt_to_string = function
  | Some p -> Path.to_string p
  | None -> ""


let ups_sym = "^"
let stay_sym = "$"
let key_sep_sym = ":"
let sub_path_sep_sym = "@"

let ups_to_str upstream =
  if upstream > 0 then
    if upstream = 1 then
      ups_sym
    else
      sprintf "%s%d" ups_sym upstream
  else ""


[%%capture_path
class path_c ?(upstream=0) ?(key_opt=None) ?(stay=false) path = object (self)

  val mutable upstream = upstream
  val mutable key_opt = (key_opt : subtree_key option)
  val mutable stay = stay

  initializer
    let _ = self in
    if upstream > 0 then
      [%debug_log "upstream: %s" self#to_string]

  method set_upstream c = upstream <- c
  method upstream = upstream

  method set_key_opt k_opt = key_opt <- k_opt
  method key_opt = key_opt

  method stay = stay
  method set_stay b = stay <- b

  method path = path
  method parent_path = Path.get_parent path
  method position = Path.get_position path
  method offset = Path.get_offset path

  method has_frac_ofs = Elem.has_frac_ofs (Path.tail path)

  method to_string =
    (Path.to_string path)^
    (if stay then stay_sym else "")^
    (ups_to_str upstream)^
    (match key_opt with
    | Some key -> key_sep_sym^(key_to_raw key)
    | None -> "")
end
]

class boundary_path ?(upstream=0) ?(key_opt=None) ?(sub_path_opt=None) path =
  object
    inherit path_c ~upstream ~key_opt path as super

    val mutable sub_path_opt = sub_path_opt

    method set_sub_path_opt sp_opt = sub_path_opt <- sp_opt
    method sub_path_opt = sub_path_opt

    method! to_string =
      super#to_string^
      (match sub_path_opt with
      | Some p -> sub_path_sep_sym^(Path.to_string p)
      | None -> "")
  end


let key_sep_pat = Str.regexp_string key_sep_sym
let sub_path_sep_pat = Str.regexp_string sub_path_sep_sym
let ups_sep_pat = Str.regexp_string ups_sym

type attr    = string
type value   = string

type boundary = boundary_path list

let boundary_to_string ?(sep=";") paths =
  Xlist.to_string (fun p -> p#to_string) sep paths

let _path_of_string create s =
  try
    match Str.split ups_sep_pat s with
    | [_] -> begin
        if Xstring.endswith s ups_sym then
          let s' = String.sub s 0 ((String.length s) - 1) in
          create 1 s' false
        else if Xstring.endswith s stay_sym then
          let s' = String.sub s 0 ((String.length s) - 1) in
          create 0 s' true
        else
          create 0 s false
    end
    | [p;u] -> create (int_of_string u) p false
    | _ -> raise (Path.Invalid_path s)
  with
    _ -> raise (Path.Invalid_path s)

[%%capture_path
let path_of_string s =
  let get ?(key_opt=None) s =
    _path_of_string
      (fun u s b -> new path_c ~upstream:u ~key_opt ~stay:b (Path.of_string s))
      s
  in
  let path =
    try
      match Str.split key_sep_pat s with
      | [p] -> get p
      | [p;k] ->
          let key_opt = Some (key_of_string k) in
          get ~key_opt p

      | _ -> raise (Path.Invalid_path s)
    with
      _ -> raise (Path.Invalid_path s)
  in
  [%debug_log "%s -> %s" s path#to_string];
  path
]

let boundary_path_of_string s =
  let get ?(key_opt=None) ?(sub_path_opt=None) s =
    _path_of_string
      (fun u s _ ->
        new boundary_path ~upstream:u ~key_opt ~sub_path_opt (Path.of_string s))
      s
  in
  try
    match Str.split key_sep_pat s with
    | [p] -> get p
    | [p;kp] ->
        let key_opt, sub_path_opt =
          match Str.split sub_path_sep_pat kp with
          | [k] -> Some (key_of_string k), None
          | [k;p] -> Some (key_of_string k), Some (Path.of_string p)
          | _ -> raise (Path.Invalid_path s)
        in
        get ~key_opt ~sub_path_opt p

    | _ -> raise (Path.Invalid_path s)
  with
    _ -> raise (Path.Invalid_path s)

let semicolon_pat = Str.regexp_string ";"
let boundary_of_string boundary =
  List.map boundary_path_of_string
    (Str.split semicolon_pat boundary)



let int_opt_to_attr a int_opt =
  match int_opt with
  | Some i -> [a, string_of_int i]
  | None -> []

let key_opt_to_attr a key_opt =
  match key_opt with
  | Some key -> [a, key_to_raw key]
  | None -> []

let is_edit_tag tag =
  tag = del_tag ||
  tag = ins_tag ||
  tag = mov_tag ||
  tag = chg_tag ||
  tag = achg_tag ||
  tag = adel_tag ||
  tag = ains_tag


type err = { reason : string;
             file   : string;
             line   : int;
             col    : int;
           }

let err_to_string { reason;
                    file;
                    line;
                    col;
                  }
    =
  sprintf "[%s:%d:%d] %s" file line col reason

let mkerr xnode f r =
  let l, c = xnode#lc in
  { reason=r; file=f; line=l; col=c; }

exception Invalid_delta of err

let invalid_delta xnode ?(file="") reason =
  raise (Invalid_delta (mkerr xnode file reason))

let setup_ns_mgr ns_mgr =
  ns_mgr#add_ns delta_prefix delta_ns

[%%capture_path
let parse_file (*options*)_ ns_mgr file =
  try
    let root = XML.parse_file ~ns:ns_mgr file in
    if root#tag = root_tag then begin
      let reversible =
        try
          bool_of_string (root#get_attr rvs_attr)
        with
          _ -> false
      in
      let normalized_delta =
        try
          bool_of_string (root#get_attr normd_attr)
        with
          _ -> false
      in
      [%debug_log "reversible=%B normalized_delta=%B" reversible normalized_delta];
      root, reversible, normalized_delta
    end
    else begin
      [%debug_log "invalid element: root#tag=%s" root#tag];
      invalid_delta root "invalid element"
    end
  with
  | Failure s -> raise (Failure s)
  | Invalid_delta _ as e -> raise e
  | e ->
      failwith
        (sprintf "Delta_base.parse_file: %s" (Printexc.to_string e))
]

[%%capture_path
let parse_bundle_file (*options*)_ ns_mgr file =
  try
    let root = XML.parse_file ~ns:ns_mgr file in
    [%debug_log "root: %s" root#to_string];
    if root#tag = bundle_tag then begin
      [%debug_log "%d sub nodes found" (List.length root#children)];
      List.map
        (fun xnode ->
          let loc =
            try
              xnode#get_attr loc_attr
            with
              XML.Attr_not_found _ -> ""
          in
          loc, xnode
        ) root#children
    end
    else
      invalid_delta root ~file "not a bundle element"
  with
  | Failure s -> raise (Failure s)
  | Invalid_delta _ as e -> raise e
  | e ->
      failwith
        (sprintf "Delta_base.parse_bundle_file: %s" (Printexc.to_string e))
]

[%%capture_path
let interpret_dir_delta options dnode =
  let verbose_msg fmt = Xprint.verbose options#verbose_flag fmt in

  if dnode#tag = root_tag then begin

    let get_path ?(path_attr=path_attr) x =
      try
        Xfile.abspath
          (Filename.concat options#root_path (x#get_attr path_attr))
      with
        XML.Attr_not_found n ->
          invalid_delta x (sprintf "does not contain \"%s\" attribute" n)
    in

    dnode#iter_children
      (fun xnode ->
        let tag = xnode#tag in
        if tag = add_file_tag then begin
          let path = get_path xnode in
          verbose_msg "adding \"%s\"..." path;
          let dir = Filename.dirname path in
          if not (Xfile.dir_exists dir) then
            Xfile.mkdir dir;

          let och = open_out path in
          xnode#iter_children
            (fun dn ->
              try
                let content = Base64.decode_exn dn#data in
                output_string och content;
              with
                Invalid_argument _ -> invalid_delta dn "invalid data"
            );
          close_out och
        end
        else if tag = remove_file_tag then begin
          let path = get_path xnode in
          verbose_msg "removing \"%s\"..." path;
          Sys.remove path
        end
        else if tag = move_file_tag then begin
          let path1 = get_path ~path_attr:path_from_attr xnode in
          let path2 = get_path ~path_attr:path_to_attr xnode in
          verbose_msg "moving \"%s\" to \"%s\"..." path1 path2;
          Xfile.move path1 path2;
        end
        else if tag = change_file_tag then begin
          let path = get_path xnode in
          verbose_msg "changing \"%s\"..." path;
          let och = open_out path in
          xnode#iter_children
            (fun dn ->
              try
                let content = Base64.decode_exn dn#data in
                output_string och content;
              with
                Invalid_argument _ -> invalid_delta dn "invalid data"
            );
          close_out och
        end
      )
  end
]


let attr_to_string (a, v) = sprintf "%s=\"%s\"" a v
let attrs_to_string al = String.concat " " (List.map attr_to_string al)


(* element output functions *)

let output_string = Xchannel.output_string
let fprintf = Xchannel.fprintf

let _mkbdry bdry_attr (paths : boundary) =
  if paths = [] then
    ""
  else
    sprintf " %s=\"%s\"" bdry_attr (boundary_to_string paths)

let mkbdry      = _mkbdry bdry_attr
let mkbdry1     = _mkbdry bdry1_attr
let mkbdry2     = _mkbdry bdry2_attr
let mkbdry_from = _mkbdry bdry_from_attr
let mkbdry_to   = _mkbdry bdry_to_attr
let mkbdry1from = _mkbdry bdry1from_attr
let mkbdry1to   = _mkbdry bdry1to_attr
let mkbdry2from = _mkbdry bdry2from_attr
let mkbdry2to   = _mkbdry bdry2to_attr

let ns_decl_to_string (p, u) = sprintf " xmlns:%s=\"%s\"" p u

let ns_decls_to_string ns_decls =
  match ns_decls with
  | [] -> ""
  | _ -> String.concat "" (List.map ns_decl_to_string ns_decls)


(* for root *)
let make_st_elem_root
    ?(extra_ns_decls=[])
    ?(irreversible_flag=false)
    ?(normalized_delta_flag=false)
    lang
    digest1 digest2
    =
  sprintf "<%s%s %s%s>"
    root_tag
    (ns_decl_to_string (delta_prefix, delta_ns))
    (attrs_to_string [(rvs_attr, string_of_bool (not irreversible_flag));
                      (normd_attr, string_of_bool normalized_delta_flag);
                      (lang_attr,lang);
                      (digest1_attr,digest1);
                      (digest2_attr,digest2)])
    (ns_decls_to_string extra_ns_decls)

let output_st_elem_root
    ?(extra_ns_decls=[])
    ?(irreversible_flag=false)
    ?(normalized_delta_flag=false)
    lang
    digest1 digest2
    ch
    =
  let s =
    make_st_elem_root ~extra_ns_decls ~irreversible_flag ~normalized_delta_flag lang digest1 digest2
  in
  fprintf ch "%s" s

let ed_elem_root = sprintf "</%s>" root_tag

let output_ed_elem_root ch = fprintf ch "%s" ed_elem_root


(* for deletion *)
let output_st_elem_bi_del stid ch path paths
    path' paths' key_opt' adj_opt' depth_opt' shift_opt'
    =
  let al =
    [ stid_attr, string_of_int stid;
      path1_attr, path#to_string;
      path2_attr,  path'#to_string;
    ] @
    (key_opt_to_attr parent_attr key_opt') @
    (int_opt_to_attr adj_attr adj_opt') @
    (int_opt_to_attr depth_attr depth_opt') @
    (int_opt_to_attr shift_attr shift_opt')
  in
  fprintf ch "<%s %s%s%s>" del_tag (attrs_to_string al) (mkbdry1 paths)
    (if paths <> paths' then mkbdry2 paths' else "")

let output_st_elem_del ch path paths =
  fprintf ch "<%s %s=\"%s\"%s>" del_tag
    path_attr path#to_string
    (mkbdry paths)

let output_ed_elem_del ch = fprintf ch "</%s>" del_tag

let make_remove_file_elem path =
  sprintf "<%s %s/>" remove_file_tag (attr_to_string (path_attr, path))


(* for insertion *)
let output_st_elem_bi_ins stid ch path paths key_opt adj_opt depth_opt shift_opt
    path' paths'
    =
  let al =
    [ stid_attr, string_of_int stid;
      path1_attr, path#to_string;
    ] @
    (key_opt_to_attr parent_attr key_opt) @
    (int_opt_to_attr adj_attr adj_opt) @
    (int_opt_to_attr depth_attr depth_opt) @
    (int_opt_to_attr shift_attr shift_opt) @
    [ path2_attr, path'#to_string ]
  in
  fprintf ch "<%s %s%s%s>" ins_tag (attrs_to_string al) (mkbdry1 paths)
    (if paths <> paths' then mkbdry2 paths' else "")

let output_st_elem_ins id ch path paths key_opt adj_opt depth_opt shift_opt =
  let al =
    [ stid_attr, string_of_int id;
      path_attr, path#to_string;
    ] @
    (key_opt_to_attr parent_attr key_opt) @
    (int_opt_to_attr adj_attr adj_opt) @
    (int_opt_to_attr depth_attr depth_opt) @
    (int_opt_to_attr shift_attr shift_opt)
  in
  fprintf ch "<%s %s%s>" ins_tag (attrs_to_string al) (mkbdry paths)

let output_ed_elem_ins ch = fprintf ch "</%s>" ins_tag

let make_add_file_elem path ch =
  let buf = Buffer.create 0 in
  Buffer.add_string buf (sprintf "<%s %s>" add_file_tag (attr_to_string (path_attr, path)));
  Buffer.add_string buf (Xchannel.string_of_input_channel ch);
  Buffer.add_string buf (sprintf "</%s>" add_file_tag);
  Buffer.contents buf

let make_change_file_elem path ch =
  let buf = Buffer.create 0 in
  Buffer.add_string buf (sprintf "<%s %s>" change_file_tag (attr_to_string (path_attr, path)));
  Buffer.add_string buf (Xchannel.string_of_input_channel ch);
  Buffer.add_string buf (sprintf "</%s>" change_file_tag);
  Buffer.contents buf


(* for move *)
let output_elem_mov ch mid mctl_opt
    path_from paths_from path_to paths_to key_opt adj_opt depth_opt shift_opt
    =
  let _al =
    match mctl_opt with
    | Some mctl ->
        [ mid_attr,      MID.to_raw mid;
          move_control_attr, move_control_to_string mctl;
          path_from_attr,path_from#to_string;
          path_to_attr,  path_to#to_string;
        ]
    | None ->
        [ mid_attr,      MID.to_raw mid;
          path_from_attr,path_from#to_string;
          path_to_attr,  path_to#to_string;
        ]
  in
  let al =
    _al @
    (key_opt_to_attr parent_attr key_opt) @
    (int_opt_to_attr adj_attr adj_opt) @
    (int_opt_to_attr depth_attr depth_opt) @
    (int_opt_to_attr shift_attr shift_opt)
  in
  fprintf ch "<%s %s%s%s/>" mov_tag
    (attrs_to_string al) (mkbdry_from paths_from) (mkbdry_to paths_to)

let output_elem_bi_mov ch mid mctl_opt
    path1from paths1from path1to paths1to key_opt1 adj_opt1 depth_opt1 shift_opt1
    path2from paths2from path2to paths2to key_opt2 adj_opt2 depth_opt2 shift_opt2
    =
  let _al =
    match mctl_opt with
    | Some mctl ->
        [ mid_attr,      MID.to_raw mid;
          move_control_attr, move_control_to_string mctl;
          path1from_attr,path1from#to_string;
          path1to_attr,  path1to#to_string;
          path2from_attr,path2from#to_string;
          path2to_attr,  path2to#to_string;
        ]
    | None ->
        [ mid_attr,      MID.to_raw mid;
          path1from_attr,path1from#to_string;
          path1to_attr,  path1to#to_string;
          path2from_attr,path2from#to_string;
          path2to_attr,  path2to#to_string;
        ]
  in
  let al =
    _al @
    (key_opt_to_attr parent1_attr key_opt1) @
    (int_opt_to_attr adj1_attr adj_opt1) @
    (int_opt_to_attr depth1_attr depth_opt1) @
    (int_opt_to_attr shift1_attr shift_opt1) @
    (key_opt_to_attr parent2_attr key_opt2) @
    (int_opt_to_attr adj2_attr adj_opt2) @
    (int_opt_to_attr depth2_attr depth_opt2) @
    (int_opt_to_attr shift2_attr shift_opt2)
  in
  fprintf ch "<%s %s%s%s%s%s/>" mov_tag
    (attrs_to_string al)
    (mkbdry1from paths1from) (mkbdry1to paths1to)
    (mkbdry2from paths2from) (mkbdry2to paths2to)

let make_move_file_elem path1 path2 =
  let al = [
    path_from_attr, path1;
    path_to_attr, path2;
  ]
  in
  sprintf "<%s %s/>" move_file_tag (attrs_to_string al)


(* for change *)
let output_st_elem_bi_chg ch path1 paths1 path2 paths2 =
  fprintf ch "<%s %s%s%s>" chg_tag
    (attrs_to_string
       [ path1_attr, path1#to_string;
         path2_attr, path2#to_string;
       ])
    (mkbdry1 paths1) (mkbdry2 paths2)

let output_st_elem_chg ch path paths =
  fprintf ch "<%s %s%s>" chg_tag
    (attrs_to_string
       [ path_attr, path#to_string;
       ])
    (mkbdry paths)

let output_st_elem_old ch = fprintf ch "<%s>" old_tag
let output_ed_elem_old ch = fprintf ch "</%s>" old_tag

let output_st_elem_new ch = fprintf ch "<%s>" new_tag
let output_ed_elem_new ch = fprintf ch "</%s>" new_tag

let output_ed_elem_chg ch = fprintf ch "</%s>" chg_tag

let make_rename_file_elem path1 path2 =
  let al = [
    path_from_attr, path1;
    path_to_attr, path2;
  ]
  in
  sprintf "<%s %s/>" rename_file_tag (attrs_to_string al)


(* for attribute change *)
let mk_elem_bi_achg path1 path2 attr oldv newv =
  sprintf "<%s %s/>" achg_tag
    (attrs_to_string
       [ path1_attr, path1#to_string;
         path2_attr, path2#to_string;
         attr_attr, attr;
         ov_attr, oldv;
         nv_attr, newv;
       ])

let mk_elem_irr_achg path attr newv =
  sprintf "<%s %s/>" achg_tag
    (attrs_to_string
       [ path_attr, path#to_string;
         attr_attr, attr;
         nv_attr, newv;
       ])


(* for attribute deletion *)
let mk_elem_bi_adel path1 path2 attr v =
  sprintf "<%s %s/>" adel_tag
    (attrs_to_string
       [ path1_attr, path1#to_string;
         path2_attr, path2#to_string;
         attr_attr, attr;
         v_attr, v;
       ])

let mk_elem_irr_adel path attr =
  sprintf "<%s %s/>" adel_tag
    (attrs_to_string
       [ path_attr, path#to_string;
         attr_attr, attr;
       ])


(* for attribute insertion *)
let mk_elem_bi_ains path1 path2 attr v =
  sprintf "<%s %s/>" ains_tag
    (attrs_to_string
       [ path1_attr, path1#to_string;
         path2_attr, path2#to_string;
         attr_attr, attr;
         v_attr, v;
       ])

let mk_elem_irr_ains path attr v =
  sprintf "<%s %s/>" ains_tag
    (attrs_to_string
       [ path_attr, path#to_string;
         attr_attr, attr;
         v_attr, v;
       ])


let tbl_add tbl k v =
  try
    let l = Hashtbl.find tbl k in
    Hashtbl.replace tbl k (v::l)
  with
    Not_found -> Hashtbl.add tbl k [v]

let tbl_add_set tbl k v =
  let s =
    try
      Hashtbl.find tbl k
    with
      Not_found ->
        let s = Xset.create 1 in
        Hashtbl.add tbl k s;
        s
  in
  Xset.add s v

let tbl_add_tbl tbl0 k0 k1 v =
  let tbl1 =
    try
      Hashtbl.find tbl0 k0
    with
      Not_found ->
        let t = Hashtbl.create 0 in
        Hashtbl.add tbl0 k0 t;
        t
  in
  let b =
    try
      v <> (Hashtbl.find tbl1 k1)
    with
      Not_found -> true
  in
  if b then
    Hashtbl.add tbl1 k1 v

let tbl_add_tbl_list tbl0 k0 k1 v =
  let tbl1 =
    try
      Hashtbl.find tbl0 k0
    with
      Not_found ->
        let t = Hashtbl.create 0 in
        Hashtbl.add tbl0 k0 t;
        t
  in
  try
    let l = Hashtbl.find tbl1 k1 in
    if not (List.mem v l) then
      Hashtbl.replace tbl1 k1 (v::l)
  with
    Not_found ->
      Hashtbl.add tbl1 k1 [v]


let tbl_add_tbl2 tbl0 k0 k1 k2 v =
  let tbl1 =
    try
      Hashtbl.find tbl0 k0
    with
      Not_found ->
        let t = Hashtbl.create 0 in
        Hashtbl.add tbl0 k0 t;
        t
  in
  let tbl2 =
    try
      Hashtbl.find tbl1 k1
    with
      Not_found ->
        let t = Hashtbl.create 0 in
        Hashtbl.add tbl1 k1 t;
        t
  in
  let b =
    try
      v <> (Hashtbl.find tbl2 k2)
    with
      Not_found -> true
  in
  if b then
    Hashtbl.add tbl2 k2 v

let tbl_add_tbl2_list tbl0 k0 k1 k2 v =
  let tbl1 =
    try
      Hashtbl.find tbl0 k0
    with
      Not_found ->
        let t = Hashtbl.create 0 in
        Hashtbl.add tbl0 k0 t;
        t
  in
  let tbl2 =
    try
      Hashtbl.find tbl1 k1
    with
      Not_found ->
        let t = Hashtbl.create 0 in
        Hashtbl.add tbl1 k1 t;
        t
  in
  try
    let l = Hashtbl.find tbl2 k2 in
    if not (List.mem v l) then
      Hashtbl.replace tbl2 k2 (v::l)
  with
    Not_found ->
      Hashtbl.add tbl2 k2 [v]


let sort_paths paths =
  let tbl = Hashtbl.create 0 in
  List.iter
    (fun path ->
      let parent, elem = Path.split path in
      tbl_add tbl parent (path, elem)
    ) paths;
  let sorted, _ =
    List.split
      (List.flatten
         (Hashtbl.fold
            (fun _ p_e_list l ->
              (List.fast_sort
                 (fun (_, e) (_, e') ->
                   Stdlib.compare e.Elem.ofs e'.Elem.ofs
                 ) p_e_list) :: l
            ) tbl []))
  in
  sorted



type content_dumper = Xchannel.out_channel -> unit


module Fmt = struct

  module Irr = struct
    type t =
      | Del of path_c * boundary

      | Ins of subtree_id * path_c * boundary
            * subtree_key option * int option * int option * int option
            * content_dumper

      | Mov of MID.t
            * move_control option
            * path_c * boundary * path_c * boundary
            * subtree_key option * int option * int option * int option

      | Chg of path_c * boundary * content_dumper

      | ChgAttr of path_c * attr * value
      | DelAttr of path_c * attr
      | InsAttr of path_c * attr * value

    let mkdel path paths =
      Del(path, paths)

    let mkins stid path paths key_opt adj_opt depth_opt shift_opt dumper =
      Ins(stid, path, paths, key_opt, adj_opt, depth_opt, shift_opt, dumper)

    let mkmov mid mctl_opt path_from paths_from path_to paths_to
        key_opt adj_opt depth_opt shift_opt =
      Mov(mid, mctl_opt, path_from, paths_from, path_to, paths_to,
          key_opt, adj_opt, depth_opt, shift_opt)

    let mkchg path paths dumper =
      Chg(path, paths, dumper)

    let mkchgattr path attr value =
      ChgAttr(path, attr, value)

    let mkdelattr path attr =
      DelAttr(path, attr)

    let mkinsattr path attr value =
      InsAttr(path, attr, value)

    let output ch = function
      | Del(path, paths) ->
          output_st_elem_del ch path paths;
          output_ed_elem_del ch

      | Ins(stid, path, paths, key_opt, adj_opt, depth_opt, shift_opt, dumper) ->
          output_st_elem_ins stid ch
            path paths key_opt adj_opt depth_opt shift_opt;
          dumper ch;
          output_ed_elem_ins ch

      | Mov(mid, mctl_opt, path_from, paths_from, path_to, paths_to,
            key_opt, adj_opt, depth_opt, shift_opt) ->
              output_elem_mov ch mid mctl_opt
                path_from paths_from path_to paths_to
                key_opt adj_opt depth_opt shift_opt

      | Chg(path, paths, dumper) ->
          output_st_elem_chg ch path paths;
          dumper ch;
          output_ed_elem_chg ch

      | ChgAttr(path, attr, value) ->
          fprintf ch "%s" (mk_elem_irr_achg path attr value)

      | DelAttr(path, attr) ->
          fprintf ch "%s" (mk_elem_irr_adel path attr)

      | InsAttr(path, attr, value) ->
          fprintf ch "%s" (mk_elem_irr_ains path attr value)

  end (* module Irr *)

  module Rev = struct
    type t =
      | Del of subtree_id
            * path_c * boundary
            * path_c * boundary
            * subtree_key option * int option * int option * int option
            * content_dumper

      | Ins of subtree_id
            * path_c * boundary
            * subtree_key option * int option * int option * int option
            * content_dumper
            * path_c * boundary

      | Mov of MID.t
            * move_control option
            * path_c * boundary * path_c * boundary
            * subtree_key option * int option * int option * int option
            * path_c * boundary * path_c * boundary
            * subtree_key option * int option * int option * int option

      | Chg of path_c * boundary
            * path_c * boundary
            * content_dumper

      | ChgAttr of path_c * attr * value * path_c * value
      | DelAttr of path_c * attr * path_c * value
      | InsAttr of path_c * attr * value * path_c

    let mkdel stid path paths
        path' paths' key_opt' adj_opt' depth_opt' shift_opt' dumper' =
      Del(stid, path, paths,
          path', paths', key_opt', adj_opt', depth_opt', shift_opt', dumper')

    let mkins stid path paths key_opt adj_opt depth_opt shift_opt dumper
        path' paths' =
      Ins(stid, path, paths, key_opt, adj_opt, depth_opt, shift_opt, dumper,
          path', paths')

    let mkmov mid
        mctl_opt
        path_from paths_from path_to paths_to
        key_opt adj_opt depth_opt shift_opt
        path_from' paths_from' path_to' paths_to'
        key_opt' adj_opt' depth_opt' shift_opt' =
      Mov(mid, mctl_opt, path_from, paths_from, path_to, paths_to,
          key_opt, adj_opt, depth_opt, shift_opt,
          path_from', paths_from', path_to', paths_to',
          key_opt', adj_opt', depth_opt', shift_opt')

    let mkchg path paths path' paths' dumper =
      Chg(path, paths, path', paths', dumper)

    let mkchgattr path attr value path' value' =
      ChgAttr(path, attr, value, path', value')

    let mkdelattr path attr path' value' =
      DelAttr(path, attr, path', value')

    let mkinsattr path attr value path' =
      InsAttr(path, attr, value, path')

    let output ch = function
      | Del(stid, path, paths,
            path', paths', key_opt', adj_opt', depth_opt', shift_opt', dumper')
        ->
          output_st_elem_bi_del stid ch path paths
            path' paths' key_opt' adj_opt' depth_opt' shift_opt';
          dumper' ch;
          output_ed_elem_del ch

      | Ins(stid, path, paths, key_opt, adj_opt, depth_opt, shift_opt, dumper,
            path', paths')
        ->
          output_st_elem_bi_ins stid ch
            path paths key_opt adj_opt depth_opt shift_opt path' paths';
          dumper ch;
          output_ed_elem_ins ch

      | Mov(mid, mctl_opt, path_from, paths_from, path_to, paths_to,
            key_opt, adj_opt, depth_opt, shift_opt,
            path_from', paths_from', path_to', paths_to',
            key_opt', adj_opt', depth_opt', shift_opt')
        ->
          output_elem_bi_mov ch mid mctl_opt
            path_from paths_from path_to paths_to
            key_opt adj_opt depth_opt shift_opt
            path_from' paths_from' path_to' paths_to'
            key_opt' adj_opt' depth_opt' shift_opt'

      | Chg(path, paths, path', paths', dumper) ->
          output_st_elem_bi_chg ch path paths path' paths';
          dumper ch;
          output_ed_elem_chg ch

      | ChgAttr(path, attr, value, path', value') ->
          fprintf ch "%s" (mk_elem_bi_achg path path' attr value value')

      | DelAttr(path, attr, path', value') ->
          fprintf ch "%s" (mk_elem_bi_adel path path' attr value')

      | InsAttr(path, attr, value, path') ->
          fprintf ch "%s" (mk_elem_bi_ains path path' attr value)

    let reverse = function
      | Del(stid, path, paths,
            path', paths', key_opt', adj_opt', depth_opt', shift_opt', dumper')
        ->
          Ins(stid, path', paths', key_opt', adj_opt', depth_opt', shift_opt', dumper',
              path, paths)

      | Ins(stid, path, paths, key_opt, adj_opt, depth_opt, shift_opt, dumper,
            path', paths')
        ->
          Del(stid, path', paths',
              path, paths, key_opt, adj_opt, depth_opt, shift_opt, dumper)

      | Mov(mid, mctl_opt, path_from, paths_from, path_to, paths_to,
            key_opt, adj_opt, depth_opt, shift_opt,
            path_from', paths_from', path_to', paths_to',
            key_opt', adj_opt', depth_opt', shift_opt')
        ->
          Mov(mid, mctl_opt, path_from', paths_from', path_to', paths_to',
              key_opt', adj_opt', depth_opt', shift_opt',
              path_from, paths_from, path_to, paths_to,
              key_opt, adj_opt, depth_opt, shift_opt)

      | Chg(path, paths, path', paths', dumper) -> Chg(path', paths', path, paths, dumper)

      | ChgAttr(path, attr, value, path', value') -> ChgAttr(path', attr, value', path, value)

      | DelAttr(path, attr, path', value') -> InsAttr(path', attr, value', path)

      | InsAttr(path, attr, value, path') -> DelAttr(path', attr, path, value)


  end (* module Rev *)

  type t = Irr of Irr.t | Rev of Rev.t

  let make_path_key path =
    Path.strip (Path.get_parent path)

  class ['node_t] node_tbl = object
    val tbl = (Hashtbl.create 0 : (Path.t, 'node_t) Hashtbl.t)
    method reg key nd = Hashtbl.add tbl key nd
    method find key = Hashtbl.find tbl key
  end

  class ['node_t] edit_tbl nd_tbl = object
    val tbl = (Hashtbl.create 0 : (Path.t, t list) Hashtbl.t)

    method reg (nd : 'node_t) (path : path_c) fmt =
      match fmt with
      | Irr (Irr.Del _|Irr.Ins _|Irr.Mov _)
      | Rev (Rev.Del _|Rev.Ins _|Rev.Mov _) ->
          let key = make_path_key path#path in
          tbl_add tbl key fmt;
          nd_tbl#reg key nd
      | _ -> ()

    method find key =
      try
        Hashtbl.find tbl key
      with
        Not_found -> []
  end

  let to_string fmt =
    let buf = Buffer.create 0 in
    let ch = new Xchannel.out_channel (Xchannel.D.of_buffer buf) in
    begin
      match fmt with
      | Irr fmt -> Irr.output ch fmt
      | Rev fmt -> Rev.output ch fmt
    end;
    Buffer.contents buf

  let sort_attrs attrs =
    List.sort (fun (n1, _) (n2, _) -> Stdlib.compare n1 n2) attrs

[%%capture_path
  let diff_attrs ?(irreversible_flag=false) path1 attrs1 path2 attrs2 =
    let sorted_attrs1 = sort_attrs attrs1 in
    let sorted_attrs2 = sort_attrs attrs2 in
    [%debug_log "sorted1=[%s]" (String.concat ";" (List.map attr_to_string sorted_attrs1))];
    [%debug_log "sorted2=[%s]" (String.concat ";" (List.map attr_to_string sorted_attrs2))];
    let sorted1 = Array.of_list sorted_attrs1 in
    let sorted2 = Array.of_list sorted_attrs2 in
    let a1 = Array.map (fun (n, _) -> n) sorted1 in
    let a2 = Array.map (fun (n, _) -> n) sorted2 in
    let mat, rel, del, ins = Adiff.adiff a1 a2 in
    let del', ins' =
      let d, i = List.split rel in
      d @ del, i @ ins
    in
    let res = ref [] in
    List.iter
      (fun (i, j) ->
        let _, v1 = sorted1.(i) in
        let _, v2 = sorted2.(j) in
        if v1 <> v2 then
          let e =
            if irreversible_flag then
              Irr (Irr.mkchgattr path1 a1.(i) v2)
            else
              Rev (Rev.mkchgattr path1 a1.(i) v1 path2 v2)
          in
          [%debug_log "%s" (to_string e)];
          res := e::!res
      ) mat;
    List.iter
      (fun i ->
        let e =
          if irreversible_flag then
            Irr (Irr.mkdelattr path1 a1.(i))
          else
            Rev (Rev.mkdelattr path1 a1.(i) path2 (snd sorted1.(i)))
        in
        [%debug_log "%s" (to_string e)];
        res := e::!res
      ) del';
    List.iter
      (fun j ->
        let e =
          if irreversible_flag then
            Irr (Irr.mkinsattr path1 a2.(j) (snd sorted2.(j)))
          else
            Rev (Rev.mkinsattr path1 a2.(j) (snd sorted2.(j)) path2)
        in
        [%debug_log "%s" (to_string e)];
        res := e::!res
      ) ins';
    !res
]

  let dump ch = function
    | Irr fmt -> Irr.output ch fmt
    | Rev fmt -> Rev.output ch fmt

  let reverse fmt =
    match fmt with
    | Irr _ -> fmt
    | Rev rev_fmt -> Rev (Rev.reverse rev_fmt)

end (* module Fmt *)
